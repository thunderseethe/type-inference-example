#![allow(dead_code)]
use std::collections::{BTreeSet, HashSet};

use ena::unify::InPlaceUnificationTable;

use self::ast::{Ast, TypedVar, Var};
use self::subst::SubstOut;
use self::ty::{Row, RowEquation, RowVar, Type, TypeVar};
use self::unification::TypeError;

mod ast {
    use crate::ty::Type;

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
    pub struct Var(pub usize);

    #[derive(PartialEq, Eq, Clone, Debug)]
    pub struct TypedVar(pub Var, pub Type);

    /// Our labels are strings, but we could imagine in a production grade compiler labels would be
    /// interned and represented by their intern token.
    pub type Label = String;

    /// Direction of our row for Project and Inject.
    /// Determines where our value shows up in our row equation (in the left or right slot).
    #[derive(Debug, PartialEq, Eq)]
    pub enum Direction {
        Left,
        Right,
    }

    /// Our Abstract syntax tree
    /// The lambda calculus + integer literals.
    #[derive(Debug, PartialEq, Eq)]
    pub enum Ast<V> {
        /// A local variable
        Var(V),
        /// An integer literal
        Int(isize),
        /// A function literal (lambda, closure).
        Fun(V, Box<Self>),
        /// Function application
        App(Box<Self>, Box<Self>),
        // --- Row Nodes ---
        // Label a node turning it into a singleton row
        Label(Label, Box<Self>),
        // Unwrap a singleton row into it's underlying value
        Unlabel(Box<Self>, Label),
        // Concat two products
        Concat(Box<Self>, Box<Self>),
        // Project a product into a sub product
        Project(Direction, Box<Self>),
        // Branch on a sum type to two handler functions
        Branch(Box<Self>, Box<Self>),
        // Inject a value into a sum type
        Inject(Direction, Box<Self>),
    }

    impl<V> Ast<V> {
        pub fn fun(arg: V, body: Self) -> Self {
            Self::Fun(arg, Box::new(body))
        }

        pub fn app(fun: Self, arg: Self) -> Self {
            Self::App(Box::new(fun), Box::new(arg))
        }

        pub fn label(label: impl ToString, value: Self) -> Self {
            Self::Label(label.to_string(), Box::new(value))
        }

        pub fn unlabel(value: Self, label: impl ToString) -> Self {
            Self::Unlabel(Box::new(value), label.to_string())
        }

        pub fn project(dir: Direction, value: Self) -> Self {
            Self::Project(dir, Box::new(value))
        }

        pub fn concat(left: Self, right: Self) -> Self {
            Self::Concat(Box::new(left), Box::new(right))
        }

        pub fn inject(dir: Direction, value: Self) -> Self {
            Self::Inject(dir, Box::new(value))
        }

        pub fn branch(left: Self, right: Self) -> Self {
            Self::Branch(Box::new(left), Box::new(right))
        }
    }
}

mod ty {
    use std::collections::HashSet;

    use ena::unify::{EqUnifyValue, UnifyKey};

    use crate::ast::Label;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct ClosedRow {
        pub fields: Vec<Label>,
        pub values: Vec<Type>,
    }
    impl ClosedRow {
        /// Merge two disjoint rows into a new row.
        pub fn merge(left: ClosedRow, right: ClosedRow) -> ClosedRow {
            let mut left_fields = left.fields.into_iter().peekable();
            let mut left_values = left.values.into_iter();
            let mut right_fields = right.fields.into_iter().peekable();
            let mut right_values = right.values.into_iter();

            let mut fields = vec![];
            let mut values = vec![];

            // Since our input rows are already sorted we can explit that and not worry about resorting
            // them here, we just have to merge our two sorted rows.
            loop {
                match (left_fields.peek(), right_fields.peek()) {
                    (Some(left), Some(right)) => {
                        if left <= right {
                            fields.push(left_fields.next().unwrap());
                            values.push(left_values.next().unwrap());
                        } else {
                            fields.push(right_fields.next().unwrap());
                            values.push(right_values.next().unwrap());
                        }
                    }
                    (Some(_), None) => {
                        fields.extend(left_fields);
                        values.extend(left_values);
                        break;
                    }
                    (None, Some(_)) => {
                        fields.extend(right_fields);
                        values.extend(right_values);
                        break;
                    }
                    (None, None) => {
                        break;
                    }
                }
            }

            ClosedRow { fields, values }
        }

        /// Check if our closed row mentions any of our unbound types or rows.
        pub fn mentions(
            &self,
            unbound_tys: &HashSet<TypeVar>,
            unbound_rows: &HashSet<RowVar>,
        ) -> bool {
            for ty in self.values.iter() {
                if ty.mentions(unbound_tys, unbound_rows) {
                    return true;
                }
            }
            false
        }
    }
    impl EqUnifyValue for ClosedRow {}

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Row {
        Open(RowVar),
        Closed(ClosedRow),
    }
    impl Row {
        pub fn single(lbl: Label, ty: Type) -> Self {
            Row::Closed(ClosedRow {
                fields: vec![lbl],
                values: vec![ty],
            })
        }

        /// This is not strcit equality (like we get with Eq).
        /// This instead checks a looser sense of equality
        /// that is helpful during unification.
        pub fn equatable(&self, other: &Self) -> bool {
            match (self, other) {
                // Open rows are equatable when their variables are equal
                (Row::Open(a), Row::Open(b)) => a == b,
                // Closed rows are equatable when their fields are equal
                (Row::Closed(a), Row::Closed(b)) => a.fields == b.fields,
                // Anything else is not equatable
                _ => false,
            }
        }
    }

    /// Our type
    /// Each AST node in our input will be annotated by a value of `Type`
    /// after type inference succeeeds.
    #[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord)]
    pub enum Type {
        /// Type of integers
        Int,
        /// A type variable, stands for a value of Type
        Var(TypeVar),
        /// A function type
        Fun(Box<Self>, Box<Self>),
        /// A product type
        Prod(Row),
        /// A sum type
        Sum(Row),
        /// Type of singleton rows
        Label(Label, Box<Self>),
    }
    impl EqUnifyValue for Type {}
    impl Type {
        pub fn fun(arg: Self, ret: Self) -> Self {
            Self::Fun(Box::new(arg), Box::new(ret))
        }

        pub fn label(label: Label, value: Self) -> Self {
            Self::Label(label, Box::new(value))
        }

        pub fn occurs_check(&self, var: TypeVar) -> Result<(), Type> {
            match self {
                Type::Int => Ok(()),
                Type::Var(v) => {
                    if *v == var {
                        Err(Type::Var(*v))
                    } else {
                        Ok(())
                    }
                }
                Type::Fun(arg, ret) => {
                    arg.occurs_check(var).map_err(|_| self.clone())?;
                    ret.occurs_check(var).map_err(|_| self.clone())
                }
                Type::Label(_, ty) => ty.occurs_check(var).map_err(|_| self.clone()),
                Type::Prod(row) | Type::Sum(row) => match row {
                    Row::Open(_) => Ok(()),
                    Row::Closed(closed_row) => {
                        for ty in closed_row.values.iter() {
                            ty.occurs_check(var).map_err(|_| self.clone())?
                        }
                        Ok(())
                    }
                },
            }
        }

        pub fn mentions(
            &self,
            unbound_tys: &HashSet<TypeVar>,
            unbound_rows: &HashSet<RowVar>,
        ) -> bool {
            match self {
                Type::Int => false,
                Type::Var(v) => unbound_tys.contains(v),
                Type::Fun(arg, ret) => {
                    arg.mentions(unbound_tys, unbound_rows)
                        || ret.mentions(unbound_tys, unbound_rows)
                }
                Type::Label(_, ty) => ty.mentions(unbound_tys, unbound_rows),
                Type::Prod(row) | Type::Sum(row) => match row {
                    Row::Open(var) => unbound_rows.contains(var),
                    Row::Closed(row) => row.mentions(unbound_tys, unbound_rows),
                },
            }
        }
    }

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
    pub struct RowVar(pub u32);
    impl UnifyKey for RowVar {
        type Value = Option<ClosedRow>;

        fn index(&self) -> u32 {
            self.0
        }

        fn from_index(u: u32) -> Self {
            Self(u)
        }

        fn tag() -> &'static str {
            "TypeVar"
        }
    }

    #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
    pub struct TypeVar(pub u32);
    impl UnifyKey for TypeVar {
        type Value = Option<Type>;

        fn index(&self) -> u32 {
            self.0
        }

        fn from_index(u: u32) -> Self {
            Self(u)
        }

        fn tag() -> &'static str {
            "TypeVar"
        }
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
    pub struct RowEquation {
        pub left: Row,
        pub right: Row,
        pub goal: Row,
    }
    impl RowEquation {
        /// Two rows are unifiable if two of their components are equatable.
        /// A row can be uniquely determined by two of it's components (the third is calculated from
        /// the two). Because of this whenever rows agree on two components we can unify both rows and
        /// possible learn new information about the third row.
        ///
        /// This only works because our row equations are commutative.
        pub fn is_unifiable(&self, other: &Self) -> bool {
            let left_equatable = self.left.equatable(&other.left);
            let right_equatable = self.right.equatable(&other.right);
            let goal_equatable = self.goal.equatable(&other.goal);
            (goal_equatable && (left_equatable || right_equatable))
                || (left_equatable && right_equatable)
        }

        /// Check unifiability the same way as `is_unifiable` but commutes the arguments.
        /// So we check left against right, and right against left. Goal is still checked against goal.
        pub fn is_comm_unifiable(&self, other: &Self) -> bool {
            let left_equatable = self.left.equatable(&other.right);
            let right_equatable = self.right.equatable(&other.left);
            let goal_equatable = self.goal.equatable(&other.goal);
            (goal_equatable && (left_equatable || right_equatable))
                || (left_equatable && right_equatable)
        }
    }
}

/// Our constraints
/// Right now this is just type equality but it will be more substantial later
#[derive(Debug)]
pub enum Constraint {
    TypeEqual(Type, Type),
    RowConcat(RowEquation),
}

/// Type inference
/// This struct holds some commong state that will useful to share between our stages of type
/// inference.
pub struct TypeInference {
    unification_table: InPlaceUnificationTable<TypeVar>,
    row_unification_table: InPlaceUnificationTable<RowVar>,
    partial_row_eqns: BTreeSet<RowEquation>,
}

mod infer {
    use std::ops::Deref;

    use crate::ast::{Ast, Direction, TypedVar, Var};
    use crate::ty::{Row, RowEquation, RowVar, Type, TypeVar};
    use crate::{Constraint, TypeInference};

    pub struct InferOut {
        pub constraints: Vec<Constraint>,
        pub typed_ast: Ast<TypedVar>,
    }
    impl InferOut {
        fn with_typed_ast(self, f: impl FnOnce(Ast<TypedVar>) -> Ast<TypedVar>) -> Self {
            InferOut {
                constraints: self.constraints,
                typed_ast: f(self.typed_ast),
            }
        }
    }

    impl InferOut {
        fn new(constraints: Vec<Constraint>, typed_ast: Ast<TypedVar>) -> Self {
            Self {
                constraints,
                typed_ast,
            }
        }
    }

    /// Constraint generation
    impl TypeInference {
        /// Create a unique type variable
        fn fresh_ty_var(&mut self) -> TypeVar {
            self.unification_table.new_key(None)
        }

        /// Create a unique row variable
        fn fresh_row_var(&mut self) -> RowVar {
            self.row_unification_table.new_key(None)
        }

        /// Create a row equation with fresh row variables
        fn fresh_row_equation(&mut self) -> RowEquation {
            RowEquation {
                left: Row::Open(self.fresh_row_var()),
                right: Row::Open(self.fresh_row_var()),
                goal: Row::Open(self.fresh_row_var()),
            }
        }

        /// Infer type of `ast`
        /// Returns a list of constraints that need to be true and the type `ast` will have if
        /// constraints hold.
        pub(crate) fn infer(
            &mut self,
            env: im::HashMap<Var, Type>,
            ast: Ast<Var>,
        ) -> (InferOut, Type) {
            match ast {
                Ast::Int(i) => (InferOut::new(vec![], Ast::Int(i)), Type::Int),
                Ast::Var(v) => {
                    let ty = &env[&v];
                    (
                        InferOut::new(vec![], Ast::Var(TypedVar(v, ty.clone()))),
                        ty.clone(),
                    )
                }
                Ast::Fun(arg, body) => {
                    let arg_ty_var = self.fresh_ty_var();
                    let env = env.update(arg, Type::Var(arg_ty_var));
                    let (body_out, body_ty) = self.infer(env, *body);
                    (
                        InferOut {
                            typed_ast: Ast::fun(
                                TypedVar(arg, Type::Var(arg_ty_var)),
                                body_out.typed_ast,
                            ),
                            ..body_out
                        },
                        Type::fun(Type::Var(arg_ty_var), body_ty),
                    )
                }
                Ast::App(fun, arg) => {
                    let (arg_out, arg_ty) = self.infer(env.clone(), *arg);

                    let ret_ty = Type::Var(self.fresh_ty_var());
                    let fun_ty = Type::fun(arg_ty, ret_ty.clone());

                    let fun_out = self.check(env, *fun, fun_ty);

                    (
                        InferOut::new(
                            arg_out
                                .constraints
                                .into_iter()
                                .chain(fun_out.constraints.into_iter())
                                .collect(),
                            Ast::app(fun_out.typed_ast, arg_out.typed_ast),
                        ),
                        ret_ty,
                    )
                }
                // Labeling
                Ast::Label(label, value) => {
                    let (out, value_ty) = self.infer(env, *value);
                    (
                        out.with_typed_ast(|ast| Ast::label(label.clone(), ast)),
                        Type::label(label, value_ty),
                    )
                }
                Ast::Unlabel(value, label) => {
                    let value_var = self.fresh_ty_var();
                    let expected_ty = Type::label(label, Type::Var(value_var));
                    (self.check(env, *value, expected_ty), Type::Var(value_var))
                }
                // Products
                Ast::Concat(left, right) => {
                    let row_eqn = self.fresh_row_equation();

                    // Concat combines two smaller rows into a larger row.
                    // To check this we check that our inputs have the types of our smaller rows left
                    // and right.
                    let left_out = self.check(env.clone(), *left, Type::Prod(row_eqn.left.clone()));
                    let right_out = self.check(env, *right, Type::Prod(row_eqn.right.clone()));

                    // If they do, then our output type is our big row goal
                    let out_ty = Type::Prod(row_eqn.goal.clone());
                    let mut constraints = left_out.constraints;
                    constraints.extend(right_out.constraints);
                    // Add a new constraint for our row equation to solve concat
                    constraints.push(Constraint::RowConcat(row_eqn));

                    (
                        InferOut {
                            constraints,
                            typed_ast: Ast::concat(left_out.typed_ast, right_out.typed_ast),
                        },
                        out_ty,
                    )
                }
                Ast::Project(dir, goal) => {
                    let row_eqn = self.fresh_row_equation();
                    // Based on the direction of our projection,
                    // our output row is either left or right
                    let sub_row = match dir {
                        Direction::Left => row_eqn.left.clone(),
                        Direction::Right => row_eqn.right.clone(),
                    };
                    // Project transforms a row into a subset of its fields, so we check our goal ast
                    // node against our goal row (not our sub_row)
                    let mut out = self.check(env, *goal, Type::Prod(row_eqn.goal.clone()));
                    // Add our row equation constraint to solve our projection
                    out.constraints.push(Constraint::RowConcat(row_eqn));
                    (
                        out.with_typed_ast(|ast| Ast::project(dir, ast)),
                        // Our sub row is the output type of the projection
                        Type::Prod(sub_row),
                    )
                }
                // Sums
                Ast::Branch(left, right) => {
                    let row_eqn = self.fresh_row_equation();
                    let ret_ty = self.fresh_ty_var();

                    // Branch expects it's two inputs to be handling functions
                    // with type: <sum> -> a
                    // So we check that our left and right AST both have handler function types that
                    // agree on return type
                    let left_out = self.check(
                        env.clone(),
                        *left,
                        Type::fun(Type::Sum(row_eqn.left.clone()), Type::Var(ret_ty)),
                    );
                    let right_out = self.check(
                        env,
                        *right,
                        Type::fun(Type::Sum(row_eqn.right.clone()), Type::Var(ret_ty)),
                    );

                    // If they do the overall type of our Branch node is a function from our goal row
                    // sum type to our return type
                    let out_ty = Type::fun(Type::Sum(row_eqn.goal.clone()), Type::Var(ret_ty));
                    // Collect all our constraints for our final output
                    let mut constraints = left_out.constraints;
                    constraints.extend(right_out.constraints);
                    constraints.push(Constraint::RowConcat(row_eqn));

                    (
                        InferOut {
                            constraints,
                            typed_ast: Ast::branch(left_out.typed_ast, right_out.typed_ast),
                        },
                        out_ty,
                    )
                }
                Ast::Inject(dir, value) => {
                    let row_eqn = self.fresh_row_equation();
                    // Like project, inject works in terms of sub rows and goal rows.
                    // But inject is _injecting_ a smaller row into a bigger row.
                    let sub_row = match dir {
                        Direction::Left => row_eqn.left.clone(),
                        Direction::Right => row_eqn.right.clone(),
                    };

                    let out_ty = Type::Sum(row_eqn.goal.clone());
                    // Because of this our sub row is the type of our value
                    let mut out = self.check(env, *value, Type::Sum(sub_row));
                    out.constraints.push(Constraint::RowConcat(row_eqn));
                    (
                        out.with_typed_ast(|ast| Ast::inject(dir, ast)),
                        // Our goal row is the type of our output
                        out_ty,
                    )
                }
            }
        }

        fn check(&mut self, env: im::HashMap<Var, Type>, ast: Ast<Var>, ty: Type) -> InferOut {
            match (ast, ty) {
                (Ast::Int(i), Type::Int) => InferOut::new(vec![], Ast::Int(i)),
                (Ast::Fun(arg, body), Type::Fun(arg_ty, ret_ty)) => {
                    let env = env.update(arg, *arg_ty);
                    self.check(env, *body, *ret_ty)
                }
                (ast @ Ast::Concat(_, _), Type::Label(lbl, ty))
                | (ast @ Ast::Project(_, _), Type::Label(lbl, ty)) => {
                    // Cast a singleton row into a product
                    self.check(env, ast, Type::Prod(Row::single(lbl, *ty)))
                }
                (ast @ Ast::Branch(_, _), Type::Label(lbl, ty))
                | (ast @ Ast::Inject(_, _), Type::Label(lbl, ty)) => {
                    // Cast a singleton row into a sum
                    self.check(env, ast, Type::Sum(Row::single(lbl, *ty)))
                }
                (Ast::Concat(left, right), Type::Prod(goal_row)) => {
                    let left_row = Row::Open(self.fresh_row_var());
                    let right_row = Row::Open(self.fresh_row_var());

                    let left_out = self.check(env.clone(), *left, Type::Prod(left_row.clone()));
                    let right_out = self.check(env, *right, Type::Prod(right_row.clone()));

                    let mut constraints = left_out.constraints;
                    constraints.extend(right_out.constraints);
                    constraints.push(Constraint::RowConcat(RowEquation {
                        left: left_row,
                        right: right_row,
                        goal: goal_row,
                    }));

                    InferOut {
                        constraints,
                        typed_ast: Ast::concat(left_out.typed_ast, right_out.typed_ast),
                    }
                }
                (Ast::Project(dir, goal), Type::Prod(sub_row)) => {
                    let goal_row = Row::Open(self.fresh_row_var());

                    let (left, right) = match dir {
                        Direction::Left => (sub_row, Row::Open(self.fresh_row_var())),
                        Direction::Right => (Row::Open(self.fresh_row_var()), sub_row),
                    };

                    let mut out = self.check(env, *goal, Type::Prod(goal_row.clone()));
                    out.constraints.push(Constraint::RowConcat(RowEquation {
                        left,
                        right,
                        goal: goal_row,
                    }));

                    out.with_typed_ast(|ast| Ast::project(dir, ast))
                }
                (Ast::Branch(left_ast, right_ast), Type::Fun(arg_ty, ret_ty)) => {
                    let mut constraints = vec![];
                    let goal = match arg_ty.deref() {
                        Type::Sum(goal) => goal.clone(),
                        _ => {
                            let goal = self.fresh_row_var();
                            constraints
                                .push(Constraint::TypeEqual(*arg_ty, Type::Sum(Row::Open(goal))));
                            Row::Open(goal)
                        }
                    };
                    let left = Row::Open(self.fresh_row_var());
                    let right = Row::Open(self.fresh_row_var());

                    let left_out = self.check(
                        env.clone(),
                        *left_ast,
                        Type::fun(Type::Sum(left.clone()), ret_ty.deref().clone()),
                    );
                    let right_out = self.check(
                        env,
                        *right_ast,
                        Type::fun(Type::Sum(right.clone()), *ret_ty),
                    );

                    constraints.extend(left_out.constraints);
                    constraints.extend(right_out.constraints);
                    constraints.push(Constraint::RowConcat(RowEquation { left, right, goal }));

                    InferOut {
                        constraints,
                        typed_ast: Ast::branch(left_out.typed_ast, right_out.typed_ast),
                    }
                }
                (Ast::Inject(dir, value), Type::Sum(goal)) => {
                    let sub_row = self.fresh_row_var();
                    let mut out = self.check(env, *value, Type::Sum(Row::Open(sub_row)));
                    let row_eqn = match dir {
                        Direction::Left => RowEquation {
                            left: Row::Open(sub_row),
                            right: Row::Open(self.fresh_row_var()),
                            goal,
                        },
                        Direction::Right => RowEquation {
                            left: Row::Open(self.fresh_row_var()),
                            right: Row::Open(sub_row),
                            goal,
                        },
                    };
                    out.constraints.push(Constraint::RowConcat(row_eqn));
                    out.with_typed_ast(|ast| Ast::inject(dir, ast))
                }
                (ast, expected_ty) => {
                    let (mut out, actual_ty) = self.infer(env, ast);
                    out.constraints
                        .push(Constraint::TypeEqual(expected_ty, actual_ty));
                    out
                }
            }
        }
    }
}

mod unification {
    use crate::ty::{ClosedRow, Row, RowEquation, RowVar, Type, TypeVar};
    use crate::{Constraint, TypeInference};

    #[derive(Debug, PartialEq, Eq)]
    pub enum TypeError {
        TypeNotEqual((Type, Type)),
        InfiniteType(TypeVar, Type),
        RowsNotEqual((ClosedRow, ClosedRow)),
    }

    /// Constraint solving
    impl TypeInference {
        pub(crate) fn unification(
            &mut self,
            constraints: Vec<Constraint>,
        ) -> Result<(), TypeError> {
            for constr in constraints {
                match constr {
                    Constraint::TypeEqual(left, right) => self.unify_ty_ty(left, right)?,
                    Constraint::RowConcat(row_eqn) => self.unify_row_eqn(row_eqn)?,
                }
            }
            Ok(())
        }

        fn normalize_closed_row(&mut self, closed: ClosedRow) -> ClosedRow {
            ClosedRow {
                fields: closed.fields,
                values: closed
                    .values
                    .into_iter()
                    .map(|ty| self.normalize_ty(ty))
                    .collect(),
            }
        }

        fn normalize_row(&mut self, row: Row) -> Row {
            match row {
                Row::Open(var) => match self.row_unification_table.probe_value(var) {
                    Some(closed) => Row::Closed(self.normalize_closed_row(closed)),
                    None => row,
                },
                Row::Closed(closed) => Row::Closed(self.normalize_closed_row(closed)),
            }
        }

        fn dispatch_any_solved(&mut self, var: RowVar, row: ClosedRow) -> Result<(), TypeError> {
            let mut changed_eqns = vec![];
            self.partial_row_eqns = std::mem::take(&mut self.partial_row_eqns)
                .into_iter()
                .filter_map(|eqn| match eqn {
                    RowEquation { left, right, goal } if left == Row::Open(var) => {
                        changed_eqns.push(RowEquation {
                            left: Row::Closed(row.clone()),
                            right,
                            goal,
                        });
                        None
                    }
                    RowEquation { left, right, goal } if right == Row::Open(var) => {
                        changed_eqns.push(RowEquation {
                            left,
                            right: Row::Closed(row.clone()),
                            goal,
                        });
                        None
                    }
                    RowEquation { left, right, goal } if goal == Row::Open(var) => {
                        changed_eqns.push(RowEquation {
                            left,
                            right,
                            goal: Row::Closed(row.clone()),
                        });
                        None
                    }
                    eqn => Some(eqn),
                })
                .collect();

            for row_eqn in changed_eqns {
                self.unify_row_eqn(row_eqn)?;
            }
            Ok(())
        }

        fn normalize_ty(&mut self, ty: Type) -> Type {
            match ty {
                Type::Int => Type::Int,
                Type::Fun(arg, ret) => {
                    let arg = self.normalize_ty(*arg);
                    let ret = self.normalize_ty(*ret);
                    Type::fun(arg, ret)
                }
                Type::Var(v) => match self.unification_table.probe_value(v) {
                    Some(ty) => self.normalize_ty(ty),
                    None => Type::Var(v),
                },
                Type::Label(label, ty) => {
                    let ty = self.normalize_ty(*ty);
                    Type::label(label, ty)
                }
                Type::Prod(row) => Type::Prod(self.normalize_row(row)),
                Type::Sum(row) => Type::Sum(self.normalize_row(row)),
            }
        }

        fn unify_ty_ty(&mut self, unnorm_left: Type, unnorm_right: Type) -> Result<(), TypeError> {
            let left = self.normalize_ty(unnorm_left);
            let right = self.normalize_ty(unnorm_right);
            match (left, right) {
                (Type::Int, Type::Int) => Ok(()),
                (Type::Fun(a_arg, a_ret), Type::Fun(b_arg, b_ret)) => {
                    self.unify_ty_ty(*a_arg, *b_arg)?;
                    self.unify_ty_ty(*a_ret, *b_ret)
                }
                (Type::Var(a), Type::Var(b)) => self
                    .unification_table
                    .unify_var_var(a, b)
                    .map_err(TypeError::TypeNotEqual),
                (Type::Var(v), ty) | (ty, Type::Var(v)) => {
                    ty.occurs_check(v)
                        .map_err(|ty| TypeError::InfiniteType(v, ty))?;
                    self.unification_table
                        .unify_var_value(v, Some(ty))
                        .map_err(TypeError::TypeNotEqual)
                }
                (Type::Prod(left), Type::Prod(right)) | (Type::Sum(left), Type::Sum(right)) => {
                    self.unify_row_row(left, right)
                }
                (Type::Label(field, ty), Type::Prod(row))
                | (Type::Prod(row), Type::Label(field, ty))
                | (Type::Label(field, ty), Type::Sum(row))
                | (Type::Sum(row), Type::Label(field, ty)) => self.unify_row_row(
                    Row::Closed(ClosedRow {
                        fields: vec![field],
                        values: vec![*ty],
                    }),
                    row,
                ),
                (left, right) => Err(TypeError::TypeNotEqual((left, right))),
            }
        }

        /// Calculate the set difference of the goal row and the sub row, returning it as a new row.
        /// Unify the subset of the goal row that matches the sub row
        fn diff_and_unify(
            &mut self,
            goal: ClosedRow,
            sub: ClosedRow,
        ) -> Result<ClosedRow, TypeError> {
            let mut diff_fields = vec![];
            let mut diff_values = vec![];
            for (field, value) in goal.fields.into_iter().zip(goal.values.into_iter()) {
                match sub.fields.binary_search(&field) {
                    Ok(indx) => {
                        self.unify_ty_ty(value, sub.values[indx].clone())?;
                    }
                    Err(_) => {
                        diff_fields.push(field);
                        diff_values.push(value);
                    }
                }
            }
            Ok(ClosedRow {
                fields: diff_fields,
                values: diff_values,
            })
        }

        fn unify_row_row(&mut self, left: Row, right: Row) -> Result<(), TypeError> {
            let left = self.normalize_row(left);
            let right = self.normalize_row(right);
            match (left, right) {
                (Row::Open(left), Row::Open(right)) => self
                    .row_unification_table
                    .unify_var_var(left, right)
                    .map_err(TypeError::RowsNotEqual),
                (Row::Open(var), Row::Closed(row)) | (Row::Closed(row), Row::Open(var)) => {
                    self.row_unification_table
                        .unify_var_value(var, Some(row.clone()))
                        .map_err(TypeError::RowsNotEqual)?;
                    self.dispatch_any_solved(var, row)
                }
                (Row::Closed(left), Row::Closed(right)) => {
                    // Check that the rows we're unifying are actually unifiable
                    if left.fields != right.fields {
                        return Err(TypeError::RowsNotEqual((left, right)));
                    }

                    // If they are, our values are already in order so we can walk them and unify each
                    // type
                    for (left_ty, right_ty) in left.values.into_iter().zip(right.values.into_iter())
                    {
                        self.unify_ty_ty(left_ty, right_ty)?;
                    }
                    Ok(())
                }
            }
        }

        fn unify_row_eqn(&mut self, row_eqn: RowEquation) -> Result<(), TypeError> {
            let left = self.normalize_row(row_eqn.left);
            let right = self.normalize_row(row_eqn.right);
            let goal = self.normalize_row(row_eqn.goal);
            match (left, right, goal) {
                // We know everything, check that it's correct
                (Row::Closed(_), Row::Closed(_), Row::Closed(_)) => todo!(),
                // We have one unknown, unify it and solve
                (Row::Open(var), Row::Closed(sub), Row::Closed(goal))
                | (Row::Closed(sub), Row::Open(var), Row::Closed(goal)) => {
                    let diff_row = self.diff_and_unify(goal, sub)?;
                    self.row_unification_table
                        .unify_var_value(var, Some(diff_row))
                        .map_err(TypeError::RowsNotEqual)
                }
                (Row::Closed(left), Row::Closed(right), Row::Open(goal)) => {
                    let closed_goal = ClosedRow::merge(left, right);
                    self.row_unification_table
                        .unify_var_value(goal, Some(closed_goal))
                        .map_err(TypeError::RowsNotEqual)
                }
                // Not enough info to solve
                (left, right, goal) => {
                    let new_eqn = RowEquation { left, right, goal };
                    // Check if we've already seen an equation that we can unify against
                    let poss_uni = self.partial_row_eqns.iter().find_map(|eqn| {
                        if eqn.is_unifiable(&new_eqn) {
                            Some(eqn.clone())
                        //Row equations commute so we have to check for that possible unification
                        } else if eqn.is_comm_unifiable(&new_eqn) {
                            // We commute our equation so we unify the correct rows later
                            Some(RowEquation {
                                left: eqn.right.clone(),
                                right: eqn.left.clone(),
                                goal: eqn.goal.clone(),
                            })
                        } else {
                            None
                        }
                    });

                    match poss_uni {
                        // Unify if we have a match
                        Some(match_eqn) => {
                            self.unify_row_row(new_eqn.left, match_eqn.left)?;
                            self.unify_row_row(new_eqn.right, match_eqn.right)?;
                            self.unify_row_row(new_eqn.goal, match_eqn.goal)?;
                        }
                        // Otherwise add our equation to our list of partial equations
                        None => {
                            self.partial_row_eqns.insert(new_eqn);
                        }
                    }
                    Ok(())
                }
            }
        }
    }
}

mod subst {
    use std::collections::HashSet;

    use crate::ast::{Ast, TypedVar};
    use crate::ty::{ClosedRow, Row, RowEquation, RowVar, Type, TypeVar};
    use crate::{Evidence, TypeInference};

    pub struct SubstOut<T> {
        pub unbound_tys: HashSet<TypeVar>,
        pub unbound_rows: HashSet<RowVar>,
        pub value: T,
    }

    impl<T> SubstOut<T> {
        pub(super) fn new(value: T) -> Self {
            Self {
                unbound_tys: HashSet::default(),
                unbound_rows: HashSet::default(),
                value,
            }
        }

        fn insert_unbound_ty(&mut self, ty_var: TypeVar) {
            self.unbound_tys.insert(ty_var);
        }
        fn with_unbound_ty(mut self, ty_var: TypeVar) -> Self {
            self.insert_unbound_ty(ty_var);
            self
        }

        fn with_unbound_row(mut self, row_var: RowVar) -> Self {
            self.unbound_rows.insert(row_var);
            self
        }

        pub(super) fn merge<U, O>(
            mut self,
            other: SubstOut<U>,
            merge_values: impl FnOnce(T, U) -> O,
        ) -> SubstOut<O> {
            self.unbound_tys.extend(other.unbound_tys);
            self.unbound_rows.extend(other.unbound_rows);
            SubstOut {
                unbound_rows: self.unbound_rows,
                unbound_tys: self.unbound_tys,
                value: merge_values(self.value, other.value),
            }
        }

        fn map<U>(self, f: impl FnOnce(T) -> U) -> SubstOut<U> {
            SubstOut {
                value: f(self.value),
                unbound_tys: self.unbound_tys,
                unbound_rows: self.unbound_rows,
            }
        }
    }

    impl TypeInference {
        fn substitute_closedrow(&mut self, row: ClosedRow) -> SubstOut<ClosedRow> {
            let mut row_out = SubstOut::new(());
            let values = row
                .values
                .into_iter()
                .map(|ty| {
                    let out = self.substitute_ty(ty);
                    row_out.unbound_rows.extend(out.unbound_rows);
                    row_out.unbound_tys.extend(out.unbound_tys);
                    out.value
                })
                .collect();
            row_out.map(|_| ClosedRow {
                fields: row.fields,
                values,
            })
        }

        fn substitute_row(&mut self, row: Row) -> SubstOut<Row> {
            match row {
                Row::Open(var) => {
                    let root = self.row_unification_table.find(var);
                    match self.row_unification_table.probe_value(root) {
                        Some(row) => self.substitute_closedrow(row).map(Row::Closed),
                        None => SubstOut::new(Row::Open(root)).with_unbound_row(root),
                    }
                }
                Row::Closed(row) => self.substitute_closedrow(row).map(Row::Closed),
            }
        }

        pub(crate) fn substitute_ty(&mut self, ty: Type) -> SubstOut<Type> {
            match ty {
                Type::Int => SubstOut::new(Type::Int),
                Type::Var(v) => {
                    let root = self.unification_table.find(v);
                    match self.unification_table.probe_value(root) {
                        Some(ty) => self.substitute_ty(ty),
                        None => SubstOut::new(Type::Var(root)).with_unbound_ty(root),
                    }
                }
                Type::Fun(arg, ret) => {
                    let arg_out = self.substitute_ty(*arg);
                    let ret_out = self.substitute_ty(*ret);
                    arg_out.merge(ret_out, Type::fun)
                }
                Type::Label(field, value) => {
                    self.substitute_ty(*value).map(|ty| Type::label(field, ty))
                }
                Type::Prod(row) => self.substitute_row(row).map(Type::Prod),
                Type::Sum(row) => self.substitute_row(row).map(Type::Sum),
            }
        }

        pub(crate) fn substitute_ast(&mut self, ast: Ast<TypedVar>) -> SubstOut<Ast<TypedVar>> {
            match ast {
                Ast::Var(v) => self
                    .substitute_ty(v.1)
                    .map(|ty| Ast::Var(TypedVar(v.0, ty))),
                Ast::Int(i) => SubstOut::new(Ast::Int(i)),
                Ast::Fun(arg, body) => self
                    .substitute_ty(arg.1)
                    .map(|ty| TypedVar(arg.0, ty))
                    .merge(self.substitute_ast(*body), Ast::fun),
                Ast::App(fun, arg) => self
                    .substitute_ast(*fun)
                    .merge(self.substitute_ast(*arg), Ast::app),
                // Label constructor and destructor
                Ast::Label(label, ast) => {
                    self.substitute_ast(*ast).map(|ast| Ast::label(label, ast))
                }
                Ast::Unlabel(ast, label) => self
                    .substitute_ast(*ast)
                    .map(|ast| Ast::unlabel(ast, label)),
                // Products constructor and destructor
                Ast::Concat(left, right) => self
                    .substitute_ast(*left)
                    .merge(self.substitute_ast(*right), Ast::concat),
                Ast::Project(dir, ast) => {
                    self.substitute_ast(*ast).map(|ast| Ast::project(dir, ast))
                }
                // Sums constructor and destructor
                Ast::Branch(left, right) => self
                    .substitute_ast(*left)
                    .merge(self.substitute_ast(*right), Ast::branch),
                Ast::Inject(dir, ast) => self.substitute_ast(*ast).map(|ast| Ast::inject(dir, ast)),
            }
        }

        pub(crate) fn substitute_row_eqn(&mut self, eqn: RowEquation) -> SubstOut<Evidence> {
            self.substitute_row(eqn.left)
                .merge(self.substitute_row(eqn.right), |l, r| (l, r))
                .merge(self.substitute_row(eqn.goal), |(left, right), goal| {
                    Evidence::RowEquation { left, right, goal }
                })
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Evidence {
    RowEquation { left: Row, right: Row, goal: Row },
}

#[derive(PartialEq, Eq, Clone, Debug)]
struct TypeScheme {
    unbound_rows: HashSet<RowVar>,
    unbound_tys: HashSet<TypeVar>,
    evidence: Vec<Evidence>,
    ty: Type,
}

fn type_infer(ast: Ast<Var>) -> Result<(Ast<TypedVar>, TypeScheme), TypeError> {
    let mut ctx = TypeInference {
        unification_table: InPlaceUnificationTable::default(),
        row_unification_table: InPlaceUnificationTable::default(),
        partial_row_eqns: BTreeSet::default(),
    };

    // Constraint generation
    let (out, ty) = ctx.infer(im::HashMap::default(), ast);

    // Constraint solving
    ctx.unification(out.constraints)?;

    // Apply our substition to our inferred types
    let subst_out = ctx
        .substitute_ty(ty)
        .merge(ctx.substitute_ast(out.typed_ast), |ty, ast| (ty, ast));

    let mut ev_out = SubstOut::new(());
    let evidence = std::mem::take(&mut ctx.partial_row_eqns)
        .into_iter()
        .filter_map(|row_eqn| match row_eqn {
            RowEquation {
                left: Row::Open(left),
                right,
                goal,
            } if subst_out.unbound_rows.contains(&left) => Some(RowEquation {
                left: Row::Open(left),
                right,
                goal,
            }),
            RowEquation {
                left: Row::Closed(left),
                right,
                goal,
            } if left.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => {
                Some(RowEquation {
                    left: Row::Closed(left),
                    right,
                    goal,
                })
            }
            RowEquation {
                left,
                right: Row::Open(right),
                goal,
            } if subst_out.unbound_rows.contains(&right) => Some(RowEquation {
                left,
                right: Row::Open(right),
                goal,
            }),
            RowEquation {
                left,
                right: Row::Closed(right),
                goal,
            } if right.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => {
                Some(RowEquation {
                    left,
                    right: Row::Closed(right),
                    goal,
                })
            }
            RowEquation {
                left,
                right,
                goal: Row::Open(goal),
                ..
            } if subst_out.unbound_rows.contains(&goal) => Some(RowEquation {
                left,
                right,
                goal: Row::Open(goal),
            }),
            RowEquation {
                left,
                right,
                goal: Row::Closed(goal),
            } if goal.mentions(&subst_out.unbound_tys, &subst_out.unbound_rows) => {
                Some(RowEquation {
                    left,
                    right,
                    goal: Row::Closed(goal),
                })
            }
            _ => None,
        })
        .map(|eqn| {
            let out = ctx.substitute_row_eqn(eqn);
            ev_out.unbound_rows.extend(out.unbound_rows);
            ev_out.unbound_tys.extend(out.unbound_tys);
            out.value
        })
        .collect();

    let subst_out = subst_out.merge(ev_out, |l, _| l);
    // Return our typed ast and it's type scheme
    Ok((
        subst_out.value.1,
        TypeScheme {
            unbound_rows: subst_out.unbound_rows,
            unbound_tys: subst_out.unbound_tys,
            evidence,
            ty: subst_out.value.0,
        },
    ))
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {

    use crate::ast::Direction;
    use crate::ty::ClosedRow;

    use super::*;

    macro_rules! set {
        () => {{ HashSet::new() }};
        ($($ele:expr),*) => {{
            let mut tmp = HashSet::new();
            $(tmp.insert($ele);)*
            tmp
        }};
    }

    #[test]
    fn infers_int() {
        let ast = Ast::Int(3);

        let ty_chk = type_infer(ast).expect("Type inference to succeed");
        assert_eq!(ty_chk.0, Ast::Int(3));
        assert_eq!(ty_chk.1.ty, Type::Int);
    }

    #[test]
    fn infers_id_fun() {
        let x = Var(0);
        let ast = Ast::fun(x, Ast::Var(x));

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(0);
        let typed_x = TypedVar(x, Type::Var(a));
        assert_eq!(ty_chk.0, Ast::fun(typed_x.clone(), Ast::Var(typed_x)));
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound_rows: set![],
                unbound_tys: set![a],
                evidence: vec![],
                ty: Type::fun(Type::Var(a), Type::Var(a)),
            }
        )
    }

    #[test]
    fn infers_k_combinator() {
        let x = Var(0);
        let y = Var(1);
        let ast = Ast::fun(x, Ast::fun(y, Ast::Var(x)));

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(0);
        let b = TypeVar(1);
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound_rows: set![],
                unbound_tys: set![a, b],
                evidence: vec![],
                ty: Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(a))),
            }
        );
    }

    #[test]
    fn infers_s_combinator() {
        let x = Var(0);
        let y = Var(1);
        let z = Var(2);
        let ast = Ast::fun(
            x,
            Ast::fun(
                y,
                Ast::fun(
                    z,
                    Ast::app(
                        Ast::app(Ast::Var(x), Ast::Var(z)),
                        Ast::app(Ast::Var(y), Ast::Var(z)),
                    ),
                ),
            ),
        );

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let a = TypeVar(2);
        let b = TypeVar(3);
        let c = TypeVar(4);
        let x_ty = Type::fun(Type::Var(a), Type::fun(Type::Var(b), Type::Var(c)));
        let y_ty = Type::fun(Type::Var(a), Type::Var(b));
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound_rows: set![],
                unbound_tys: set![a, b, c],
                evidence: vec![],
                ty: Type::fun(x_ty, Type::fun(y_ty, Type::fun(Type::Var(a), Type::Var(c)))),
            }
        )
    }

    fn single_row(field: impl ToString, value: Type) -> ClosedRow {
        ClosedRow {
            fields: vec![field.to_string()],
            values: vec![value],
        }
    }

    #[test]
    fn test_wand_combinator() {
        let m = Var(0);
        let n = Var(1);

        let ast = Ast::fun(
            m,
            Ast::fun(
                n,
                Ast::unlabel(
                    Ast::project(Direction::Left, Ast::concat(Ast::Var(m), Ast::Var(n))),
                    "x",
                ),
            ),
        );

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let m = RowVar(2);
        let n = RowVar(3);
        let goal = RowVar(0);
        let a = TypeVar(2);
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound_rows: set![n, RowVar(1), m, goal],
                unbound_tys: set![a],
                evidence: vec![
                    Evidence::RowEquation {
                        left: Row::Open(m),
                        right: Row::Open(n),
                        goal: Row::Open(goal)
                    },
                    Evidence::RowEquation {
                        left: Row::Closed(single_row("x", Type::Var(a))),
                        right: Row::Open(RowVar(1)),
                        goal: Row::Open(goal)
                    }
                ],
                ty: Type::fun(
                    Type::Prod(Row::Open(m)),
                    Type::fun(Type::Prod(Row::Open(n)), Type::Var(a))
                )
            }
        );
    }

    #[test]
    fn test_sums() {
        let f = Var(0);
        let g = Var(1);
        let x = Var(2);
        let ast = Ast::fun(
            f,
            Ast::fun(
                g,
                Ast::fun(
                    x,
                    Ast::app(
                        Ast::branch(Ast::Var(f), Ast::Var(g)),
                        Ast::inject(Direction::Right, Ast::label("Con", Ast::Var(x))),
                    ),
                ),
            ),
        );

        let ty_chk = type_infer(ast).expect("Type inference to succeed");

        let f = RowVar(3);
        let g = RowVar(4);
        let goal = RowVar(2);
        let a = TypeVar(2);
        let r = TypeVar(3);
        assert_eq!(
            ty_chk.1,
            TypeScheme {
                unbound_rows: set![g, f, RowVar(0), goal],
                unbound_tys: set![a, r],
                evidence: vec![
                    Evidence::RowEquation {
                        left: Row::Open(RowVar(0)),
                        right: Row::Closed(single_row("Con", Type::Var(a))),
                        goal: Row::Open(goal)
                    },
                    Evidence::RowEquation {
                        left: Row::Open(f),
                        right: Row::Open(g),
                        goal: Row::Open(goal)
                    }
                ],
                ty: Type::fun(
                    Type::fun(Type::Sum(Row::Open(f)), Type::Var(r)),
                    Type::fun(
                        Type::fun(Type::Sum(Row::Open(g)), Type::Var(r)),
                        Type::fun(Type::Var(a), Type::Var(r))
                    )
                ),
            }
        );
    }

    #[test]
    fn type_infer_fails() {
        let x = Var(0);
        let ast = Ast::app(Ast::fun(x, Ast::app(Ast::Var(x), Ast::Int(3))), Ast::Int(1));

        let ty_chk_res = type_infer(ast);

        assert_eq!(
            ty_chk_res,
            Err(TypeError::TypeNotEqual((
                Type::fun(Type::Int, Type::Var(TypeVar(1))),
                Type::Int
            )))
        );
    }
}
