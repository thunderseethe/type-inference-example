# Type Inference Example

Implementation of Type Inference discussed in https://thunderseethe.dev/posts/type-inference/

The blog post walks through the constraint generation and constraint solving, but does not cover the final substitution we do to tie everything together.
To see that code check out [substitute](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L258) and [substitute_ast](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L281).

If you want to play around with the code, everything is driven by [type_infer](https://github.com/thunderseethe/type-inference-example/blob/main/src/main.rs#L313). You can call it from `main` to type check any input AST.
