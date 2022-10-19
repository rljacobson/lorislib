# Wrapping Atom in an Expression Enum

An `Expression` is a syntactically correct "thing", a symbol, function, sequence, non-sequence variable,
or sequence variable. We try to keep `Expression`s immutable. We can use `Rc<Expression>`, aliased to
`RcExpression`, as a garbage collected copy-on-write smart pointer. Every `Expression` is a composition
of `Atoms`, so every `Expression` _is_ an atom, that is, has an atom as its root. Therefore, `Expression`
is an enum whose variants wrap each `Atom` type. We use `EnumDiscriminants` from `strum` to derive the
`ExpressionKind` enum whose variants are only the names (no data) of the variants in `Expression`.

But why wrap `Atom` at all? Why not use `Atom` directly?

    "[I]t is a common, and annoying, pattern in Rust today to have to make a struct for every enum variant and then
    just have the enum wrap those structs. This gives you the ability to have a "type for an enum variant", but is
    annoying and inconvenient."
    https://github.com/rust-lang/lang-team/issues/122#issuecomment-964459769

* We use `Expression` as an adapter from whatever expression tree scheme we want to the pattern matcher. It lets us 
  change the term rewriting system arbitrarily without needing to touch the pattern matcher. It is a mechanism for  
  decoupling.
* Variants of an enum are not themselves types. The type system cannot be used to monomorphize on specific enum 
  variants. If you want functions to only take a particular variant, or if you want methods on a particular variant, 
  you are out of luck. An inner struct wrapped by a variant, on the other hand, can do any of these things.

# Limitation of traits as supertypes 

Every match generator must also have a static method `try rule` that checks if it
applies to the active match equation and, if it does, returns an
instance of itself. Unfortunately, static methods cannot be used with
trait objects, and since this static method must return a type that
implements `MatchGenerator`, not a `MatchGenerator` trait object, I don't see a way
to do this. 
