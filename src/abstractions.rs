/*!

Types/type aliases that abstract over the implementing backing type.

# Background and Motivation

A motivating example is the `IString` type, an interned string type. A number of external crates could provide this
functionality. This module redirects to whatever chosen implementation we want. To use the
[`string_cache` crate](https://crates.io/crates/string_cache), we just define `IString` as an alias for
`string_cache::DefaultAtom`:

```ignore
pub use string_cache::DefaultAtom as IString;
```

If we want to later change to the [`ustr` crate](https://crates.io/crates/ustr), we just define `IString` to be an
alias for `ustr::Ustr` instead:

```ignore
pub use ustr::Ustr as IString;
```

The `ustr` and `string_cache` crates conveniently have very similar public APIs. For types or infrastructure with very
different backing implementations, we define an abstraction layer over the implementation.

*/


// Interned string. Use `DefaultAtom` for a global cache that can be used across threads. Use `Atom` for a thread-local
// string cache.
pub use string_cache::DefaultAtom as IString;
// pub use ustr::Ustr as IString;
