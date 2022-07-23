`NonEmpty` vector implementation, with non-emptiness ensured by construction.

Inherits slices' methods through the `Deref` and `DerefMut` traits.

`Vec`'s methods are manually overriden. Some important differences:
* `len` returns `NonZeroUsize` and `is_empty` always returns `false`.
* `first(_mut)`, `last(_mut)`, `split_first(_mut)`, `split_last(_mut)` don't return `Option`.
* `pop` and `remove` return `None` if there is only one element.

For example usage, please look at the embedded unit testing.
