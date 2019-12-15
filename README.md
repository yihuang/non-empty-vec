`NonEmpty` vector implementation, ensure non-emptiness by construction.

Inherits `Vec`'s immutable methods through `Deref` trait, not implements `DerefMut`.

The differences from `Vec`:
* `len` returns `NonZeroUsize`, `is_empty` always returns `false`.
* `first(_mut)`, `last(_mut)`, `split_first(_mut)`, `split_last(_mut)` don't return `Option`.
* `pop` returns `None` if there is only one element in it.

More usages please look at the embedded unit testing.
