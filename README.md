Non empty vector, ensure non empty by construction.

Inherits `Vec`'s methods through `Deref` trait, not implement `DerefMut`.

Overridden some methods:
* `len` returns `NonZeroUsize`, `is_empty` always returns `false`.
* `first(_mut)`, `last(_mut)`, `split_first(_mut)`, `split_last(_mut)` don't return `Option`.
* `pop` returns `None` if there is only one element in it.
