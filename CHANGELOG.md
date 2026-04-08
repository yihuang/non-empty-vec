## v0.2.4

- Add `with_capacity` constructor.
- Add `new_unchecked` unsafe constructor.
- Add `no_std` support (via `std` feature flag, enabled by default).
- Add `NonEmptySlice<T>` type: a non-empty slice reference wrapper.
- Add `drain` method.
- Add `drain_filter` method and `DrainFilter` iterator.
- Add `leak` and `into_boxed_slice` methods.
- Add `capacity`, `reserve`, `reserve_exact`, `try_reserve`, `try_reserve_exact`, `shrink_to_fit`, `shrink_to` methods.
- Add `resize`, `resize_with`, `insert`, `remove`, `swap_remove`, `append`, `extend_from_slice`, `extend_from_within` methods.
- Add `dedup`, `dedup_by`, `dedup_by_key` methods.
- Add `Default`, `TryFrom<Box<[T]>>`, `From<Box<NonEmptySlice<T>>>` implementations.
- Add `Write` impl for `NonEmpty<u8>` (requires `std` feature).
- `NonEmpty<T>` now derefs to `NonEmptySlice<T>` instead of `[T]`.

## v0.2.3

- [#12](https://github.com/yihuang/non-empty-vec/pull/12) Add `ne_vec![element; n]` macro.

## v0.2.2

- [#11](https://github.com/yihuang/non-empty-vec/pull/11) Add `truncate` method

## v0.2.1

- [#8](https://github.com/yihuang/non-empty-vec/pull/8) Add `AsMut<[T]>`
- [#9](https://github.com/yihuang/non-empty-vec/pull/9) Impl IntoIterator
- [#10](https://github.com/yihuang/non-empty-vec/pull/10) Derive `Hash` implementation.

## v0.2.0

- [#6](https://github.com/yihuang/non-empty-vec/pull/6) Remove unsafe `AsMut` implementation.
- [#3](https://github.com/yihuang/non-empty-vec/pull/3) Change `new` to construct singleton.
- [#4](https://github.com/yihuang/non-empty-vec/pull/4) Add macro similar to std's `vec!`

## v0.1.2

* Change impl Into -> impl From.

## v0.1.1

* Add `push` method.
