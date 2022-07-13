use std::convert::TryFrom;
use std::iter::FusedIterator;
use std::num::NonZeroUsize;
use std::ops::{self, RangeBounds};
use std::slice::{Iter, IterMut, SliceIndex};
use std::vec::IntoIter;

#[cfg(feature = "serde")]
use serde::{de::Error, Deserialize, Deserializer, Serialize, Serializer};

/// Calls [`std::hint::unreachable_unchecked`] in release mode, and panics in debug mode.
macro_rules! unreachable_unchecked {
    () => {{
        #[cfg(debug_assertions)]
        ::std::unreachable!();
        #[allow(unreachable_code)]
        ::std::hint::unreachable_unchecked()
    }};
}

/// Non empty vector, ensure non empty by construction.
/// Inherits `Vec`'s methods through `Deref` trait, not implement `DerefMut`.
/// Overridden these methods:
/// * `len` returns `NonZeroUsize` and `is_empty` always returns `false`.
/// * `first(_mut)`, `last(_mut)`, `split_first(_mut)`, `split_last(_mut)` don't return `Option`.
/// * `pop` returns `None` if there is only one element in it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NonEmpty<T>(Vec<T>);

impl<T> NonEmpty<T> {
    #[inline]
    pub fn new(v: T) -> Self {
        Self(vec![v])
    }

    /// Constructs a non-empty vec without checking its size.
    ///
    /// # Safety
    /// `vec` should not be empty.
    #[inline]
    pub unsafe fn new_unchecked(vec: Vec<T>) -> Self {
        Self(vec)
    }

    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }

    #[inline]
    pub fn as_mut_ptr(&mut self) -> *const T {
        self.0.as_mut_ptr()
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.0.len() <= 1 {
            None
        } else {
            self.0.pop()
        }
    }

    #[inline]
    pub fn push(&mut self, v: T) {
        self.0.push(v)
    }

    #[inline]
    pub fn truncate(&mut self, len: NonZeroUsize) {
        self.0.truncate(len.get())
    }

    /// Converts the vector into a boxed slice.
    ///
    /// Note that this will drop any excess capacity.
    #[inline]
    pub fn into_boxed_slice(self) -> Box<NonEmptySlice<T>> {
        // SAFETY: This instance is non-empty, so we can
        // safely make a `NonEmptySlice` from it.
        unsafe { NonEmptySlice::unchecked_boxed(self.0.into_boxed_slice()) }
    }
}

impl<T> From<(Vec<T>, T)> for NonEmpty<T> {
    fn from((mut xs, x): (Vec<T>, T)) -> NonEmpty<T> {
        xs.push(x);
        NonEmpty(xs)
    }
}

impl<T> From<(T, Vec<T>)> for NonEmpty<T> {
    fn from((x, mut xs): (T, Vec<T>)) -> NonEmpty<T> {
        xs.insert(0, x);
        NonEmpty(xs)
    }
}

impl<T> From<NonEmpty<T>> for Vec<T> {
    fn from(v: NonEmpty<T>) -> Self {
        v.0
    }
}

/// Returns a unit-length vector containing the default element value.
impl<T: Default> Default for NonEmpty<T> {
    fn default() -> Self {
        ne_vec![T::default()]
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct EmptyError;

impl<T> TryFrom<Vec<T>> for NonEmpty<T> {
    type Error = EmptyError;
    fn try_from(xs: Vec<T>) -> Result<Self, Self::Error> {
        if xs.is_empty() {
            Err(EmptyError)
        } else {
            Ok(NonEmpty(xs))
        }
    }
}

impl<T> From<Box<NonEmptySlice<T>>> for NonEmpty<T> {
    #[inline]
    fn from(slice: Box<NonEmptySlice<T>>) -> Self {
        let v = Vec::from(slice.into_boxed_slice());
        // SAFETY: We constructed this vector from a `NonEmptySlice`,
        // so it's guaranteed to be non-empty.
        unsafe { Self::new_unchecked(v) }
    }
}
impl<T> TryFrom<Box<[T]>> for NonEmpty<T> {
    type Error = EmptyError;
    #[inline]
    fn try_from(value: Box<[T]>) -> Result<Self, Self::Error> {
        let v = Vec::from(value);
        Self::try_from(v)
    }
}

impl<T> ops::Deref for NonEmpty<T> {
    type Target = NonEmptySlice<T>;
    fn deref(&self) -> &Self::Target {
        unsafe {
            // SAFETY: This type is guaranteed to be non-empty, so we don't
            // need to check the length when wrapping into a `NonEmptySlice`.
            NonEmptySlice::unchecked(&self.0)
        }
    }
}
impl<T> ops::DerefMut for NonEmpty<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe {
            // SAFETY: This type is guaranteed to be non-empty, so we don't
            // need to check the length when wrapping into a `NonEmptySlice`.
            NonEmptySlice::unchecked_mut(&mut self.0)
        }
    }
}

impl<T> AsRef<[T]> for NonEmpty<T> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T> AsMut<[T]> for NonEmpty<T> {
    fn as_mut(&mut self) -> &mut [T] {
        self.0.as_mut()
    }
}

impl<T> AsRef<Vec<T>> for NonEmpty<T> {
    fn as_ref(&self) -> &Vec<T> {
        &self.0
    }
}

impl<T, I: SliceIndex<[T]>> ops::Index<I> for NonEmpty<T> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        ops::Index::index(self.as_slice(), index)
    }
}
impl<T, I: SliceIndex<[T]>> ops::IndexMut<I> for NonEmpty<T> {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        ops::IndexMut::index_mut(self.as_mut_slice(), index)
    }
}

impl<T> IntoIterator for NonEmpty<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
impl<'a, T> IntoIterator for &'a NonEmpty<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, T> IntoIterator for &'a mut NonEmpty<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> NonEmpty<T> {
    /// Removes the specified range from the vector in bulk, returning the removed items as an iterator.
    /// # Panics
    /// If the range specified would remove all elements from the vector. There must be at least 1 element left over.
    /// # Examples
    /// Removing all but the first element.
    /// ```
    /// # use non_empty_vec::{NonEmpty, ne_vec};
    /// let mut v = ne_vec!(0, 1, 2, 3, 4, 5);
    /// let removed: Vec<_> = v.drain(1..).collect();
    /// assert_eq!(removed, vec![1, 2, 3, 4, 5]);
    /// assert_eq!(v, ne_vec![0]);
    /// ```
    ///
    /// Removing all but the last element.
    /// ```
    /// # use non_empty_vec::{NonEmpty, ne_vec};
    /// let mut v = ne_vec!(0, 1, 2, 3, 4, 5);
    /// let removed: Vec<_> = v.drain(..v.len().get()-1).collect();
    /// assert_eq!(removed, vec![0, 1, 2, 3, 4]);
    /// assert_eq!(v, ne_vec![5]);
    /// ```
    /// Removing all elements (these panic).
    /// ```should_panic
    /// # use non_empty_vec::ne_vec;
    /// # let mut v = ne_vec!(0, 1, 2, 3, 4, 5);
    /// v.drain(..);
    /// ```
    /// ```should_panic
    /// # use non_empty_vec::ne_vec;
    /// # let mut v = ne_vec!(0, 1, 2, 3, 4, 5);
    /// v.drain(0..v.len().get());
    /// ```
    #[track_caller]
    pub fn drain<R: RangeBounds<usize>>(&mut self, range: R) -> std::vec::Drain<T> {
        // whether or not there is space leftover in the start of the vector.
        let leftover_start = match range.start_bound() {
            core::ops::Bound::Included(&start) => start > 0,
            core::ops::Bound::Excluded(_) => true,
            core::ops::Bound::Unbounded => false,
        };
        if !leftover_start {
            // whether or not there is space leftover in the end of the vector.
            let leftover_end = match range.end_bound() {
                core::ops::Bound::Excluded(&end) => end < self.len().get(),
                core::ops::Bound::Included(&end) => end < self.len().get() - 1,
                core::ops::Bound::Unbounded => false,
            };
            if !leftover_end {
                panic!(
                    "range specified for `NonEmpty::drain` must leave at least one element left"
                );
            }
        }
        self.0.drain(range)
    }

    /// Calls a predicate with every element of this vector, removing each element for which the predicate returns `true`.
    /// All removed elements are yielded from the returned iterator.
    /// # Examples
    /// Normal use.
    /// ```
    /// // Filter out odd entries
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1,2,3,4,5,6];
    /// assert!(v.drain_filter(|i| *i % 2 == 1).eq([1, 3, 5]));
    /// assert_eq!(v, ne_vec![2, 4, 6]);
    /// ```
    /// At least one element is always left behind.
    /// ```
    /// // When there's only one element left, the predicate never even gets called on it.
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1];
    /// v.drain_filter(|_| unreachable!());
    /// assert_eq!(v, ne_vec![1]);
    ///
    /// // This also applies if all elements before the final get removed.
    /// let mut v = ne_vec![1, 2, 3, 4, 5];
    /// let removed = v.drain_filter(|&mut i| if i < 5 {
    ///     true
    /// } else {
    ///     unreachable!()
    /// });
    /// assert!(removed.eq(1..=4));
    /// assert_eq!(v, ne_vec![5]);
    /// ```
    /// Lazy execution.
    /// ```
    /// // Nothing gets removed until the iterator is consumed
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1,2,3,4];
    /// v.drain_filter(|_| true);
    /// assert_eq!(v, ne_vec![1,2,3,4]);
    /// ```
    #[inline]
    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilter<T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        DrainFilter::new(self, f)
    }
}

#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    vec: &'a mut NonEmpty<T>,
    f: F,

    // Always `0 <= left <= right <= vec.len()`, usually `left < right`.
    // When `left == right`, the iterator is complete.
    left: usize,
    right: usize,
}
impl<'a, T, F> DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    #[inline]
    pub fn new(vec: &'a mut NonEmpty<T>, f: F) -> Self {
        let left = 0;
        let right = vec.len().get();
        Self {
            vec,
            f,
            left,
            right,
        }
    }
}

impl<'a, T, F> Iterator for DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        // Loop until either we find an element or the list is depleted.
        loop {
            // Only try draining this element if there would be more elements leftover.
            let any_yielded = self.left > 0 || self.right < self.vec.0.len();
            if (any_yielded || self.right - self.left > 1) && self.left < self.right {
                // If the elment passes the predicate, remove it and yield it.
                if (self.f)(&mut self.vec[self.left]) {
                    let item = self.vec.0.remove(self.left);
                    self.right -= 1;
                    break Some(item);
                }
                // If it doesn't pass, leave the element and repeat the loop.
                else {
                    self.left += 1;
                }
            }
            // We've reached the point where we only have one element left, so leave it.
            else {
                break None;
            }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let max = self.right - self.left;
        (0, Some(max))
    }
}
impl<'a, T, F> DoubleEndedIterator for DrainFilter<'a, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        // Loop until either we find an element or the list is depleted.
        loop {
            // Only try draining this element if there would be more elements leftover.
            let any_yielded = self.right < self.vec.0.len() || self.left > 0;
            if (any_yielded || self.right - self.left > 1) && self.right > self.left {
                // If the elment passes the predicate, remove it and yield it.
                if (self.f)(&mut self.vec[self.right - 1]) {
                    let item = self.vec.0.remove(self.right - 1);
                    self.right -= 1;
                    break Some(item);
                }
                // If it doesn't pass, leave the element and repeat the loop.
                else {
                    self.right -= 1;
                }
            }
            // We've reached the point where we only have one element left, so leave it.
            else {
                break None;
            }
        }
    }
}
impl<'a, T, F> FusedIterator for DrainFilter<'a, T, F> where F: FnMut(&mut T) -> bool {}

#[cfg(feature = "serde")]
impl<T: Serialize> Serialize for NonEmpty<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.as_slice().serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de>> Deserialize<'de> for NonEmpty<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Self::try_from(<Vec<T>>::deserialize(deserializer)?)
            .map_err(|_| D::Error::custom("empty vector"))
    }
}

/// Wrapper for a slice that is guaranteed to have `len > 0`. This allows
/// many operations to be infallible, such as [`first`](#method.first)
/// or [`split_last_mut`](#method.split_last_mut).
///
/// This invariant may be relied upon in unsafe code.
///
/// `NonEmptySlice` dereferences to an `std` slice, so all of the familiar methods are still available.
#[derive(Eq, Ord, Hash)]
#[repr(transparent)]
pub struct NonEmptySlice<T>([T]);

impl<T> NonEmptySlice<T> {
    /// Creates a new `NonEmptySlice` without checking the length.
    /// # Safety
    /// Ensure that the input slice is not empty.
    /// # Examples
    /// For a slice that is known not to be empty.
    /// ```
    /// # use non_empty_vec::NonEmptySlice;
    /// let s = unsafe {
    ///     // SAFETY: The passed slice is non-empty.
    ///     NonEmptySlice::unchecked(&[1])
    /// };
    /// assert_eq!(s, &[1]);
    /// ```
    /// Improper use (instant undefined behavior).
    /// ```ignore
    /// # use non_empty_vec::NonEmptySlice;
    /// let s: &NonEmptySlice<String> = unsafe { NonEmptySlice::unchecked(&[]) };
    /// // Please don't try this.
    /// println!("{}", s.first().as_str());
    /// ```
    #[inline]
    pub const unsafe fn unchecked(slice: &[T]) -> &Self {
        debug_assert!(!slice.is_empty());
        // SAFETY: This type is `repr(transparent)`, so we can safely
        // cast the references like this.
        &*(slice as *const _ as *const Self)
    }
    /// Creates a new `NonEmptySlice` without checking the length.
    /// # Safety
    /// Ensure that the input slice is not empty.
    #[inline]
    pub unsafe fn unchecked_mut(slice: &mut [T]) -> &mut Self {
        debug_assert!(!slice.is_empty());
        // SAFETY: This type is `repr(transparent)`, so we can safely
        // cast the references like this.
        &mut *(slice as *mut _ as *mut Self)
    }
    /// Creates a boxed `NonEmptySlice` without checking the length.
    /// # Safety
    /// Ensure that the input slice is not empty.
    #[inline]
    pub unsafe fn unchecked_boxed(slice: Box<[T]>) -> Box<Self> {
        debug_assert!(!slice.is_empty());
        // SAFETY: This type is `repr(transparent)`, so we can safely
        // cast the pointers like this.
        // `Box` does not necessarily have a guaranteed type layout
        // so it's safer to use methods to convert to/from raw pointers.
        let ptr = Box::into_raw(slice) as *mut Self;
        Box::from_raw(ptr)
    }

    /// Converts a reference into a [non-empty slice](NonEmptySlice) of length `1`.
    /// # Example
    /// ```
    /// # use non_empty_vec::NonEmptySlice;
    /// let slice = NonEmptySlice::from_ref(&5);
    /// assert_eq!(slice, &[5]);
    /// ```
    #[inline]
    pub fn from_ref(val: &T) -> &Self {
        let slice = core::slice::from_ref(val);
        // SAFETY: `slice::from_ref` returns a slice of length 1, so it's non-empty.
        unsafe { Self::unchecked(slice) }
    }
    /// Converts a mutable reference into a [non-empty slice](NonEmptySlice) of length `1`.
    #[inline]
    pub fn from_mut(val: &mut T) -> &mut Self {
        let slice = core::slice::from_mut(val);
        unsafe { Self::unchecked_mut(slice) }
    }

    /// Creates a new `NonEmptySlice` from a primitive slice. Returns [`None`] if the slice is empty.
    /// # Examples
    /// ```
    /// # use non_empty_vec::NonEmptySlice;
    /// // Non-empty input
    /// assert!(NonEmptySlice::from_slice(&[1]).is_some());
    /// // Empty input
    /// assert!(NonEmptySlice::<()>::from_slice(&[]).is_none());
    /// ```
    #[inline]
    pub const fn from_slice(slice: &[T]) -> Option<&Self> {
        if !slice.is_empty() {
            // SAFETY: We just checked that it's not empty,
            // so we can safely create a `NonEmptySlice`.
            unsafe { Some(Self::unchecked(slice)) }
        } else {
            None
        }
    }
    /// Creates a new `NonEmptySlice` from a primitive slice. Returns [`None`] if the slice is empty.
    #[inline]
    pub fn from_mut_slice(slice: &mut [T]) -> Option<&mut Self> {
        if !slice.is_empty() {
            // SAFETY: We just checked that it's not empty,
            // so we can safely create a `NonEmptySlice`.
            unsafe { Some(Self::unchecked_mut(slice)) }
        } else {
            None
        }
    }
    /// Creates a new `NonEmptySlice` from a primitive slice. Returns [`None`] if the slice is empty.
    #[inline]
    pub fn from_boxed_slice(slice: Box<[T]>) -> Option<Box<Self>> {
        if !slice.is_empty() {
            // SAFETY: We just checked that it's not empty,
            // so we can safely create a `NonEmptySlice`.
            unsafe { Some(Self::unchecked_boxed(slice)) }
        } else {
            None
        }
    }

    /// Converts this `NonEmptySlice` into a primitive slice.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        &self.0
    }
    /// Converts this `NonEmptySlice` into a primitive slice.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.0
    }
    /// Converts this `NonEmptySlice` into a primitive boxed slice.
    #[inline]
    pub fn into_boxed_slice(self: Box<Self>) -> Box<[T]> {
        // SAFETY: This type is `repr(transparent)`, so we can
        // safely cast the pointer like this.
        let ptr = Box::into_raw(self) as *mut [T];
        unsafe { Box::from_raw(ptr) }
    }

    /// Returns the length of this slice.
    #[inline]
    pub const fn len(&self) -> NonZeroUsize {
        unsafe { NonZeroUsize::new_unchecked(self.0.len()) }
    }
    /// Returns `false`.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Returns a raw pointer to this slice's buffer. See [`slice::as_ptr`] for more info.
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.0.as_ptr()
    }
    /// Returns a raw pointer to this slice's buffer. See [`slice::as_ptr`] for more info.
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self.0.as_mut_ptr()
    }

    /// Returns a reference to the first element of this slice.
    /// # Example
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let v = ne_vec![1, 2, 3];
    /// assert_eq!(v.first(), &1);
    /// ```
    #[inline]
    pub const fn first(&self) -> &T {
        if let [first, ..] = self.as_slice() {
            first
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }
    /// Returns a mutable reference to the first element of this slice.
    /// # Example
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1, 2, 3];
    /// *v.first_mut() = 10;
    /// assert_eq!(v, ne_vec![10, 2, 3]);
    /// ```
    #[inline]
    pub fn first_mut(&mut self) -> &mut T {
        if let [first, ..] = self.as_mut_slice() {
            first
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }

    /// Returns a reference to the last element of this slice.
    /// # Example
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1, 2, 3];
    /// assert_eq!(v.last(), &3);
    /// ```
    #[inline]
    pub const fn last(&self) -> &T {
        if let [.., last] = self.as_slice() {
            last
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }
    /// Returns a mutable reference to the last element of this slice.
    /// # Example
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1, 2, 3];
    /// *v.last_mut() = 10;
    /// assert_eq!(v, ne_vec![1, 2, 10]);
    /// ```
    #[inline]
    pub fn last_mut(&mut self) -> &mut T {
        if let [.., last] = self.as_mut_slice() {
            last
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }

    /// Splits this slice into
    /// * A reference to the first element.
    /// * A slice to the rest of the elements.
    ///
    /// This method is not usually very helpful, but it may shorten some expressions.
    /// It is mainly included for the sake of parity with [`split_first_mut`](#method.split_first_mut).
    #[inline]
    pub const fn split_first(&self) -> (&T, &[T]) {
        if let [first, rest @ ..] = self.as_slice() {
            (first, rest)
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }
    /// Splits this slice into
    /// * A mutable reference to the first element.
    /// * A mutable slice to the rest of the elements.
    ///
    /// This method is useful for breaking up a contiguous slice into multiple
    /// smaller references, which can each be mutated independently without
    /// tripping off the borrow checker.
    ///
    /// # Examples
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![1, 2, 3, 4];
    /// let (first, rest) = v.split_first_mut();
    /// *first *= 2;
    /// rest[1] += 2;
    /// assert_eq!(v, ne_vec![2, 2, 5, 4]);
    /// ```
    ///
    /// Only one element.
    /// ```
    /// # use non_empty_vec::ne_vec;
    /// let mut v = ne_vec![4];
    /// let (first, rest) = v.split_first_mut();
    /// assert_eq!(*first, 4);
    /// assert_eq!(rest, &[]);
    /// ```
    #[inline]
    pub fn split_first_mut(&mut self) -> (&mut T, &mut [T]) {
        if let [first, rest @ ..] = self.as_mut_slice() {
            (first, rest)
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }

    /// Splits this slice into
    /// * A reference to the last element.
    /// * A slice to the rest of the elements.
    ///
    /// This method is not usually very helpful, but it may shorten some expressions.
    /// It is mainly included for the sake of parity with [`split_last_mut`](#method.split_last_mut).
    #[inline]
    pub fn split_last(&self) -> (&T, &[T]) {
        if let [rest @ .., last] = self.as_slice() {
            (last, rest)
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }
    /// Splits this slice into
    /// * A mutable reference to the last element.
    /// * A mutable slice to the rest of the elements.
    ///
    /// This method is useful for breaking up a contiguous slice into multiple
    /// smaller references, which can each be mutated independently without
    /// tripping off the borrow checker.
    #[inline]
    pub fn split_last_mut(&mut self) -> (&mut T, &mut [T]) {
        if let [rest @ .., last] = self.as_mut_slice() {
            (last, rest)
        } else {
            // SAFETY: This instance is non-empty, so the above pattern will always match.
            unsafe { unreachable_unchecked!() }
        }
    }
}

impl<'a, T> TryFrom<&'a [T]> for &'a NonEmptySlice<T> {
    type Error = EmptyError;
    fn try_from(value: &'a [T]) -> Result<Self, Self::Error> {
        NonEmptySlice::from_slice(value).ok_or(EmptyError)
    }
}
impl<'a, T> TryFrom<&'a mut [T]> for &'a mut NonEmptySlice<T> {
    type Error = EmptyError;
    fn try_from(value: &'a mut [T]) -> Result<Self, Self::Error> {
        NonEmptySlice::from_mut_slice(value).ok_or(EmptyError)
    }
}
impl<T> TryFrom<Box<[T]>> for Box<NonEmptySlice<T>> {
    type Error = EmptyError;
    fn try_from(value: Box<[T]>) -> Result<Self, Self::Error> {
        NonEmptySlice::from_boxed_slice(value).ok_or(EmptyError)
    }
}

impl<T> ops::Deref for NonEmptySlice<T> {
    type Target = [T];
    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
impl<T> ops::DerefMut for NonEmptySlice<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T> AsRef<[T]> for NonEmptySlice<T> {
    #[inline]
    fn as_ref(&self) -> &[T] {
        self
    }
}
impl<T> AsMut<[T]> for NonEmptySlice<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for NonEmptySlice<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", &self.0)
    }
}

impl<T: PartialEq, U: ?Sized + AsRef<[T]>> PartialEq<U> for NonEmptySlice<T> {
    #[inline]
    fn eq(&self, other: &U) -> bool {
        &self.0 == other.as_ref()
    }
}
impl<T: PartialEq> PartialEq<NonEmptySlice<T>> for [T] {
    #[inline]
    fn eq(&self, other: &NonEmptySlice<T>) -> bool {
        *self == other.0
    }
}
impl<T: PartialOrd, U: ?Sized + AsRef<[T]>> PartialOrd<U> for NonEmptySlice<T> {
    #[inline]
    fn partial_cmp(&self, other: &U) -> Option<std::cmp::Ordering> {
        self.0.partial_cmp(other.as_ref())
    }
}
impl<T: PartialOrd> PartialOrd<NonEmptySlice<T>> for [T] {
    #[inline]
    fn partial_cmp(&self, other: &NonEmptySlice<T>) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.0)
    }
}

impl<'a, T> IntoIterator for &'a NonEmptySlice<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl<'a, T> IntoIterator for &'a mut NonEmptySlice<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

/// Constructs a [`NonEmpty`] vector, similar to std's `vec` macro.
///
/// This macro will generally try to check the validity of the length at compile time if it can.
///
/// If the length is an expression (e.g. `ne_vec![(); { 0 }]`), the check is performed at runtime
/// to allow the length to be dynamic.
///
/// # Examples
/// Proper use.
/// ```
/// # use non_empty_vec::*;
/// # use std::convert::TryFrom;
/// assert_eq!(
///     ne_vec![1, 2, 3],
///     NonEmpty::try_from(vec![1, 2, 3_i32]).unwrap(),
/// );
///
/// assert_eq!(
///     ne_vec![1; 3],
///     NonEmpty::try_from(vec![1, 1, 1]).unwrap(),
/// );
/// ```
/// Improper use.
/// ```compile_fail
/// # use non_empty_vec::*;
/// let _ = ne_vec![];
/// ```
///
/// ```compile_fail
/// # use non_empty_vec::*;
/// let _ = ne_vec![1; 0];
/// ```
///
/// ```compile_fail
/// # use non_empty_vec::*;
/// let _ = ne_vec![1; 0usize];
/// ```
///
/// ```should_panic
/// # use non_empty_vec::*;
/// let n = 0;
/// let _ = ne_vec![1; n];
/// ```
#[macro_export]
macro_rules! ne_vec {
    () => {
        ::std::compile_error!("`NonEmpty` vector must be non-empty")
    };
    ($($x:expr),+ $(,)?) => {
        unsafe { $crate::NonEmpty::new_unchecked(vec![$($x),+]) }
    };
    ($elem:expr; 0) => {
        // if 0 is passed to the macro we can generate a good compile error
        ne_vec![]
    };
    ($elem:expr; $n:literal) => {{
        // extra guard to reject compilation if $n ends up being 0 in some other way (e.g. ne_vec![1; 0usize])
        const _ASSERT_NON_ZERO: [(); $n - 1] = [(); $n - 1];
        unsafe { $crate::NonEmpty::new_unchecked(vec![$elem; $n]) }
    }};
    ($elem:expr; $n:expr) => {{
        // if $n is an expression, we cannot check the length at compile time and do it at runtime
        if $n == 0 {
            ::std::panic!("`NonEmpty` vector must be non-empty");
        }
        unsafe { $crate::NonEmpty::new_unchecked(vec![$elem; $n]) }
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        // From
        let mut list: NonEmpty<i32> = (vec![1, 2], 3).into();
        assert_eq!(list, (1, vec![2, 3]).into());
        assert_eq!(&*list, &[1, 2, 3]);

        // Index
        list[0] = 2;
        assert_eq!(list[0], 2);
        list[0] = 1;
        assert_eq!(list[0], 1);

        // slice methods
        assert_eq!(list.len().get(), 3);
        assert_eq!(list.as_slice(), &[1, 2, 3]);

        // TryFrom
        assert_eq!(<NonEmpty<i32>>::try_from(vec![]).ok(), None);
        assert_eq!(
            &*<NonEmpty<i32>>::try_from(vec![1, 2, 3]).unwrap(),
            &[1, 2, 3]
        );

        // Iterator
        assert_eq!(
            list.iter().map(|n| n * 2).collect::<Vec<_>>(),
            vec![2, 4, 6]
        );

        // Single
        let single = NonEmpty::new(15_i32);
        assert_eq!(single.len().get(), 1);
        assert_eq!(single[0], 15);
    }

    #[test]
    fn default() {
        assert_eq!(NonEmpty::<i32>::default(), ne_vec![0]);
        assert_eq!(NonEmpty::<&str>::default(), ne_vec![""]);
    }

    #[test]
    fn into_iter() {
        let mut list = ne_vec![1, 2, 3];

        for (a, b) in [1, 2, 3].iter().zip(&list) {
            assert_eq!(a, b);
        }

        for a in &mut list {
            *a += 1;
        }
        assert_eq!(list.as_slice(), &[2, 3, 4]);

        for (a, b) in vec![2, 3, 4].into_iter().zip(list) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn drain_filter() {
        // Filter out odd numbers.
        let mut v = ne_vec![1, 2, 3, 4, 5, 6];
        assert!(v.drain_filter(|val| *val % 2 == 1).eq([1, 3, 5]));
        assert_eq!(v, ne_vec![2, 4, 6]);

        // singleton
        let mut v = ne_vec![1];
        for _ in v.drain_filter(|_| unreachable!()) {}
        assert_eq!(v, ne_vec![1]);

        // leftover
        let mut v = ne_vec![1, 2, 3];
        let removed = v.drain_filter(|&mut val| if val < 3 { true } else { unreachable!() });
        assert!(removed.eq([1, 2]));
        assert_eq!(v, ne_vec![3]);

        // double-ended, meet in middle
        let mut v = ne_vec![1, 2, 3, 4, 5, 6];
        let mut rem = v.drain_filter(|val| *val % 2 == 1);
        assert_eq!(rem.next(), Some(1));
        assert_eq!(rem.next_back(), Some(5));
        assert_eq!(rem.next_back(), Some(3));
        assert_eq!(rem.next(), None);
        assert_eq!(rem.next_back(), None);

        // rev
        let mut v = ne_vec![1, 2, 3, 4, 5, 6];
        let rem = v.drain_filter(|val| *val % 2 == 0).rev();
        assert!(rem.eq([6, 4, 2]));
        assert_eq!(v, ne_vec![1, 3, 5]);

        // singleton-back
        let mut v = ne_vec![1];
        for _ in v.drain_filter(|_| unreachable!()) {}
        assert_eq!(v, ne_vec![1]);

        // leftover-back
        let mut v = ne_vec![1, 2, 3];
        let removed = v
            .drain_filter(|&mut val| if val > 1 { true } else { unreachable!() })
            .rev();
        assert!(removed.eq([3, 2]));
        assert_eq!(v, ne_vec![1]);

        // meet in middle, unreachable
        let mut v = ne_vec![1, 2, 3];
        let mut rem = v.drain_filter(|&mut val| if val == 2 { unreachable!() } else { true });
        assert_eq!(rem.next_back(), Some(3));
        assert_eq!(rem.next(), Some(1));
        assert_eq!(rem.next_back(), None);
        assert_eq!(rem.next(), None);
        assert_eq!(v, ne_vec![2]);
    }

    #[test]
    fn initialize_macro() {
        assert_eq!(ne_vec![1; 3].as_slice(), &[1, 1, 1]);
        assert_eq!(ne_vec!["string"; 5].as_slice(), &["string"; 5]);
    }

    #[test]
    #[should_panic]
    fn initialize_macro_zero_size() {
        // ne_vec![1; 0] results in a compile error
        let n = 0;
        let _ = ne_vec![1; n];
    }

    #[cfg(feature = "serde")]
    #[test]
    fn serialize() {
        use serde_json;

        let vec: NonEmpty<u32> = (1, vec![]).into();
        assert_eq!(
            serde_json::from_str::<NonEmpty<u32>>(&serde_json::to_string(&vec).unwrap()).unwrap(),
            vec
        );
    }
}
