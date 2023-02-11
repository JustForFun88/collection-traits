#[cfg(test)]
mod tests;

use super::IntoIter;
use core::ops::ControlFlow;

mod guard;
use guard::Guard;

mod try_trait;
use try_trait::{ChangeOutputType, NeverShortCircuit, Residual, Try};

mod collect_array;
use collect_array::{try_collect_into_array, try_process};

/// A trait for converting `I: IntoIterator<Item = T>` into `[T; N]` and for
/// other such conversions.
///
/// By implementing `ArrayFromIterator` on a type, you determine how it will
/// be created from the iterator, returning an error if something goes wrong.
///
/// This is typical, for example, if you want to create a fixed length array
/// from an iterator and return an error if there are not enough elements in
/// the iterator to create the array.
///
/// This trait was created to be able to build an array of `T` from an iterator.
/// However, since it makes no sense to forbid the implementation of this trait,
/// the given purpose of this trait is rather conditional, and this trait can be
/// implemented, for example, for [`Vec<T>`].
///
/// This trait exists only because it is not possible to implement the same trait
/// twice for `[T; N]` without using unstable
/// [`feature(min_specialization)`](https://github.com/rust-lang/rust/issues/31844).
/// Therefore, the possible common trait `TryFromIterator` has been split into two
/// traits [`ArrayFromIterator`] and [`CollectionArrayFromIterator`] respectively.
///
/// If you want to create a collection from the contents of an iterator, the
/// [`Iterator::collect()`] method is preferred. See the [`Iterator::collect()`]
/// documentation for more information.
///
/// Note that you can pass to this function not only `IntoIterator`, but
/// also a mutable reference to it.
///
/// See also: [`IntoIterator`].
///
/// # Fixme
///
/// The traits [`ArrayFromIterator`] and [`CollectionArrayFromIterator`]
/// should be merged into a single trait (e.g. `TryFromIterator`) as soon
/// as `#![feature(min_specialization)]` stabilizes.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use collection_traits::ArrayFromIterator;
/// use core::ops::ControlFlow;
///
/// // IntoIterator<Item = T> --> [T; N]
/// let mut iter = 0..10;
/// let array: [_; 3] = ArrayFromIterator::try_from_iter(&mut iter).unwrap();
/// assert_eq!(array, [0, 1, 2]);
/// // Iterator can still be used
/// assert_eq!(iter.collect::<Vec<_>>(), [3, 4, 5, 6, 7, 8, 9]);
///
/// // IntoIterator<Item = Result<T, E>> --> Result<[T; N], E>
/// let iter = (0..3).map(Result::<_, i32>::Ok);
/// let array: Result<[_; 3], _> = ArrayFromIterator::try_from_iter(iter).unwrap();
/// assert_eq!(array, Ok([0, 1, 2]));
///
/// // IntoIterator<Item = Option<V>> --> Option<[T; N]>
/// let array: Option<[_; 3]> = ArrayFromIterator::try_from_iter((0..3).map(Some)).unwrap();
/// assert_eq!(array, Some([0, 1, 2]));
///
/// // IntoIterator<Item = ControlFlow<B, V>> --> ControlFlow<B, [T; N]>
/// let iter = (0..3).map(ControlFlow::<i32, _>::Continue);
/// let array: ControlFlow<_, [_; 3]> = ArrayFromIterator::try_from_iter(iter).unwrap();
/// assert_eq!(array, ControlFlow::Continue([0, 1, 2]));
/// ```
///
/// Using [`TryCollectArray::try_collect_array`] to implicitly use
/// `TryFromIterator`:
///
/// [`TryCollectArray::try_collect_array`]: crate::TryCollectArray::try_collect_array
///
/// ```
/// use collection_traits::TryCollectArray;
///
/// let array: [_; 10] = (0..10).try_collect_array().unwrap();
/// assert_eq!(array, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
/// ```
pub trait ArrayFromIterator<A>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to create a value from an iterator.
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = A>;
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = T> --> [T; N]
// ///////////////////////////////////////////////////////////////////////////////////
impl<T, const N: usize> ArrayFromIterator<T> for [T; N] {
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = T>,
    {
        let mut iter = iter.into_iter().map(NeverShortCircuit);
        try_collect_into_array(&mut iter).map(|NeverShortCircuit(array)| array)
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = Result<T, E>> --> Result<[T; N], E>
// ///////////////////////////////////////////////////////////////////////////////////
impl<T, E, const N: usize> ArrayFromIterator<Result<T, E>> for Result<[T; N], E> {
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = Result<T, E>>,
    {
        try_collect_into_array(&mut iter.into_iter())
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = Option<T>> --> Option<[T; N]>
// ///////////////////////////////////////////////////////////////////////////////////
impl<T, const N: usize> ArrayFromIterator<Option<T>> for Option<[T; N]> {
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = Option<T>>,
    {
        try_collect_into_array(&mut iter.into_iter())
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = ControlFlow<B, T>> --> ControlFlow<B, [T; N]>
// ///////////////////////////////////////////////////////////////////////////////////
impl<B, T, const N: usize> ArrayFromIterator<ControlFlow<B, T>> for ControlFlow<B, [T; N]> {
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = ControlFlow<B, T>>,
    {
        try_collect_into_array(&mut iter.into_iter())
    }
}

/// A trait for converting `I: IntoIterator<Item = IntoIterator<Item = V>>`
/// into `[T; N]` where `T: FromIterator<V>` and for other such conversions.
///
/// By implementing `CollectionArrayFromIterator` on a type, you determine
/// how it will be created from the iterator, returning an error if something
/// goes wrong.
///
/// This is typical, for example, if you want to create a fixed length array
/// from an iterator and return an error if there are not enough elements in
/// the iterator to create the array.
///
/// This trait was created to be able to build an array of `T` collections from
/// an iterator, each element of which is also an iterator. However, since it
/// makes no sense to forbid the implementation of this trait, the given purpose
/// of this trait is rather conditional, and this trait can be implemented, for
/// example, for [`Vec<T>`].
///
/// This trait exists only because it is not possible to implement the same trait
/// twice for `[T; N]` without using unstable
/// [`feature(min_specialization)`](https://github.com/rust-lang/rust/issues/31844).
/// Therefore, the possible common trait `TryFromIterator` has been split into two
/// traits [`ArrayFromIterator`] and [`CollectionArrayFromIterator`] respectively.
///
/// If you want to create a collection from the contents of an iterator, the
/// [`Iterator::collect()`] method is preferred. See the [`Iterator::collect()`]
/// documentation for more information.
///
/// Note that you can pass to this function not only `IntoIterator`, but
/// also a mutable reference to it.
///
/// See also: [`IntoIterator`].
///
/// # Fixme
///
/// The traits [`ArrayFromIterator`] and [`CollectionArrayFromIterator`]
/// should be merged into a single trait (e.g. `TryFromIterator`) as soon
/// as `#![feature(min_specialization)]` stabilizes.
///
/// # Examples
///
/// Basic usage:
///
/// ```
/// use collection_traits::CollectionArrayFromIterator;
/// use core::ops::ControlFlow;
///
/// // IntoIterator<Item = IntoIterator<Item = V>> --> [T; N]
/// // where T: FromIterator<V>,
/// let mut iter = (0..4).map(|_| 0..10);
/// let array: [Vec<_>; 3] = CollectionArrayFromIterator::try_from_iter(&mut iter).unwrap();
/// for vector in array {
///     assert_eq!(vector, (0..10).collect::<Vec<_>>());
/// }
///
/// // Iterator can still be used
/// assert_eq!(
///     iter.next().unwrap().collect::<Vec<_>>(),
///     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
/// );
///
/// // IntoIterator<Item = IntoIterator<Item = Result<V, E>>> --> Result<[T; N], E>
/// // where T: FromIterator<V>,
/// let iter = (0..3).map(|_| (1..10).map(Result::<_, i32>::Ok));
/// let array: Result<[Vec<_>; 3], _> = CollectionArrayFromIterator::try_from_iter(iter).unwrap();
/// for vector in array.unwrap() {
///     assert_eq!(vector, (1..10).collect::<Vec<_>>());
/// }
///
/// // IntoIterator<Item = IntoIterator<Item = Option<V>>> --> Option<[T; N]>
/// // where T: FromIterator<V>,
/// let iter = (0..3).map(|_| (1..10).map(Some));
/// let array: Option<[Vec<_>; 3]> = CollectionArrayFromIterator::try_from_iter(iter).unwrap();
/// for vector in array.unwrap() {
///     assert_eq!(vector, (1..10).collect::<Vec<_>>());
/// }
///
/// // IntoIterator<Item = IntoIterator<Item = ControlFlow<B, V>>> --> ControlFlow<B, [T; N]>
/// // where T: FromIterator<V>
/// let iter = (0..3).map(|_| (1..10).map(ControlFlow::<i32, _>::Continue));
/// let array: ControlFlow<_, [Vec<_>; 3]> =
///     CollectionArrayFromIterator::try_from_iter(iter).unwrap();
/// match array {
///     ControlFlow::Continue(array) => {
///         for vector in array {
///             assert_eq!(vector, (1..10).collect::<Vec<_>>());
///         }
///     }
///     ControlFlow::Break(_) => panic!(),
/// }
/// ```
///
/// Using [`TryCollectArray::try_collect_collections_array`] to implicitly use
/// `TryFromIterator`:
///
/// [`TryCollectArray::try_collect_collections_array`]: crate::TryCollectArray::try_collect_collections_array
///
/// ```
/// use collection_traits::TryCollectArray;
///
/// let mut iter = (0..3).map(|_| 0..10);
/// let array: [Vec<_>; 3] = iter.try_collect_collections_array().unwrap();
/// for vector in array {
///     assert_eq!(vector, (0..10).collect::<Vec<_>>());
/// }
/// ```
pub trait CollectionArrayFromIterator<A>: Sized {
    /// The type returned in the event of a conversion error.
    type Error;

    /// Attempts to create a value from an iterator.
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = A>;
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = IntoIterator<Item = V>> --> [T; N]
// where T: FromIterator<V>,
// ///////////////////////////////////////////////////////////////////////////////////

impl<I, T, V, const N: usize> CollectionArrayFromIterator<I> for [T; N]
where
    I: IntoIterator<Item = V>,
    T: FromIterator<V>,
{
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = I>,
    {
        let mut iter = iter
            .into_iter()
            .map(|inner_iter| NeverShortCircuit(inner_iter.into_iter().collect()));
        try_collect_into_array(&mut iter).map(|NeverShortCircuit(array)| array)
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = IntoIterator<Item = Result<V, E>>> --> Result<[T; N], E>
// where T: FromIterator<V>,
// ///////////////////////////////////////////////////////////////////////////////////

impl<I, T, V, E, const N: usize> CollectionArrayFromIterator<I> for Result<[T; N], E>
where
    I: IntoIterator<Item = Result<V, E>>,
    T: FromIterator<V>,
{
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = I>,
    {
        let mut iter = iter
            .into_iter()
            .map(|iter| try_process(iter.into_iter(), |i| i.collect::<T>()));
        try_collect_into_array(&mut iter)
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = IntoIterator<Item = Option<V>>> --> Option<[T; N]>
// where T: FromIterator<V>,
// ///////////////////////////////////////////////////////////////////////////////////

impl<I, T, V, const N: usize> CollectionArrayFromIterator<I> for Option<[T; N]>
where
    I: IntoIterator<Item = Option<V>>,
    T: FromIterator<V>,
{
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = I>,
    {
        let mut iter = iter
            .into_iter()
            .map(|iter| try_process(iter.into_iter(), |i| i.collect::<T>()));
        try_collect_into_array(&mut iter)
    }
}

// ///////////////////////////////////////////////////////////////////////////////////
// IntoIterator<Item = IntoIterator<Item = ControlFlow<B, V>>> --> ControlFlow<B, [T; N]>
// where T: FromIterator<V>,
// ///////////////////////////////////////////////////////////////////////////////////

impl<I, T, V, B, const N: usize> CollectionArrayFromIterator<I> for ControlFlow<B, [T; N]>
where
    I: IntoIterator<Item = ControlFlow<B, V>>,
    T: FromIterator<V>,
{
    type Error = IntoIter<T, N>;

    #[inline]
    fn try_from_iter<Iter>(iter: Iter) -> Result<Self, Self::Error>
    where
        Iter: IntoIterator<Item = I>,
    {
        let mut iter = iter
            .into_iter()
            .map(|iter| try_process(iter.into_iter(), |i| i.collect::<T>()));
        try_collect_into_array(&mut iter)
    }
}
