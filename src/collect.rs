mod into_iter;
pub use into_iter::IntoIter;

mod try_from;
pub use try_from::{ArrayFromIterator, CollectionArrayFromIterator};

/// A fallible version [`collect`][`Iterator::collect`], primarily intended
/// for creating fixed-length arrays. Converts an iterator to an array with
/// [`TryCollectArray::try_collect_array()`] and an array of collections with
/// [`TryCollectArray::try_collect_collections_array()`].
///
/// Also, if a failure is encountered during [`TryCollectArray::try_collect_array()`]
/// or [`TryCollectArray::try_collect_collections_array()`], the iterator is still
/// valid and may continue to be used, in which case it will continue iterating
/// starting after the element that triggered the failure. See the examples below
/// for an example of how this works.
///
/// Iimplemented for all iterators and allows you to collect any types that
/// implements [`CollectionArrayFromIterator`] or [`ArrayFromIterator`],
/// respectively.
///
/// This trait has two separate methods [`TryCollectArray::try_collect_array()`]
/// and [`TryCollectArray::try_collect_collections_array()`] due to instability
/// of the specialization ([`feature(min_specialization)`](https://github.com/rust-lang/rust/issues/31844)).
///
/// # Examples
///
/// Basic usage of [`TryCollectArray::try_collect_array()`]:
///
/// ```
/// use collection_traits::TryCollectArray;
///
/// // Successfully collecting an iterator of `IntoIterator<Item = i32>`
/// // into `[i32; N]`:
/// let u = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
///
/// let v = u.into_iter().try_collect_array::<[_; 9]>().unwrap();
/// assert_eq!(v, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
///
/// // Successfully collecting an iterator of `IntoIterator<Item = Option<i32>>`
/// // into `Option<[Vec<i32>; N]>`:
/// let u = vec![Some(1), Some(2), Some(3), Some(4), Some(5)];
///
/// let v = u.into_iter().try_collect_array::<Option<[_; 5]>>().unwrap();
/// assert_eq!(v, Some([1, 2, 3, 4, 5]));
///
/// ```
///
/// Basic usage of [`TryCollectArray::try_collect_collections_array()`]:
///
/// ```
/// use collection_traits::TryCollectArray;
///
/// // Successfully collecting an iterator of
/// // `IntoIterator<Item = IntoIterator<Item = i32>>`
/// // into `[Vec<i32>; N]`:
/// let u = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
///
/// let v = u.into_iter().try_collect_collections_array::<[Vec<_>; 3]>().unwrap();
/// assert_eq!(v, [vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]);
///
/// // Successfully collecting an iterator of
/// // `IntoIterator<Item = IntoIterator<Item = Result<i32, i32>>>`
/// // into `Result<[Vec<i32>; N], i32>`:
/// let u: Vec<Vec<Result<i32, i32>>> = vec![
///     vec![Ok(1), Ok(2), Ok(3)],
///     vec![Ok(4), Ok(5), Ok(6)],
///     vec![Ok(7), Ok(8), Ok(9)],
/// ];
///
/// let v = u
///     .into_iter()
///     .try_collect_collections_array::<Result<[Vec<_>; 3], _>>()
///     .unwrap();
/// assert_eq!(v, Ok([vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]));
///
/// let u: Vec<Vec<Result<i32, i32>>> = vec![
///     vec![Ok(1), Err(2), Ok(3)],
///     vec![Ok(4), Ok(5), Ok(6)],
///     vec![Ok(7), Ok(8), Ok(9)],
/// ];
///
/// let mut iter = u.into_iter();
/// let v = iter
///     .try_collect_collections_array::<Result<[Vec<_>; 3], _>>()
///     .unwrap();
/// assert_eq!(v, Err(2));
///
/// // Iterator can still be used
/// let v = iter
///     .try_collect_collections_array::<Result<[Vec<_>; 2], _>>()
///     .unwrap();
/// assert_eq!(v, Ok([vec![4, 5, 6], vec![7, 8, 9]]));
/// ```
pub trait TryCollectArray: Iterator {
    /// Converts an iterator to a type that implements [`ArrayFromIterator`],
    /// primarily intended for creating fixed-length arrays, i.e. to convert
    /// `I: IntoIterator<Item = T>` to `[T; N]` and for other similar
    /// transformations.
    ///
    /// Also, if a failure occurs during collection, the iterator is still valid
    /// and can continue to be used, in which case it will continue iterating
    /// from the element that caused the failure. See the last example below for
    /// an example of how this works.
    ///
    /// # Examples
    ///
    /// Basic usage of [`TryCollectArray::try_collect_array()`]:
    ///
    /// ```
    /// use collection_traits::TryCollectArray;
    ///
    /// // Successfully collecting an iterator of `IntoIterator<Item = i32>`
    /// // into `[i32; N]`:
    /// let u = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    ///
    /// let v = u.into_iter().try_collect_array::<[_; 9]>().unwrap();
    /// assert_eq!(v, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    ///
    /// // Successfully collecting an iterator of `IntoIterator<Item = Option<i32>>`
    /// // into `Option<[Vec<i32>; N]>`:
    /// let u = vec![Some(1), Some(2), Some(3), Some(4), Some(5)];
    ///
    /// let v = u.into_iter().try_collect_array::<Option<[_; 5]>>().unwrap();
    /// assert_eq!(v, Some([1, 2, 3, 4, 5]));
    ///
    /// // Failing to collect in the same way:
    ///
    /// let u = vec![Some(1), Some(2), None, Some(4), Some(5)];
    ///
    /// let v = u.into_iter().try_collect_array::<Option<[_; 5]>>().unwrap();
    /// assert_eq!(v, None);
    ///
    /// // A similar example, but with `Result`:
    ///
    /// let u: Vec<Result<i32, i32>> = vec![Ok(1), Ok(2), Ok(3), Ok(4), Ok(5)];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_array::<Result<[_; 5], _>>()
    ///     .unwrap();
    /// assert_eq!(v, Ok([1, 2, 3, 4, 5]));
    ///
    /// let u = vec![Ok(1), Ok(2), Err(3), Ok(4), Ok(5)];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_array::<Result<[_; 5], _>>()
    ///     .unwrap();
    /// assert_eq!(v, Err(3));
    /// ```
    ///
    /// Finally with [`ControlFlow`]. Note also that the iterator can
    /// continue to be used, even if a failure is encountered:
    ///
    /// ```
    /// use collection_traits::TryCollectArray;
    /// use core::ops::ControlFlow::{self, Break, Continue};
    ///
    /// let u = [Continue(1), Break(2), Continue(3), Continue(4), Continue(5)];
    /// let mut it = u.into_iter();
    ///
    /// let v = it.try_collect_array::<ControlFlow<_, [_; 3]>>().unwrap();
    /// assert_eq!(v, Break(2));
    ///
    /// // Iterator can still be used
    /// let v = it.try_collect_array::<ControlFlow<_, [_; 3]>>().unwrap();
    /// assert_eq!(v, Continue([3, 4, 5]));
    /// ```
    ///
    /// [`ControlFlow`]: https://doc.rust-lang.org/stable/std/ops/enum.ControlFlow.html
    #[inline]
    fn try_collect_array<B>(&mut self) -> Result<B, B::Error>
    where
        B: ArrayFromIterator<Self::Item>,
    {
        B::try_from_iter(self)
    }

    /// Converts an iterator to a type that implements [`CollectionArrayFromIterator`],
    /// primarily intended for creating fixed-length arrays, i.e. to convert
    /// `I: IntoIterator<Item = IntoIterator<Item = V>>` into `[T; N]` where
    /// `T: FromIterator<V>` and for other similar transformations.
    ///
    /// Also, if a failure occurs during collection, the iterator is still valid
    /// and can continue to be used, in which case it will continue iterating
    /// from the element that caused the failure. See the last example below for
    /// an example of how this works.
    ///
    /// # Examples
    ///
    /// Basic usage of [`TryCollectArray::try_collect_collections_array()`]:
    ///
    /// ```
    /// use collection_traits::TryCollectArray;
    ///
    /// // Successfully collecting an iterator of
    /// // `IntoIterator<Item = IntoIterator<Item = i32>>`
    /// // into `[Vec<i32>; N]`:
    /// let u = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
    ///
    /// let v = u.into_iter().try_collect_collections_array::<[Vec<_>; 3]>().unwrap();
    /// assert_eq!(v, [vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]);
    ///
    /// // Successfully collecting an iterator of
    /// // `IntoIterator<Item = IntoIterator<Item = Option<i32>>>`
    /// // into `Option<[Vec<i32>; N]>`:
    /// let u = vec![
    ///     vec![Some(1), Some(2), Some(3)],
    ///     vec![Some(4), Some(5), Some(6)],
    ///     vec![Some(7), Some(8), Some(9)],
    /// ];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_collections_array::<Option<[Vec<_>; 3]>>()
    ///     .unwrap();
    /// assert_eq!(v, Some([vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]));
    ///
    /// // Failing to collect in the same way:
    ///
    /// let u = vec![
    ///     vec![Some(1), Some(2), Some(3)],
    ///     vec![Some(4), Some(5), Some(6)],
    ///     vec![Some(7), None, Some(9)],
    /// ];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_collections_array::<Option<[Vec<_>; 3]>>()
    ///     .unwrap();
    /// assert_eq!(v, None);
    ///
    /// // A similar example, but with `Result`:
    ///
    /// let u: Vec<Vec<Result<i32, i32>>> = vec![
    ///     vec![Ok(1), Ok(2), Ok(3)],
    ///     vec![Ok(4), Ok(5), Ok(6)],
    ///     vec![Ok(7), Ok(8), Ok(9)],
    /// ];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_collections_array::<Result<[Vec<_>; 3], _>>()
    ///     .unwrap();
    /// assert_eq!(v, Ok([vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]));
    ///
    /// let u: Vec<Vec<Result<i32, i32>>> = vec![
    ///     vec![Ok(1), Ok(2), Ok(3)],
    ///     vec![Ok(4), Ok(5), Ok(6)],
    ///     vec![Ok(7), Err(8), Ok(9)],
    /// ];
    ///
    /// let v = u
    ///     .into_iter()
    ///     .try_collect_collections_array::<Result<[Vec<_>; 3], _>>()
    ///     .unwrap();
    /// assert_eq!(v, Err(8));
    /// ```
    ///
    /// Finally with [`ControlFlow`]. Note also that the iterator can
    /// continue to be used, even if a failure is encountered:
    ///
    /// ```
    /// use collection_traits::TryCollectArray;
    /// use core::ops::ControlFlow::{self, Break, Continue};
    ///
    /// let u = [
    ///     [Continue(1), Continue(2), Break(3)],
    ///     [Continue(4), Continue(5), Continue(6)],
    ///     [Continue(7), Continue(8), Continue(9)],
    ///     [Continue(10), Continue(11), Continue(12)],
    /// ];
    /// let mut it = u.into_iter();
    ///
    /// let v = it.try_collect_collections_array::<ControlFlow<_, [Vec<_>; 3]>>().unwrap();
    /// assert_eq!(v, Break(3));
    ///
    /// // Iterator can still be used
    /// let v = it.try_collect_collections_array::<ControlFlow<_, [Vec<_>; 3]>>().unwrap();
    /// assert_eq!(
    ///     v,
    ///     Continue([vec![4, 5, 6], vec![7, 8, 9], vec![10, 11, 12]])
    /// );
    /// ```
    ///
    /// [`ControlFlow`]: https://doc.rust-lang.org/std/ops/enum.ControlFlow.html
    #[inline]
    fn try_collect_collections_array<B>(&mut self) -> Result<B, B::Error>
    where
        B: CollectionArrayFromIterator<Self::Item>,
    {
        B::try_from_iter(self)
    }
}

impl<T: Iterator> TryCollectArray for T {}
