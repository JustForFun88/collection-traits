use crate::{Equivalent, ValueCollectionRef, ValueContain};
use smallvec::SmallVec;
use std::collections;

/// A trait that allows abstraction from different types of sequence
/// collections.
///
/// Provides an API that allows you to work with both the owning or
/// reference variable.
///
/// # Note
///
/// When implementing this trait, you need to be careful about the type `E`
/// of the  lookup value. For greater flexibility, there are no restrictions
/// on the type of search value, but one of two conditions must be met:
///
/// 1. If it is possible to implement it, then it is desirable to specify the
///    condition `E: Equivalent<Self::Value>`.
/// 2. If the first condition cannot be met, the value **must be** any borrowed
///    form of the container's value type (i.e. `Self::Value: Borrow<E>` ) .
///
/// Note that a container that implements `E: Equivalent<Self::Value>` will also
/// accept all `E` lookup values such as `Self::Value: Borrow<E>`, but the reverse
/// is not true.
pub trait VecCollectionRef<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + Sized,
    E: ?Sized,
{
    /// Returns a reference to the value at the `index` in
    /// the vector, or `None` if the `index` is out of bounds.
    ///
    /// The implementation of the method depends on the container type,
    /// so it can take as `O(1)` so as `O(log n)` time.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionRef;
    /// let vec = vec!["Joe", "Mike", "Robert"];
    /// // Unfortunately, when calling the `VecCollectionRef` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(
    ///     Some(&"Robert"),
    ///     VecCollectionRef::<str>::get_value_at(&vec, 2)
    /// );
    ///
    /// // But you do not need to specify the type E when using VecCollectionRef
    /// // as trait bound
    /// fn get_at<T>(collection: &T, index: usize) -> Option<&T::Value>
    /// where
    ///     T: VecCollectionRef,
    /// {
    ///     collection.get_value_at(index)
    /// }
    /// assert_eq!(Some(&"Robert"), get_at(&vec, 2));
    /// assert_eq!(None, get_at(&vec, 5));
    /// ```
    fn get_value_at(&self, index: usize) -> Option<&Self::Value>;

    /// Extracts a slice containing the entire vector. This method does not
    /// exist for some container types, so [`Option`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::VecCollectionRef;
    /// use std::collections::VecDeque;
    ///
    /// let vec = vec!["Joe", "Mike", "Robert"];
    /// // Unfortunately, when calling the `VecCollectionRef` methods directly,
    /// // you need to specify the type `E` because the compiler can't infer it.
    /// assert_eq!(
    ///     &["Joe", "Mike", "Robert"],
    ///     VecCollectionRef::<str>::collection_as_slice(&vec).unwrap()
    /// );
    ///
    /// // But you do not need to specify the type E when using VecCollectionRef
    /// // as trait bound
    /// fn as_slice<T: VecCollectionRef>(collection: &T) -> Option<&[T::Value]> {
    ///     collection.collection_as_slice()
    /// }
    /// assert_eq!(&["Joe", "Mike", "Robert"], as_slice(&vec).unwrap());
    ///
    /// let vec = VecDeque::from(["Joe", "Mike", "Robert"]);
    /// assert_eq!(None, as_slice(&vec));
    /// ```
    fn collection_as_slice(&self) -> Option<&[Self::Value]>;
}

impl<T, E: ?Sized> VecCollectionRef<E> for &T
where
    T: VecCollectionRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecCollectionRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecCollectionRef<E>>::collection_as_slice(self)
    }
}

impl<T, E: ?Sized> VecCollectionRef<E> for &mut T
where
    T: VecCollectionRef<E>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        <T as VecCollectionRef<E>>::get_value_at(self, index)
    }
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        <T as VecCollectionRef<E>>::collection_as_slice(self)
    }
}

impl<T, E> VecCollectionRef<E> for Vec<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecCollectionRef<E> for im::Vector<T>
where
    T: Clone,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, E> VecCollectionRef<E> for collections::VecDeque<T>
where
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        None
    }
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }
}

impl<T, A, E> VecCollectionRef<E> for SmallVec<A>
where
    A: smallvec::Array<Item = T>,
    E: ?Sized + Equivalent<T>,
{
    #[inline]
    fn get_value_at(&self, index: usize) -> Option<&Self::Value> {
        self.get(index)
    }

    #[inline]
    fn collection_as_slice(&self) -> Option<&[Self::Value]> {
        Some(self.as_slice())
    }
}
