use super::{Equivalent, ValueCollectionRef, ValueContain};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections::{self, btree_set, hash_set};

mod set_ref;
pub use set_ref::SetCollectionRef;

mod set_mut;
pub use set_mut::SetCollectionMut;

/// A trait that allows you to abstract from various types of set
/// collections.
///
/// Provides an API that allows you to convert a `SetCollection`
/// to a consuming iterator.
///
/// # Note
///
/// Note that this trait guarantees that all values are unique and do not
/// repeat within the container.
///
/// To prevent this invariant from being violated, the implementation of
/// this trait outside of this crate is prohibited (via [`SetCollectionRef`]).
//
// # Notes about the implementation of the trait within this crate
//
// When implementing this trait, you need to be careful about the type `E`
// of the  lookup value. For greater flexibility, there are no restrictions
// on the type of search value, but one of two conditions must be met:
//
// 1. If it is possible to implement it, then it is desirable to specify
//    the condition `E: Equivalent<Self::Value>`.
// 2. If the first condition cannot be met (e.g. for [`std::collections::HashSet`]),
//    the value **must be** any borrowed form of the container's value type (i.e.
//    `Self::Value: Borrow<E>` ) .
//
// Note that a container that implements `E: Equivalent<Self::Value>` will also
// accept all `E` lookup values such as `Self::Value: Borrow<E>`, but the reverse
// is not true.
pub trait SetCollection<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + SetCollectionRef<E> + SetCollectionMut<E>,
    E: ?Sized,
{
    /// An owning iterator over the values of a collection in arbitrary order.
    /// The iterator element type is `Self::Value`.
    ///
    /// This `type` is created by the [`SetCollection::into_collection_iter()`].
    /// See its documentation for more.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollection;
    /// use hashbrown::HashSet;
    ///
    /// let set: HashSet<_> = ["a", "b", "c"].into();
    ///
    /// // Unfortunately, when calling SetCollection methods directly,
    /// // you need to specify the type E
    /// let mut values = SetCollection::<str>::into_collection_iter(set);
    /// let mut vec = vec![values.next(), values.next(), values.next()];
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, [Some("a"), Some("b"), Some("c")]);
    ///
    /// // It is fused iterator
    /// assert_eq!(values.next(), None);
    /// assert_eq!(values.next(), None);
    /// ```
    type IntoIter: Iterator<Item = Self::Value>;

    /// Creates a consuming iterator visiting all the values in arbitrary order.
    /// The set cannot be used after calling this. The iterator element type
    /// is `Self::Value`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollection;
    /// use hashbrown::HashSet;
    /// use std::collections::BTreeSet;
    ///
    /// let set: HashSet<_> = ["a", "b", "c"].into();
    ///
    /// // Unfortunately, when calling SetCollection methods directly,
    /// // you need to specify the type E
    /// let mut vec = SetCollection::<str>::into_collection_iter(set).collect::<Vec<_>>();
    ///
    /// // The `IntoKeys` iterator produces keys in arbitrary order, so the
    /// // keys must be sorted to test them against a sorted array.
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    ///
    /// // But you do not need to specify the type E when using SetCollection
    /// // as trait bound
    /// fn collection_iter<T>(collection: T) -> impl Iterator<Item = T::Value>
    /// where
    ///     T: SetCollection,
    /// {
    ///     collection.into_collection_iter()
    /// }
    ///
    /// let set: HashSet<_> = ["a", "b", "c"].into();
    ///
    /// let mut vec = collection_iter(set).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    ///
    /// let set: BTreeSet<_> = ["a", "b", "c"].into();
    ///
    /// let mut vec = collection_iter(set).collect::<Vec<_>>();
    /// vec.sort_unstable();
    /// assert_eq!(vec, ["a", "b", "c"]);
    /// ```
    fn into_collection_iter(self) -> Self::IntoIter;
}

impl<T, Q, S> SetCollection<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoIter = hash_set::IntoIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T, Q, S> SetCollection<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type IntoIter = hashbrown::hash_set::IntoIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T, Q, S> SetCollection<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type IntoIter = indexmap::set::IntoIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T: Clone, Q, S> SetCollection<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoIter = im::hashset::ConsumingIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T, Q> SetCollection<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoIter = btree_set::IntoIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T: Clone, Q> SetCollection<Q> for im::OrdSet<T>
where
    T: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    type IntoIter = im::ordset::ConsumingIter<T>;

    #[inline]
    fn into_collection_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}
