use super::{Equivalent, ValueCollectionRef, ValueContain};
use crate::{
    im_iters::ITER_PERFORMANCE_TIPPING_SIZE_DIFF, ImHashDifference, ImHashIntersection,
    ImHashSymmetricDifference, ImOrdDifference, ImOrdIntersection, ImOrdSymmetricDifference,
};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections::{self, btree_set, hash_set};

/// A private module that guarantees that the user of the [`SetContainerRef`]
/// trait (and other set traits) cannot implement this trait on a container
/// that is not actually a set and thus blocks the possibility of violating
/// the invariant provided by the `SetContainerRef` trait, namely the invariant
/// that each possible value appears at most once in the collection.
///
/// SHOULD BE IMPLEMENTED ONLY FOR TYPES THAT REPRESENT A SOME SET TYPE!!!
///  
/// Without this private module, the user can implement the [`SetContainerRef`]
/// trait for example for `[T; N]` where `T: SetContainerRef`.
///
/// [`SetContainerRef`]: crate::SetContainerRef
mod private_set_containers {
    use std::collections;
    pub trait Sealed {}

    impl<T, S> Sealed for collections::HashSet<T, S> {}

    impl<T, S> Sealed for hashbrown::HashSet<T, S> {}

    impl<T, S> Sealed for im::HashSet<T, S> {}

    impl<T, S> Sealed for indexmap::IndexSet<T, S> {}

    impl<T> Sealed for collections::BTreeSet<T> {}

    impl<T> Sealed for im::OrdSet<T> {}

    impl<T: Sealed> Sealed for &T {}

    impl<T: Sealed> Sealed for &mut T {}
}

/// A trait that allows you to abstract from various types of set
/// collections.
///
/// Provides an API that allows you to work with both the owning or
/// reference variable.
///
/// # Note
///
/// Note that this trait guarantees that all values are unique and do not
/// repeat within the container.
///
/// To prevent this invariant from being violated, the implementation of
/// this trait outside of this crate is prohibited.
//
// # Notes about the implementation of the trait within this crate
//
// When implementing this trait, you need to be careful about the type `E`
// of the  lookup key. For greater flexibility, there are no restrictions
// on the type of search key, but one of two conditions must be met:
//
// 1. If it is possible to implement it, then it is desirable to specify
//    the condition `E: Equivalent<Self::Value>`.
// 2. If the first condition cannot be met (e.g. for [`std::collections::HashSet`]),
//    the key **must be** any borrowed form of the container's key type (i.e.
//    `Self::Value: Borrow<E>` ) .
//
// Note that a container that implements `E: Equivalent<Self::Value>` will also
// accept all `E` lookup keys such as `Self::Value: Borrow<E>`, but the reverse
// is not true.
pub trait SetCollectionRef<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + Sized + private_set_containers::Sealed,
    E: ?Sized,
{
    /// A lazy iterator producing elements in the difference of `set`s.
    ///
    /// It is created by the [`SetCollectionRef::collection_difference()`].
    /// See its documentation for more.
    type Difference<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// A lazy iterator producing elements in the intersection of `set`s.
    ///
    /// It is created by the [`SetCollectionRef::collection_intersection()`].
    /// See its documentation for more.
    type Intersection<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// A lazy iterator producing elements in the symmetric difference of `HashSet`s.
    ///
    /// It is created by the [`SetCollectionRef::collection_symmetric_difference()`].
    /// See its documentation for more.
    type SymmetricDifference<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    /// Visits the values representing the difference,
    /// i.e., the values that are in `self` but not in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionRef;
    /// use hashbrown::HashSet;
    ///
    /// let a: HashSet<_> = HashSet::from([1, 2, 3]);
    /// let b: HashSet<_> = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`. Unfortunately, when calling SetCollectionRef
    /// // methods directly, you need to specify the type E
    /// let diff: HashSet<_> = SetCollectionRef::<i32>::collection_difference(&a, &b).collect();
    /// assert_eq!(diff, HashSet::from([&1]));
    ///
    /// // But you do not need to specify the type E when using SetCollectionRef
    /// // as trait bound
    /// fn difference<'a, T>(set_1: &'a T, set_2: &'a T) -> T::Difference<'a>
    /// where
    ///     T: SetCollectionRef,
    /// {
    ///     set_1.collection_difference(set_2)
    /// }
    ///
    /// let diff: Vec<_> = difference(&a, &b).collect();
    /// assert_eq!(diff, [&1]);
    ///
    /// // Note that difference is not symmetric, and `b - a` means something else:
    /// let diff: Vec<_> = difference(&b, &a).collect();
    /// assert_eq!(diff, [&4]);
    /// ```
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a>;

    /// Visits the values representing the intersection,
    /// i.e., the values that are both in `self` and `other`.
    ///
    /// When an equal element is present in `self` and `other`
    /// then the resulting `Intersection` may yield references to
    /// one or the other. This can be relevant if `T` contains fields which
    /// are not compared by its `Eq` implementation, and may hold different
    /// value between the two equal copies of `T` in the two sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionRef;
    /// use hashbrown::HashSet;
    ///
    /// let a: HashSet<_> = HashSet::from([1, 2, 3]);
    /// let b: HashSet<_> = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`. Unfortunately, when calling SetCollectionRef
    /// // methods directly, you need to specify the type E
    /// let diff: HashSet<_> = SetCollectionRef::<i32>::collection_intersection(&a, &b).collect();
    /// assert_eq!(diff, [2, 3].iter().collect());
    ///
    /// // But you do not need to specify the type E when using SetCollectionRef
    /// // as trait bound
    /// fn intersection<'a, T>(set_1: &'a T, set_2: &'a T) -> T::Intersection<'a>
    /// where
    ///     T: SetCollectionRef,
    /// {
    ///     set_1.collection_intersection(set_2)
    /// }
    ///
    /// let diff: HashSet<_> = intersection(&a, &b).collect();
    /// assert_eq!(diff, [2, 3].iter().collect());
    ///
    /// let diff: HashSet<_> = intersection(&b, &a).collect();
    /// assert_eq!(diff, [2, 3].iter().collect());
    /// ```
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a>;

    /// Visits the values representing the symmetric difference,
    /// i.e., the values that are in `self` or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionRef;
    /// use hashbrown::HashSet;
    ///
    /// let a: HashSet<_> = HashSet::from([1, 2, 3]);
    /// let b: HashSet<_> = HashSet::from([4, 2, 3, 4]);
    ///
    /// // Can be seen as `a - b`. Unfortunately, when calling SetCollectionRef
    /// // methods directly, you need to specify the type E
    /// let diff: HashSet<_> =
    ///     SetCollectionRef::<i32>::collection_symmetric_difference(&a, &b).collect();
    /// assert_eq!(diff, [1, 4].iter().collect());
    ///
    /// // But you do not need to specify the type E when using SetCollectionRef
    /// // as trait bound
    /// fn symmetric_difference<'a, T>(set_1: &'a T, set_2: &'a T) -> T::SymmetricDifference<'a>
    /// where
    ///     T: SetCollectionRef,
    /// {
    ///     set_1.collection_symmetric_difference(set_2)
    /// }
    ///
    /// let diff1: HashSet<_> = symmetric_difference(&a, &b).collect();
    /// let diff2: HashSet<_> = symmetric_difference(&b, &a).collect();
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 4].iter().collect());
    /// ```
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a>;

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionRef;
    /// use hashbrown::HashSet;
    ///
    /// let a: HashSet<_> = HashSet::from([1, 2, 3]);
    /// let mut b = HashSet::new();
    ///
    /// // Unfortunately, when calling SetCollectionRef
    /// // methods directly, you need to specify the type E
    /// assert_eq!(SetCollectionRef::<i32>::is_disjoint(&a, &b), true);
    ///
    /// // But you do not need to specify the type E when using SetCollectionRef
    /// // as trait bound
    /// fn is_disjoint<T: SetCollectionRef>(set_1: &T, set_2: &T) -> bool {
    ///     set_1.is_disjoint(set_2)
    /// }
    ///
    /// b.insert(4);
    /// assert_eq!(is_disjoint(&a, &b), true);
    /// b.insert(1);
    /// assert_eq!(is_disjoint(&a, &b), false);
    /// ```
    fn is_disjoint(&self, other: &Self) -> bool;

    /// Returns `true` if the set is a subset of another,
    /// i.e., `other` contains at least all the values in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collection_traits::SetCollectionRef;
    /// use hashbrown::HashSet;
    ///
    /// let sup: HashSet<_> = HashSet::from([1, 2, 3]);
    /// let mut set = HashSet::new();
    ///
    /// // Unfortunately, when calling SetCollectionRef
    /// // methods directly, you need to specify the type E
    /// assert_eq!(SetCollectionRef::<i32>::is_subset(&set, &sup), true);
    ///
    /// // But you do not need to specify the type E when using SetCollectionRef
    /// // as trait bound
    /// fn is_subset<T: SetCollectionRef>(set_1: &T, set_2: &T) -> bool {
    ///     set_1.is_subset(set_2)
    /// }
    ///
    /// set.insert(2);
    /// assert_eq!(is_subset(&set, &sup), true);
    /// set.insert(4);
    /// assert_eq!(is_subset(&set, &sup), false);
    /// ```
    fn is_subset(&self, other: &Self) -> bool;
}

impl<T, E: ?Sized> SetCollectionRef<E> for &T
where
    T: SetCollectionRef<E>,
{
    type Difference<'a> = T::Difference<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    type Intersection<'a> = T::Intersection<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    type SymmetricDifference<'a> = T::SymmetricDifference<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        <T as SetCollectionRef<E>>::collection_difference(self, other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        <T as SetCollectionRef<E>>::collection_intersection(self, other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        <T as SetCollectionRef<E>>::collection_symmetric_difference(self, other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        <T as SetCollectionRef<E>>::is_disjoint(self, other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        <T as SetCollectionRef<E>>::is_subset(self, other)
    }
}

impl<T, E: ?Sized> SetCollectionRef<E> for &mut T
where
    T: SetCollectionRef<E>,
{
    type Difference<'a> = T::Difference<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    type Intersection<'a> = T::Intersection<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    type SymmetricDifference<'a> = T::SymmetricDifference<'a>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        <T as SetCollectionRef<E>>::collection_difference(self, other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        <T as SetCollectionRef<E>>::collection_intersection(self, other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        <T as SetCollectionRef<E>>::collection_symmetric_difference(self, other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        <T as SetCollectionRef<E>>::is_disjoint(self, other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        <T as SetCollectionRef<E>>::is_subset(self, other)
    }
}

impl<T, Q, S> SetCollectionRef<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Difference<'a>  = hash_set::Difference<'a, T, S> where Self: 'a, T:'a, S:'a;
    type Intersection<'a>  = hash_set::Intersection<'a, T, S> where Self: 'a, T:'a, S:'a;
    type SymmetricDifference<'a>  = hash_set::SymmetricDifference<'a, T, S>
    where
        Self: 'a, T:'a, S:'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q, S> SetCollectionRef<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type Difference<'a>  = hashbrown::hash_set::Difference<'a, T, S> where Self: 'a, T:'a, S:'a;
    type Intersection<'a>  = hashbrown::hash_set::Intersection<'a, T, S> where Self: 'a, T:'a, S:'a;
    type SymmetricDifference<'a>  = hashbrown::hash_set::SymmetricDifference<'a, T, S>
    where
        Self: 'a, T:'a, S:'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q, S> SetCollectionRef<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type Difference<'a>  = indexmap::set::Difference<'a, T, S> where Self: 'a, T: 'a, S: 'a;
    type Intersection<'a>  = indexmap::set::Intersection<'a, T, S> where Self: 'a, T: 'a, S: 'a;
    type SymmetricDifference<'a>  = indexmap::set::SymmetricDifference<'a, T, S, S>
    where
        Self: 'a, T: 'a, S: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T: Clone, Q, S> SetCollectionRef<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type Difference<'a> = ImHashDifference<'a, T, S>
    where
        Self: 'a,
        Self::Value: 'a,
        S: 'a;

    type Intersection<'a> = ImHashIntersection<'a, T, S>
    where
        Self: 'a,
        Self::Value: 'a,
        S: 'a;

    type SymmetricDifference<'a> = ImHashSymmetricDifference<'a, T, S>
    where
        Self: 'a,
        Self::Value: 'a,
        S: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        ImHashDifference::new(self, other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        ImHashIntersection::new(self, other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        ImHashSymmetricDifference::new(self, other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v.borrow()))
        } else {
            other.iter().all(|v| !self.contains(v.borrow()))
        }
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        im::HashSet::is_subset(self, other.clone())
    }
}

impl<T, Q> SetCollectionRef<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Difference<'a>  = btree_set::Difference<'a, T> where Self: 'a, T: 'a;
    type Intersection<'a>  = btree_set::Intersection<'a, T> where Self: 'a, T: 'a;
    type SymmetricDifference<'a>  = btree_set::SymmetricDifference<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q> SetCollectionRef<Q> for im::OrdSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Difference<'a> = ImOrdDifference<'a, T>
    where
        Self: 'a,
        Self::Value: 'a;

    type Intersection<'a> = ImOrdIntersection<'a, T>
    where
        Self: 'a,
        Self::Value: 'a;

    type SymmetricDifference<'a> = ImOrdSymmetricDifference<'a, T>
    where
        Self: 'a,
        Self::Value: 'a;

    #[inline]
    fn collection_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        ImOrdDifference::new(self, other)
    }

    #[inline]
    fn collection_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        ImOrdIntersection::new(self, other)
    }

    #[inline]
    fn collection_symmetric_difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> Self::SymmetricDifference<'a> {
        ImOrdSymmetricDifference::new(self, other)
    }

    #[inline]
    fn is_disjoint(&self, other: &Self) -> bool {
        <Self as SetCollectionRef<Q>>::collection_intersection(self, other)
            .next()
            .is_none()
    }

    #[inline]
    fn is_subset(&self, other: &Self) -> bool {
        use core::cmp::Ordering::{Equal, Greater, Less};
        // Same result as self.difference(other).next().is_none()
        // but the code below is faster (hugely in some cases).
        if self.len() > other.len() {
            return false;
        }
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (self.get_min(), self.get_max()) {
                (self_min, self_max)
            } else {
                return true; // self is empty
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.get_min(), other.get_max()) {
                (other_min, other_max)
            } else {
                return false; // other is empty
            };
        let mut self_iter = self.iter();
        match self_min.cmp(other_min) {
            Less => return false,
            Equal => {
                self_iter.next();
            }
            Greater => (),
        }
        match self_max.cmp(other_max) {
            Greater => return false,
            Equal => {
                self_iter.next_back();
            }
            Less => (),
        }
        if self_iter.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF {
            for next in self_iter {
                if !other.contains(next.borrow()) {
                    return false;
                }
            }
        } else {
            let mut other_iter = other.iter();
            other_iter.next();
            other_iter.next_back();
            let mut self_next = self_iter.next();
            while let Some(self1) = self_next {
                match other_iter.next().map_or(Less, |other1| self1.cmp(other1)) {
                    Less => return false,
                    Equal => self_next = self_iter.next(),
                    Greater => (),
                }
            }
        }
        true
    }
}
