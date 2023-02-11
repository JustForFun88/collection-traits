use super::{Equivalent, ValueContain, ValueCollectionRef};
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

pub trait SetContainerRef<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + Sized + private_set_containers::Sealed,
    E: ?Sized,
{
    type Difference<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;
    type Intersection<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;
    type SymmetricDifference<'a>: Iterator<Item = &'a Self::Value>
    where
        Self: 'a,
        Self::Value: 'a;

    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a>;
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a>;
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a>;
    fn cont_is_disjoint(&self, other: &Self) -> bool;
    fn cont_is_subset(&self, other: &Self) -> bool;
}

impl<T, E: ?Sized> SetContainerRef<E> for &T
where
    T: SetContainerRef<E>,
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        <T as SetContainerRef<E>>::cont_difference(self, other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        <T as SetContainerRef<E>>::cont_intersection(self, other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        <T as SetContainerRef<E>>::cont_symmetric_difference(self, other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        <T as SetContainerRef<E>>::cont_is_disjoint(self, other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        <T as SetContainerRef<E>>::cont_is_subset(self, other)
    }
}

impl<T, E: ?Sized> SetContainerRef<E> for &mut T
where
    T: SetContainerRef<E>,
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        <T as SetContainerRef<E>>::cont_difference(self, other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        <T as SetContainerRef<E>>::cont_intersection(self, other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        <T as SetContainerRef<E>>::cont_symmetric_difference(self, other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        <T as SetContainerRef<E>>::cont_is_disjoint(self, other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        <T as SetContainerRef<E>>::cont_is_subset(self, other)
    }
}

impl<T, Q, S> SetContainerRef<Q> for collections::HashSet<T, S>
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q, S> SetContainerRef<Q> for hashbrown::HashSet<T, S>
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q, S> SetContainerRef<Q> for indexmap::IndexSet<T, S>
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T: Clone, Q, S> SetContainerRef<Q> for im::HashSet<T, S>
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        ImHashDifference::new(self, other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        ImHashIntersection::new(self, other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        ImHashSymmetricDifference::new(self, other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(v.borrow()))
        } else {
            other.iter().all(|v| !self.contains(v.borrow()))
        }
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        im::HashSet::is_subset(self, other.clone())
    }
}

impl<T, Q> SetContainerRef<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type Difference<'a>  = btree_set::Difference<'a, T> where Self: 'a, T: 'a;
    type Intersection<'a>  = btree_set::Intersection<'a, T> where Self: 'a, T: 'a;
    type SymmetricDifference<'a>  = btree_set::SymmetricDifference<'a, T> where Self: 'a, T: 'a;

    #[inline]
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        self.difference(other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        self.intersection(other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        self.symmetric_difference(other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        self.is_disjoint(other)
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
        self.is_subset(other)
    }
}

impl<T, Q> SetContainerRef<Q> for im::OrdSet<T>
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
    fn cont_difference<'a>(&'a self, other: &'a Self) -> Self::Difference<'a> {
        ImOrdDifference::new(self, other)
    }

    #[inline]
    fn cont_intersection<'a>(&'a self, other: &'a Self) -> Self::Intersection<'a> {
        ImOrdIntersection::new(self, other)
    }

    #[inline]
    fn cont_symmetric_difference<'a>(&'a self, other: &'a Self) -> Self::SymmetricDifference<'a> {
        ImOrdSymmetricDifference::new(self, other)
    }

    #[inline]
    fn cont_is_disjoint(&self, other: &Self) -> bool {
        <Self as SetContainerRef<Q>>::cont_intersection(self, other)
            .next()
            .is_none()
    }

    #[inline]
    fn cont_is_subset(&self, other: &Self) -> bool {
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
