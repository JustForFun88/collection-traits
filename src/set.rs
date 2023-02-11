use super::{Equivalent, ValueContain, ValueCollectionRef};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections::{self, btree_set, hash_set};

mod set_ref;
pub use set_ref::SetContainerRef;

mod set_mut;
pub use set_mut::SetContainerMut;

pub trait SetContainer<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + SetContainerRef<E> + SetContainerMut<E>,
    E: ?Sized,
{
    type IntoValues: Iterator<Item = Self::Value>;
    fn into_cont_values(self) -> Self::IntoValues;
}

impl<T, Q, S> SetContainer<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoValues = hash_set::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, Q, S> SetContainer<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type IntoValues = hashbrown::hash_set::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, Q, S> SetContainer<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    type IntoValues = indexmap::set::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T: Clone, Q, S> SetContainer<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    type IntoValues = im::hashset::ConsumingIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T, Q> SetContainer<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    type IntoValues = btree_set::IntoIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}

impl<T: Clone, Q> SetContainer<Q> for im::OrdSet<T>
where
    T: Borrow<Q> + Ord,
    Q: Ord + ?Sized,
{
    type IntoValues = im::ordset::ConsumingIter<T>;

    #[inline]
    fn into_cont_values(self) -> Self::IntoValues {
        self.into_iter()
    }
}
