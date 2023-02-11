use super::{Equivalent, SetContainerRef, ValueContain, ValueCollectionRef};
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use std::collections;

pub trait SetContainerMut<E = <Self as ValueContain>::Value>
where
    Self: ValueCollectionRef<E> + SetContainerRef<E>,
    E: ?Sized,
{
    fn cont_insert(&mut self, value: Self::Value) -> bool;
    fn cont_remove(&mut self, key: &E) -> bool;
    fn cont_take(&mut self, key: &E) -> Option<Self::Value>;
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value>;
    fn cont_clear(&mut self);
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool;
}

impl<T, E> SetContainerMut<E> for &mut T
where
    E: ?Sized,
    T: SetContainerMut<E>,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        <T as SetContainerMut<E>>::cont_insert(self, value)
    }

    #[inline]
    fn cont_remove(&mut self, key: &E) -> bool {
        <T as SetContainerMut<E>>::cont_remove(self, key)
    }

    #[inline]
    fn cont_take(&mut self, key: &E) -> Option<Self::Value> {
        <T as SetContainerMut<E>>::cont_take(self, key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        <T as SetContainerMut<E>>::cont_replace(self, value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        <T as SetContainerMut<E>>::cont_clear(self)
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        <T as SetContainerMut<E>>::cont_retain(self, f)
    }
}

impl<T, Q, S> SetContainerMut<Q> for collections::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q, S> SetContainerMut<Q> for hashbrown::HashSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q, S> SetContainerMut<Q> for indexmap::IndexSet<T, S>
where
    T: Hash + Eq,
    Q: ?Sized + Hash + Equivalent<T>,
    S: BuildHasher,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T: Clone, Q, S> SetContainerMut<Q> for im::HashSet<T, S>
where
    T: Hash + Eq + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        if !self.contains(value.borrow()) {
            im::HashSet::insert(self, value);
            return true;
        }
        false
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key).is_some()
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.insert(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T, Q> SetContainerMut<Q> for collections::BTreeSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        self.insert(value)
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key)
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.take(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.replace(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        self.retain(f)
    }
}

impl<T: Clone, Q> SetContainerMut<Q> for im::OrdSet<T>
where
    T: Ord + Borrow<Q>,
    Q: ?Sized + Ord,
{
    #[inline]
    fn cont_insert(&mut self, value: Self::Value) -> bool {
        if !self.contains(value.borrow()) {
            im::OrdSet::insert(self, value);
            return true;
        }
        false
    }

    #[inline]
    fn cont_remove(&mut self, key: &Q) -> bool {
        self.remove(key).is_some()
    }

    #[inline]
    fn cont_take(&mut self, key: &Q) -> Option<Self::Value> {
        self.remove(key)
    }

    #[inline]
    fn cont_replace(&mut self, value: Self::Value) -> Option<Self::Value> {
        self.insert(value)
    }

    #[inline]
    fn cont_clear(&mut self) {
        self.clear()
    }

    #[inline]
    fn cont_retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Self::Value) -> bool,
    {
        let values = self.iter().cloned().collect::<Vec<_>>();
        for value in values {
            if !f(&value) {
                self.remove(value.borrow());
            }
        }
    }
}
