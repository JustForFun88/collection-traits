use crate::SetContainerRef;
use core::borrow::Borrow;
use core::hash::{BuildHasher, Hash};
use im::HashSet;

pub struct ImHashDifference<'a, T: 'a, S: 'a> {
    // iterator of the first set
    iter: im::hashset::Iter<'a, T>,
    // the second set
    other: &'a im::HashSet<T, S>,
}

impl<T, S> ImHashDifference<'_, T, S> {
    #[inline]
    pub(crate) fn new<'a>(
        set: &'a HashSet<T, S>,
        other: &'a HashSet<T, S>,
    ) -> ImHashDifference<'a, T, S> {
        ImHashDifference {
            iter: set.iter(),
            other,
        }
    }
}

impl<'a, T, S> Iterator for ImHashDifference<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<T, S> core::iter::FusedIterator for ImHashDifference<'_, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

pub struct ImHashIntersection<'a, T: 'a, S: 'a> {
    // iterator of the first set
    iter: im::hashset::Iter<'a, T>,
    // the second set
    other: &'a im::HashSet<T, S>,
}

impl<T, S> ImHashIntersection<'_, T, S> {
    #[inline]
    pub(crate) fn new<'a>(
        set: &'a HashSet<T, S>,
        other: &'a HashSet<T, S>,
    ) -> ImHashIntersection<'a, T, S> {
        if set.len() <= other.len() {
            ImHashIntersection {
                iter: set.iter(),
                other,
            }
        } else {
            ImHashIntersection {
                iter: other.iter(),
                other: set,
            }
        }
    }
}

impl<'a, T, S> Iterator for ImHashIntersection<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        loop {
            let elt = self.iter.next()?;
            if self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<T, S> core::iter::FusedIterator for ImHashIntersection<'_, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}

pub struct ImHashSymmetricDifference<'a, T: 'a, S: 'a> {
    iter: core::iter::Chain<ImHashDifference<'a, T, S>, ImHashDifference<'a, T, S>>,
}

impl<T: Hash + Eq + Clone, S: BuildHasher> ImHashSymmetricDifference<'_, T, S> {
    #[inline]
    pub(crate) fn new<'a, Q>(
        set: &'a HashSet<T, S>,
        other: &'a HashSet<T, S>,
    ) -> ImHashSymmetricDifference<'a, T, S>
    where
        T: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        ImHashSymmetricDifference {
            iter: set.cont_difference(other).chain(other.cont_difference(set)),
        }
    }
}

impl<'a, T, S> Iterator for ImHashSymmetricDifference<'a, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T, S> core::iter::FusedIterator for ImHashSymmetricDifference<'_, T, S>
where
    T: Eq + Hash,
    S: BuildHasher,
{
}
