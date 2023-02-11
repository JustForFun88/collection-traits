use core::cmp::Ordering::{Equal, Greater, Less};
use im::OrdSet;

// This constant is used by functions that compare two sets.
// It estimates the relative size at which searching performs better
// than iterating, based on the benchmarks in
// https://github.com/ssomers/rust_bench_btreeset_intersection.
// It's used to divide rather than multiply sizes, to rule out overflow,
// and it's a power of two to make that division cheap.
pub(crate) const ITER_PERFORMANCE_TIPPING_SIZE_DIFF: usize = 16;

pub struct ImOrdDifference<'a, T: Ord + 'a> {
    inner: ImOrdDifferenceInner<'a, T>,
}

enum ImOrdDifferenceInner<'a, T: Ord + 'a> {
    Stitch {
        // iterate all of `self` and some of `other`, spotting matches along the way
        self_iter: im::ordset::Iter<'a, T>,
        other_iter: core::iter::Peekable<im::ordset::Iter<'a, T>>,
    },
    Search {
        // iterate `self`, look up in `other`
        self_iter: im::ordset::Iter<'a, T>,
        other_set: &'a im::OrdSet<T>,
    },
    Iterate(im::ordset::Iter<'a, T>), // simply produce all elements in `self`
}

impl<T: Ord> ImOrdDifference<'_, T> {
    #[inline]
    pub(crate) fn new<'a>(set: &'a OrdSet<T>, other: &'a OrdSet<T>) -> ImOrdDifference<'a, T> {
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (set.get_min(), set.get_max()) {
                (self_min, self_max)
            } else {
                return ImOrdDifference {
                    inner: ImOrdDifferenceInner::Iterate(set.iter()),
                };
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.get_min(), other.get_max()) {
                (other_min, other_max)
            } else {
                return ImOrdDifference {
                    inner: ImOrdDifferenceInner::Iterate(set.iter()),
                };
            };
        ImOrdDifference {
            inner: match (self_min.cmp(other_max), self_max.cmp(other_min)) {
                (Greater, _) | (_, Less) => ImOrdDifferenceInner::Iterate(set.iter()),
                (Equal, _) => {
                    let mut self_iter = set.iter();
                    self_iter.next();
                    ImOrdDifferenceInner::Iterate(self_iter)
                }
                (_, Equal) => {
                    let mut self_iter = set.iter();
                    self_iter.next_back();
                    ImOrdDifferenceInner::Iterate(self_iter)
                }
                _ if set.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    ImOrdDifferenceInner::Search {
                        self_iter: set.iter(),
                        other_set: other,
                    }
                }
                _ => ImOrdDifferenceInner::Stitch {
                    self_iter: set.iter(),
                    other_iter: other.iter().peekable(),
                },
            },
        }
    }
}

impl<'a, T: Ord> Iterator for ImOrdDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            ImOrdDifferenceInner::Stitch {
                self_iter,
                other_iter,
            } => {
                let mut self_next = self_iter.next()?;
                loop {
                    match other_iter
                        .peek()
                        .map_or(Less, |other_next| self_next.cmp(other_next))
                    {
                        Less => return Some(self_next),
                        Equal => {
                            self_next = self_iter.next()?;
                            other_iter.next();
                        }
                        Greater => {
                            other_iter.next();
                        }
                    }
                }
            }
            ImOrdDifferenceInner::Search {
                self_iter,
                other_set,
            } => loop {
                let self_next = self_iter.next()?;
                if !other_set.contains(self_next) {
                    return Some(self_next);
                }
            },
            ImOrdDifferenceInner::Iterate(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (self_len, other_len) = match &self.inner {
            ImOrdDifferenceInner::Stitch {
                self_iter,
                other_iter,
            } => (self_iter.len(), other_iter.len()),
            ImOrdDifferenceInner::Search {
                self_iter,
                other_set,
            } => (self_iter.len(), other_set.len()),
            ImOrdDifferenceInner::Iterate(iter) => (iter.len(), 0),
        };
        (self_len.saturating_sub(other_len), Some(self_len))
    }

    #[inline]
    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: Ord> core::iter::FusedIterator for ImOrdDifference<'_, T> {}

pub struct ImOrdIntersection<'a, T: Ord + 'a> {
    inner: ImOrdIntersectionInner<'a, T>,
}

enum ImOrdIntersectionInner<'a, T: Ord + 'a> {
    Stitch {
        // iterate similarly sized sets jointly, spotting matches along the way
        a: im::ordset::Iter<'a, T>,
        b: im::ordset::Iter<'a, T>,
    },
    Search {
        // iterate a small set, look up in the large set
        small_iter: im::ordset::Iter<'a, T>,
        large_set: &'a im::OrdSet<T>,
    },
    Answer(Option<&'a T>), // return a specific element or emptiness
}

impl<T: Ord> ImOrdIntersection<'_, T> {
    #[inline]
    pub(crate) fn new<'a>(set: &'a OrdSet<T>, other: &'a OrdSet<T>) -> ImOrdIntersection<'a, T> {
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (set.get_min(), set.get_max()) {
                (self_min, self_max)
            } else {
                return ImOrdIntersection {
                    inner: ImOrdIntersectionInner::Answer(None),
                };
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.get_min(), other.get_max()) {
                (other_min, other_max)
            } else {
                return ImOrdIntersection {
                    inner: ImOrdIntersectionInner::Answer(None),
                };
            };
        ImOrdIntersection {
            inner: match (self_min.cmp(other_max), self_max.cmp(other_min)) {
                (Greater, _) | (_, Less) => ImOrdIntersectionInner::Answer(None),
                (Equal, _) => ImOrdIntersectionInner::Answer(Some(self_min)),
                (_, Equal) => ImOrdIntersectionInner::Answer(Some(self_max)),
                _ if set.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    ImOrdIntersectionInner::Search {
                        small_iter: set.iter(),
                        large_set: other,
                    }
                }
                _ if other.len() <= set.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    ImOrdIntersectionInner::Search {
                        small_iter: other.iter(),
                        large_set: set,
                    }
                }
                _ => ImOrdIntersectionInner::Stitch {
                    a: set.iter(),
                    b: other.iter(),
                },
            },
        }
    }
}

impl<'a, T: Ord> Iterator for ImOrdIntersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            ImOrdIntersectionInner::Stitch { a, b } => {
                let mut a_next = a.next()?;
                let mut b_next = b.next()?;
                loop {
                    match a_next.cmp(b_next) {
                        Less => a_next = a.next()?,
                        Greater => b_next = b.next()?,
                        Equal => return Some(a_next),
                    }
                }
            }
            ImOrdIntersectionInner::Search {
                small_iter,
                large_set,
            } => loop {
                let small_next = small_iter.next()?;
                if large_set.contains(small_next) {
                    return Some(small_next);
                }
            },
            ImOrdIntersectionInner::Answer(answer) => answer.take(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            ImOrdIntersectionInner::Stitch { a, b } => (0, Some(core::cmp::min(a.len(), b.len()))),
            ImOrdIntersectionInner::Search { small_iter, .. } => (0, Some(small_iter.len())),
            ImOrdIntersectionInner::Answer(None) => (0, Some(0)),
            ImOrdIntersectionInner::Answer(Some(_)) => (1, Some(1)),
        }
    }

    #[inline]
    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: Ord> core::iter::FusedIterator for ImOrdIntersection<'_, T> {}

pub struct ImOrdSymmetricDifference<'a, T: Ord + 'a>(MergeIterInner<im::ordset::Iter<'a, T>>);

impl<T: Ord> ImOrdSymmetricDifference<'_, T> {
    #[inline]
    pub(crate) fn new<'a>(
        set: &'a OrdSet<T>,
        other: &'a OrdSet<T>,
    ) -> ImOrdSymmetricDifference<'a, T> {
        ImOrdSymmetricDifference(MergeIterInner::new(set.iter(), other.iter()))
    }
}

impl<'a, T: Ord> Iterator for ImOrdSymmetricDifference<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (a_next, b_next) = self.0.nexts(Self::Item::cmp);
            if a_next.and(b_next).is_none() {
                return a_next.or(b_next);
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_len, b_len) = self.0.lens();
        // No checked_add, because even if a and b refer to the same set,
        // and T is a zero-sized type, the storage overhead of sets limits
        // the number of elements to less than half the range of usize.
        (0, Some(a_len + b_len))
    }

    #[inline]
    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: Ord> core::iter::FusedIterator for ImOrdSymmetricDifference<'_, T> {}

/// Core of an iterator that merges the output of two strictly ascending iterators,
/// for instance a union or a symmetric difference.
struct MergeIterInner<I: Iterator> {
    a: I,
    b: I,
    peeked: Option<Peeked<I>>,
}

/// Benchmarks faster than wrapping both iterators in a Peekable,
/// probably because we can afford to impose a FusedIterator bound.
#[derive(Clone, Debug)]
enum Peeked<I: Iterator> {
    A(I::Item),
    B(I::Item),
}

impl<I: Iterator> MergeIterInner<I> {
    /// Creates a new core for an iterator merging a pair of sources.
    fn new(a: I, b: I) -> Self {
        MergeIterInner { a, b, peeked: None }
    }

    /// Returns the next pair of items stemming from the pair of sources
    /// being merged. If both returned options contain a value, that value
    /// is equal and occurs in both sources. If one of the returned options
    /// contains a value, that value doesn't occur in the other source (or
    /// the sources are not strictly ascending). If neither returned option
    /// contains a value, iteration has finished and subsequent calls will
    /// return the same empty pair.
    fn nexts<Cmp>(&mut self, cmp: Cmp) -> (Option<I::Item>, Option<I::Item>)
    where
        I: core::iter::Iterator,
        Cmp: Fn(&I::Item, &I::Item) -> core::cmp::Ordering,
    {
        let mut a_next;
        let mut b_next;
        match self.peeked.take() {
            Some(Peeked::A(next)) => {
                a_next = Some(next);
                b_next = self.b.next();
            }
            Some(Peeked::B(next)) => {
                b_next = Some(next);
                a_next = self.a.next();
            }
            None => {
                a_next = self.a.next();
                b_next = self.b.next();
            }
        }
        if let (Some(ref a1), Some(ref b1)) = (&a_next, &b_next) {
            match cmp(a1, b1) {
                Less => self.peeked = b_next.take().map(Peeked::B),
                Greater => self.peeked = a_next.take().map(Peeked::A),
                Equal => (),
            }
        }
        (a_next, b_next)
    }

    /// Returns a pair of upper bounds for the `size_hint` of the final iterator.
    pub fn lens(&self) -> (usize, usize)
    where
        I: ExactSizeIterator,
    {
        match self.peeked {
            Some(Peeked::A(_)) => (1 + self.a.len(), self.b.len()),
            Some(Peeked::B(_)) => (self.a.len(), 1 + self.b.len()),
            _ => (self.a.len(), self.b.len()),
        }
    }
}
