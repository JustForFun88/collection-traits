use super::{ChangeOutputType, Guard, IntoIter, Residual, Try};
use core::mem::{self, MaybeUninit};
use core::ops::ControlFlow;

/// Pulls `N` items from `iter` and returns them as an array. If the iterator
/// yields fewer than `N` items, `Err` is returned containing an iterator over
/// the already yielded items.
///
/// Any `Try::Residual`s encountered will stop the inner iterator and
/// be propagated back to the overall result (as `Ok(Try::from_residual(r.into()))`).
///
/// Since the iterator is passed as a mutable reference and this function calls
/// `next` at most `N` times, the iterator can still be used afterwards to
/// retrieve the remaining items.
///
/// If `iter.next()` panicks, all items already yielded by the iterator are
/// dropped.
#[inline]
pub(super) fn try_collect_into_array<I, T, R, const N: usize>(
    iter: &mut I,
) -> Result<R::TryType, IntoIter<T, N>>
where
    I: Iterator,
    I::Item: Try<Output = T, Residual = R>,
    R: Residual<[T; N]>,
{
    if N == 0 {
        // SAFETY: An empty array is always inhabited and has no validity invariants.
        return Ok(Try::from_output(unsafe { mem::zeroed() }));
    }

    // SAFETY: The `assume_init` is safe because the type we are claiming to have
    // initialized here is a bunch of `MaybeUninit`s, which do not require initialization.
    let mut array: [MaybeUninit<T>; N] = unsafe { MaybeUninit::uninit().assume_init() };
    let mut guard = Guard {
        array_mut: &mut array,
        initialized: 0,
    };

    for _ in 0..N {
        match iter.next() {
            Some(item_result) => {
                let item: T = match item_result.branch() {
                    ControlFlow::Break(r) => {
                        return Ok(Try::from_residual(r));
                    }
                    ControlFlow::Continue(elem) => elem,
                };

                // SAFETY: `guard.initialized` starts at 0, which means push can be called
                // at most N times, which this loop does.
                unsafe {
                    guard.push_unchecked(item);
                }
            }
            None => {
                let alive = 0..guard.initialized;
                mem::forget(guard);
                // SAFETY: `array` was initialized with exactly `initialized` number of elements.
                return Err(unsafe { IntoIter::new_unchecked(array, alive) });
            }
        }
    }

    mem::forget(guard);
    // SAFETY:
    // 1. All elements of the array were populated in the loop above;
    // 2. `MaybeUninit<T>` is `#[repr(transparent)]` so it is guaranteed
    //    to have the same size, alignment, and ABI as T
    //    (https://doc.rust-lang.org/stable/std/mem/union.MaybeUninit.html#layout-1)
    let output: [T; N] = unsafe { mem::transmute_copy(&array) };
    Ok(Try::from_output(output))
}

/// Process the given iterator as if it yielded a the item's `Try::Output`
/// type instead. Any `Try::Residual`s encountered will stop the inner iterator
/// and be propagated back to the overall result.
#[inline]
pub(super) fn try_process<I, T, R, F, U>(iter: I, mut f: F) -> ChangeOutputType<I::Item, U>
where
    I: Iterator,
    I::Item: Try<Output = T, Residual = R>,
    for<'a> F: FnMut(GenericShunt<'a, I, R>) -> U,
    R: Residual<U>,
{
    let mut residual = None;
    let shunt = GenericShunt {
        iter,
        residual: &mut residual,
    };
    let value = f(shunt);
    match residual {
        Some(r) => Try::from_residual(r),
        None => Try::from_output(value),
    }
}

/// An iterator adapter that produces output as long as the underlying
/// iterator produces values where `Try::branch` says to `ControlFlow::Continue`.
///
/// If a `ControlFlow::Break` is encountered, the iterator stops and the
/// residual is stored.
pub(super) struct GenericShunt<'a, I, R> {
    iter: I,
    residual: &'a mut Option<R>,
}

impl<I, R> Iterator for GenericShunt<'_, I, R>
where
    I: Iterator,
    I::Item: Try<Residual = R>,
{
    type Item = <I::Item as Try>::Output;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(value) = self.iter.next() {
            match Try::branch(value) {
                ControlFlow::Continue(output) => return Some(output),
                ControlFlow::Break(residual) => {
                    *self.residual = Some(residual);
                    return None;
                }
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.residual.is_some() {
            (0, Some(0))
        } else {
            let (_, upper) = self.iter.size_hint();
            (0, upper)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::collect::try_from::NeverShortCircuit;
    use crate::collect::try_from::Try;
    use core::ops::ControlFlow::{Break, Continue};

    #[cfg(not(miri))]
    const N: usize = 128; // must be divisible by 4
    #[cfg(miri)]
    const N: usize = 16; // must be divisible by 4

    #[test]
    #[allow(clippy::unnecessary_fold)]
    fn test() {
        let iter = (0..N).map(NeverShortCircuit);
        let vec: Vec<_> = match try_process(iter, |i| i.collect()).branch() {
            ControlFlow::Continue(vec) => vec,
            ControlFlow::Break(never) => match never {},
        };
        assert_eq!(vec, (0..N).collect::<Vec<_>>());

        let iter = (0..N).map(Result::<_, usize>::Ok);
        let result: Result<Vec<_>, usize> = try_process(iter, |i| i.collect());
        assert_eq!(result, Ok((0..N).collect()));

        let iter = (0..N).map(|x| if x < N / 16 { Ok(x) } else { Err(x) });
        let result: Result<Vec<_>, usize> = try_process(iter, |i| i.collect());
        assert_eq!(result, Err(N / 16));

        let iter = (0..N).map(Some);
        let result: Option<Vec<_>> = try_process(iter, |i| i.collect());
        assert_eq!(result, Some((0..N).collect()));

        let iter = (0..N).map(|x| if x < N / 16 { Some(x) } else { None });
        let result: Option<Vec<_>> = try_process(iter, |i| i.collect());
        assert_eq!(result, None);

        let iter = (0..N).map(ControlFlow::<usize, _>::Continue);
        let result: ControlFlow<_, Vec<_>> = try_process(iter, |i| i.collect());
        assert_eq!(result, ControlFlow::Continue((0..N).collect()));

        let iter = (0..N).map(|x| if x < N / 16 { Continue(x) } else { Break(x) });
        let result: ControlFlow<_, Vec<_>> = try_process(iter, |i| i.collect());
        assert_eq!(result, Break(N / 16));
    }
}
