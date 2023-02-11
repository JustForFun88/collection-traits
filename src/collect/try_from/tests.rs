use std::ops::ControlFlow;

use super::*;

#[cfg(not(miri))]
const N: usize = 50;
#[cfg(miri)]
const N: usize = 10;
const ARRAY_LEN: usize = 3;

#[test]
fn test_array_from_iterator() {
    let vector = (0..N).collect::<Vec<_>>();
    let vector_into_iter = (0..(N - 1)).collect::<Vec<_>>();

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = V>,
    // ////////////////////////////////////////////////////////////////////

    let array: [_; N] = ArrayFromIterator::try_from_iter(0..N).unwrap();
    assert_eq!(array.as_slice(), &vector);

    let error: Result<[_; N], _> = ArrayFromIterator::try_from_iter(0..(N - 1));
    assert_eq!(error.unwrap_err().as_slice(), &vector_into_iter);

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = Result<V, E>>
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..N).map(Result::<_, usize>::Ok);
    let result: Result<[_; N], _> = ArrayFromIterator::try_from_iter(iter).unwrap();

    assert_eq!(result.unwrap().as_slice(), &vector);

    let iter = (0..N).map(|x| if x < N / 2 { Ok(x) } else { Err(x) });

    let result: Result<[_; N], _> = ArrayFromIterator::try_from_iter(iter).unwrap();
    assert_eq!(result, Err(N / 2));

    let iter = (0..(N - 1)).map(Result::<_, usize>::Ok);
    let error: Result<Result<[_; N], _>, _> = ArrayFromIterator::try_from_iter(iter);
    assert_eq!(error.unwrap_err().as_slice(), &vector_into_iter);

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = Option<V>>
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..N).map(Some);
    let result: Option<[_; N]> = ArrayFromIterator::try_from_iter(iter).unwrap();

    assert_eq!(result.unwrap().as_slice(), &vector);

    let iter = (0..N).map(|x| if x < N / 2 { Some(x) } else { None });

    let result: Option<[_; N]> = ArrayFromIterator::try_from_iter(iter).unwrap();
    assert_eq!(result, None);

    let iter = (0..(N - 1)).map(Some);
    let error: Result<Option<[_; N]>, _> = ArrayFromIterator::try_from_iter(iter);
    assert_eq!(error.unwrap_err().as_slice(), &vector_into_iter);

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = ControlFlow<B, V>>,
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..N).map(ControlFlow::<usize, usize>::Continue);
    let result: ControlFlow<_, [_; N]> = ArrayFromIterator::try_from_iter(iter).unwrap();

    match result {
        ControlFlow::Continue(val) => assert_eq!(val.as_slice(), &vector),
        ControlFlow::Break(_) => panic!(),
    }

    let iter = (0..N).map(|x| {
        if x < N / 2 {
            ControlFlow::Continue(x)
        } else {
            ControlFlow::Break(x)
        }
    });

    let result: ControlFlow<_, [_; N]> = ArrayFromIterator::try_from_iter(iter).unwrap();
    assert_eq!(result, ControlFlow::Break(N / 2));

    let iter = (0..(N - 1)).map(ControlFlow::<usize, usize>::Continue);
    let error: Result<ControlFlow<_, [_; N]>, _> = ArrayFromIterator::try_from_iter(iter);
    assert_eq!(error.unwrap_err().as_slice(), &vector_into_iter);
}

#[test]
fn test_collection_array_from_iterator() {
    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = V>,
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..ARRAY_LEN).map(|_| 0..N);
    let array: [Vec<_>; ARRAY_LEN] = match CollectionArrayFromIterator::try_from_iter(iter) {
        Ok(array) => array,
        Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
    };
    for vector in array {
        assert_eq!(vector, (0..N).collect::<Vec<_>>());
    }

    let iter = (0..(ARRAY_LEN - 1)).map(|_| 0..N);
    let result: Result<[Vec<_>; ARRAY_LEN], _> = CollectionArrayFromIterator::try_from_iter(iter);

    match result {
        Ok(array) => panic!("Unexpected result: {array:?}"),
        Err(into_iter) => {
            assert_eq!(into_iter.len(), ARRAY_LEN - 1);
            for vector in into_iter {
                assert_eq!(vector, (0..N).collect::<Vec<_>>());
            }
        }
    }

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = Result<V, E>>
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..ARRAY_LEN).map(|_| (0..N).map(Result::<_, usize>::Ok));
    let result: Result<[Vec<_>; ARRAY_LEN], _> =
        match CollectionArrayFromIterator::try_from_iter(iter) {
            Ok(result) => result,
            Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
        };

    match result {
        Ok(array) => {
            for vec in array {
                assert_eq!(vec, (0..N).collect::<Vec<_>>());
            }
        }
        Err(err) => panic!("Unexpected result: {err:?}"),
    }

    let iter = (0..ARRAY_LEN).map(|i| {
        (0..N).map(move |x| {
            if i < (ARRAY_LEN - 1) {
                Ok(x)
            } else {
                if x < N / 2 {
                    Ok(x)
                } else {
                    Err(x)
                }
            }
        })
    });

    let result: Result<[Vec<_>; ARRAY_LEN], _> =
        match CollectionArrayFromIterator::try_from_iter(iter) {
            Ok(result) => result,
            Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
        };
    assert_eq!(result, Err(N / 2));

    let iter = (0..(ARRAY_LEN - 1)).map(|_| (0..N).map(Result::<_, usize>::Ok));
    let result: Result<Result<[Vec<_>; ARRAY_LEN], _>, _> =
        CollectionArrayFromIterator::try_from_iter(iter);

    match result {
        Ok(inner_res) => panic!("Unexpected result: {inner_res:?}"),
        Err(into_iter) => {
            assert_eq!(into_iter.len(), ARRAY_LEN - 1);
            for vector in into_iter {
                assert_eq!(vector, (0..N).collect::<Vec<_>>());
            }
        }
    }

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = Option<V>>
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..ARRAY_LEN).map(|_| (0..N).map(Some));
    let result: Option<[Vec<_>; ARRAY_LEN]> = match CollectionArrayFromIterator::try_from_iter(iter)
    {
        Ok(result) => result,
        Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
    };

    match result {
        Some(array) => {
            for vec in array {
                assert_eq!(vec, (0..N).collect::<Vec<_>>());
            }
        }
        None => panic!("Unexpected result"),
    }

    let iter = (0..ARRAY_LEN).map(|i| {
        (0..N).map(move |x| {
            if i < (ARRAY_LEN - 1) {
                Some(x)
            } else {
                if x < N / 2 {
                    Some(x)
                } else {
                    None
                }
            }
        })
    });

    let result: Option<[Vec<_>; ARRAY_LEN]> = match CollectionArrayFromIterator::try_from_iter(iter)
    {
        Ok(result) => result,
        Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
    };
    assert_eq!(result, None);

    let iter = (0..(ARRAY_LEN - 1)).map(|_| (0..N).map(Some));
    let result: Result<Option<[Vec<_>; ARRAY_LEN]>, _> =
        CollectionArrayFromIterator::try_from_iter(iter);

    match result {
        Ok(inner_res) => panic!("Unexpected result: {inner_res:?}"),
        Err(into_iter) => {
            assert_eq!(into_iter.len(), ARRAY_LEN - 1);
            for vector in into_iter {
                assert_eq!(vector, (0..N).collect::<Vec<_>>());
            }
        }
    }

    // ////////////////////////////////////////////////////////////////////
    // Collect from IntoIterator<Item = ControlFlow<B, V>>,
    // ////////////////////////////////////////////////////////////////////

    let iter = (0..ARRAY_LEN).map(|_| (0..N).map(ControlFlow::<usize, _>::Continue));
    let result: ControlFlow<_, [Vec<_>; ARRAY_LEN]> =
        match CollectionArrayFromIterator::try_from_iter(iter) {
            Ok(result) => result,
            Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
        };

    match result {
        ControlFlow::Continue(array) => {
            for vec in array {
                assert_eq!(vec, (0..N).collect::<Vec<_>>());
            }
        }
        ControlFlow::Break(br) => panic!("Unexpected result: {br:?}"),
    }

    let iter = (0..ARRAY_LEN).map(|i| {
        (0..N).map(move |x| {
            if i < (ARRAY_LEN - 1) {
                ControlFlow::Continue(x)
            } else {
                if x < N / 2 {
                    ControlFlow::Continue(x)
                } else {
                    ControlFlow::Break(x)
                }
            }
        })
    });

    let result: ControlFlow<_, [Vec<_>; ARRAY_LEN]> =
        match CollectionArrayFromIterator::try_from_iter(iter) {
            Ok(result) => result,
            Err(into_iter) => panic!("Unexpected result: {into_iter:?}"),
        };
    assert_eq!(result, ControlFlow::Break(N / 2));

    let iter = (0..(ARRAY_LEN - 1)).map(|_| (0..N).map(ControlFlow::<usize, _>::Continue));
    let result: Result<ControlFlow<_, [Vec<_>; ARRAY_LEN]>, _> =
        CollectionArrayFromIterator::try_from_iter(iter);

    match result {
        Ok(inner_res) => panic!("Unexpected result: {inner_res:?}"),
        Err(into_iter) => {
            assert_eq!(into_iter.len(), ARRAY_LEN - 1);
            for vector in into_iter {
                assert_eq!(vector, (0..N).collect::<Vec<_>>());
            }
        }
    }
}

#[test]
#[should_panic = "panic in iter"]
fn test_panic() {
    let iter = (0..N).map(|i| {
        if i < N - 1 {
            i
        } else {
            panic!("panic in iter")
        }
    });
    let array: Result<[_; N], _> = ArrayFromIterator::try_from_iter(iter);

    match array {
        Ok(_) => panic!("Unexpected Ok"),
        Err(_) => panic!("Unexpected Err"),
    }
}

#[test]
#[should_panic = "panic in iter"]
fn test_collection_panic() {
    let iter = (0..ARRAY_LEN).map(|i| {
        if i < ARRAY_LEN - 1 {
            0..N
        } else {
            panic!("panic in iter")
        }
    });
    let array: Result<[Vec<_>; ARRAY_LEN], _> = CollectionArrayFromIterator::try_from_iter(iter);

    match array {
        Ok(_) => panic!("Unexpected Ok"),
        Err(_) => panic!("Unexpected Err"),
    }
}
