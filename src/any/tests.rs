use super::*;
use crate::TryCollectArray;
use core::fmt::Debug;
use std::borrow::Cow;

#[cfg(not(miri))]
const N: usize = 50;
#[cfg(miri)]
const N: usize = 10;
const ARRAY_LEN: usize = 3;

fn test_container_ref<'a, T, K, V, Q, FV>(container: &'a T, keys: &[K], values: &[V], vec_eq: &[FV])
where
    T: AnyCollectionRef<Q, Key = K, Value = V> + Debug + ?Sized,
    K: Hash + Eq + Clone + Debug + Ord + Borrow<Q>,
    Q: ?Sized + Hash + Eq,
    V: PartialEq + Clone + Debug + Ord + 'a,
    FV: PartialEq + Debug + From<&'a T::Value>,
{
    use core::any::type_name;

    let (cont_len, keys_len, values_len, vec_eq_len) = (
        container.collection_len(),
        keys.len(),
        values.len(),
        vec_eq.len(),
    );
    assert!(
        cont_len == keys_len,
        "Container length \"{cont_len}\" is not equal to keys length \"{keys_len}\".\n\
        Container type: {}",
        type_name::<T>()
    );
    assert!(
        cont_len == values_len,
        "Container length \"{cont_len}\" is not equal to values length \"{values_len}\".\n\
        Container type: {}",
        type_name::<T>()
    );
    assert!(
        cont_len == vec_eq_len,
        "Container length \"{cont_len}\" is not equal to vec_eq length \"{vec_eq_len}\".\n\
        Container type: {}",
        type_name::<T>()
    );

    let mut container_keys = container.collection_keys().cloned().collect::<Vec<_>>();
    container_keys.sort_unstable();
    assert_eq!(
        container_keys,
        keys,
        "\nContainer type: {}",
        type_name::<T>()
    );

    let mut container_values = container.collection_values().cloned().collect::<Vec<_>>();
    container_values.sort_unstable();
    assert_eq!(
        container_values,
        values,
        "\nContainer type: {}",
        type_name::<T>()
    );

    for ((key, value), equiv) in keys.iter().zip(values).zip(vec_eq) {
        assert!(
            container.contains_eq(key.borrow()),
            "Container \"{container:?}\" does not contain key \"{key:?}\".\n\
            Container type: {}",
            type_name::<T>()
        );
        assert_eq!(
            container.get_value(key.borrow()),
            Some(value),
            "\nKey: {key:?}\nContainer type: {}\nContainer: {container:?}\nValues: {values:?}\n",
            type_name::<T>()
        );
        let equivalent = container.get_converted::<FV>(key.borrow());
        assert_eq!(
            equivalent.as_ref(),
            Some(equiv),
            "\nKey: {key:?}\nContainer type: {}\nContainer: {container:?}\nValues: {vec_eq:?}\n",
            type_name::<T>()
        );
    }
}

#[cfg(test)]
fn as_slices_array<T, U, const N: usize>(array: &[T; N]) -> [&[U]; N]
where
    T: AsRef<[U]>,
{
    let mut outputs: [&[U]; N] = [&[]; N];

    for (elem, value) in outputs.iter_mut().zip(array) {
        *elem = value.as_ref();
    }
    outputs
}

#[test]
fn test_any_container_ref_for_all_vec_and_set_types() {
    let iter = (0..N).map(|x| x.to_string());
    let iter_arr = (0..ARRAY_LEN).map(|i| ((i * N)..((i + 1) * N)).map(|x| x.to_string()));

    let container = iter.clone().collect::<Vec<_>>();
    let containers_arr: [Vec<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();

    let mut keys = container.clone();
    keys.sort_unstable();
    let values = keys.clone();
    let vec_eq = values.iter().map(Cow::<str>::from).collect::<Vec<_>>();

    let mut keys_arr = containers_arr
        .iter()
        .flat_map(|x| x.iter())
        .cloned()
        .collect::<Vec<_>>();
    keys_arr.sort_unstable();
    let values_arr = keys_arr.clone();
    let vec_eq_arr = values_arr.iter().map(Cow::<str>::from).collect::<Vec<_>>();

    // Slice
    test_container_ref::<_, _, _, str, _>(container.as_slice(), &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container.as_slice(), &keys, &values, &vec_eq);
    let slice_array = as_slices_array(&containers_arr);
    test_container_ref::<_, _, _, str, _>(&slice_array, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&slice_array, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::Vec
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::Vec
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // im::Vector
    let container = iter.clone().collect::<im::Vector<_>>();
    let containers_arr: [im::Vector<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of im::Vector
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::VecDeque
    let container = iter.clone().collect::<collections::VecDeque<_>>();
    let containers_arr: [collections::VecDeque<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::VecDeque
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::LinkedList
    let container = iter.clone().collect::<collections::LinkedList<_>>();
    let containers_arr: [collections::LinkedList<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::LinkedList
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::BinaryHeap
    let container = iter.clone().collect::<collections::BinaryHeap<_>>();
    let containers_arr: [collections::BinaryHeap<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::BinaryHeap
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // smallVec::SmallVec
    let container = iter.clone().collect::<SmallVec<[String; 5]>>();
    let containers_arr: [SmallVec<[String; 5]>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of smallVec::SmallVec
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::HashSet
    let container = iter.clone().collect::<collections::HashSet<_>>();
    let containers_arr: [collections::HashSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::HashSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // hashbrown::HashSet
    let container = iter.clone().collect::<hashbrown::HashSet<_>>();
    let containers_arr: [hashbrown::HashSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of hashbrown::HashSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // indexmap::IndexSet
    let container = iter.clone().collect::<indexmap::IndexSet<_>>();
    let containers_arr: [indexmap::IndexSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of indexmap::IndexSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // im::HashSet
    let container = iter.clone().collect::<im::HashSet<_>>();
    let containers_arr: [im::HashSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of im::HashSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::BTreeSet
    let container = iter.clone().collect::<collections::BTreeSet<_>>();
    let containers_arr: [collections::BTreeSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::BTreeSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // im::OrdSet
    let container = iter.collect::<im::OrdSet<_>>();
    let containers_arr: [im::OrdSet<String>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, str, _>(&container, &keys, &values, &vec_eq);
    // Array of im::OrdSet
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, str, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);
}

#[test]
fn test_any_container_ref_for_all_map_types() {
    let iter = (0..N).map(|x| (x, (x + 1000).to_string()));
    let iter_arr =
        (0..ARRAY_LEN).map(|i| ((i * N)..((i + 1) * N)).map(|x| (x, (x + 1000).to_string())));

    // collections::HashMap
    let container = iter.clone().collect::<collections::HashMap<_, _>>();
    let mut keys = container.keys().cloned().collect::<Vec<_>>();
    let mut values = container.values().cloned().collect::<Vec<_>>();
    keys.sort_unstable();
    values.sort_unstable();
    let vec_eq = values.iter().map(Cow::<str>::from).collect::<Vec<_>>();

    let mut keys_arr = iter_arr
        .clone()
        .flatten()
        .map(|(x, _)| x)
        .collect::<Vec<_>>();
    keys_arr.sort_unstable();
    let mut values_arr = iter_arr
        .clone()
        .flatten()
        .map(|(_, y)| y)
        .collect::<Vec<_>>();
    values_arr.sort_unstable();
    let vec_eq_arr = values_arr.iter().map(Cow::<str>::from).collect::<Vec<_>>();

    // collections::HashMap
    let containers_arr: [collections::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::HashMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // hashbrown::HashMap
    let container = iter.clone().collect::<hashbrown::HashMap<_, _>>();
    let containers_arr: [hashbrown::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of hashbrown::HashMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // im::HashMap
    let container = iter.clone().collect::<im::HashMap<_, _>>();
    let containers_arr: [im::HashMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of im::HashMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // indexmap::IndexMap
    let container = iter.clone().collect::<indexmap::IndexMap<_, _>>();
    let containers_arr: [indexmap::IndexMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of indexmap::IndexMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // collections::BTreeMap
    let container = iter.clone().collect::<collections::BTreeMap<_, _>>();
    let containers_arr: [collections::BTreeMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of collections::BTreeMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);

    // im::OrdMap
    let container = iter.collect::<im::OrdMap<_, _>>();
    let containers_arr: [im::OrdMap<_, _>; ARRAY_LEN] =
        iter_arr.clone().try_collect_collections_array().unwrap();
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &values);
    test_container_ref::<_, _, _, usize, _>(&container, &keys, &values, &vec_eq);
    // Array of im::OrdMap
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &values_arr);
    test_container_ref::<_, _, _, usize, _>(&containers_arr, &keys_arr, &values_arr, &vec_eq_arr);
}

#[test]
fn test_generic_usage() {
    fn contain_key<T>(cont: &T, key: &T::Key) -> bool
    where
        T: AnyCollectionRef + ?Sized,
    {
        cont.contains_eq(key)
    }

    fn contain_borrow_key<T, Q: ?Sized>(cont: &T, key: &Q) -> bool
    where
        T: AnyCollectionRef<Q> + ?Sized,
        T::Key: Borrow<Q>,
    {
        cont.contains_eq(key)
    }

    let slice = Vec::from([1.to_string()]);
    let std_vec = Vec::from([2.to_string()]);
    let im_vec = im::Vector::from([3.to_string()].as_slice());
    let vec_deq = collections::VecDeque::from([4.to_string()]);
    let lin_list = collections::LinkedList::from([5.to_string()]);
    let bin_heah = collections::BinaryHeap::from([6.to_string()]);
    let small_vec = SmallVec::<[String; 1]>::from([7.to_string()]);

    assert!(contain_key(slice.as_slice(), &1.to_string()));
    assert!(contain_key(&std_vec, &2.to_string()));
    assert!(contain_key(&im_vec, &3.to_string()));
    assert!(contain_key(&vec_deq, &4.to_string()));
    assert!(contain_key(&lin_list, &5.to_string()));
    assert!(contain_key(&bin_heah, &6.to_string()));
    assert!(contain_key(&small_vec, &7.to_string()));

    assert!(contain_borrow_key(slice.as_slice(), 1.to_string().as_str()));
    assert!(contain_borrow_key(&std_vec, 2.to_string().as_str()));
    assert!(contain_borrow_key(&im_vec, 3.to_string().as_str()));
    assert!(contain_borrow_key(&vec_deq, 4.to_string().as_str()));
    assert!(contain_borrow_key(&lin_list, 5.to_string().as_str()));
    assert!(contain_borrow_key(&bin_heah, 6.to_string().as_str()));
    assert!(contain_borrow_key(&small_vec, 7.to_string().as_str()));

    assert!(!contain_key(slice.as_slice(), &10.to_string()));
    assert!(!contain_key(&std_vec, &20.to_string()));
    assert!(!contain_key(&im_vec, &30.to_string()));
    assert!(!contain_key(&vec_deq, &40.to_string()));
    assert!(!contain_key(&lin_list, &50.to_string()));
    assert!(!contain_key(&bin_heah, &60.to_string()));
    assert!(!contain_key(&small_vec, &70.to_string()));

    assert!(!contain_borrow_key(
        slice.as_slice(),
        10.to_string().as_str()
    ));
    assert!(!contain_borrow_key(&std_vec, 20.to_string().as_str()));
    assert!(!contain_borrow_key(&im_vec, 30.to_string().as_str()));
    assert!(!contain_borrow_key(&vec_deq, 40.to_string().as_str()));
    assert!(!contain_borrow_key(&lin_list, 50.to_string().as_str()));
    assert!(!contain_borrow_key(&bin_heah, 60.to_string().as_str()));
    assert!(!contain_borrow_key(&small_vec, 70.to_string().as_str()));

    let std_hash_map = collections::HashMap::from([(8.to_string(), 9.to_string())]);
    let brown_hash_map: hashbrown::HashMap<_, _> =
        hashbrown::HashMap::from([(10.to_string(), 11.to_string())]);
    let im_hash_map: im::HashMap<_, _> =
        im::HashMap::from([(12.to_string(), 13.to_string())].as_slice());
    let index_hash_map: indexmap::IndexMap<_, _> =
        indexmap::IndexMap::from([(14.to_string(), 15.to_string())]);
    let std_btree_map = collections::BTreeMap::from([(16.to_string(), 17.to_string())]);
    let im_ord_map: im::OrdMap<String, String> =
        im::OrdMap::from([(18.to_string(), 19.to_string())].as_slice());

    assert!(contain_key(&std_hash_map, &8.to_string()));
    assert!(contain_key(&brown_hash_map, &10.to_string()));
    assert!(contain_key(&im_hash_map, &12.to_string()));
    assert!(contain_key(&index_hash_map, &14.to_string()));
    assert!(contain_key(&std_btree_map, &16.to_string()));
    assert!(contain_key(&im_ord_map, &18.to_string()));

    assert!(contain_borrow_key(&std_hash_map, 8.to_string().as_str()));
    assert!(contain_borrow_key(&brown_hash_map, 10.to_string().as_str()));
    assert!(contain_borrow_key(&im_hash_map, 12.to_string().as_str()));
    assert!(contain_borrow_key(&index_hash_map, 14.to_string().as_str()));
    assert!(contain_borrow_key(&std_btree_map, 16.to_string().as_str()));
    assert!(contain_borrow_key(&im_ord_map, 18.to_string().as_str()));

    assert!(!contain_key(&std_hash_map, &80.to_string()));
    assert!(!contain_key(&brown_hash_map, &100.to_string()));
    assert!(!contain_key(&im_hash_map, &120.to_string()));
    assert!(!contain_key(&index_hash_map, &140.to_string()));
    assert!(!contain_key(&std_btree_map, &160.to_string()));
    assert!(!contain_key(&im_ord_map, &180.to_string()));

    assert!(!contain_borrow_key(&std_hash_map, 80.to_string().as_str()));
    assert!(!contain_borrow_key(
        &brown_hash_map,
        100.to_string().as_str()
    ));
    assert!(!contain_borrow_key(&im_hash_map, 120.to_string().as_str()));
    assert!(!contain_borrow_key(
        &index_hash_map,
        140.to_string().as_str()
    ));
    assert!(!contain_borrow_key(
        &std_btree_map,
        160.to_string().as_str()
    ));
    assert!(!contain_borrow_key(&im_ord_map, 180.to_string().as_str()));

    let std_hash_set = collections::HashSet::from([20.to_string()]);
    let brown_hash_set: hashbrown::HashSet<_> = hashbrown::HashSet::from([21.to_string()]);
    let index_hash_set: indexmap::IndexSet<_> = indexmap::IndexSet::from([22.to_string()]);
    let im_hash_set: im::HashSet<_> = im::HashSet::from([23.to_string()].as_slice());
    let std_btree_set: collections::BTreeSet<_> = collections::BTreeSet::from([24.to_string()]);
    let im_ord_set: im::OrdSet<_> = im::OrdSet::from([25.to_string()].as_slice());

    assert!(contain_key(&std_hash_set, &20.to_string()));
    assert!(contain_key(&brown_hash_set, &21.to_string()));
    assert!(contain_key(&index_hash_set, &22.to_string()));
    assert!(contain_key(&im_hash_set, &23.to_string()));
    assert!(contain_key(&std_btree_set, &24.to_string()));
    assert!(contain_key(&im_ord_set, &25.to_string()));

    assert!(contain_borrow_key(&std_hash_set, 20.to_string().as_str()));
    assert!(contain_borrow_key(&brown_hash_set, 21.to_string().as_str()));
    assert!(contain_borrow_key(&index_hash_set, 22.to_string().as_str()));
    assert!(contain_borrow_key(&im_hash_set, 23.to_string().as_str()));
    assert!(contain_borrow_key(&std_btree_set, 24.to_string().as_str()));
    assert!(contain_borrow_key(&im_ord_set, 25.to_string().as_str()));

    assert!(!contain_key(&std_hash_set, &200.to_string()));
    assert!(!contain_key(&brown_hash_set, &210.to_string()));
    assert!(!contain_key(&index_hash_set, &220.to_string()));
    assert!(!contain_key(&im_hash_set, &230.to_string()));
    assert!(!contain_key(&std_btree_set, &240.to_string()));
    assert!(!contain_key(&im_ord_set, &250.to_string()));

    assert!(!contain_borrow_key(&std_hash_set, 200.to_string().as_str()));
    assert!(!contain_borrow_key(
        &brown_hash_set,
        210.to_string().as_str()
    ));
    assert!(!contain_borrow_key(
        &index_hash_set,
        220.to_string().as_str()
    ));
    assert!(!contain_borrow_key(&im_hash_set, 230.to_string().as_str()));
    assert!(!contain_borrow_key(
        &std_btree_set,
        240.to_string().as_str()
    ));
    assert!(!contain_borrow_key(&im_ord_set, 250.to_string().as_str()));

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
        .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
        .unwrap();

    assert!(contain_key(&arr, &1.to_string()));
    assert!(!contain_key(&arr, &10.to_string()));

    assert!(contain_borrow_key(&arr, 1.to_string().as_str()));
    assert!(!contain_borrow_key(&arr, 10.to_string().as_str()));
}

#[test]
fn doc_test() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use core::borrow::Borrow;
    use hashbrown::HashMap;

    let map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);

    // You do not need to specify the type E when calling this `AnyContainerRef`
    // method directly.
    assert_eq!(map1.get_value(&"a".to_string()), Some(&1));
    assert_eq!(map1.get_value("b"), Some(&2));

    // Also, there is no need to specify the type E when using AnyContainerRef
    // as a trait binding (although specifying it will give more flexibility).
    fn get_value<'a, 'b, T>(cont: &'a T, key: &'b T::Key) -> Option<&'a T::Value>
    where
        T: AnyCollectionRef + ?Sized,
    {
        cont.get_value(key)
    }

    fn get_value_borrow_key<'a, 'b, T, Q: ?Sized>(cont: &'a T, key: &'b Q) -> Option<&'a T::Value>
    where
        T: AnyCollectionRef<Q> + ?Sized,
        T::Key: Borrow<Q>,
    {
        cont.get_value(key)
    }

    assert_eq!(get_value(&map1, &"a".to_string()), Some(&1));
    // assert_eq!(get_value(&map1, "a"), Some(&1)); // Err: expected struct `String`, found `str`

    assert_eq!(get_value_borrow_key(&map1, &"a".to_string()), Some(&1));
    assert_eq!(get_value_borrow_key(&map1, "a"), Some(&1));

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
        .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
        .unwrap();

    assert_eq!(get_value(&arr, &"1".to_string()), Some(&"1".to_owned()));
    assert_eq!(
        get_value_borrow_key(&arr, &"5".to_string()),
        Some(&"5".to_owned())
    );
    assert_eq!(get_value_borrow_key(&arr, "8"), Some(&"8".to_owned()));
}

#[test]
fn test1() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use hashbrown::HashMap;

    let mut map1: HashMap<String, i32> = HashMap::new();

    // Unfortunately, when calling AnyContainerRef methods directly,
    // you need to specify the type E
    assert_eq!(AnyCollectionRef::<String>::collection_len(&map1), 0);
    assert_eq!(AnyCollectionRef::<str>::collection_len(&map1), 0);

    map1.insert("a".to_owned(), 1);

    let map2: HashMap<usize, usize> = HashMap::from([(1, 1), (2, 2)]);

    // But you do not need to specify the type E when using AnyContainerRef
    // as trait bound
    fn get_len<T: AnyCollectionRef>(container: &T) -> usize {
        container.collection_len()
    }

    assert_eq!(get_len(&map1), 1);
    assert_eq!(get_len(&map2), 2);

    let arr = (0..3)
        .map(|_| 0..3)
        .try_collect_collections_array::<[Vec<_>; 3]>()
        .unwrap();

    // Array::len and AnyContainerRef::container_len are not the same value
    assert_eq!(arr.len(), 3);
    assert_eq!(get_len(&arr), 9);
}

#[test]
fn test2() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use hashbrown::HashMap;

    let mut map1: HashMap<String, i32> = HashMap::new();

    // Unfortunately, when calling AnyContainerRef methods directly,
    // you need to specify the type E
    assert!(AnyCollectionRef::<String>::is_collection_empty(&map1));
    assert!(AnyCollectionRef::<str>::is_collection_empty(&map1));

    map1.insert("a".to_owned(), 1);

    let map2: HashMap<usize, usize> = HashMap::from([(1, 1), (2, 2)]);

    // But you do not need to specify the type E when using AnyContainerRef
    // as trait bound
    fn is_container_empty<T: AnyCollectionRef>(container: &T) -> bool {
        container.is_collection_empty()
    }

    assert!(!is_container_empty(&map1));
    assert!(!is_container_empty(&map2));

    let arr = (0..3)
        .map(|_| 0..0)
        .try_collect_collections_array::<[Vec<_>; 3]>()
        .unwrap();

    // Array::len and AnyContainerRef::container_len are not the same value
    assert!(!arr.is_empty());
    assert!(is_container_empty(&arr));
}

#[test]
fn test3() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use core::borrow::Borrow;
    use hashbrown::HashMap;

    let map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);

    // You do not need to specify the type E when calling this `AnyContainerRef`
    // method directly.
    assert!(map1.contains_eq(&"a".to_string()));
    assert!(map1.contains_eq("b"));

    // Also, there is no need to specify the type E when using AnyContainerRef
    // as a trait binding (although specifying it will give more flexibility).
    fn contain_key<T>(cont: &T, key: &T::Key) -> bool
    where
        T: AnyCollectionRef + ?Sized,
    {
        cont.contains_eq(key)
    }

    fn contain_borrow_key<T, Q: ?Sized>(cont: &T, key: &Q) -> bool
    where
        T: AnyCollectionRef<Q> + ?Sized,
        T::Key: Borrow<Q>,
    {
        cont.contains_eq(key)
    }

    assert!(contain_key(&map1, &"a".to_string()));
    // assert!(contain_key(&map1, "a")); // Err: expected struct `String`, found `str`

    assert!(contain_borrow_key(&map1, &"a".to_string()));
    assert!(contain_borrow_key(&map1, "a"));

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
        .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
        .unwrap();

    assert!(contain_key(&arr, &"1".to_string()));
    assert!(contain_borrow_key(&arr, &"5".to_string()));
    assert!(contain_borrow_key(&arr, "8"));
}

#[test]
fn test4() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use core::borrow::Borrow;
    use hashbrown::HashMap;

    let map1: HashMap<String, i32> = HashMap::from([("a".into(), 1), ("b".into(), 2)]);

    // You do not need to specify the type E when calling this `AnyContainerRef`
    // method directly.
    assert_eq!(map1.get_value(&"a".to_string()), Some(&1));
    assert_eq!(map1.get_value("b"), Some(&2));

    // Also, there is no need to specify the type E when using AnyContainerRef
    // as a trait binding (although specifying it will give more flexibility).
    fn get_value<'a, 'b, T>(cont: &'a T, key: &'b T::Key) -> Option<&'a T::Value>
    where
        T: AnyCollectionRef + ?Sized,
    {
        cont.get_value(key)
    }

    fn get_value_borrow_key<'a, 'b, T, Q: ?Sized>(cont: &'a T, key: &'b Q) -> Option<&'a T::Value>
    where
        T: AnyCollectionRef<Q> + ?Sized,
        T::Key: Borrow<Q>,
    {
        cont.get_value(key)
    }

    assert_eq!(get_value(&map1, &"a".to_string()), Some(&1));
    // assert_eq!(get_value(&map1, "a"), Some(&1)); // Err: expected struct `String`, found `str`

    assert_eq!(get_value_borrow_key(&map1, &"a".to_string()), Some(&1));
    assert_eq!(get_value_borrow_key(&map1, "a"), Some(&1));

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)).map(|x| x.to_string()))
        .try_collect_collections_array::<[hashbrown::HashSet<_>; 3]>()
        .unwrap();

    assert_eq!(get_value(&arr, &"1".to_string()), Some(&"1".to_owned()));
    assert_eq!(
        get_value_borrow_key(&arr, &"5".to_string()),
        Some(&"5".to_owned())
    );
    assert_eq!(get_value_borrow_key(&arr, "8"), Some(&"8".to_owned()));
}

#[test]
fn test5() {
    use crate::AnyCollectionRef;
    use std::borrow::Cow;
    use std::collections::HashMap;

    let mut map1 = HashMap::new();
    map1.insert(1, "a".to_owned());
    assert_eq!(map1.get_converted::<Cow<_>>(&1), Some(Cow::from("a")));
    assert_eq!(map1.get_converted::<Cow<_>>(&2), None);

    let mut map2 = HashMap::new();
    map2.insert(2, "b".to_owned());

    let arr = [map1, map2];
    assert_eq!(arr.get_converted::<Cow<_>>(&1), Some(Cow::from("a")));
    assert_eq!(arr.get_converted::<Cow<_>>(&2), Some(Cow::from("b")));
    assert_eq!(arr.get_converted::<Cow<_>>(&3), None);

    // When key and value are the same
    let vec = vec!["a".to_owned(), "b".into(), "c".into()];
    assert_eq!(vec.get_converted::<Cow<_>>("a"), Some(Cow::from("a")));
}

#[test]
fn test6() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use hashbrown::HashMap;

    let map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);

    // Unfortunately, when calling AnyContainerRef methods directly,
    // you need to specify the type E
    let mut keys = AnyCollectionRef::<i32>::collection_keys(&map1).collect::<Vec<_>>();
    keys.sort_unstable();
    assert_eq!(keys, [&1, &2, &3]);

    let map2: HashMap<i32, i32> = HashMap::from([(4, 40), (5, 50), (6, 60)]);

    // But you do not need to specify the type E when using AnyContainerRef
    // as trait bound
    fn get_all_keys<T: AnyCollectionRef>(container: &T) -> Vec<&T::Key> {
        container.collection_keys().collect::<Vec<_>>()
    }

    let mut keys = get_all_keys(&map1);
    keys.sort_unstable();
    assert_eq!(keys, [&1, &2, &3]);

    let mut keys = get_all_keys(&map2);
    keys.sort_unstable();
    assert_eq!(keys, [&4, &5, &6]);

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)))
        .try_collect_collections_array::<[Vec<_>; 3]>()
        .unwrap();

    let keys = get_all_keys(&arr);
    assert_eq!(keys, [&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}

#[test]
fn test7() {
    use crate::{AnyCollectionRef, TryCollectArray};
    use hashbrown::HashMap;

    let map1: HashMap<i32, i32> = HashMap::from([(1, 10), (2, 20), (3, 30)]);

    // Unfortunately, when calling AnyContainerRef methods directly,
    // you need to specify the type E
    let mut values = AnyCollectionRef::<i32>::collection_values(&map1).collect::<Vec<_>>();
    values.sort_unstable();
    assert_eq!(values, [&10, &20, &30]);

    let map2: HashMap<i32, i32> = HashMap::from([(4, 40), (5, 50), (6, 60)]);

    // But you do not need to specify the type E when using AnyContainerRef
    // as trait bound
    fn get_all_values<T: AnyCollectionRef>(container: &T) -> Vec<&T::Value> {
        container.collection_values().collect::<Vec<_>>()
    }

    let mut values = get_all_values(&map1);
    values.sort_unstable();
    assert_eq!(values, [&10, &20, &30]);

    let mut values = get_all_values(&map2);
    values.sort_unstable();
    assert_eq!(values, [&40, &50, &60]);

    let arr = (0..3)
        .map(|i| ((i * 3)..((i + 1) * 3)))
        .try_collect_collections_array::<[Vec<_>; 3]>()
        .unwrap();

    let values = get_all_values(&arr);
    assert_eq!(values, [&0, &1, &2, &3, &4, &5, &6, &7, &8]);
}
