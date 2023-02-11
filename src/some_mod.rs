use core::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoltInfo {
    pub name: String,
    pub version: String,
    pub display_name: String,
    pub author: String,
    pub description: String,
    pub repository: Option<String>,
    pub wasm: bool,
    pub updated_at_ts: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoltMetadata {
    pub name: String,
    pub version: String,
    pub display_name: String,
    pub author: String,
    pub description: String,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct VoltID {
    pub author: String,
    pub name: String,
}

impl fmt::Display for VoltID {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.author, self.name)
    }
}

// pub trait AAAContainerRef {
//     type Key;
//     type Value;

//     fn contains_eq<E>(&self, key: &E) -> bool
//     where
//         E: ?Sized + Equivalent<Self::Key>;
// }

// impl<K, V> AAAContainerRef for collections::HashMap<K, V>
// where
//     K: Eq + Hash,
// {
//     type Key = K;

//     type Value = V;

//     fn contains_eq<E>(&self, key: &E) -> bool
//     where
//         K: Borrow<E>,
//         E: ?Sized + Hash + Eq,
//     {
//         self.contains_key(key)
//     }
// }
