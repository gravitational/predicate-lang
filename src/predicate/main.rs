//extern crate proc_macro;
//use proc_macro::TokenStream;

// https://crates.io/crates/syn

//#[proc_macro_derive(Query)]
//pub fn derive_query(_item: TokenStream) -> TokenStream {
//    "fn answer() -> u32 { 42 }".parse().unwrap()
//}

use std::collections::HashMap;

#[derive(Debug, Clone)]
struct User {
    name: String,
    sso_traits: HashMap<String, String>,
}

trait Query<T> {
    fn fact(&self, arg: &T) -> Option<T>;
    fn arg(&self) -> T;
}

#[derive(Debug, Clone)]
struct Attribute {
    id: String,
    key: String,
    val: String,
}

impl Query<Attribute> for Attribute {
    fn fact(&self, a: &Self) -> Option<Self> {
        if self.id == a.id && self.key == a.key && self.val == a.val {
            return Some(self.clone());
        }
        None
    }

    fn arg(&self) -> Self {
        self.clone()
    }
}

impl Attribute {
    fn new(id: &str, key: &str, val: &str) -> Self {
        Self {
            id: id.to_string(),
            key: key.to_string(),
            val: val.to_string(),
        }
    }
}

type Predicate<T> = fn(&dyn Db, &dyn Query<T>) -> Option<T>;

trait Collection<T> {
    fn find(&self, db: &dyn Db, q: &dyn Query<T>) -> Option<T>;
    fn push(&mut self, p: Predicate<T>);
}

struct VecCollection<T> {
    vals: Vec<Predicate<T>>,
}

impl<T> VecCollection<T> {
    fn new() -> Self {
        Self { vals: vec![] }
    }
}

impl<T> Collection<T> for VecCollection<T> {
    fn find(&self, db: &dyn Db, q: &dyn Query<T>) -> Option<T> {
        for pred in self.vals.iter() {
            match pred(db, q) {
                Some(t) => return Some(t),
                None => continue,
            }
        }
        None
    }

    fn push(&mut self, p: Predicate<T>) {
        self.vals.push(p);
    }
}

trait Db {
    fn get_attrs(&self) -> &dyn Collection<Attribute>;
    fn get_user_attrs(&self) -> &dyn Collection<Attribute>;
}

struct LocalDb {
    attrs: VecCollection<Attribute>,
    user_attrs: VecCollection<Attribute>,
}

impl LocalDb {
    fn new() -> Self {
        Self {
            attrs: VecCollection::<Attribute>::new(),
            user_attrs: VecCollection::<Attribute>::new(),
        }
    }
}

impl Db for LocalDb {
    fn get_attrs(&self) -> &dyn Collection<Attribute> {
        &self.attrs
    }

    fn get_user_attrs(&self) -> &dyn Collection<Attribute> {
        &self.user_attrs
    }
}

fn main() {
    let mut db = LocalDb::new();

    // let mut sso_attrs: Vec<Predicate<Attribute>> = vec![];

    // declares a fact: Bob has attributre, key:val
    db.attrs
        .push(|_, q| q.fact(&Attribute::new("bob", "key", "val")));

    // any user named alice has attribute key:val
    db.attrs.push(|_, q| match q.arg().id.as_str() {
        "alice" => Some(Attribute::new(&q.arg().id, "key", "val")),
        _ => None,
    });

    /*
        // if a user has sso_attribute group: admins, assign attribute env: prod
        predicates.push(
            |q| match find(&Attribute(q.arg().id, "group", "admins"), &z) {
                Some(_) => Some(Attribute::new(&q.arg().id, "env", "prod")),
                _ => None,
            },
        );
    */
    println!(
        "bob: {:?}\n",
        db.attrs
            .find(&db as &dyn Db, &Attribute::new("bob", "key", "val")),
    );
    println!(
        "alice: {:?}\n",
        db.attrs.find(&db, &Attribute::new("alice", "key", "val"))
    );
}
