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

type Predicate<T> = fn(&dyn Query<T>) -> Option<T>;

// find finds first matching query on the predicate and returns it or None
// if nothing matches
fn find<T>(q: &dyn Query<T>, predicates: &Vec<Predicate<T>>) -> Option<T> {
    for pred in predicates.into_iter() {
        match pred(q) {
            Some(t) => return Some(t),
            None => continue,
        }
    }
    None
}

/*
trait Db  {
    fn attributes() -> &Vec<Predicate<Attribute>>,
}
*/

fn main() {
    let mut predicates: Vec<Predicate<Attribute>> = vec![];

    // declares a fact: Bob has attributre, key:val
    predicates.push(|q| q.fact(&Attribute::new("bob", "key", "val")));

    // any user named alice has attribute key:val
    predicates.push(|q| match q.arg().id.as_str() {
        "alice" => Some(Attribute::new(&q.arg().id, "key", "val")),
        _ => None,
    });

    // if a user has sso_attribute group: admins, assign attribute env: prod
    predicates.push(|q| match q.arg().id.as_str() {
        "alice" => Some(Attribute::new(&q.arg().id, "key", "val")),
        _ => None,
    });

    println!(
        "bob: {:?}\n",
        find(&Attribute::new("bob", "key", "val"), &predicates),
    );
    println!(
        "alice: {:?}\n",
        find(&Attribute::new("alice", "key", "val"), &predicates)
    );
}
