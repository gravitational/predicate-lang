use std::collections::HashMap;
use std::fmt;
use std::fmt::Debug;

#[derive(Debug, Clone)]
pub struct User {
    name: String,
    sso_traits: HashMap<String, String>,
}

pub trait Query<T> {
    fn fact(&self, arg: &T) -> Option<T>;
    fn arg(&self) -> T;
}

#[derive(Clone, PartialEq)]
pub struct Attribute {
    pub id: Arg<String>,
    pub key: Arg<String>,
    pub val: Arg<String>,
}

impl std::fmt::Debug for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Attribute")
            .field("id", &self.id)
            .field("key", &self.key)
            .field("val", &self.val)
            .finish()
    }
}

impl Query<Attribute> for Attribute {
    fn fact(&self, a: &Self) -> Option<Self> {
        if self.id == a.id && self.key == a.key && self.val == a.val {
            return Some(a.clone());
        }
        None
    }

    fn arg(&self) -> Self {
        self.clone()
    }
}

impl Attribute {
    pub fn literal<Z: Into<String>>(id: Z, key: Z, val: Z) -> Self {
        Self {
            id: Arg::new(id),
            key: Arg::new(key),
            val: Arg::new(val),
        }
    }

    pub fn new<Z: Into<Arg<String>>>(id: Z, key: Z, val: Z) -> Self {
        Self {
            id: id.into(),
            key: key.into(),
            val: val.into(),
        }
    }
}

impl Into<Arg<String>> for String {
    fn into(self) -> Arg<String> {
        Arg::new(self.clone())
    }
}

#[derive(Clone)]
pub struct Arg<T: Debug + Clone> {
    v: Option<T>,
    compare: Option<fn(other: &T) -> bool>,
}

impl<T: Debug + Clone> Arg<T> {
    pub fn var() -> Self {
        Self {
            v: None,
            compare: None,
        }
    }
    pub fn new<Z: Into<T>>(v: Z) -> Self {
        Self {
            v: Some(v.into()),
            compare: None,
        }
    }
    pub fn compare(f: fn(other: &T) -> bool) -> Self {
        Self {
            v: None,
            compare: Some(f),
        }
    }
}

impl<T: Debug + Clone> std::fmt::Debug for Arg<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.v.fmt(f)
    }
}

impl<T: PartialEq + Debug + Clone> PartialEq for Arg<T> {
    fn eq(&self, other: &Self) -> bool {
        if let Some(cmp) = &self.compare {
            if let Some(b) = &other.v {
                return cmp(b);
            }
            // unbound arg will match any other argument
            return true;
        }
        if let Some(a) = &self.v {
            if let Some(b) = &other.v {
                return a == b;
            }
        } else {
            // unbound arg will match any other argument
            return true;
        }
        false
    }
}

pub type Predicate<T> = fn(&dyn Db, &dyn Query<T>) -> Option<T>;

pub trait Collection<T> {
    fn find(&self, db: &dyn Db, q: &dyn Query<T>) -> Option<T>;
    fn find_all(&self, db: &dyn Db, q: &dyn Query<T>) -> Vec<T>;
    fn push(&mut self, p: Predicate<T>);
}

pub struct VecCollection<T> {
    pub vals: Vec<Predicate<T>>,
}

impl<T> VecCollection<T> {
    pub fn new() -> Self {
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

    fn find_all(&self, db: &dyn Db, q: &dyn Query<T>) -> Vec<T> {
        let mut res = vec![];
        for pred in self.vals.iter() {
            match pred(db, q) {
                Some(t) => res.push(t),
                None => continue,
            }
        }
        res
    }

    fn push(&mut self, p: Predicate<T>) {
        self.vals.push(p);
    }
}

pub trait Db {
    fn get_attrs(&self) -> &dyn Collection<Attribute>;
    fn get_sso_attrs(&self) -> &dyn Collection<Attribute>;
}

pub struct LocalDb {
    pub attrs: VecCollection<Attribute>,
    pub sso_attrs: VecCollection<Attribute>,
}

impl LocalDb {
    pub fn new() -> Self {
        Self {
            attrs: VecCollection::<Attribute>::new(),
            sso_attrs: VecCollection::<Attribute>::new(),
        }
    }
}

impl Db for LocalDb {
    fn get_attrs(&self) -> &dyn Collection<Attribute> {
        &self.attrs
    }

    fn get_sso_attrs(&self) -> &dyn Collection<Attribute> {
        &self.sso_attrs
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basics() {
        let mut db = LocalDb::new();

        // declares a fact: Bob has attributre, key:val
        db.attrs
            .push(|_, q| q.fact(&Attribute::literal("bob", "key", "val")));

        db.attrs
            .push(|_, q| q.fact(&Attribute::literal("alice", "key", "val")));

        // any user has attribute source: demo
        db.attrs.push(|_, q| {
            q.fact(&Attribute::new(
                q.arg().id,
                Arg::new("soruce"),
                Arg::new("demo"),
            ))
        });

        // Alice has sso_attribute group:admins
        db.sso_attrs
            .push(|_, q| q.fact(&Attribute::literal("alice", "group", "admins")));

        // Alice has sso_attribute team-
        db.sso_attrs
            .push(|_, q| q.fact(&Attribute::literal("alice", "team-devs", "true")));

        // if a user has sso_attribute group: admins, assign attribute env: prod
        db.attrs.push(|db, q| {
            match db.get_sso_attrs().find(
                db,
                &Attribute::new(q.arg().id, Arg::new("group"), Arg::new("admins")),
            ) {
                Some(_) => q.fact(&Attribute::new(
                    q.arg().id,
                    Arg::new("env"),
                    Arg::new("prod"),
                )),
                _ => None,
            }
        });

        // if a user has sso_attribute that starts with `team-`, assign them this attribute: verified
        db.attrs.push(|db, q| {
            match db.get_sso_attrs().find(
                db,
                &Attribute::new(
                    q.arg().id,
                    Arg::compare(|x| x.starts_with("team-")),
                    Arg::var(),
                ),
            ) {
                Some(a) => q.fact(&Attribute::new(q.arg().id, a.key, Arg::new("verified"))),
                _ => None,
            }
        });

        assert_eq!(
            db.attrs
                .find(&db as &dyn Db, &Attribute::literal("bob", "key", "val")),
            Some(Attribute::literal("bob", "key", "val")),
            "Bob has attribute key: val",
        );

        println!(
            "What attributes bob has? {:?}\n",
            db.attrs.find_all(
                &db,
                &Attribute::new(
                    Arg::<String>::new("bob"),
                    Arg::<String>::var(),
                    Arg::<String>::var()
                )
            )
        );

        println!(
            "Who has attribute key: val? {:?}\n",
            db.attrs.find_all(
                &db,
                &Attribute::new(
                    Arg::<String>::var(),
                    Arg::<String>::new("key"),
                    Arg::<String>::new("val")
                )
            )
        );

        println!(
            "Does alice have attribute env, prod? {:?}\n",
            db.attrs
                .find(&db, &Attribute::literal("alice", "env", "prod"))
        );

        println!(
            "Does alice have attribute team-devs? {:?}\n",
            db.attrs.find(
                &db,
                &Attribute::new(Arg::new("alice"), Arg::new("team-devs"), Arg::var())
            )
        );

        println!(
            "Does bob have attribute env, prod? {:?}\n",
            db.attrs
                .find(&db, &Attribute::literal("bob", "env", "prod"))
        );

        println!(
            "What attriubutes alice has? {:?}\n",
            db.attrs.find_all(
                &db,
                &Attribute::new(Arg::new("alice"), Arg::var(), Arg::var())
            )
        );
    }
}
