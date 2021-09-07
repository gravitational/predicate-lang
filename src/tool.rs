//extern crate proc_macro;
//use proc_macro::TokenStream;

// https://crates.io/crates/syn

//#[proc_macro_derive(Query)]
//pub fn derive_query(_item: TokenStream) -> TokenStream {
//    "fn answer() -> u32 { 42 }".parse().unwrap()
//}

mod predicate;
use predicate::*;

fn main() {
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

    println!(
        "Does bob have attriube key, val? {:?}\n",
        db.attrs
            .find(&db as &dyn Db, &Attribute::literal("bob", "key", "val")),
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
