use crepe::crepe;

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
enum Action {
    SSH,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
struct User {
    name: &'static str,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
struct Host {
    name: &'static str,
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug)]
enum Target {
    Host(Host),
}

crepe! {
    @output
    #[derive(Debug)]
    struct Allow(Action, User, Target, &'static str);

    struct Member(User, &'static str);

    Allow(Action::SSH, User{name: "alice"}, Target::Host(Host{name: "mars"}), "root");

    Allow(Action::SSH, u, t, p) <-
        Member(u, "admin"),
        ( p  == "root");
}

fn main() {
    let runtime = Crepe::new();
    /*
    runtime.extend(&[Allow(
        Action::SSH,
        User { name: "alice" },
        Target::Host {},
        "root",
    )]);*/

    let results = runtime.run();
    println!("results: {:?}", results);
}
