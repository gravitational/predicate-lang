use crepe::crepe;

crepe! {
    @input
    struct Edge(i32, i32);

    @output
    struct Reachable(i32, i32);

    Reachable(x, y) <- Edge(x, y);
    Reachable(x, z) <- Edge(x, y), Reachable(y, z);
}

fn main() {
    let mut runtime = Crepe::new();
    runtime.extend(&[Edge(1, 2), Edge(2, 3), Edge(3, 4), Edge(2, 5)]);

    let (reachable,) = runtime.run();
    for Reachable(x, y) in reachable {
        println!("node {} can reach node {}", x, y);
    }
}
