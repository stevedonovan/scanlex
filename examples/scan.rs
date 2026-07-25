extern crate scanlex;

fn main() {
    let def = "foo 0.1 0.0 + 1.0e4 1e-3-5+4 0.1e+2";
    let text = std::env::args().skip(1).next().unwrap_or(def.to_string());
    let mut scan = scanlex::Scanner::new(&text);
    // println!("{:?}", scan.get_number());
    println!("{}", scan.get_number().err().unwrap());
    for t in scan {
        println!("{:?}", t);
    }
}
