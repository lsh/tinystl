use std::io::Write;
use tinystl::StlData;

pub fn main() {
    let args = std::env::args().collect::<Vec<String>>();
    let data = StlData::read_from_file(&args[1]).unwrap();
    let mut out = std::io::stdout().lock();
    writeln!(&mut out, "{}", data.triangles.len()).unwrap();
}
