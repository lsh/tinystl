// All based on the tests from microstl
// https://github.com/cry-inc/microstl/blob/master/tests/tests.cpp

use std::path::PathBuf;
use tinystl::{Encoding, Error, StlData};

fn read_file_unchecked<P: AsRef<std::path::Path>>(test_path: P) -> StlData {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push(test_path);
    let res = StlData::read_from_file(&path);
    assert!(res.is_ok());
    res.unwrap()
}

fn read_file<P: AsRef<std::path::Path>>(test_path: P) -> Result<StlData, Error> {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push(test_path);
    let res = StlData::read_from_file(&path);
    assert!(res.is_err());
    res
}

#[test]
fn minimal_ascii_file() {
    let res = read_file_unchecked("testdata/simple_ascii.stl");
    assert_eq!(res.name, "minimal");
    assert_eq!(res.encoding, Some(Encoding::Ascii));
    assert!(res.header.is_none());
    assert_eq!(res.triangles.len(), 1);
    assert_eq!(res.normals[0], [-1.0, 0.0, 0.0]);
    assert_eq!(res.triangles[0].v1, [0.0; 3]);
    assert_eq!(res.triangles[0].v2, [0.0, 0.0, 1.0]);
    assert_eq!(res.triangles[0].v3, [0.0, 1.0, 1.0]);
}

#[test]
fn ascii_file_with_creative_white_space() {
    let res = read_file_unchecked("testdata/crazy_whitespace_ascii.stl");
    assert_eq!(res.name, "min \t imal");
    assert_eq!(res.encoding, Some(Encoding::Ascii));
    assert!(res.header.is_none());
    assert_eq!(res.triangles.len(), 1);
    assert_eq!(res.normals[0], [-1.0, 0.0, 0.0]);
    assert_eq!(res.triangles[0].v1, [0.0; 3]);
    assert_eq!(res.triangles[0].v2, [0.0, 0.0, 1.0]);
    assert_eq!(res.triangles[0].v3, [0.0, 1.0, 1.0]);
}

#[test]
fn small_ascii_file() {
    let res = read_file_unchecked("testdata/half_donut_ascii.stl");

    assert_eq!(res.name, "Half Donut");
    assert_eq!(res.encoding, Some(Encoding::Ascii));
    assert!(res.header.is_none());
    assert_eq!(res.triangles.len(), 288);
}

#[test]
fn binary_file() {
    let res = read_file_unchecked("testdata/stencil_binary.stl");
    assert!(res.name.is_empty());
    assert_eq!(res.encoding, Some(Encoding::Binary));
    assert_eq!(res.header, Some([0; 80]));
    assert_eq!(res.triangles.len(), 2330);
}

#[test]
pub fn binary_freecad() {
    let res = read_file_unchecked("testdata/box_freecad_binary.stl");
    assert!(res.name.is_empty());
    assert_eq!(res.encoding, Some(Encoding::Binary));
    assert!(res.header.is_some());
    assert_eq!(res.triangles.len(), 12);
    assert_eq!(res.normals[11], [0.0, 0.0, 1.0]);
    assert_eq!(res.triangles[11].v1, [20.0, 0.0, 20.0]);
    assert_eq!(res.triangles[11].v2, [0.0, 0.0, 20.0]);
    assert_eq!(res.triangles[11].v3, [20.0, -20.0, 20.0]);
}

#[test]
fn meshlab_ascii() {
    let res = read_file_unchecked("testdata/box_meshlab_ascii.stl");
    assert_eq!(res.name, "STL generated by MeshLab");
    assert_eq!(res.encoding, Some(Encoding::Ascii));
    assert!(res.header.is_none());
    assert_eq!(res.triangles.len(), 12);
    assert_eq!(res.normals[11], [0.0, 0.0, 1.0]);
    assert_eq!(res.triangles[11].v1, [20.0, 0.0, 20.0]);
    assert_eq!(res.triangles[11].v2, [0.0, 0.0, 20.0]);
    assert_eq!(res.triangles[11].v3, [20.0, -20.0, 20.0]);
}

#[test]
fn utf8_file_name() {
    let res = read_file_unchecked("testdata/简化字.stl");
    assert_eq!(res.triangles.len(), 1);
}

#[test]
fn data_buffer() {
    let data = include_bytes!("../testdata/simple_ascii.stl").to_vec();
    assert!(!data.is_empty());
    let res = StlData::read_buffer(data.as_slice());
    assert!(res.is_ok());
    let res = res.unwrap();
    assert_eq!(res.triangles.len(), 1);
}

#[test]
fn sphere() {
    let mut reader = StlData {
        force_normals: true,
        ..Default::default()
    };
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("testdata/sphere_binary.stl");
    let res = reader.set_from_file(&path);
    assert!(res.is_ok());
    assert_eq!(reader.triangles.len(), 1360);
    let radius = 10.0;
    let allowed_deviation = 0.00001;
    for (f, normal) in reader.triangles.iter().zip(reader.normals) {
        // Check if all vertices are on the sphere surface
        let length1 = (f.v1[0] * f.v1[0] + f.v1[1] * f.v1[1] + f.v1[2] * f.v1[2]).sqrt();
        assert!((length1 - radius).abs() < allowed_deviation);
        let length2 = (f.v2[0] * f.v2[0] + f.v2[1] * f.v2[1] + f.v2[2] * f.v2[2]).sqrt();
        assert!((length2 - radius).abs() < allowed_deviation);
        let length3 = (f.v3[0] * f.v3[0] + f.v3[1] * f.v3[1] + f.v3[2] * f.v3[2]).sqrt();
        assert!((length3 - radius).abs() < allowed_deviation);

        // Check if origin is "behind" the normal plane
        // (normal of all sphere surface triangle should point away from the origin)
        let origin = [0.0; 3];
        let tmp = [
            origin[0] - f.v1[0],
            origin[1] - f.v1[1],
            origin[2] - f.v1[2],
        ];
        let dot = normal[0] * tmp[0] + normal[1] * tmp[1] + normal[2] * tmp[2];
        assert!(dot < 0.0);

        // Check normal vector length
        let length = (normal[0] * normal[0] + normal[1] * normal[1] + normal[2] * normal[2]).sqrt();
        assert!((length - 1.0).abs() < allowed_deviation);
    }
}

#[test]
fn incomplete_vertex_ascii() {
    let res = read_file("testdata/incomplete_vertex_ascii.stl");
    assert!(matches!(res, Err(Error::Parse(6))));
}

#[test]
fn incomplete_normal_ascii() {
    let res = read_file("testdata/incomplete_normal_ascii.stl");
    assert!(matches!(res, Err(Error::Parse(2))));
}

#[test]
fn empty_file() {
    let res = read_file("testdata/empty_file.stl");
    assert!(matches!(res, Err(Error::MissingData)));
}

#[test]
fn non_existing() {
    let res = read_file("does_not_exist.stl");
    if let Err(Error::Io(e)) = res {
        assert_eq!(e.kind(), std::io::ErrorKind::NotFound);
    } else {
        panic!("Encounted an unexpected error");
    }
}

#[test]
fn incomplete_binary() {
    let res = read_file("testdata/incomplete_binary.stl");
    assert!(matches!(res, Err(Error::MissingData)));
}
