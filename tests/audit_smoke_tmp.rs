use cfb::{CompoundFile, OpenOptions};
use std::io::{Cursor, Write};

fn base_v3() -> Vec<u8> {
    let mut comp =
        CompoundFile::create_with_version(cfb::Version::V3, Cursor::new(Vec::new())).unwrap();
    comp.create_stream("mini").unwrap().write_all(&[7u8; 80]).unwrap();
    comp.create_stream("big").unwrap().write_all(&[9u8; 2000]).unwrap();
    let cursor = comp.into_inner();
    cursor.into_inner()
}

#[test]
fn clean_file_has_no_findings() {
    let data = base_v3();
    let report = OpenOptions::new().audit_with(Cursor::new(data.clone())).unwrap();
    for f in report.findings() {
        eprintln!("FINDING: {f}");
    }
    assert!(report.is_clean(), "expected clean, got {:?}", report.findings());
}
