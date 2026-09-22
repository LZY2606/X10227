use cfb::CompoundFile;
use std::io::Cursor;

fn main() {
    let bytes: Vec<u8> = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    eprintln!("auditing {} bytes", bytes.len());
    let report = cfb::audit_structure(Cursor::new(bytes)).unwrap();
    eprintln!("findings: {}", report.findings().len());
    for f in report.findings() {
        eprintln!("  [{:?}/{:?}] {}", f.table(), f.kind(), f);
    }
    eprintln!("plan: {:?}", report.repair_plan().map(|p| p.dry_run().len()));
}
