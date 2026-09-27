use std::convert::TryInto;
use cfb::{CompoundFile, Corruption, OpenOptions, Table, Version};
use std::io::{Cursor, Read, Seek, SeekFrom, Write};

fn build() -> Vec<u8> {
    let mut comp = CompoundFile::create_with_version(Version::V3, Cursor::new(Vec::new())).unwrap();
    comp.create_stream("mini1").unwrap().write_all(&[1u8; 80]).unwrap();
    comp.create_stream("mini2").unwrap().write_all(&[2u8; 128]).unwrap();
    comp.create_stream("big1").unwrap().write_all(&[3u8; 1500]).unwrap();
    comp.create_stream("big2").unwrap().write_all(&[4u8; 1100]).unwrap();
    comp.into_inner().into_inner()
}
fn rd(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(data[off..off+4].try_into().unwrap())
}
fn wr(data: &mut [u8], off: usize, v: u32) {
    data[off..off+4].copy_from_slice(&v.to_le_bytes());
}
fn fat_off(sector: usize) -> usize { 512 + 4*sector }
fn dir_field(stream_id: u32, field: usize) -> usize {
    let sector = 1 + stream_id/4;
    let slot = stream_id%4;
    (sector as usize)*512 + slot as usize*128 + field
}
fn audit(data: &[u8]) -> cfb::AuditReport {
    OpenOptions::new().audit_with(Cursor::new(data.to_vec())).unwrap()
}
fn show(tag: &str, data: &[u8]) {
    let r = audit(data);
    println!("== {tag} ==");
    for f in r.findings() {
        println!("  {:?}/{:?} off={} ctx={:?}: {}", f.table, f.corruption, f.offset, f.context, f.message);
    }
    let plan = r.plan();
    for st in plan.steps() {
        println!("    step: {}", st.description);
    }
}

#[test]
fn inject() {
    let mut data = build();
    // print base layout
    println!("len={}, fms={:#x}", data.len(), rd(&data,0x3c));
    let fds = rd(&data,0x30);
    for slot in 0..8 {
        let base = (fds as usize+1)*512 + slot*128;
        let start = rd(&data,base+116);
        let len = u32::from_le_bytes(data[base+120..base+124].try_into().unwrap());
        let ot = data[base+66];
        if ot != 0 { println!("entry {slot} type {ot} start={start:#x} len={len}"); }
    }
    for i in 0..data.len()/512-1 { print!("fat[{i}]={:#x} ", rd(&data,fat_off(i))); }
    println!();
    show("clean", &data);

    // 1) FAT cycle: big1 chain. Need big1 sectors: print them first.
}
