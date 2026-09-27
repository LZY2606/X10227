use std::convert::TryInto;
use cfb::{CompoundFile, Version};
use std::io::{Cursor, Write};

fn build() -> Vec<u8> {
    let mut comp = CompoundFile::create_with_version(Version::V3, Cursor::new(Vec::new())).unwrap();
    comp.create_storage("st").unwrap();
    comp.create_stream("mini1").unwrap().write_all(&[1u8; 80]).unwrap();
    comp.create_stream("mini2").unwrap().write_all(&[2u8; 128]).unwrap();
    comp.create_stream("big1").unwrap().write_all(&[3u8; 1500]).unwrap();
    comp.into_inner().into_inner()
}

fn rd(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(data[off..off+4].try_into().unwrap())
}

#[test]
fn layout() {
    let data = build();
    // sector 0 is FAT at file offset 512
    println!("file len = {}", data.len());
    println!("num sectors = {}", data.len()/512 - 1);
    for i in 0..data.len()/512 - 1 {
        println!("fat[{i}] = {:#010x}", rd(&data, 512 + 4*i));
    }
    // directory entries
    // first_dir_sector at header 0x30
    let fds = rd(&data, 0x30);
    println!("first dir sector = {fds}");
    let fms = rd(&data, 0x3c);
    let nms = rd(&data, 0x40);
    println!("first minifat = {fms}, num minifat = {nms}");
    for slot in 0..4 {
        let base = ((fds+1)*512) as usize + slot*128;
        let nl = u16::from_le_bytes(data[base+64..base+66].try_into().unwrap());
        let name: String = String::from_utf16(&data[base..base+64].chunks(2)
            .take((nl as usize/2).saturating_sub(1).max(1))
            .map(|c| u16::from_le_bytes(c.try_into().unwrap())).collect::<Vec<_>>())
            .unwrap_or_default();
        let ot = data[base+66];
        let start = rd(&data, base+116);
        let len = u64::from_le_bytes(data[base+120..base+128].try_into().unwrap()) & 0xffff_ffff;
        println!("entry {slot}: type={ot} name={name:?} start={start} len={len}");
    }
    // miniFAT
    if fms != 0xffff_ffff {
        println!("minifat chain sector {fms}:");
        for i in 0..128 {
            let v = rd(&data, (fms as usize+1)*512 + 4*i);
            if v != 0xffff_ffff { print!(" {i}:{v:#x}"); }
        }
        println!();
    }
}
