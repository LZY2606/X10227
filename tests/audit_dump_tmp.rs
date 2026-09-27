use std::convert::TryInto;
use cfb::{CompoundFile, Version};
use std::io::{Cursor, Write};

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
#[test]
fn dump() {
    let data = build();
    let n = data.len()/512 - 1;
    println!("sectors={n}");
    for i in 0..n { print!("fat[{i}]={:#x} ", rd(&data,512+4*i)); }
    println!();
    // walk dir chain from header
    let mut d = rd(&data,0x30);
    let mut dirs = vec![];
    while d != 0xffff_ffff { dirs.push(d); d = rd(&data,512+4*d as usize); }
    println!("dir sectors={dirs:?}, minifat start={:#x}", rd(&data,0x3c));
    for (id,&sec) in dirs.iter().enumerate() {
        for slot in 0..4u32 {
            let sid = id as u32*4+slot;
            let base=(sec as usize+1)*512+slot as usize*128;
            let ot = data[base+66];
            if ot==0 || ot==255 {continue;}
            let nl0 = u16::from_le_bytes(data[base+64..base+66].try_into().unwrap()) as usize;
            if nl0==0 || nl0>64 {continue;}
            let nl = nl0;
            let units: Vec<u16> = data[base..base+2*(nl/2).min(64)].chunks(2)
                .map(|c| u16::from_le_bytes(c.try_into().unwrap())).collect();
            let name = String::from_utf16_lossy(&units);
            let start = rd(&data,base+116);
            let len = u32::from_le_bytes(data[base+120..base+124].try_into().unwrap());
            println!("sid={sid} type={ot} name={name:?} start={start:#x} len={len}");
        }
    }
}
