use std::convert::TryInto;
use cfb::{CompoundFile, Version};
use std::io::{Cursor, Write};

fn fat_at(bytes: &[u8], sector_len: usize, i: u32) -> u32 {
    let off = sector_len + (i as usize) * 4; // FAT is sector 1 in V3 fresh file
    u32::from_le_bytes(bytes[off..off+4].try_into().unwrap())
}

#[test]
fn dump_layout() {
    let cursor = Cursor::new(Vec::new());
    let mut comp = CompoundFile::create_with_version(Version::V3, cursor).unwrap();
    comp.create_stream("mini").unwrap().write_all(&[7u8; 200]).unwrap();
    comp.create_stream("big").unwrap().write_all(&[9u8; 900]).unwrap();
    comp.flush().unwrap();
    let bytes = comp.into_inner().into_inner();
    let sl = 512usize;
    let n = bytes.len() / sl - 1;
    println!("total sectors: {}", n);
    for i in 0..n as u32 {
        println!("fat[{i}] = {:#010x}", fat_at(&bytes, sl, i));
    }
    // directory entries
    // find dir chain: header first_dir_sector at offset 48
    let fds = u32::from_le_bytes(bytes[48..52].try_into().unwrap());
    let fmf = u32::from_le_bytes(bytes[60..64].try_into().unwrap());
    println!("first_dir_sector={fds} first_minifat_sector={fmf}");
    for e in 0..(n*4) {
        let base = (1 + fds as usize)*sl + e*128;
        if base+128 > bytes.len() { break; }
        let namelen = u16::from_le_bytes(bytes[base+64..base+66].try_into().unwrap());
        let objtype = bytes[base+66];
        let start = u32::from_le_bytes(bytes[base+116..base+120].try_into().unwrap());
        let len = u64::from_le_bytes(bytes[base+120..base+128].try_into().unwrap());
        if objtype != 0 || namelen != 0 {
            let name = String::from_utf16_lossy(&{
                let mut v = Vec::new();
                let nchars = (namelen as usize).saturating_sub(2)/2;
                for k in 0..nchars { v.push(u16::from_le_bytes(bytes[base+2*k..base+2*k+2].try_into().unwrap())); }
                v
            });
            println!("entry {e}: type={objtype} name={name:?} start={start} len={len}");
        }
    }
    // mini FAT entries
    for i in 0..16u32 {
        let off = (1+fmf as usize)*sl + i as usize*4;
        if off+4 <= bytes.len() {
            println!("minifat[{i}] = {:#x}", u32::from_le_bytes(bytes[off..off+4].try_into().unwrap()));
        }
    }
    // header initial difat
    for i in 0..3 {
        let off = 76 + i*4;
        println!("difat[{i}]={:#x}", u32::from_le_bytes(bytes[off..off+4].try_into().unwrap()));
    }
    std::fs::write("/tmp/cfbscratch/baseline.bin", &bytes).unwrap();
}
