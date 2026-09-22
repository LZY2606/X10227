use cfb::{CompoundFile, Version};
use std::convert::TryInto;
use std::io::{Cursor, Write};
fn ru32(d: &[u8], o: usize) -> u32 { u32::from_le_bytes(d[o..o+4].try_into().unwrap()) }
fn wu32(d: &mut [u8], o: usize, v: u32) { d[o..o+4].copy_from_slice(&v.to_le_bytes()) }
fn build() -> Vec<u8> {
    let mut comp = CompoundFile::create_with_version(Version::V3, Cursor::new(Vec::new())).unwrap();
    comp.create_storage("/dir/").unwrap();
    // A >4096-byte stream uses regular (FAT) sectors.
    let mut s = comp.create_stream("/big").unwrap();
    s.write_all(&vec![7u8; 5000]).unwrap();
    drop(s);
    let mut s2 = comp.create_stream("/mini").unwrap();
    s2.write_all(&b"hello mini"[..]).unwrap();
    drop(s2);
    comp.flush().unwrap();
    comp.into_inner().into_inner()
}
fn main() {
    let bytes = build();
    let sl = 512usize;
    let fat_sec = ru32(&bytes, 76) as usize;
    let first_dir = ru32(&bytes, 48);
    let first_minifat = ru32(&bytes, 60);
    eprintln!("fat_sec={fat_sec} dir={first_dir} minifat={first_minifat} len={}", bytes.len());
    let foff = |n: u32| sl + fat_sec*sl + n as usize*4;
    let walk = |d: &[u8], start: u32| -> Vec<u32> {
        let mut v=vec![]; let mut c=start; let mut k=0;
        while c!=0xFFFFFFFE { v.push(c); c=ru32(d, foff(c)); k+=1; if k>200 {break;} }
        v
    };
    let dir_chain = walk(&bytes, first_dir);
    eprintln!("dir_chain={dir_chain:?} minifat_chain={:?}", walk(&bytes, first_minifat));
    let deoff = |id: u32| -> usize {
        let sector = dir_chain[(id/4) as usize];
        sl + sector as usize*sl + (id%4) as usize*128
    };
    std::fs::write("/tmp/c_clean.bin", &bytes).unwrap();
    for id in 0..(dir_chain.len() as u32*4) {
        let off=deoff(id); let start=ru32(&bytes,off+116);
        let len=u64::from_le_bytes(bytes[off+120..off+128].try_into().unwrap());
        if len>0 { eprintln!("entry {id} start={start} len={len} chain={:?}",
            if len>=4096 {walk(&bytes,start)} else {vec![]}); }
    }
    // 1. cross link: minifat chain -> big stream first FAT sector
    let mut big_start=None;
    for id in 0..(dir_chain.len() as u32*4) {
        let off=deoff(id);
        let len=u64::from_le_bytes(bytes[off+120..off+128].try_into().unwrap());
        if len>=4096 { big_start=Some(ru32(&bytes,off+116)); }
    }
    if let Some(bs)=big_start {
        let mut c=bytes.clone();
        // point the sector just before minifat chain's end... minifat is 1 sector;
        // point its FAT edge to big's sector
        wu32(&mut c, foff(first_minifat), bs);
        std::fs::write("/tmp/c_cross.bin",&c).unwrap();
    }
    // 2. cycle: minifat self-loop in FAT
    let mut c=bytes.clone(); wu32(&mut c, foff(first_minifat), first_minifat);
    std::fs::write("/tmp/c_cycle.bin",&c).unwrap();
    // 3. truncated directory: last dir sector points OOB
    let last_dir=*dir_chain.last().unwrap();
    let mut c=bytes.clone(); wu32(&mut c, foff(last_dir), 99999);
    std::fs::write("/tmp/c_truncdir.bin",&c).unwrap();
    // 4. orphan regular sector: a FREE sector -> EOC, no owner
    let num=(bytes.len()/sl-1) as u32;
    let mut fsd=None;
    for n in 0..num { if ru32(&bytes,foff(n))==0xFFFFFFFF {fsd=Some(n);break;} }
    if let Some(fs)=fsd { let mut c=bytes.clone(); wu32(&mut c, foff(fs), 0xFFFFFFFE);
        std::fs::write("/tmp/c_orphan.bin",&c).unwrap(); eprintln!("orphan sector {fs}"); }
    // 5. mini OOB: corrupt /mini start
    let mut c=bytes.clone();
    for id in 0..(dir_chain.len() as u32*4) {
        let off=deoff(id);
        let len=u64::from_le_bytes(bytes[off+120..off+128].try_into().unwrap());
        if len>0 && len<4096 { wu32(&mut c, off+116, 7777); }
    }
    std::fs::write("/tmp/c_minioob.bin",&c).unwrap();
    // 6. length mismatch (inflate mini stream length)
    let mut c=bytes.clone();
    for id in 0..(dir_chain.len() as u32*4) {
        let off=deoff(id);
        let len=u64::from_le_bytes(bytes[off+120..off+128].try_into().unwrap());
        if len>0 && len<4096 {
            c[off+120..off+128].copy_from_slice(&(len+6400).to_le_bytes());
        }
    }
    std::fs::write("/tmp/c_lenmismatch.bin",&c).unwrap();
    eprintln!("generated");
}
