use std::convert::TryInto;
use cfb::{CompoundFile, Version};
use std::io::{Cursor, Write};

fn rd(bytes: &[u8], o: usize) -> u32 {
    u32::from_le_bytes(bytes[o..o + 4].try_into().unwrap())
}

fn summarize(bytes: &[u8]) {
    println!("=== len {} ===", bytes.len());
    let sector_shift = rd(bytes, 30) as u16 | ((rd(bytes, 31) as u16) << 8);
    let sector_len = 1usize << sector_shift;
    let num_sectors = (bytes.len() - 512) / sector_len;
    println!("sector_len {sector_len} num_sectors {num_sectors}");
    println!("num_dir_sectors {} num_fat {} first_dir {} first_minifat {} num_minifat {} first_difat {} num_difat {}",
        rd(bytes, 40), rd(bytes, 44), rd(bytes, 48), rd(bytes, 60), rd(bytes, 64), rd(bytes, 68), rd(bytes, 72));
    let difat0 = rd(bytes, 76);
    let fat_base = 512 + difat0 as usize * sector_len;
    let mut fat = vec![];
    for i in 0..num_sectors {
        fat.push(rd(bytes, fat_base + i * 4));
    }
    println!("FAT: {:?}", fat);
    let first_dir = rd(bytes, 48);
    // walk chain
    let mut chain = vec![];
    let mut cur = first_dir;
    while cur < 0xfffffffeu32 {
        chain.push(cur);
        cur = fat[cur as usize];
    }
    println!("dir chain {chain:?}");
    let first_minifat = rd(bytes, 60);
    if first_minifat != 0xffffffff {
        let mut mc = vec![];
        let mut c = first_minifat;
        while c < 0xfffffffeu32 { mc.push(c); c = fat[c as usize]; }
        println!("minifat chain {mc:?}");
        let mb = 512 + mc[0] as usize * sector_len;
        let mut mf = vec![];
        for _ in 0..(sector_len / 4) { mf.push(rd(bytes, mb + mf.len() * 4)); }
        while mf.last() == Some(&0xffffffff) { mf.pop(); }
        println!("minifat: {mf:?}");
    }
    for (idx, &s) in chain.iter().enumerate() {
        let base = 512 + s as usize * sector_len;
        for e in 0..(sector_len / 128) {
            let o = base + e * 128;
            let name_len = u16::from_le_bytes([bytes[o + 64], bytes[o + 65]]) as usize;
            if name_len == 0 { continue; }
            let name = String::from_utf16_lossy(
                &(0..(name_len / 2).saturating_sub(1)).map(|i| {
                    u16::from_le_bytes([bytes[o + 2 * i], bytes[o + 2 * i + 1]])
                }).collect::<Vec<u16>>());
            println!("dir[{}] sector {s} entry {e}: name {name:?} type {} start {} len {}",
                idx * (sector_len / 128) + e, bytes[o + 66], rd(bytes, o + 116),
                u64::from_le_bytes(bytes[o + 120..o + 128].try_into().unwrap()));
        }
    }
}

fn main() {
    let mut comp = CompoundFile::create_with_version(Version::V3, Cursor::new(Vec::new())).unwrap();
    comp.create_storage("/a").unwrap();
    let mut s = comp.create_stream("/a/mini").unwrap();
    s.write_all(&[7u8; 100]).unwrap();
    let mut s = comp.create_stream("/big").unwrap();
    s.write_all(&[9u8; 700]).unwrap();
    let mut cursor = comp.into_inner();
    cursor.flush().unwrap();
    summarize(&cursor.into_inner());

    // also empty baseline
    let comp = CompoundFile::create_with_version(Version::V3, Cursor::new(Vec::new())).unwrap();
    let mut cursor = comp.into_inner();
    cursor.flush().unwrap();
    summarize(&cursor.into_inner());
}
