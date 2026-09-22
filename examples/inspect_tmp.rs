fn main() {
    let mut comp = cfb::CompoundFile::create(std::io::Cursor::new(Vec::new())).unwrap();
    use std::io::Write;
    comp.create_stream("/a").unwrap().write_all(&vec![7u8; 5000]).unwrap();
    let mut c = comp;
    c.create_storage("/s/").unwrap();
    c.create_stream("/s/b").unwrap().write_all(&vec![9u8; 5000]).unwrap();
    c.flush().unwrap();
    let buf = c.into_inner().into_inner();
    let sector_len = 512usize;
    let hdr = &buf[..512];
    let rd = |o: usize| u32::from_le_bytes(hdr[o..o+4].try_into().unwrap());
    println!("num_fat_sectors={} first_dir={} first_minifat={} num_minifat={} first_difat={}",
        rd(44), rd(48), rd(60), rd(64), rd(68));
    let first_fat_sector = u32::from_le_bytes(hdr[76..80].try_into().unwrap());
    println!("first fat sector from DIFAT[0]={}", first_fat_sector);
    let fat_off = 512 + first_fat_sector as usize * sector_len;
    let n = sector_len/4;
    let fat: Vec<u32> = (0..n).map(|i| u32::from_le_bytes(buf[fat_off+4*i..fat_off+4*i+4].try_into().unwrap())).collect();
    let printable = fat.iter().take_while(|&&v| v != 0xffffffff).count().max(1);
    for (i, &v) in fat.iter().enumerate().take(printable + 1) {
        println!("FAT[{}] = {:#010x}", i, v);
    }
    println!("file len = {}", buf.len());
}
