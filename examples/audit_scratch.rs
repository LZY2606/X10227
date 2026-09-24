use std::convert::TryInto;
use std::io::{Cursor, Write};

use cfb::audit::audit_bytes;

const SECTOR_LEN: usize = 4096;
const EOC: u32 = 0xfffffffe;

fn u32le(data: &[u8], off: usize) -> u32 {
    u32::from_le_bytes(data[off..off + 4].try_into().unwrap())
}
fn u64le(data: &[u8], off: usize) -> u64 {
    u64::from_le_bytes(data[off..off + 8].try_into().unwrap())
}
fn set_u32(data: &mut Vec<u8>, off: usize, val: u32) {
    data[off..off + 4].copy_from_slice(&val.to_le_bytes());
}
fn set_u64(data: &mut Vec<u8>, off: usize, val: u64) {
    data[off..off + 8].copy_from_slice(&val.to_le_bytes());
}

fn build() -> Vec<u8> {
    let mut buf = Vec::new();
    let mut cfb = cfb::CompoundFile::create(Cursor::new(&mut buf)).unwrap();
    cfb.create_stream("/mini").unwrap().write_all(&[7u8; 100]).unwrap();
    cfb.create_stream("/big").unwrap().write_all(&vec![9u8; 9000]).unwrap();
    cfb.flush().unwrap();
    drop(cfb);
    buf
}

struct EntryLoc {
    start: u32,
    len: u64,
    off: usize,
}

fn entries(data: &[u8], names: &[&str]) -> Vec<(String, EntryLoc)> {
    let fat_sector = u32le(data, 76);
    let mut sector = u32le(data, 48);
    let mut out = Vec::new();
    while sector != EOC {
        let base = (sector as usize + 1) * SECTOR_LEN;
        for slot in 0..32 {
            let e = base + slot * 128;
            let name_len_chars =
                u16::from_le_bytes([data[e + 64], data[e + 65]]) as usize / 2;
            if name_len_chars >= 2 && e + 2 * (name_len_chars - 1) + 2 <= data.len()
            {
                let units: Vec<u16> = (0..name_len_chars - 1)
                    .map(|i| {
                        u16::from_le_bytes([
                            data[e + 2 * i],
                            data[e + 2 * i + 1],
                        ])
                    })
                    .collect();
                if let Ok(name) = String::from_utf16(&units) {
                    println!("entry name {:?} start={} len={}", name, u32le(data, e+116), u64le(data, e+120));
                    if names.contains(&name.as_str()) {
                        out.push((
                            name,
                            EntryLoc {
                                start: u32le(data, e + 116),
                                len: u64le(data, e + 120),
                                off: e,
                            },
                        ));
                    }
                }
            }
        }
        let fat_off =
            (fat_sector as usize + 1) * SECTOR_LEN + sector as usize * 4;
        sector = u32le(data, fat_off);
    }
    out
}

fn get<'a>(v: &'a [(String, EntryLoc)], name: &str) -> &'a EntryLoc {
    &v.iter().find(|(n, _)| n == name).unwrap().1
}

fn fat_at(data: &[u8], sector: u32) -> u32 {
    let fat_sector = u32le(data, 76);
    u32le(
        data,
        (fat_sector as usize + 1) * SECTOR_LEN + sector as usize * 4,
    )
}
fn set_fat(data: &mut Vec<u8>, sector: u32, val: u32) {
    let fat_sector = u32le(data, 76);
    set_u32(
        data,
        (fat_sector as usize + 1) * SECTOR_LEN + sector as usize * 4,
        val,
    );
}
fn chain(data: &[u8], start: u32) -> Vec<u32> {
    let mut ids = vec![start];
    let mut cur = start;
    loop {
        let n = fat_at(data, cur);
        if n == EOC {
            break;
        }
        ids.push(n);
        cur = n;
    }
    ids
}

fn show(label: &str, data: &[u8]) {
    let report = audit_bytes(data).unwrap();
    println!(
        "=== {} clean={} findings={}",
        label,
        report.is_clean(),
        report.findings().len()
    );
    for f in report.findings() {
        println!(
            "  {:?} {:?} @ {}: {}",
            f.table, f.corruption, f.location, f.detail
        );
    }
    let plan = report.repair_plan();
    println!(
        "  repairable={} patches={} prereq={} target={}",
        plan.is_repairable(),
        plan.num_patches(),
        plan.prerequisite_digest(),
        plan.target_digest()
    );
}

fn main() {
    let clean = build();
    let ents = entries(&clean, &["Root Entry", "mini", "big"]);
    for (n, e) in &ents {
        println!("entry {} start={} len={}", n, e.start, e.len);
    }
    show("clean", &clean);
    let root = get(&ents, "Root Entry");
    let mini = get(&ents, "mini");
    let big = get(&ents, "big");
    let minifat_sector = u32le(&clean, 60);
    println!("minifat sector {}", minifat_sector);

    // 1. cross link: last big sector -> ministream container
    let big_chain = chain(&clean, big.start);
    println!("big chain {:?}", big_chain);
    let mut d = clean.clone();
    set_fat(&mut d, *big_chain.last().unwrap(), root.start);
    show("cross-link", &d);

    // 2. cycle
    let mut d = clean.clone();
    set_fat(&mut d, *big_chain.last().unwrap(), big.start);
    show("fat-cycle", &d);

    // 3. orphan: detach big stream's chain from its directory entry
    let mut d = clean.clone();
    set_u32(&mut d, big.off + 116, EOC);
    set_u64(&mut d, big.off + 120, 0);
    show("orphan", &d);

    // 4. mini oob
    let mut d = clean.clone();
    set_u32(&mut d, mini.off + 116, 123456789);
    show("mini-oob", &d);

    // 5. length mismatch
    let mut d = clean.clone();
    set_u64(&mut d, big.off + 120, 1_000_000);
    show("length-mismatch", &d);

    // 6. minifat cycle
    let mut d = clean.clone();
    let moff = (minifat_sector as usize + 1) * SECTOR_LEN
        + mini.start as usize * 4;
    set_u32(&mut d, moff, mini.start);
    show("minifat-cycle", &d);

    // 7. double occupancy: free chain ... make mini container sector also
    //    pointed from big's last
    let mut d = clean.clone();
    // Make big chain exactly 2 sectors so last points to root container.
    set_fat(&mut d, *big_chain.last().unwrap(), root.start);
    show("double-occupancy", &d);
}
