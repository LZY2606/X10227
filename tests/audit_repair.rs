//! Regression material for
//! "rust-cfb: damaged-allocation-chain audit and read-only repair plan".
//!
//! Every case enters through the real public surface: `CompoundFile::create`
//! builds a valid compound file, bytes are corrupted at computed offsets, and
//! auditing / planning / applying all go through `cfb::audit`,
//! `OpenOptions::audit_with`, `AuditReport`, and `RepairPlan`.  Nothing about
//! the crate's internal final objects is fabricated by these tests.

use cfb::{
    ApplyOutcome, ChainLayer, CompoundFile, Evidence, OpenOptions, RepairPlan,
};
use std::io::{self, Cursor, Read, Seek, SeekFrom, Write};

//===========================================================================//
// Fixture helpers.

/// A valid V3 compound file with:
/// * a large stream `big` (> 4 KiB, regular-FAT backed, 2 sectors),
/// * a small stream `small` (< 4 KiB, MiniFAT backed, 2 mini sectors).
struct Baseline {
    data: Vec<u8>,
    sector_len: u64,
    big_entry: u32,
    small_entry: u32,
}

fn build_baseline() -> Baseline {
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let sector_len = comp.version().sector_len() as u64;
    comp.create_stream("big")
        .unwrap()
        .write_all(&vec![b'B'; (sector_len * 2) as usize])
        .unwrap();
    comp.create_stream("small")
        .unwrap()
        .write_all(&[b's'; 100])
        .unwrap();
    comp.flush().unwrap();
    let data = comp.into_inner().into_inner();

    // Locate the entries by scanning directory-entry slots for names.
    let big_entry = find_entry(&data, sector_len, "big");
    let small_entry = find_entry(&data, sector_len, "small");
    Baseline { data, sector_len, big_entry, small_entry }
}

fn find_entry(data: &[u8], sector_len: u64, name: &str) -> u32 {
    let encoded: Vec<u16> = name.encode_utf16().collect();
    let entries_per_sector = (sector_len / 128) as u32;
    let num_sectors = data.len() as u64 / sector_len - 1;
    for sector in 0..num_sectors as u32 {
        for slot in 0..entries_per_sector {
            let base =
                (sector as u64 + 1) * sector_len + slot as u64 * 128;
            let mut matches = true;
            for (i, unit) in encoded.iter().enumerate() {
                let off = base + (i as u64) * 2;
                let value = u16::from_le_bytes([
                    data[off as usize],
                    data[off as usize + 1],
                ]);
                if value != *unit {
                    matches = false;
                    break;
                }
            }
            if matches {
                return sector * entries_per_sector + slot;
            }
        }
    }
    panic!("entry {name} not found")
}

fn read_u32(data: &[u8], offset: u64) -> u32 {
    u32::from_le_bytes(
        data[offset as usize..offset as usize + 4]
            .try_into()
            .unwrap(),
    )
}

fn write_u32(data: &mut [u8], offset: u64, value: u32) {
    data[offset as usize..offset as usize + 4]
        .copy_from_slice(&value.to_le_bytes());
}

fn entry_field(sector_len: u64, entry_id: u32, offset_in_entry: u64) -> u64 {
    let entries_per_sector = sector_len / 128;
    let sector = entry_id as u64 / entries_per_sector;
    let slot = entry_id as u64 % entries_per_sector;
    (sector + 1) * sector_len + slot * 128 + offset_in_entry
}

fn start_sector_offset(sector_len: u64, entry_id: u32) -> u64 {
    entry_field(sector_len, entry_id, 116)
}

/// Finds the FAT cell offset (in the file) for `fat_index`.
fn fat_cell_offset(data: &[u8], sector_len: u64, fat_index: u32) -> u64 {
    // Parse the header DIFAT (baseline has one FAT sector, no DIFAT sectors).
    let first_fat_sector = read_u32(data, 76) as u64;
    let entries_per_sector = sector_len / 4;
    let fat_sector = first_fat_sector + (fat_index as u64 / entries_per_sector);
    let within = fat_index as u64 % entries_per_sector;
    (fat_sector + 1) * sector_len + within * 4
}

/// Returns the regular sector ids of the big stream, in chain order.
fn chain_of(data: &[u8], sector_len: u64, start: u32) -> Vec<u32> {
    let mut chain = vec![start];
    let mut cur = start;
    loop {
        let cell = read_u32(data, fat_cell_offset(data, sector_len, cur));
        if cell == 0xFFFFFFFE {
            break;
        }
        chain.push(cell);
        cur = cell;
    }
    chain
}

fn audit(data: &[u8]) -> cfb::AuditReport {
    cfb::audit(Cursor::new(data)).expect("audit should run")
}

fn has_finding(
    report: &cfb::AuditReport,
    predicate: impl Fn(&Evidence) -> bool,
) -> bool {
    report.evidence().iter().any(predicate)
}

//===========================================================================//
// Baseline: small reproducible inputs first.

#[test]
fn audit_baseline_valid_file_is_clean() {
    let baseline = build_baseline();
    let report = audit(&baseline.data);
    assert!(
        report.is_clean(),
        "valid file must audit clean, got: {:?}",
        report.evidence()
    );
}

#[test]
fn audit_through_open_options_entry() {
    let baseline = build_baseline();
    let report = OpenOptions::new()
        .audit_with(Cursor::new(baseline.data.clone()))
        .expect("audit_with");
    assert!(report.is_clean());
}

#[test]
fn audit_rejects_bad_header_with_existing_error_layer() {
    let mut bad = build_baseline().data;
    bad[0] ^= 0xFF;
    let err = cfb::audit(Cursor::new(bad)).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
}

//===========================================================================//
// Fixed inputs: the six required corruption cases.

#[test]
fn audit_finding_crossed_chains_double_allocation() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();

    // Two streams own disjoint FAT chains.  Make the first sector of `big`
    // also point back into the second stream's chain: redirect big's start
    // to the sector already owned by `big`'s second ... instead, splice:
    // take a sector from small's regular chain?  small is mini.  Use two big
    // streams by adding a second large stream.
    let mut comp = CompoundFile::create(Cursor::new(Vec::new())).unwrap();
    let sector_len = comp.version().sector_len() as u64;
    comp.create_stream("a")
        .unwrap()
        .write_all(&vec![b'a'; sector_len as usize])
        .unwrap();
    comp.create_stream("b")
        .unwrap()
        .write_all(&vec![b'b'; sector_len as usize])
        .unwrap();
    comp.flush().unwrap();
    let mut data = comp.into_inner().into_inner();
    let a_entry = find_entry(&data, sector_len, "a");
    let b_entry = find_entry(&data, sector_len, "b");
    let a_start = read_u32(&data, start_sector_offset(sector_len, a_entry));
    let b_start = read_u32(&data, start_sector_offset(sector_len, b_entry));
    assert_ne!(a_start, b_start);

    // Splice: make b's chain point at a's sector (both were EOC).  This makes
    // a_start reachable from two directory entries.
    write_u32(
        &mut data,
        fat_cell_offset(&data, sector_len, b_start),
        a_start,
    );
    write_u32(
        &mut data,
        fat_cell_offset(&data, sector_len, a_start),
        0xFFFFFFFE,
    );

    let report = audit(&data);
    let crossing = report
        .evidence()
        .iter()
        .find(|e| matches!(
            e,
            Evidence::DoubleAllocation {
                layer: ChainLayer::Fat,
                ..
            }
        ))
        .expect("crossed chain must be reported as double allocation");
    let context = crossing.to_string();
    assert!(context.contains("entry"), "context must name owners: {context}");
    // It must not be mislabeled as a cycle or out-of-bounds.
    assert!(!has_finding(&report, |e| matches!(
        e,
        Evidence::Cycle { layer: ChainLayer::Fat, .. }
    )));
    assert!(!has_finding(&report, |e| matches!(
        e,
        Evidence::OutOfBounds { layer: ChainLayer::Fat, .. }
    )));
    let _ = baseline;
}

#[test]
fn audit_finding_fat_cycle() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();
    let big_start = read_u32(
        &data,
        start_sector_offset(baseline.sector_len, baseline.big_entry),
    );
    let chain = chain_of(&data, baseline.sector_len, big_start);
    assert_eq!(chain.len(), 2);
    // Point the second sector back to the first -> FAT cycle.
    write_u32(
        &mut data,
        fat_cell_offset(&data, baseline.sector_len, chain[1]),
        chain[0],
    );

    let report = audit(&data);
    let cycle = report
        .evidence()
        .iter()
        .find(|e| matches!(
            e,
            Evidence::Cycle { layer: ChainLayer::Fat, .. }
        ))
        .expect("FAT cycle must be reported");
    assert_eq!(cycle.first_location(), chain[0]);
    let context = cycle.to_string();
    assert!(context.contains(&chain[0].to_string()));
    // Distinct from double allocation.
    assert!(!has_finding(&report, |e| matches!(
        e,
        Evidence::DoubleAllocation { .. }
    )));
}

#[test]
fn audit_finding_truncated_directory_chain() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();
    // The directory chain starts at first_dir_sector (header offset 48).
    let first_dir = read_u32(&data, 48);
    // Short-circuit the directory chain after its first sector: the former
    // next directory sector becomes unreachable.
    write_u32(
        &mut data,
        fat_cell_offset(&data, baseline.sector_len, first_dir),
        0xFFFFFFFE,
    );

    let report = audit(&data);
    let trunc = report
        .evidence()
        .iter()
        .find(|e| matches!(e, Evidence::TruncatedDirectory { .. }))
        .expect("truncated directory must be reported");
    let context = trunc.to_string();
    assert!(
        context.to_lowercase().contains("director"),
        "context should describe directory truncation: {context}"
    );
}

#[test]
fn audit_finding_orphan_sector() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();
    let big_start = read_u32(
        &data,
        start_sector_offset(baseline.sector_len, baseline.big_entry),
    );
    let chain = chain_of(&data, baseline.sector_len, big_start);

    // Detach the tail sector of `big`: mark the first sector EOC, leaving the
    // second sector's non-free cell reachable from nothing.  This also
    // shrinks the stream, so a length mismatch is expected alongside, but the
    // orphan class itself must be present and distinct.
    write_u32(
        &mut data,
        fat_cell_offset(&data, baseline.sector_len, chain[0]),
        0xFFFFFFFE,
    );

    let report = audit(&data);
    let orphan = report
        .evidence()
        .iter()
        .find(|e| matches!(
            e,
            Evidence::OrphanSector { layer: ChainLayer::Fat, sector_id }
                if *sector_id == chain[1]
        ))
        .expect("detached tail sector must be reported as orphan");
    assert_eq!(orphan.first_location(), chain[1]);

    // A pristine orphan-only construction: append an extra sector to the file
    // whose FAT cell is EOC but that nothing references.
    let mut data2 = baseline.data.clone();
    let sector_len = baseline.sector_len as usize;
    let old_num_sectors = data2.len() as u64 / baseline.sector_len - 1;
    data2.extend(std::iter::repeat(0u8).take(sector_len));
    // The FAT cell for the new sector is currently FREE (padding); set EOC so
    // it is "used" but unreachable.
    let new_sector = old_num_sectors as u32;
    let cell = fat_cell_offset(&data2, baseline.sector_len, new_sector);
    if (cell + 4) as usize <= data2.len() {
        write_u32(&mut data2, cell, 0xFFFFFFFE);
    }
    let report2 = audit(&data2);
    assert!(
        has_finding(&report2, |e| matches!(
            e,
            Evidence::OrphanSector { layer: ChainLayer::Fat, sector_id }
                if *sector_id == new_sector
        )),
        "appended detached sector must be orphan: {:?}",
        report2.evidence()
    );
}

#[test]
fn audit_finding_mini_stream_out_of_bounds() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();

    // Locate the MiniFAT chain and read the small stream's mini chain.
    let minifat_start = read_u32(&data, 60);
    let minifat_chain =
        chain_of(&data, baseline.sector_len, minifat_start);
    assert!(!minifat_chain.is_empty(), "baseline has a MiniFAT");
    let small_mini_start = read_u32(
        &data,
        start_sector_offset(baseline.sector_len, baseline.small_entry),
    );

    // The small stream spans 2 mini sectors (100 bytes).  Corrupt the second
    // mini FAT cell to point past the mini stream's size.
    let entries_per_sector = baseline.sector_len / 4;
    let fat_sector_index = 1u64 / entries_per_sector;
    let within = 1u64 % entries_per_sector;
    let minifat_cell = (minifat_chain[fat_sector_index as usize] as u64 + 1)
        * baseline.sector_len
        + within * 4;
    write_u32(&mut data, minifat_cell, 0x0000_0100);

    let report = audit(&data);
    let oob = report
        .evidence()
        .iter()
        .find(|e| matches!(
            e,
            Evidence::OutOfBounds { layer: ChainLayer::MiniFat, .. }
        ))
        .expect("mini stream OOB must be reported");
    // The first violating location is the cell that points out.
    let context = oob.to_string();
    assert!(context.contains("MiniFAT"), "{context}");
    // The small stream still starts within bounds; the breach is at its
    // second link, distinct from FAT-layer findings.
    assert!(small_mini_start < 0x100);
    assert!(!has_finding(&report, |e| matches!(
        e,
        Evidence::OutOfBounds { layer: ChainLayer::Fat, .. }
    )));
}

#[test]
fn audit_separates_length_mismatch_from_chain_corruption() {
    let baseline = build_baseline();
    let mut data = baseline.data.clone();
    // Inflate `big`'s declared stream_len (offset 120 in the entry) without
    // touching the FAT: declared 10 sectors, chain only 2.
    let len_off = entry_field(baseline.sector_len, baseline.big_entry, 120);
    data[len_off as usize..len_off as usize + 8]
        .copy_from_slice(&(baseline.sector_len as u64 * 10).to_le_bytes());

    let report = audit(&data);
    let mismatch = report
        .evidence()
        .iter()
        .find(|e| matches!(
            e,
            Evidence::LengthMismatch { layer: ChainLayer::Fat, .. }
        ))
        .expect("declared length mismatch must be reported");
    if let Evidence::LengthMismatch { declared, actual, entry_id, what, .. } =
        mismatch
    {
        assert_eq!(*declared, baseline.sector_len * 10);
        assert_eq!(*actual, baseline.sector_len * 2);
        assert_eq!(*entry_id, Some(baseline.big_entry));
        let _ = what;
    } else {
        unreachable!();
    }
    // No other corruption class fires for a length-only edit.
    assert!(!has_finding(&report, |e| matches!(
        e,
        Evidence::Cycle { .. }
            | Evidence::OutOfBounds { .. }
            | Evidence::DoubleAllocation { .. }
            | Evidence::OrphanSector { .. }
    )));
}

#[test]
fn plan_is_bound_to_prerequisite_digest_and_rejects_changed_file() {
    let baseline = build_baseline();
    let mut corrupted = baseline.data.clone();
    let big_start = read_u32(
        &corrupted,
        start_sector_offset(baseline.sector_len, baseline.big_entry),
    );
    let chain = chain_of(&corrupted, baseline.sector_len, big_start);
    write_u32(
        &mut corrupted,
        fat_cell_offset(&corrupted, baseline.sector_len, chain[1]),
        chain[0],
    );

    let report = audit(&corrupted);
    let plan = report
        .repair_plan(Cursor::new(corrupted.clone()))
        .expect("plan on unchanged bytes");
    assert!(!plan.is_empty());

    // Preview is descriptive and never writes.
    let preview = plan.preview();
    assert!(preview.iter().any(|step| step
        .description()
        .contains("cycle")));

    // Change one byte after planning.
    let mut changed = corrupted.clone();
    changed[1000] ^= 0x01;
    let outcome = plan
        .apply(Cursor::new(changed))
        .expect("apply returns Stale, not an IO error");
    assert!(matches!(outcome, ApplyOutcome::Stale));
    // Digest fingerprints differ and are stable values.
    assert_ne!(report.digest().fingerprint(), {
        let mut other = corrupted.clone();
        other[1000] ^= 0x01;
        cfb::audit(Cursor::new(other)).unwrap().digest().fingerprint()
    });
}

#[test]
fn dry_run_never_writes_bytes() {
    let baseline = build_baseline();
    let mut corrupted = baseline.data.clone();
    let big_start = read_u32(
        &corrupted,
        start_sector_offset(baseline.sector_len, baseline.big_entry),
    );
    let chain = chain_of(&corrupted, baseline.sector_len, big_start);
    write_u32(
        &mut corrupted,
        fat_cell_offset(&corrupted, baseline.sector_len, chain[1]),
        chain[0],
    );
    let before = corrupted.clone();

    let report = audit(&corrupted);
    // Build a plan against a read-only-by-type cursor: &[u8] cannot write,
    // so the mere fact this compiles and runs proves planning writes nothing.
    let plan = report
        .repair_plan(Cursor::new(corrupted.as_slice()))
        .expect("planning needs Read+Seek only");
    let _ = plan.preview();
    assert_eq!(corrupted, before, "planning/preview must not mutate bytes");
}
