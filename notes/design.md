# Design notes
- audit entry: OpenOptions::audit_with(Read+Seek) -> AuditReport
- repair: RepairPlan::{check_with(dry run), apply_with} ; digest gate
- internal shared: audit.rs reuses Header::read_from + constants; audit re-runs over in-memory image
