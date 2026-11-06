# provenance/evidence/cmpkit-audit: fresh-reviewer audit of the memchr-A, memchr-B and strlen-A acceptances (cmpkit 4bbd3a74be89)

AUDIT.md is the reviewer's report, copied by mk_audit_slice.py (not shipped: its table holds the replaced text) with lane names, a local scratch path and a working-branch name replaced; REWRITES.tsv lists each replacement by count, the sha256 of the replaced text and the text written. Verdict: ACCEPT for all three slices, 0 rows refused, 0 REAL differences; the chain-only claim matches the tables. Its two settleable not-certified rows are settled by measurement in each slice's tables/cmpkit-4bbd3a74be89/settled2.tsv (memchr-A, memchr-B) or tables/settled2.tsv (strlen-A).

| file | kind | role |
|---|---|---|
| `AUDIT.md` | record | the audit: method, findings D1-D7, the full differing-target-list check, every row checked |
| `REWRITES.tsv` | table | the name / path replacements |
