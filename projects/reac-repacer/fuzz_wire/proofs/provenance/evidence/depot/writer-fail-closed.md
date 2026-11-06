# The two writers of our own lines: output clean, tracked, fail-closed on their inputs

emit_col.py (writes A/AB05.v and A/AB1m.v; sha256 5c27368758a6... (0d3ce8de66c8 before a comment-only change)) and own_line_names.py (the post-step of the knock
run's record-name rename, writes the two rewritten comment lines of A/AD3a.v and A/AD3b.v; sha256 c5df37a0727b...).
(1) Output: AB05.v carries no lane / worker name, working branch or host path (the binscan of record v8 over it: 0
hits); the two lines own_line_names.py writes name the record by its commit (`commit f529bfe14c7`). The detector of both scripts passes the binscan of record v8 (0 hits). (2) Tracked: both
are committed beside this file (evidence/depot/emit_col.py, evidence/depot/own_line_names.py), at the commit that
carries this record. (3) Fail closed: neither takes an option that adds text; emit_col.py copies the donor's header
lines and plan body, own_line_names.py writes rewritten lines. Each now REFUSES lane / worker / branch / host text in
what it copies or writes, and writes nothing unless every file passes:
- emit_col.py, clean inputs (the pinned plan and AB1m): rc 0, AB05.v byte-equal to the committed file. Planted: the same
  plan with a worker name (`for <worker>`, one of the stream's worker names) put into its copied notice line: rc 1, `emit_col: REFUSED AB05: copied text carries
  lane / branch / host text at input line(s) 4 (<worker>); nothing written` (the name it found), no output directory.
- own_line_names.py, clean input (A/AD3a.v and A/AD3b.v as at 88b42b3e7e49): rc 0, both files byte-equal to the
  committed ones. Planted: A/AD3a.v:135 with `(for <worker>)` (the same worker name) added to our line: rc 1, `own_line_names: REFUSED
  A/AD3a.v:135: the rewritten line still carries '<worker>'; nothing written` (the name it found), both files unchanged.
