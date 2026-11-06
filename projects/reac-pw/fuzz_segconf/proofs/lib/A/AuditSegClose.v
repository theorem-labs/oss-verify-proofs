(* reac-pw/fuzz_segconf, image A: the audit of the two DELIVERED closed theorems only (the image-A owner's decision of
   2026-10-30 17:5xZ): each command walks its theorem's whole closure. No sub-closure is audited.
   Proves no function (kind: audit). *)
From OSSVerify.reac_pw.fuzz_segconf Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require SegClose.

Check (SegClose.seg_asan_halts_closed : Statements.asan_halts).
Check (SegClose.seg_asan_agrees_closed : Statements.asan_agrees).
Print Assumptions SegClose.seg_asan_halts_closed.
Print Assumptions SegClose.seg_asan_agrees_closed.
