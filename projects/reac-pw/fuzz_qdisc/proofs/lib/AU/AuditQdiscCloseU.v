(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/AU closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   AU/YD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: YD2o.ASAN_UBSAN_T_closed, YD2o.knock_asan_ubsan_agrees_closed and YD2o.knock_asan_ubsan_halts_closed
   (the lib/AU/YD2o.v assembly, which closes Statements.asan_ubsan_agrees / asan_ubsan_halts at B := YD2l.TfibB), and
   the allocator closure at that B in lib/AU/YKnockAllocClose.v.
   CONDITIONAL parts, kept for the record: KnockAsanTop's asan_ubsan_*_of_asan_side take ASAN_UBSAN_T as a premise, and
   KnockClose's knock_asan_ubsan_*_of_parts are stated inside Section asan_ubsan over the Hypotheses H_STARTUP_U,
   H_ALLOC_MALLOC_U, H_ALLOC_FREE_U, H_RT_MEMCPY_U, H_TRACES_B_U, H_DRIVER_U, so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   YD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image B from proofs/libreac/fuzz_knock/lib/AU/
   AuditKnockCloseU.v at origin/ossv/recipes 88154566652, in the form of this library's lib/A/AuditQdiscClose.v: the same
   pairs for qdisc's lib/AU/YD2o.v and lib/AU/YQdiscAllocClose.v and the asan_ubsan parts of lib/A/QdiscAsanTop.v and
   lib/A/QdiscClose.v. qdisc's allocator closure is the one-trace text (no YD3j), and QdiscClose's asan_ubsan Section
   also takes image B's trace tables (Tfib_universe_U, Tfib_universe_ok_U, Tfib_drv_traces_U, Tfib_universe_drv_U) as
   Section arguments, which YD2o passes from lib/AU/YCej.v and YCejTfib.v; YD2o.qdisc_driver_TfibB_U (H_DRIVER_U at
   YD2l.TfibB) is audited too. Names knock_* -> qdisc_*, module paths changed. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require YD2o YQdiscAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require QdiscAsanTop QdiscClose.
Check YD2o.ASAN_UBSAN_T_closed.
Print Assumptions YD2o.ASAN_UBSAN_T_closed.
Check YD2o.qdisc_asan_ubsan_agrees_closed.
Print Assumptions YD2o.qdisc_asan_ubsan_agrees_closed.
Check YD2o.qdisc_asan_ubsan_halts_closed.
Print Assumptions YD2o.qdisc_asan_ubsan_halts_closed.
Check YD2o.qdisc_driver_TfibB_U.
Print Assumptions YD2o.qdisc_driver_TfibB_U.
Check YQdiscAllocClose.qdisc_amalloc_closed_U.
Print Assumptions YQdiscAllocClose.qdisc_amalloc_closed_U.
Check YQdiscAllocClose.qdisc_afree_closed_U.
Print Assumptions YQdiscAllocClose.qdisc_afree_closed_U.
Check YQdiscAllocClose.qdisc_aicpy_closed_U.
Print Assumptions YQdiscAllocClose.qdisc_aicpy_closed_U.
Check QdiscAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions QdiscAsanTop.asan_ubsan_agrees_of_asan_side.
Check QdiscAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions QdiscAsanTop.asan_ubsan_halts_of_asan_side.
Check QdiscClose.qdisc_asan_ubsan_agrees_of_parts.
Print Assumptions QdiscClose.qdisc_asan_ubsan_agrees_of_parts.
Check QdiscClose.qdisc_asan_ubsan_halts_of_parts.
Print Assumptions QdiscClose.qdisc_asan_ubsan_halts_of_parts.
