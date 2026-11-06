(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/A closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   A/AD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: AD2o.ASAN_T_closed, AD2o.knock_asan_agrees_closed and AD2o.knock_asan_halts_closed (h-small-a11's
   lib/A/AD2o.v assembly, which closes Statements.asan_agrees / asan_halts at B := AD2l.TfibB), and the allocator
   closure at that B in lib/A/KnockAllocClose.v (c-libc-fmt).
   CONDITIONAL parts, kept for the record: KnockAsanTop's *_of_asan_side take ASAN_T / ASAN_UBSAN_T as premises, and
   KnockClose's *_of_parts are stated inside Section asan / asan_ubsan over the Hypotheses H_STARTUP, H_ALLOC_MALLOC,
   H_ALLOC_FREE, H_RT_MEMCPY, H_TRACES_B, H_DRIVER (and their _U twins), so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   AD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v
   at origin/ossv/recipes 6ebe35ba632: the same pairs for qdisc's AD2o, QdiscAllocClose, QdiscAsanTop and QdiscClose;
   qdisc's allocator closure is the one-trace text of fuzz_identity (no AD3j); names knock_* -> qdisc_*, module paths
   changed (h-small-a3). *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.A Require AD2o QdiscAllocClose QdiscAsanTop QdiscClose.
Check AD2o.ASAN_T_closed.
Print Assumptions AD2o.ASAN_T_closed.
Check AD2o.qdisc_asan_agrees_closed.
Print Assumptions AD2o.qdisc_asan_agrees_closed.
Check AD2o.qdisc_asan_halts_closed.
Print Assumptions AD2o.qdisc_asan_halts_closed.
Check QdiscAllocClose.qdisc_amalloc_closed.
Print Assumptions QdiscAllocClose.qdisc_amalloc_closed.
Check QdiscAllocClose.qdisc_afree_closed.
Print Assumptions QdiscAllocClose.qdisc_afree_closed.
Check QdiscAllocClose.qdisc_aicpy_closed.
Print Assumptions QdiscAllocClose.qdisc_aicpy_closed.
Check QdiscAsanTop.asan_agrees_of_asan_side.
Print Assumptions QdiscAsanTop.asan_agrees_of_asan_side.
Check QdiscAsanTop.asan_halts_of_asan_side.
Print Assumptions QdiscAsanTop.asan_halts_of_asan_side.
Check QdiscAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions QdiscAsanTop.asan_ubsan_agrees_of_asan_side.
Check QdiscAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions QdiscAsanTop.asan_ubsan_halts_of_asan_side.
Check QdiscClose.qdisc_asan_agrees_of_parts.
Print Assumptions QdiscClose.qdisc_asan_agrees_of_parts.
Check QdiscClose.qdisc_asan_halts_of_parts.
Print Assumptions QdiscClose.qdisc_asan_halts_of_parts.
Check QdiscClose.qdisc_asan_ubsan_agrees_of_parts.
Print Assumptions QdiscClose.qdisc_asan_ubsan_agrees_of_parts.
Check QdiscClose.qdisc_asan_ubsan_halts_of_parts.
Print Assumptions QdiscClose.qdisc_asan_ubsan_halts_of_parts.
