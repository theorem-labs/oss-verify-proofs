(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/AU closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   AU/YD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: YD2o.ASAN_UBSAN_T_closed, YD2o.knock_asan_ubsan_agrees_closed and YD2o.knock_asan_ubsan_halts_closed
   (a Theorem Labs lane's lib/AU/YD2o.v assembly, which closes Statements.asan_ubsan_agrees / asan_ubsan_halts at
   B := YD2l.TfibB), and the allocator closure at that B in lib/AU/YKnockAllocClose.v (a Theorem Labs lane).
   CONDITIONAL parts, kept for the record: KnockAsanTop's asan_ubsan_*_of_asan_side take ASAN_UBSAN_T as a premise, and
   KnockClose's knock_asan_ubsan_*_of_parts are stated inside Section asan_ubsan over the Hypotheses H_STARTUP_U,
   H_ALLOC_MALLOC_U, H_ALLOC_FREE_U, H_RT_MEMCPY_U, H_TRACES_B_U, H_DRIVER_U, so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   YD2o assembly, not from these conditional parts. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require YD2o YKnockAllocClose.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require KnockAsanTop KnockClose.
Check YD2o.ASAN_UBSAN_T_closed.
Print Assumptions YD2o.ASAN_UBSAN_T_closed.
Check YD2o.knock_asan_ubsan_agrees_closed.
Print Assumptions YD2o.knock_asan_ubsan_agrees_closed.
Check YD2o.knock_asan_ubsan_halts_closed.
Print Assumptions YD2o.knock_asan_ubsan_halts_closed.
Check YKnockAllocClose.knock_amalloc_closed_U.
Print Assumptions YKnockAllocClose.knock_amalloc_closed_U.
Check YKnockAllocClose.knock_afree_closed_U.
Print Assumptions YKnockAllocClose.knock_afree_closed_U.
Check YKnockAllocClose.knock_aicpy_closed_U.
Print Assumptions YKnockAllocClose.knock_aicpy_closed_U.
Check KnockAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions KnockAsanTop.asan_ubsan_agrees_of_asan_side.
Check KnockAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions KnockAsanTop.asan_ubsan_halts_of_asan_side.
Check KnockClose.knock_asan_ubsan_agrees_of_parts.
Print Assumptions KnockClose.knock_asan_ubsan_agrees_of_parts.
Check KnockClose.knock_asan_ubsan_halts_of_parts.
Print Assumptions KnockClose.knock_asan_ubsan_halts_of_parts.
