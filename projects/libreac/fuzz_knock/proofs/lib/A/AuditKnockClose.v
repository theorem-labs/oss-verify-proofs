(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/A closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   A/AD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: AD2o.ASAN_T_closed, AD2o.knock_asan_agrees_closed and AD2o.knock_asan_halts_closed (a Theorem Labs lane's
   lib/A/AD2o.v assembly, which closes Statements.asan_agrees / asan_halts at B := AD2l.TfibB), and the allocator
   closure at that B in lib/A/KnockAllocClose.v (a Theorem Labs lane).
   CONDITIONAL parts, kept for the record: KnockAsanTop's *_of_asan_side take ASAN_T / ASAN_UBSAN_T as premises, and
   KnockClose's *_of_parts are stated inside Section asan / asan_ubsan over the Hypotheses H_STARTUP, H_ALLOC_MALLOC,
   H_ALLOC_FREE, H_RT_MEMCPY, H_TRACES_B, H_DRIVER (and their _U twins), so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   AD2o assembly, not from these conditional parts. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require AD2o KnockAllocClose KnockAsanTop KnockClose.
Check AD2o.ASAN_T_closed.
Print Assumptions AD2o.ASAN_T_closed.
Check AD2o.knock_asan_agrees_closed.
Print Assumptions AD2o.knock_asan_agrees_closed.
Check AD2o.knock_asan_halts_closed.
Print Assumptions AD2o.knock_asan_halts_closed.
Check KnockAllocClose.knock_amalloc_closed.
Print Assumptions KnockAllocClose.knock_amalloc_closed.
Check KnockAllocClose.knock_afree_closed.
Print Assumptions KnockAllocClose.knock_afree_closed.
Check KnockAllocClose.knock_aicpy_closed.
Print Assumptions KnockAllocClose.knock_aicpy_closed.
Check KnockAsanTop.asan_agrees_of_asan_side.
Print Assumptions KnockAsanTop.asan_agrees_of_asan_side.
Check KnockAsanTop.asan_halts_of_asan_side.
Print Assumptions KnockAsanTop.asan_halts_of_asan_side.
Check KnockAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions KnockAsanTop.asan_ubsan_agrees_of_asan_side.
Check KnockAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions KnockAsanTop.asan_ubsan_halts_of_asan_side.
Check KnockClose.knock_asan_agrees_of_parts.
Print Assumptions KnockClose.knock_asan_agrees_of_parts.
Check KnockClose.knock_asan_halts_of_parts.
Print Assumptions KnockClose.knock_asan_halts_of_parts.
Check KnockClose.knock_asan_ubsan_agrees_of_parts.
Print Assumptions KnockClose.knock_asan_ubsan_agrees_of_parts.
Check KnockClose.knock_asan_ubsan_halts_of_parts.
Print Assumptions KnockClose.knock_asan_ubsan_halts_of_parts.
