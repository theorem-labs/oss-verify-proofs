(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the audit file of libreac/fuzz_knock's lib/A closing build of record (cbrec): Check + Print
   Assumptions pairs only. Each axiom printed must be on toolchain/allowed-axioms.txt; no Section kd placeholder of
   A/AD3j.v (layout_grow_kd, depot_ok_kd, as_const_g2, am_depot_mono_kd, am_alloc_depot_kd) may appear.
   CLOSED tops: AD2o.ASAN_T_closed, AD2o.knock_asan_agrees_closed and AD2o.knock_asan_halts_closed (the
   lib/A/AD2o.v assembly, which closes Statements.asan_agrees / asan_halts at B := AD2l.TfibB), and the allocator
   closure at that B in lib/A/KnockAllocClose.v.
   CONDITIONAL parts, kept for the record: KnockAsanTop's *_of_asan_side take ASAN_T / ASAN_UBSAN_T as premises, and
   KnockClose's *_of_parts are stated inside Section asan / asan_ubsan over the Hypotheses H_STARTUP, H_ALLOC_MALLOC,
   H_ALLOC_FREE, H_RT_MEMCPY, H_TRACES_B, H_DRIVER (and their _U twins), so after End they are functions of those
   premises; their Print Assumptions shows axioms only, not those premises. The closed Statements.* come from the
   AD2o assembly, not from these conditional parts. *)
(* Modified by Theorem Labs, 2026-10: taken for reac-pw/fuzz_qdisc image A from proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v
   at origin/ossv/recipes 6ebe35ba632: the same pairs for qdisc's AD2o, QdiscAllocClose, QdiscAsanTop and QdiscClose;
   qdisc's allocator closure is the one-trace text of fuzz_identity (no AD3j); names knock_* -> qdisc_*, module paths
   changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_qdisc/lib/A/AuditQdiscClose.v at 56ce9edaafc, for reac-pw/fuzz_role
   image A: the same pairs for role's AD2o, RoleAllocClose, RoleAsanTop and RoleClose, with `About` for each top (it
   lists the leading arguments: AD2o's open Section Variables role_lib_x_all and role_plain_slot_ag while their files
   have not landed, RoleAsanTop.PLAIN_SLOT_AG for the agreement statements, RoleClose's Section parts); names
   qdisc_* -> role_*, module paths changed. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/AuditRoleClose.v at fa745625e7df, for reac-pw/fuzz_rate
   image A: the same pairs for rate's AD2o, RateAllocClose, RateAsanTop and RateClose (AD2o's open Section Hypothesis
   CCSV, check_csv's contract, while its walk has not landed), and a Check that
   lib/AgreeRate.v plain_slot_ag has exactly the type RateAsanTop.PLAIN_SLOT_AG that AD2o passes it at; the Print
   Assumptions of AD2o's three closed tops are in lib/A/AuditRateCloseT.v, AuditRateCloseH.v and AuditRateCloseA.v
   (one top per file: each walks the whole closure, and the three in this one file took 2741 s); names role_* ->
   rate_*, module paths changed. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require AgreeRate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require YD2o YRateAllocClose.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require RateAsanTop RateClose.
Local Open Scope Z_scope.
Check (AgreeRate.plain_slot_ag : RateAsanTop.PLAIN_SLOT_AG).
Print Assumptions AgreeRate.plain_slot_ag.
About YD2o.ASAN_UBSAN_T_closed.
About YD2o.rate_asan_ubsan_agrees_closed.
About YD2o.rate_asan_ubsan_halts_closed.
Check YRateAllocClose.rate_amalloc_closed_U.
Print Assumptions YRateAllocClose.rate_amalloc_closed_U.
Check YRateAllocClose.rate_afree_closed_U.
Print Assumptions YRateAllocClose.rate_afree_closed_U.
Check YRateAllocClose.rate_aicpy_closed_U.
Print Assumptions YRateAllocClose.rate_aicpy_closed_U.
About RateAsanTop.asan_ubsan_agrees_of_asan_side.
Print Assumptions RateAsanTop.asan_ubsan_agrees_of_asan_side.
About RateAsanTop.asan_ubsan_halts_of_asan_side.
Print Assumptions RateAsanTop.asan_ubsan_halts_of_asan_side.
About RateClose.ASAN_UBSAN_T_of_parts.
Print Assumptions RateClose.ASAN_UBSAN_T_of_parts.
About RateClose.rate_asan_ubsan_agrees_of_parts.
Print Assumptions RateClose.rate_asan_ubsan_agrees_of_parts.
About RateClose.rate_asan_ubsan_halts_of_parts.
Print Assumptions RateClose.rate_asan_ubsan_halts_of_parts.
