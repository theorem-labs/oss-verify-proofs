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
   image A: `About` for every closed and conditional top (it lists the leading arguments: none for AD2o's closed tops and
   its closed program contract role_lib_x_all_closed, RoleAsanTop.PLAIN_SLOT_AG for the conditional agreement statements,
   RoleClose's Section parts) and ONE `Print Assumptions`, of role_asan_tops, the conjunction of the two closed
   statement tops role_asan_halts_closed and role_asan_agrees_closed (one traversal of the shared closure; each Print
   Assumptions re-traverses it, about 10 minutes on the lane VM); everything the file printed before (ASAN_T_closed,
   role_lib_x_all_closed, RoleAllocClose, the conditional tops) lies in that closure; names qdisc_* -> role_*, module
   paths changed. *)
From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require AD2o RoleAllocClose RoleAsanTop RoleClose.
About AD2o.role_lib_x_all_closed.
About AD2o.ASAN_T_closed.
About AD2o.role_asan_halts_closed.
About AD2o.role_asan_agrees_closed.
Check RoleAllocClose.role_amalloc_closed.
Check RoleAllocClose.role_afree_closed.
Check RoleAllocClose.role_aicpy_closed.
About RoleAsanTop.asan_agrees_of_asan_side.
About RoleAsanTop.asan_halts_of_asan_side.
About RoleAsanTop.asan_ubsan_agrees_of_asan_side.
About RoleAsanTop.asan_ubsan_halts_of_asan_side.
About RoleClose.ASAN_T_of_parts.
About RoleClose.ASAN_UBSAN_T_of_parts.
About RoleClose.role_asan_agrees_of_parts.
About RoleClose.role_asan_halts_of_parts.
About RoleClose.role_asan_ubsan_agrees_of_parts.
About RoleClose.role_asan_ubsan_halts_of_parts.
Definition role_asan_tops : OSSVerify.reac_pw.fuzz_role.Statements.asan_halts /\
  OSSVerify.reac_pw.fuzz_role.Statements.asan_agrees :=
  conj AD2o.role_asan_halts_closed AD2o.role_asan_agrees_closed.
Print Assumptions role_asan_tops.
