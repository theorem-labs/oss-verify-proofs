(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the image-B twin of lib/A/AuditRoleClose.v of this library (whose Modified-by lines
   trace it to proofs/libreac/fuzz_knock/lib/A/AuditKnockClose.v), for reac-pw/fuzz_role's asan-ubsan image: the same
   pairs for lib/AU/YD2o.v, lib/AU/YRoleAllocClose.v and the closed program contract lib/AU/RPgLibX.v role_lib_x_all;
   module names A.Axyz -> AU.Yxyz, names role_* -> role_*_U / role_asan_ubsan_*. *)
(* The audit file of fuzz_role's image-B close: `About` for every closed and conditional top (it lists the leading
   arguments: none for YD2o's closed tops, its shape equation and driver slot, and RPgLibX's closed program contract
   role_lib_x_all beyond its statement's own LEAF / AFREE / AMALLOC premises; RoleAsanTop.PLAIN_SLOT_AG for the
   conditional agreement statements; RoleClose's Section parts for the *_of_parts), `Check` of the three allocator
   parts, and ONE `Print Assumptions`, of role_asan_ubsan_tops, the conjunction of the two closed statement tops
   role_asan_ubsan_halts_closed and role_asan_ubsan_agrees_closed (one traversal of the shared closure; everything
   else this file names lies in that closure). Each axiom printed must be on toolchain/allowed-axioms.txt. *)
From OSSVerify.reac_pw.fuzz_role Require Statements.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require YD2o YRoleAllocClose RPgLibX.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RoleAsanTop RoleClose.
About AU.RPgLibX.role_lib_x_all.
About YD2o.role_shape_leaf.
About YD2o.role_driver_TfibB_U.
About YD2o.ASAN_UBSAN_T_closed.
About YD2o.role_asan_ubsan_halts_closed.
About YD2o.role_asan_ubsan_agrees_closed.
Check YRoleAllocClose.role_amalloc_closed_U.
Check YRoleAllocClose.role_afree_closed_U.
Check YRoleAllocClose.role_aicpy_closed_U.
About RoleAsanTop.asan_ubsan_agrees_of_asan_side.
About RoleAsanTop.asan_ubsan_halts_of_asan_side.
About RoleClose.ASAN_UBSAN_T_of_parts.
About RoleClose.role_asan_ubsan_agrees_of_parts.
About RoleClose.role_asan_ubsan_halts_of_parts.
Definition role_asan_ubsan_tops : OSSVerify.reac_pw.fuzz_role.Statements.asan_ubsan_halts /\
  OSSVerify.reac_pw.fuzz_role.Statements.asan_ubsan_agrees :=
  conj YD2o.role_asan_ubsan_halts_closed YD2o.role_asan_ubsan_agrees_closed.
Print Assumptions role_asan_ubsan_tops.
