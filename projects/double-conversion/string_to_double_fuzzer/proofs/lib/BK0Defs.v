(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages BothPlanImages BothTableL AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanMainLib AsanShape AsanMainDefs BothMainDefs BothMain MainItabBoth PlanFormsBoth BK0HS_jc BK0HS_jt BK0HS_jt2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition K0_C_W : class := [(QLook,4,4); (QFlen,6,65535); (QRoom,1,64512)].
Definition K0_HT_big : list (nat * (nat * acs)) := [(70%nat, (3%nat, HS_jt))].
Definition K0_HT_quick : list (nat * (nat * acs)) := [(72%nat, (3%nat, HS_jt2))].
Definition K0_HT_mc : list (nat * (nat * acs)) := [(72%nat, (3%nat, HS_jt2))].
Definition K0_ST_a05889 : acs := (mcase_lo (mcase_hi (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) (EVar 14) 7936).
Definition K0_ST_a00001 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) (EVar 14) 7).
Definition K0_ST_a00008 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) (EVar 14) 7).
Definition K0_ST_a00009 : acs := (mcase_lo (mcase_hi (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) (EVar 14) 16).
Definition K0_ST_a00017 : acs := (mcase_hi (mcase_hi (mcase_lo (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 8) (EVar 14) 16).
Definition K0_ST_a00049 : acs := (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) (EVar 14) 64).
Definition K0_ST_a00065 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) (EVar 14) 64).
Definition K0_ST_a00097 : acs := (mcase_lo (mcase_hi (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) (EVar 14) 128).
Definition K0_ST_a00129 : acs := (mcase_hi (mcase_hi (mcase_hi (mcase_lo (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 48) (EVar 14) 96) (EVar 14) 128).
Definition K0_ST_a00161 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) (EVar 14) 192).
Definition K0_ST_a00193 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) (EVar 14) 192).
Definition K0_ST_a00225 : acs := (mcase_lo (mcase_hi (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) (EVar 14) 256).
Definition K0_ST_a00257 : acs := (mcase_hi (mcase_hi (mcase_lo (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 224) (EVar 14) 256).
Definition K0_ST_a00289 : acs := (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) (EVar 14) 320).
Definition K0_ST_a00321 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) (EVar 14) 320).
Definition K0_ST_a00353 : acs := (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) (EVar 14) 384).
Definition K0_ST_a00385 : acs := (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_lo HS_jc (EVar 14) 416) (EVar 14) 160) (EVar 14) 288) (EVar 14) 352) (EVar 14) 384).
Definition K0_ST_a00417 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 448).
Definition K0_ST_a00449 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 448).
Definition K0_ST_a00641 : acs := (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 896) (EVar 14) 888).
Definition K0_ST_a00889 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 896) (EVar 14) 888).
Definition K0_ST_a00897 : acs := (mcase_hi (mcase_hi (mcase_lo (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 640) (EVar 14) 896).
Definition K0_ST_a01409 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 1920) (EVar 14) 1912).
Definition K0_ST_a01913 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 1920) (EVar 14) 1912).
Definition K0_ST_a01921 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 1920).
Definition K0_ST_a02945 : acs := (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 3968) (EVar 14) 3960).
Definition K0_ST_a03961 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 3968) (EVar 14) 3960).
Definition K0_ST_a03969 : acs := (mcase_hi (mcase_hi (mcase_hi (mcase_lo (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 1408) (EVar 14) 2944) (EVar 14) 3968).
Definition K0_ST_a04096 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) (EVar 14) 4096).
Definition K0_ST_a04097 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) (EVar 14) 4096).
Definition K0_ST_a07937 : acs := (mcase_hi (mcase_hi (mcase_lo (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 5888) (EVar 14) 7936).
Definition K0_ST_a12033 : acs := (mcase_lo (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 16128) (EVar 14) 16120).
Definition K0_ST_a16121 : acs := (mcase_hi (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 16128) (EVar 14) 16120).
Definition K0_ST_a16129 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 16128).
Definition K0_ST_a24065 : acs := (mcase_lo (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 32248).
Definition K0_ST_a32249 : acs := (mcase_hi (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 32248).
Definition K0_ST_a32257 : acs := (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 48128).
Definition K0_ST_a48129 : acs := (mcase_lo (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 48128) (EVar 14) 64504).
Definition K0_ST_a64505 : acs := (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi (mcase_hi HS_jc (EVar 14) 416) (EVar 14) 4095) (EVar 14) 12032) (EVar 14) 24064) (EVar 14) 32256) (EVar 14) 48128) (EVar 14) 64504).
