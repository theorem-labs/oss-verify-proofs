(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlParser.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section S.
Variable HK : RawAlloc.PState -> list MallocBlocks.block -> (word -> option byte) -> Model -> Prop.

Ltac lw_small := rewrite ysx32_small by lia.
(* [comment removed for export] *)
Ltac kill1 K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; intros K.
Lemma land3_of_mod4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
(* [comment removed for export] *)
Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite ybv_swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma ycb_null_spec : ycb_null_stmt.
Proof.
  unfold ycb_null_stmt. intros until m. intros _ MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold RY_CB_NULL, wz. step. step. unfold ycb_null_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_boolean_spec : ycb_boolean_stmt.
Proof.
  unfold ycb_boolean_stmt. intros until m. intros _ MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold RY_CB_BOOLEAN, wz. step. step. unfold ycb_boolean_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_string_spec : ycb_string_stmt.
Proof.
  unfold ycb_string_stmt. intros until m. intros _ MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  unfold RY_CB_STRING, wz. step. step. unfold ycb_string_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_number_spec : ycb_number_stmt.
Proof.
  unfold ycb_number_stmt. intros until m. intros _ MI A2 L.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  subst a2. unfold RY_CB_NUMBER, wz.
  step. if_cases K0; zify_cond K0.
  1:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. unfold ycb_number_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_start_map_spec : ycb_start_map_stmt.
Proof.
  unfold ycb_start_map_stmt. intros until m. intros [CXP CXA] CR OV MI A0.
  pose proof (munch_refl [(CX + 4, CX + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC. pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn in CB.
  pose proof (land3_of_mod4 _ CXA) as L3.
  subst a0. unfold RY_CB_START_MAP, wz.
  step. if_cases K0; zify_cond K0. 1:{ kill1 K0. lia. }
  step. step. step. if_cases K1; zify_cond K1. 1:{ kill1 K1. lia. }
  step. lw_small. step. rewrite (unsigned_lit (cx_objectLevel cx)) by lia. rewrite swrap32_small by lia.
  step. if_cases K2; zify_cond K2.
  1:{ exfalso. revert K2. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. step.
  unfold ycb_start_map_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.

Lemma ycb_map_key_spec : ycb_map_key_stmt.
Proof.
  unfold ycb_map_key_stmt. intros until m. intros [CXP CXA] CR OV MI A0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC. pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn in CB.
  pose proof (land3_of_mod4 _ CXA) as L3.
  subst a0. unfold RY_CB_MAP_KEY, wz.
  step. if_cases K0; zify_cond K0. 1:{ kill1 K0. lia. }
  step. step. if_cases K1; zify_cond K1. 1:{ kill1 K1. lia. }
  step. lw_small. step. if_cases K2; zify_cond K2.
  1:{ exfalso. revert K2. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. unfold ycb_map_key_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_end_map_spec : ycb_end_map_stmt.
Proof.
  unfold ycb_end_map_stmt. intros until m. intros [CXP CXA] CR OV MI A0.
  pose proof (munch_refl [(CX + 4, CX + 8)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC. pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn in CB.
  pose proof (land3_of_mod4 _ CXA) as L3.
  subst a0. unfold RY_CB_END_MAP, wz.
  step. if_cases K0; zify_cond K0. 1:{ kill1 K0. lia. }
  step. step. step. if_cases K1; zify_cond K1. 1:{ kill1 K1. lia. }
  step. lw_small. step. if_cases K2; zify_cond K2.
  1:{ exfalso. revert K2. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. step. step.
  unfold ycb_end_map_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    replace (cx_objectLevel cx + -1) with (cx_objectLevel cx - 1) by lia.
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.

Lemma ycb_start_array_spec : ycb_start_array_stmt.
Proof.
  unfold ycb_start_array_stmt. intros until m. intros [CXP CXA] CR OV MI A0.
  pose proof (munch_refl [(CX, CX + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC. pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn in CB.
  pose proof (land3_of_mod4 _ CXA) as L3.
  subst a0. unfold RY_CB_START_ARRAY, wz.
  step. if_cases K0; zify_cond K0. 1:{ kill1 K0. lia. }
  step. step. step. if_cases K1; zify_cond K1. 1:{ kill1 K1. lia. }
  step. lw_small. step. rewrite (unsigned_lit (cx_arrayLevel cx)) by lia. rewrite swrap32_small by lia.
  step. if_cases K2; zify_cond K2.
  1:{ exfalso. revert K2. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. step.
  unfold ycb_start_array_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.

Lemma ycb_end_array_spec : ycb_end_array_stmt.
Proof.
  unfold ycb_end_array_stmt. intros until m. intros [CXP CXA] CR OV MI A0.
  pose proof (munch_refl [(CX, CX + 4)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC. pose proof (rw_cells_bound _ _ _ _ CC) as CB. cbn in CB.
  pose proof (land3_of_mod4 _ CXA) as L3.
  subst a0. unfold RY_CB_END_ARRAY, wz.
  step. if_cases K0; zify_cond K0. 1:{ kill1 K0. lia. }
  step. step. step. if_cases K1; zify_cond K1. 1:{ kill1 K1. lia. }
  step. lw_small. step. if_cases K2; zify_cond K2.
  1:{ exfalso. revert K2. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. step. step.
  unfold ycb_end_array_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    replace (cx_arrayLevel cx + -1) with (cx_arrayLevel cx - 1) by lia.
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.
End S.
End RC__1.
