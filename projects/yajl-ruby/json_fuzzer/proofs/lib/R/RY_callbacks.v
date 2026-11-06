(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMalloc_iface RYajlRep RYajl_iface.
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

Lemma ycb_null_spec : ycb_null_stmt.
Proof.
  unfold ycb_null_stmt. intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RY_CB_NULL, wz. step. step. unfold ycb_null_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_boolean_spec : ycb_boolean_stmt.
Proof.
  unfold ycb_boolean_stmt. intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RY_CB_BOOLEAN, wz. step. step. unfold ycb_boolean_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_string_spec : ycb_string_stmt.
Proof.
  unfold ycb_string_stmt. intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold RY_CB_STRING, wz. step. step. unfold ycb_string_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_number_spec : ycb_number_stmt.
Proof.
  unfold ycb_number_stmt. intros until m. intros MI A2 L.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  subst a2. unfold RY_CB_NUMBER, wz.
  step. if_cases K0; zify_cond K0.
  1:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  step. step. unfold ycb_number_rpost. finish. all: reflexivity.
Qed.

Lemma ycb_start_map_spec : ycb_start_map_stmt.
Proof.
  unfold ycb_start_map_stmt. intros until m. intros CR OV MI A0.
  pose proof (munch_refl [(CX + 4, CX + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC.
  subst a0. unfold RY_CB_START_MAP, wz.
  step. step. lw_small. step. step. step. step.
  unfold ycb_start_map_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.

Lemma ycb_map_key_spec : ycb_map_key_stmt.
Proof.
  unfold ycb_map_key_stmt. intros until m. intros CR OV MI A0.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC.
  subst a0. unfold RY_CB_MAP_KEY, wz.
  step. lw_small. step. if_cases K0; zify_cond K0.
  1:{ exfalso. revert K0. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
      all: try (unfold bv_half_modulus, bv_modulus; cbn -[Z.lt Z.le Z.opp Z.add Z.sub Z.mul]; lia). }
  step. step. unfold ycb_map_key_rpost. finish. all: reflexivity.
Qed.
Lemma ycb_end_map_spec : ycb_end_map_stmt.
Proof.
  unfold ycb_end_map_stmt. intros until m. intros CR OV MI A0.
  pose proof (munch_refl [(CX + 4, CX + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC.
  subst a0. unfold RY_CB_END_MAP, wz.
  step. step. lw_small. step. if_cases K0; zify_cond K0.
  1:{ exfalso. revert K0. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
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
  unfold ycb_start_array_stmt. intros until m. intros CR OV MI A0.
  pose proof (munch_refl [(CX, CX + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC.
  subst a0. unfold RY_CB_START_ARRAY, wz.
  step. step. lw_small. step. step. step. step.
  unfold ycb_start_array_rpost. finish.
  - reflexivity.
  - unfold ctx_rep, ctx_cells. cbn [cx_arrayLevel cx_objectLevel]. split; [|lia].
    match goal with H : rw_cells _ _ CX _ |- _ => exact H end.
Qed.

Lemma ycb_end_array_spec : ycb_end_array_stmt.
Proof.
  unfold ycb_end_array_stmt. intros until m. intros CR OV MI A0.
  pose proof (munch_refl [(CX, CX + 4)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  destruct CR as (CC & R1 & R2). unfold ctx_cells in CC.
  subst a0. unfold RY_CB_END_ARRAY, wz.
  step. step. lw_small. step. if_cases K0; zify_cond K0.
  1:{ exfalso. revert K0. rewrite ?bv_signed_small; unfold wz; rewrite ?unsigned_lit by lia; try lia.
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
