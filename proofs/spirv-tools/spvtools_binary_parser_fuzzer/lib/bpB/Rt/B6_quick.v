(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst B6_tac B6_rip.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma hull_words : forall d k, 0 <= d -> 1 <= k <= 64 ->
  sh (hull_lo d) = 8 * (sh d / 8) /\
  sh (hull_hi (d + k)) = 8 * (sh (d + k - 1) / 8) + 8 /\
  (sh (d + k - 1) / 8 = sh d / 8 \/ sh (d + k - 1) / 8 = sh d / 8 + 1) /\
  8 * (sh d / 8) <= sh d /\ sh d <= sh (d + k - 1) /\ sh (d + k - 1) < 8 * (sh (d + k - 1) / 8) + 8.
Proof.
  intros d k Hd Hk. unfold sh, hull_lo, hull_hi. rewrite ASHADOW_BASE_val.
  repeat split; Z.div_mod_to_equations; nia.
Qed.

Lemma rw_cells_CB_length : forall mm A k bs, rw_cells asegs mm A [CB k bs] -> length bs = k.
Proof. intros mm A k bs [[[H _] _] _]. exact H. Qed.

Section QRead.
  Variables (mm : word -> option byte) (q1 : Z) (qj : list byte).
  Hypothesis QA : u8arr asegs mm (8 * q1) qj.
  Lemma q_read : forall x, 8 * q1 <= x < 8 * q1 + Z.of_nat (length qj) ->
    ov_read_bytes asegs mm (wa x) 1 = Some [nth (Z.to_nat (x - 8 * q1)) qj (b8 0)].
  Proof.
    intros x Hx. eapply (u8arr_read asegs mm (8 * q1) qj (x - 8 * q1)); [exact QA | | lia | f_equal; lia].
    apply nth_error_nth'. lia.
  Qed.
End QRead.

Lemma hull_chunk : forall mm (d k : Z), 0 <= d -> 1 <= k <= 64 -> d + k + 8 <= 2^47 ->
  stk asegs mm (sh (hull_lo d)) (sh (hull_hi (d + k))) ->
  exists qj, rw_cells asegs mm (8 * (sh d / 8)) [CB (length qj) qj]
    /\ 8 * (sh (d + k - 1) / 8) + 8 = 8 * (sh d / 8) + Z.of_nat (length qj)
    /\ ((sh (d + k - 1) / 8 = sh d / 8 /\ length qj = 8%nat) \/ (sh (d + k - 1) / 8 = sh d / 8 + 1 /\ length qj = 16%nat)).
Proof.
  intros mm d k Hd Hk Htop SV.
  destruct (hull_words d k Hd Hk) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3). rewrite HLO, HHI in SV.
  pose proof (sh_range_app d ltac:(unfold AAPP_HI; lia)) as SR1. rewrite ASHADOW_BASE_val in SR1.
  destruct HQ2 as [E|E]; rewrite E in SV |- *.
  - destruct (stk_carve asegs mm _ _ 8 SV ltac:(lia)) as [_ [qj QW]].
    replace (8 * (sh d / 8) + 8 - Z.of_nat 8) with (8 * (sh d / 8)) in QW by lia.
    pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| left; split; reflexivity].
  - destruct (stk_carve asegs mm _ _ 16 SV ltac:(lia)) as [_ [qj QW]].
    replace (8 * (sh d / 8 + 1) + 8 - Z.of_nat 16) with (8 * (sh d / 8)) in QW by lia.
    pose proof (rw_cells_CB_length _ _ _ _ QW) as L. exists qj. rewrite L. split; [exact QW|]. split; [lia| right; split; reflexivity].
Qed.

Lemma ACONST_layout_flag : forall mm, ACONST mm ->
  rw_cells asegs mm 1596424 [C8 (Z_to_bv 64 1645849)] /\ rw_cells asegs mm 1645848 [C1 (b8 1); C1 (b8 1)].
Proof.
  intros mm ACx.
  change 1596424 with AGOT_RINTRIN. change 1645849 with ARINTRIN_CELL. change 1645848 with AINITED_CELL.
  split; (eapply ACONST_cell; [exact ACx|]; cbn; clear; tauto).
Qed.
