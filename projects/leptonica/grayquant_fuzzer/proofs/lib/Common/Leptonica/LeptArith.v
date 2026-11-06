(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition dval (d : Z) : Prop := d = 1 \/ d = 2 \/ d = 4 \/ d = 8 \/ d = 16 \/ d = 24 \/ d = 32.
Definition wpl_of (w d : Z) : Z := (w * d + 31) / 32.
Definition spp_of (d : Z) : Z := if ((d =? 24) || (d =? 32))%bool then 3 else 1.

(* [comment removed for export] *)
Lemma depth_test_ok : forall d, dval d ->
  c_eq (v_andi (v_srl (Z_to_bv 64 4311810326) (Z_to_bv 64 d)) 1) (Z_to_bv 64 0) = false.
Proof. intros d [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity. Qed.

Lemma depth_test_bad : forall d, 0 <= d <= 32 -> ~ dval d ->
  c_eq (v_andi (v_srl (Z_to_bv 64 4311810326) (Z_to_bv 64 d)) 1) (Z_to_bv 64 0) = true.
Proof.
  intros d Hd ND. unfold dval in ND.
  assert (C : d = 0 \/ d = 3 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ d = 15 \/
              d = 17 \/ d = 18 \/ d = 19 \/ d = 20 \/ d = 21 \/ d = 22 \/ d = 23 \/ d = 25 \/ d = 26 \/ d = 27 \/ d = 28 \/
              d = 29 \/ d = 30 \/ d = 31) by lia.
  repeat (destruct C as [->|C]; [vm_compute; reflexivity|]). subst; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma spp_test : forall d, dval d ->
  c_eq (v_andi (v_addiw (Z_to_bv 64 d) (-24)) (-9)) (Z_to_bv 64 0) = ((d =? 24) || (d =? 32))%bool.
Proof. intros d [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity. Qed.

Lemma spp_of_range : forall d, 1 <= spp_of d <= 3.
Proof. intros d. unfold spp_of. destruct ((d =? 24) || (d =? 32))%bool; lia. Qed.

(* [comment removed for export] *)
Lemma cdepth_test_ok : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8) ->
  c_eq (v_andi (v_srl (Z_to_bv 64 278) (Z_to_bv 64 d)) 1) (Z_to_bv 64 0) = false.
Proof. intros d [->|[->|[->| ->]]]; vm_compute; reflexivity. Qed.

Lemma sllw_1 : forall d, (d = 1 \/ d = 2 \/ d = 4 \/ d = 8) -> v_sllw (Z_to_bv 64 1) (Z_to_bv 64 d) = Z_to_bv 64 (2 ^ d).
Proof. intros d [->|[->|[->| ->]]]; apply bv_eq; vm_compute; reflexivity. Qed.

Lemma zbv_srli : forall a k, 0 <= a < 2 ^ 64 -> 0 <= k -> v_srli (Z_to_bv 64 a) k = Z_to_bv 64 (a / 2 ^ k).
Proof. intros a k Ha Hk. unfold v_srli. rewrite u_Z2bv by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma dval_dec : forall d, {dval d} + {~ dval d}.
Proof.
  intros d. unfold dval.
  destruct (Z.eq_dec d 1) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 2) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 4) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 8) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 16) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 24) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  destruct (Z.eq_dec d 32) as [->|?]; [left; repeat (first [left; reflexivity | right]); reflexivity|].
  right. lia.
Qed.

Lemma dval_range : forall d, dval d -> 1 <= d <= 32.
Proof. intros d; unfold dval; lia. Qed.

Lemma wpl_of_range : forall w d, 1 <= w <= 1000000 -> dval d -> 1 <= wpl_of w d <= w.
Proof.
  intros w d Hw Hd. pose proof (dval_range d Hd). unfold wpl_of.
  split; [apply Z.div_le_lower_bound; nia |].
  assert ((w * d + 31) / 32 < w + 1) by (apply Z.div_lt_upper_bound; nia). lia.
Qed.

Lemma zneq_w : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

(* [comment removed for export] *)
Ltac fixv v tac :=
  lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => replace x with v by (symmetry; tac) end.

(* [comment removed for export] *)
Section Fence.
Context {fx : FPState}.
Lemma step_fence : forall segs regs pc mem rom w a b c d e,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Fence a b c d e, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst regs (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w a b c d e Hf He Hd. step_pipeline Hf He Hd. rewrite b_npc4. reflexivity. Qed.
End Fence.
Ltac stepfence F D := chain_step; [reflexivity | exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F eq_refl D) | step_simpl].
