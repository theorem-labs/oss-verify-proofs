(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import W2Lib LeptNuma.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition D_ONE : Z := 0x3ff0000000000000.     (* [comment removed for export] *)
Definition D_MONE : Z := 0xbff0000000000000.    (* [comment removed for export] *)
Definition D_HALF : Z := 0x3fe0000000000000.    (* [comment removed for export] *)
Definition D_LO : Z := 0xc1e0000000200000.      (* [comment removed for export] *)
Definition D_HI : Z := 0x41e0000000000000.      (* [comment removed for export] *)
Definition F_ONE : Z := 0x3f800000.             (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ngi_neg (c : Z) : bool := fst (fp_lt fmt_single c 0).

Definition ngi_ok (v : Z) : bool :=
  let c := f32i v in (0 <=? c) && (c <? 2 ^ 32) && negb (ngi_neg c).

Fixpoint all_upto (f : Z -> bool) (n : nat) (x : Z) : bool :=
  match n with O => true | S k => f x && all_upto f k (x + 1) end.

Lemma all_upto_spec : forall f n x, all_upto f n x = true -> forall v, x <= v < x + Z.of_nat n -> f v = true.
Proof.
  intros f n. induction n as [|k IH]; intros x H v Hv; [cbn in Hv; lia|].
  cbn [all_upto] in H. apply andb_true_iff in H. destruct H as [H0 H1].
  destruct (Z.eq_dec v x) as [->|Ne]; [exact H0|]. apply (IH (x + 1) H1). lia.
Qed.

Lemma ngi_all : all_upto ngi_ok (Z.to_nat 20000) 0 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma ngi_table : forall v, 0 <= v <= 19999 -> 0 <= f32i v < 2 ^ 32 /\ ngi_neg (f32i v) = false.
Proof.
  intros v Hv. pose proof (all_upto_spec ngi_ok _ 0 ngi_all v ltac:(rewrite Z2Nat.id; lia)) as H.
  unfold ngi_ok in H. cbv zeta in H.
  repeat (apply andb_true_iff in H; destruct H as [H ?]).
  match goal with H : (0 <=? _) = true |- _ => apply Z.leb_le in H end.
  match goal with H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
  match goal with H : negb ?b = true |- _ => destruct b eqn:EN; [discriminate H|] end.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma f32u_one : fst (fp_of_int fmt_single RNE false 32 1) = F_ONE.
Proof. vm_cast_no_check (eq_refl F_ONE). Qed.
Lemma delta_not_neg : fst (fp_lt fmt_single F_ONE 0) = false.
Proof. vm_cast_no_check (eq_refl false). Qed.

(* [comment removed for export] *)
Lemma fpv_cell_load : forall z, 0 <= z < 2 ^ 32 -> bv_extract 0 32 (le_bytes_to_word (Z_to_le_bytes 4 z)) = Z_to_bv 32 z.
Proof.
  intros z Hz. unfold le_bytes_to_word. rewrite (lez4 z Hz).
  apply bv_eq. rewrite bv_extract_unsigned, !Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64. change (Z.of_N 32) with 32.
  rewrite (Z.mod_small z (2 ^ 64)) by lia. rewrite (Z.mod_small z (2 ^ 64)) by lia. reflexivity.
Qed.
