(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem FP.   (* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Ed_iface.                     (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition S_ZERO : word := Z_to_bv 64 0xffffffff00000000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition flw_val (w : word) : word := nan_box (bv_extract 0 32 (le_bytes_to_word (le4 w))).

(* [comment removed for export] *)
Definition ival_round (md : rmode) (sgn half v : word) : word :=
  Z_to_bv 64 (fst (fp_fma fmt_double md (bv_unsigned sgn) (bv_unsigned half) (bv_unsigned (fcvt_d_s RNE v)))).

(* [comment removed for export] *)
Lemma ival_rebox : forall k, nan_box (low32 (ival_w k)) = ival_w k.
Proof. intros k. unfold ival_w, fcvt_s_w. rewrite low32_nan_box. reflexivity. Qed.

(* [comment removed for export] *)
Definition zr (n : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat n)).
Lemma forallb_zr : forall (f : Z -> bool) n, forallb f (zr n) = true -> forall k, 0 <= k < n -> f k = true.
Proof.
  intros f n H k Hk. rewrite forallb_forall in H. apply H. unfold zr. apply in_map_iff. exists (Z.to_nat k). split; [lia|].
  apply in_seq. lia.
Qed.

Definition ival_chk (k : Z) : bool :=
  negb (flt_s (flw_val (ival_w k)) S_ZERO)
  && Z.eqb (bv_unsigned (fcvt_w_d RTZ (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))))) k
  && flt_d D_GUARD_LO (ival_round RNE D_ONE D_HALF (flw_val (ival_w k)))
  && flt_d (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))) D_GUARD_HI.

Lemma ival_chk_all : forallb ival_chk (zr 20001) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ival_sign : forall k, 0 <= k <= 20000 -> flt_s (flw_val (ival_w k)) S_ZERO = false.
Proof.
  intros k Hk. pose proof (forallb_zr ival_chk 20001 ival_chk_all k ltac:(lia)) as H. unfold ival_chk in H.
  rewrite !andb_true_iff in H. destruct H as (((H & _) & _) & _). destruct (flt_s (flw_val (ival_w k)) S_ZERO); [discriminate | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma ival_exact : forall k, 0 <= k <= 20000 -> fcvt_w_d RTZ (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))) = Z_to_bv 64 k.
Proof.
  intros k Hk. pose proof (forallb_zr ival_chk 20001 ival_chk_all k ltac:(lia)) as H. unfold ival_chk in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & H) & _) & _). apply Z.eqb_eq in H. apply bv_eq. rewrite H. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. rewrite Z.mod_small; [reflexivity | lia].
Qed.

(* [comment removed for export] *)
Lemma ival_guard_lo : forall k, 0 <= k <= 20000 -> flt_d D_GUARD_LO (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))) = true.
Proof.
  intros k Hk. pose proof (forallb_zr ival_chk 20001 ival_chk_all k ltac:(lia)) as H. unfold ival_chk in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & _) & H) & _). exact H.
Qed.
Lemma ival_guard_hi : forall k, 0 <= k <= 20000 -> flt_d (ival_round RNE D_ONE D_HALF (flw_val (ival_w k))) D_GUARD_HI = true.
Proof.
  intros k Hk. pose proof (forallb_zr ival_chk 20001 ival_chk_all k ltac:(lia)) as H. unfold ival_chk in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & _) & _) & H). exact H.
Qed.

(* [comment removed for export] *)
Definition ival_chk_neg (k : Z) : bool :=
  flt_s (flw_val (ival_w k)) S_ZERO
  && Z.eqb (bv_unsigned (fcvt_w_d RTZ (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))))) (bv_unsigned (Z_to_bv 64 k))
  && flt_d D_GUARD_LO (ival_round RNE D_MONE D_HALF (flw_val (ival_w k)))
  && flt_d (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))) D_GUARD_HI.
Lemma ival_chk_m1 : ival_chk_neg (-1) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ival_sign_neg : forall k, -1 <= k < 0 -> flt_s (flw_val (ival_w k)) S_ZERO = true.
Proof.
  intros k Hk. replace k with (-1) by lia. pose proof ival_chk_m1 as H. unfold ival_chk_neg in H.
  rewrite !andb_true_iff in H. destruct H as (((H & _) & _) & _). exact H.
Qed.
Lemma ival_exact_neg : forall k, -1 <= k < 0 -> fcvt_w_d RTZ (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))) = Z_to_bv 64 k.
Proof.
  intros k Hk. replace k with (-1) by lia. pose proof ival_chk_m1 as H. unfold ival_chk_neg in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & H) & _) & _). apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.
Lemma ival_guard_lo_neg : forall k, -1 <= k < 0 -> flt_d D_GUARD_LO (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))) = true.
Proof.
  intros k Hk. replace k with (-1) by lia. pose proof ival_chk_m1 as H. unfold ival_chk_neg in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & _) & H) & _). exact H.
Qed.
Lemma ival_guard_hi_neg : forall k, -1 <= k < 0 -> flt_d (ival_round RNE D_MONE D_HALF (flw_val (ival_w k))) D_GUARD_HI = true.
Proof.
  intros k Hk. replace k with (-1) by lia. pose proof ival_chk_m1 as H. unfold ival_chk_neg in H.
  rewrite !andb_true_iff in H. destruct H as (((_ & _) & _) & H). exact H.
Qed.
