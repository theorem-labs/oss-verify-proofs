(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChLib FxChNull FxChFix FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require AcMrg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift OSSVerify.Proofs.fast_float.from_chars.lib.AAC.AcMrg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma tmap_tset : forall {A B} (f : A -> B) k v t, tmap f (tset k v t) = tset k (f v) (tmap f t).
Proof.
  intros A B f k. induction k as [k IH|k IH|]; intros v [|l w r]; cbn [tset tmap]; try reflexivity;
    rewrite ?IH; try reflexivity.
  all: cbn [tmap]; rewrite ?IH; reflexivity.
Qed.
Lemma rset_shift : forall n R k l, tmap (lshift n) (rset R k l) = rset (tmap (lshift n) R) k (lshift n l).
Proof. intros n R k l. unfold rset. destruct k; [apply tmap_tset | apply tmap_tset | reflexivity]. Qed.

Lemma cmp_succ : forall m, Pos.compare m (Pos.succ m) = Lt.
Proof. intros m. apply Pos.compare_lt_iff. lia. Qed.
Lemma NA_shift : forall n m, NA (n + m) = lshift n (NA m).
Proof.
  intros n m. unfold NA, lshift, ladd, lscale, lvar. cbn [l_c l_t tscale].
  change (w64 (65536 * 1)) with 65536. change (w64 (4096 * 1)) with 4096. cbn [Z.eqb].
  cbn [tadd]. rewrite !cmp_succ. cbn [tadd tshift List.map fst snd]. f_equal. rewrite Pos.add_succ_r. reflexivity.
Qed.
Lemma NP_shift : forall n m, NP (n + m) = lshift n (NP m).
Proof.
  intros n m. unfold NP, laddc, lshift, ladd, lscale, lvar. cbn [l_c l_t tscale].
  change (w64 (8192 * 1)) with 8192. change (w64 (512 * 1)) with 512. cbn [Z.eqb].
  cbn [tadd]. rewrite !cmp_succ. cbn [tadd tshift List.map fst snd]. f_equal. rewrite Pos.add_succ_r. reflexivity.
Qed.

Lemma rshift_RGz : forall n b z k, rshift n (RGz b z k TEmpty) = RGz (lshift n b) z k TEmpty.
Proof. intros n b z k. reflexivity. Qed.

Lemma null_post_mrg : forall n L S nZ vis piece,
  null_post (mrg (sst_shift n L) S) nZ vis piece = mrg (sst_shift n (null_post L nZ vis piece)) S.
Proof.
  intros n L S nZ vis piece. unfold null_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
  rewrite rset_shift, <- (NA_shift n (s_next L)). f_equal.
  - rewrite map_app, app_assoc. f_equal. f_equal. unfold null_rgs.
    destruct vis, piece; cbn [app List.map]; rewrite ?rshift_RGz, ?(NA_shift n (s_next L)), ?(NP_shift n (s_next L)); reflexivity.
  - rewrite map_app, app_assoc. f_equal. f_equal. unfold null_facts. cbn [List.map fshift].
    rewrite <- (NA_shift n (s_next L)).
    assert (E1 : lshift n (laddc (NA (s_next L)) (- SH_HI)) = laddc (NA (n + s_next L)) (- SH_HI)) by (rewrite NA_shift; reflexivity).
    rewrite E1. f_equal. f_equal. f_equal. f_equal. unfold lshift, lvar. cbn. rewrite Pos.add_succ_r. reflexivity.
  - rewrite !Pos.add_succ_r. reflexivity.
Qed.

Lemma fix_post_mrg : forall n L S a, fix_post (mrg (sst_shift n L) S) (lshift n a) = mrg (sst_shift n (fix_post L a)) S.
Proof. intros n L S a. unfold fix_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite rset_shift. reflexivity. Qed.
Lemma add_post_mrg : forall n L S a z pc,
  add_post (mrg (sst_shift n L) S) (lshift n a) z (option_map (lshift n) pc) = mrg (sst_shift n (add_post L a z pc)) S.
Proof.
  intros n L S a z pc. unfold add_post, mrg, sst_shift. cbn [s_pc s_regs s_rgs s_facts s_next s_resv].
  rewrite map_app, app_assoc. f_equal. unfold add_rgs. destruct pc; reflexivity.
Qed.
Lemma rget_mrg : forall n L S k, rget (s_regs (mrg (sst_shift n L) S)) k = lshift n (rget (s_regs L) k).
Proof. intros n L S k. unfold mrg, sst_shift. cbn [s_regs]. apply rget_shift. Qed.
