(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel A_RegConsts A_Gsh.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem RT_gshacc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition go_ok_d (d : RGM.desc) : bool :=
  (RGM.d_beg d + RGM.d_size d <=? SEGTOP_A) && ((RGM.d_beg d + RGM.d_size d <=? RGM.c_tab A_RGC) || (RGM.c_tabend A_RGC <=? RGM.d_beg d)).
Definition go_exact1 (p : Z * Z) : bool :=
  existsb (fun d => (RGM.d_beg d =? fst p) && (RGM.d_size d =? snd p) && go_ok_d d) A_GTAB.
Definition go_cover1 (p : Z * Z) : bool :=
  existsb (fun d => (RGM.d_beg d <=? fst p) && (fst p + snd p <=? RGM.d_beg d + RGM.d_size d) && go_ok_d d) A_GTAB.

Lemma go_ok_d_spec : forall d, go_ok_d d = true ->
  RGM.d_beg d + RGM.d_size d <= SEGTOP_A /\ (RGM.d_beg d + RGM.d_size d <= RGM.c_tab A_RGC \/ RGM.c_tabend A_RGC <= RGM.d_beg d).
Proof.
  intros d H. unfold go_ok_d in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. split; [exact H1|].
  apply orb_prop in H2 as [H2|H2]; apply Z.leb_le in H2; [left | right]; exact H2.
Qed.

Lemma go_exact1_sound : forall p, go_exact1 p = true -> A_GOBJ (fst p) (snd p).
Proof.
  intros p H. unfold go_exact1 in H. apply existsb_exists in H as (d & Hin & H).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
  destruct (go_ok_d_spec d H3) as [K1 K2]. exists d. rewrite <- H1, <- H2. exact (conj Hin (conj eq_refl (conj eq_refl (conj K1 K2)))).
Qed.

Lemma go_cover1_sound : forall p, go_cover1 p = true -> exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz.
Proof.
  intros p H. unfold go_cover1 in H. apply existsb_exists in H as (d & Hin & H).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (go_ok_d_spec d H3) as [K1 K2]. exists (RGM.d_beg d), (RGM.d_size d).
  split; [exists d; exact (conj Hin (conj eq_refl (conj eq_refl (conj K1 K2)))) | exact (conj H1 H2)].
Qed.

Theorem go_exact_sound : forall l, forallb go_exact1 l = true -> Forall (fun p => A_GOBJ (fst p) (snd p)) l.
Proof. intros l H. apply Forall_forall. intros p Hp. exact (go_exact1_sound p (proj1 (forallb_forall _ _) H p Hp)). Qed.

Theorem go_cover_sound : forall l, forallb go_cover1 l = true ->
  Forall (fun p => exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) l.
Proof. intros l H. apply Forall_forall. intros p Hp. exact (go_cover1_sound p (proj1 (forallb_forall _ _) H p Hp)). Qed.

(* [comment removed for export] *)
Theorem go_both_sound : forall le lc, forallb go_exact1 le && forallb go_cover1 lc = true ->
  Forall (fun p => A_GOBJ (fst p) (snd p)) le /\ Forall (fun p => exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) lc.
Proof. intros le lc H. apply andb_prop in H as [H1 H2]. exact (conj (go_exact_sound le H1) (go_cover_sound lc H2)). Qed.
