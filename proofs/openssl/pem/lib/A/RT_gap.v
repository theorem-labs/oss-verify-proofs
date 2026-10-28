(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells ImageA.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel A_RegConsts A_Gsh.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem RT_state RT_rep RT_gshacc RT_iclifts_pem Fz_gochk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GAP_FILE : Z := 0xa18c0.
Definition GAP_FILE_SZ : Z := 21.
Definition B_GOBJ (b s : Z) : Prop := A_GOBJ b s \/ (b = GAP_FILE /\ s = GAP_FILE_SZ).

Lemma gobj_lift : forall b s, A_GOBJ b s -> B_GOBJ b s.
Proof. intros b s H. left. exact H. Qed.
Lemma gap_gobj : B_GOBJ GAP_FILE GAP_FILE_SZ.
Proof. right. split; reflexivity. Qed.
Lemma gobj_lift_exact : forall l : list (Z * Z), Forall (fun p => A_GOBJ (fst p) (snd p)) l -> Forall (fun p => B_GOBJ (fst p) (snd p)) l.
Proof. intros l H. eapply Forall_impl; [| exact H]. intros p Hp. exact (gobj_lift _ _ Hp). Qed.
Lemma gobj_lift_cover : forall l : list (Z * Z),
  Forall (fun p => exists b sz, A_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) l ->
  Forall (fun p => exists b sz, B_GOBJ b sz /\ b <= fst p /\ fst p + snd p <= b + sz) l.
Proof. intros l H. eapply Forall_impl; [| exact H]. intros p (b & sz & G & H1 & H2). exists b, sz. split; [exact (gobj_lift _ _ G)| split; assumption]. Qed.

Lemma gap_tab : A_GOBJ GAP_FILE GAP_FILE_SZ.
Proof. exact (go_exact1_sound (GAP_FILE, GAP_FILE_SZ) ltac:(vm_compute; reflexivity)). Qed.

Theorem rta_acc_global_B : RT_iface_pem.acc_global_fact RTA B_GOBJ.
Proof.
  intros Σ m b s a n HA [G | [-> ->] ] H1 H2; [exact (rta_acc_global Σ m b s a n HA G H1 H2)|].
  exact (rta_acc_global Σ m _ _ a n HA gap_tab H1 H2).
Qed.

Theorem rta_gsh_byte_B : RT_iface_pem.gsh_byte_fact RTA B_GOBJ.
Proof.
  intros Σ m b s g HA [G | [-> ->] ] H1 H2 G8; [exact (rta_gsh_byte Σ m b s g HA G H1 H2 G8)|].
  exact (rta_gsh_byte Σ m _ _ g HA gap_tab H1 H2 G8).
Qed.

Theorem rta_art_facts_pem_B : art_facts_pem RTA B_GOBJ.
Proof. exact (mkAFP RTA B_GOBJ rta_acc_global_B rta_gsh_byte_B rta_live_mem rta_live_hi rta_frame_mem). Qed.
