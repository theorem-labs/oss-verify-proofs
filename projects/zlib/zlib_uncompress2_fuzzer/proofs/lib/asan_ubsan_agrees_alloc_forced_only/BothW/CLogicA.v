(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState ITree Nodes Decode CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Monad CMonad.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import AProto ATsafeCore.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Notation M := Monad.M.

Section CANSEC1. Context {rc : runConstT}.
Section CTS.
Context {St : Type}.
Variable NMAX : nat.
Local Notation TS := (TS NMAX).
Local Notation TSM := (TSM NMAX (St:=St)).
Local Notation preT := (preT (St:=St)).
Local Notation postM := (postM (St:=St)).

Lemma TS_hmap : forall {R R'} (g : R -> hist -> R') (t : itree node R) h RNG A mo (Q' : postT R'),
  TS RNG A t mo (fun r RNG' A' mo' => forall h', Q' (g r h') RNG' A' mo') -> TS RNG A (hmap g t h) mo Q'.
Proof.
  intros R R' g t. induction t as [r|n k IH]; intros h RNG A mo Q' H; cbn in H |- *.
  - destruct H as [HA HQ]. split; [exact HA| apply HQ].
  - destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
    intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
    exists RNG', A'. split; [exact HF|]. split; [exact HL|]. apply IH. exact HT.
Qed.

Lemma TSM_mtag {X} (P : preT) (m : M St X) (Q : postM X) h :
  TSM P m Q -> TSM P (mtag m h) (fun ah => Q (fst ah)).
Proof.
  intros H RNG A s mo Hp. unfold mtag. apply TS_hmap. eapply TS_mono; [exact (H _ _ _ _ Hp)|].
  intros [|[x s']] RNG' A' mo' _ H1 h'; cbn in *; [exact I| exact H1].
Qed.

Definition cTSM {X} (P : preT) (mc : MC St X) (Q : postM X) : Prop :=
  forall D h, TSM P (RESX D h mc) (fun ah => Q (fst ah)).

Lemma cTSM_lift {X} (P : preT) (m : M St X) (Q : postM X) : TSM P m Q -> cTSM P (clift m) Q.
Proof. intros H D h. rewrite RESX_lift. apply TSM_mtag. exact H. Qed.

Lemma cTSM_conseq {X} (P P' : preT) (mc : MC St X) (Q Q' : postM X) :
  cTSM P mc Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) ->
  (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> cTSM P' mc Q'.
Proof. intros H HP HQ D h. eapply TSM_conseq; [apply H| exact HP|]. intros ah RNG A s mo. apply HQ. Qed.
Lemma cTSM_pre {X} (P P' : preT) (mc : MC St X) (Q : postM X) :
  cTSM P mc Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) -> cTSM P' mc Q.
Proof. intros H HP. eapply cTSM_conseq; [exact H| exact HP| auto]. Qed.
Lemma cTSM_post {X} (P : preT) (mc : MC St X) (Q Q' : postM X) :
  cTSM P mc Q -> (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> cTSM P mc Q'.
Proof. intros H HQ. eapply cTSM_conseq; [exact H| auto| exact HQ]. Qed.

Lemma cTSM_ret {X} (x : X) (P : preT) (Q : postM X) :
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo /\ Q x RNG A s mo) -> cTSM P (cmret x) Q.
Proof. intros H D h. rewrite RESX_ret. apply TSM_ret. exact H. Qed.

Lemma cTSM_ret' {X} (x : X) (P : preT) :
  (forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) -> cTSM P (cmret x) (fun _ => P).
Proof. intros HA. apply cTSM_ret. intros RNG A s mo Hp. split; [apply (HA _ _ _ _ Hp)| exact Hp]. Qed.

Lemma cTSM_bind {X Y} (P : preT) (mc : MC St X) (fc : X -> MC St Y) (Q1 : postM X) (Q : postM Y) :
  cTSM P mc Q1 -> (forall x, cTSM (fun RNG A s mo => acct_ok NMAX RNG A mo /\ Q1 x RNG A s mo) (fc x) Q) -> cTSM P (cmbind mc fc) Q.
Proof. intros H1 H2 D h. rewrite RESX_bind. eapply TSM_bind; [apply H1|]. intros ah. apply H2. Qed.

Lemma cTSM_bind' {X Y} (P : preT) (mc : MC St X) (fc : X -> MC St Y) (Q1 : postM X) (Q : postM Y) :
  cTSM P mc Q1 -> (forall x, cTSM (Q1 x) (fc x) Q) -> cTSM P (cmbind mc fc) Q.
Proof. intros Hm Hf. eapply cTSM_bind; [exact Hm|]. intros x. eapply cTSM_pre; [apply Hf|]. intros RNG A s mo [_ H]; exact H. Qed.

Lemma cTSM_seq {X Y} (P P1 : preT) (mc : MC St X) (fc : X -> MC St Y) (Q : postM Y) :
  cTSM P mc (fun _ => P1) -> (forall x, cTSM P1 (fc x) Q) -> cTSM P (cmbind mc fc) Q.
Proof. intros Hm Hf. eapply cTSM_bind'; [exact Hm| exact Hf]. Qed.

Lemma cTSM_choice {X} (P : preT) (a b : MC St X) (Q : postM X) : cTSM P a Q -> cTSM P b Q -> cTSM P (cchoice a b) Q.
Proof. intros Ha Hb D h. rewrite RESX_choice. destruct (D h); [apply Ha| apply Hb]. Qed.

Lemma cTSM_false {X} (mc : MC St X) (Q : postM X) : cTSM (fun _ _ _ _ => False) mc Q.
Proof. intros D h RNG A s mo []. Qed.

Lemma cTSM_pure {X} (P : preT) (phi : Prop) (mc : MC St X) (Q : postM X) :
  (forall RNG A s mo, P RNG A s mo -> phi) -> (phi -> cTSM P mc Q) -> cTSM P mc Q.
Proof. intros Hphi H D h. eapply TSM_pure; [exact Hphi|]. intros Hp. apply (H Hp). Qed.

Lemma cTSM_pure' {X} (phi : Prop) (Pr : preT) (mc : MC St X) (Q : postM X) :
  (phi -> cTSM Pr mc Q) -> cTSM (fun RNG A s mo => phi /\ Pr RNG A s mo) mc Q.
Proof. intros H D h RNG A s mo [Hphi Hp]. apply (H Hphi D h). exact Hp. Qed.

Lemma cTSM_pure_r {X} (phi : Prop) (Pr : preT) (mc : MC St X) (Q : postM X) :
  (phi -> cTSM Pr mc Q) -> cTSM (fun RNG A s mo => Pr RNG A s mo /\ phi) mc Q.
Proof. intros H D h RNG A s mo [Hp Hphi]. apply (H Hphi D h). exact Hp. Qed.

Lemma cTSM_exI {X T} (P : T -> preT) (mc : MC St X) (Q : postM X) :
  (forall x, cTSM (P x) mc Q) -> cTSM (fun RNG A s mo => exists x, P x RNG A s mo) mc Q.
Proof. intros H D h. apply TSM_exI. intros x. apply H. Qed.

Lemma cTSM_if' {X} (b : bool) (Pr : preT) (m1 m2 : MC St X) (Q : postM X) :
  (b = true -> cTSM Pr m1 Q) -> (b = false -> cTSM Pr m2 Q) -> cTSM Pr (if b then m1 else m2) Q.
Proof. intros H1 H2. destruct b; [apply H1| apply H2]; reflexivity. Qed.

Lemma cTSM_RES {X} (P : preT) (mc : MC St X) (Q : postM X) :
  cTSM P mc Q -> forall D h, TSM P (RES D h mc) Q.
Proof.
  intros H D h. rewrite RES_RESX. eapply TSM_bind; [apply H|]. intros ah.
  apply TSM_ret. intros RNG A s mo [HA HQ]. split; [exact HA| exact HQ].
Qed.

End CTS.
End CANSEC1.
