(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto MonadF AU_kit AM_model.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Fixpoint may_ret {R} (t : itree node R) (r : R) : Prop :=
  match t with
  | Ret r' => r' = r
  | Vis _ k => exists x, may_ret (k x) r
  end.

Lemma may_ret_bind : forall {A B} (t : itree node A) (f : A -> itree node B) r,
  may_ret (bind node t f) r -> exists a, may_ret t a /\ may_ret (f a) r.
Proof.
  intros A B t. induction t as [a|n k IH]; intros f r H; cbn in H.
  - exists a. split; [reflexivity| exact H].
  - destruct H as [x Hx]. destruct (IH x f r Hx) as (a & H1 & H2). exists a. split; [| exact H2]. cbn. exists x. exact H1.
Qed.

Lemma may_ret_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) b,
  may_ret (ebind t f) (Ok b) -> exists a, may_ret t (Ok a) /\ may_ret (f a) (Ok b).
Proof.
  intros A B t f b H. unfold ebind in H. apply may_ret_bind in H as ([|a] & H1 & H2).
  - cbn in H2. discriminate.
  - exists a. split; assumption.
Qed.

(* [comment removed for export] *)
Notation MA := (Monad.M APS).
Definition cl_stable {X} (c : MA X) : Prop :=
  forall s x s', may_ret (c s) (Ok (x, s')) -> aps_cl s' = aps_cl s.

Lemma cl_stable_ret : forall {X} (x : X), cl_stable (mret x).
Proof. intros X x s y s' H. cbn in H. injection H. intros -> _. reflexivity. Qed.
Lemma cl_stable_unr : forall {X}, cl_stable (munr (A:=X)).
Proof. intros X s y s' H. cbn in H. discriminate. Qed.
Lemma cl_stable_get : cl_stable mget.
Proof. intros s y s' H. cbn in H. injection H. intros -> _. reflexivity. Qed.
Lemma cl_stable_upd_m : forall st, cl_stable (mupd (aset_m st)).
Proof. intros st s y s' H. cbn in H. injection H. intros <-. reflexivity. Qed.
Lemma cl_stable_bind : forall {X Y} (c : MA X) (f : X -> MA Y),
  cl_stable c -> (forall x, cl_stable (f x)) -> cl_stable (mbind c f).
Proof.
  intros X Y c f Hc Hf s y s' H. unfold mbind in H. apply may_ret_ebind in H as ([x s1] & H1 & H2). cbn [fst snd] in H2.
  rewrite (Hf x s1 y s' H2). exact (Hc s x s1 H1).
Qed.
Lemma cl_stable_alift : forall {R} (t : AM R), cl_stable (alift t).
Proof.
  intros R t s y s' H. unfold alift in H. apply may_ret_ebind in H as (a & _ & H2). cbn in H2. injection H2. intros <- _. reflexivity.
Qed.

Lemma cl_stable_amalloc : forall n, cl_stable (amalloc_M n).
Proof.
  intros n. unfold amalloc_M. apply cl_stable_bind; [apply cl_stable_get|]. intros s0.
  apply cl_stable_bind; [apply cl_stable_alift|]. intros x.
  apply cl_stable_bind; [apply cl_stable_upd_m|]. intros []. apply cl_stable_ret.
Qed.
Lemma cl_stable_afree : forall p, cl_stable (afree_M p).
Proof.
  intros p. unfold afree_M. apply cl_stable_bind; [apply cl_stable_get|]. intros s0.
  apply cl_stable_bind; [apply cl_stable_alift|]. intros x. apply cl_stable_upd_m.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma cl_stable_opnew : forall n, cl_stable (opnewA n).
Proof.
  intros n. unfold opnewA, HarnessM.opnew. apply cl_stable_bind; [apply cl_stable_amalloc|]. intros [p|]; [apply cl_stable_ret|].
  apply cl_stable_bind; [apply cl_stable_unr|]. intros [].
Qed.
Lemma cl_stable_opdelete : forall p, cl_stable (opdeleteA p).
Proof. intros p. unfold opdeleteA, HarnessM.opdelete. apply cl_stable_afree. Qed.
Lemma cl_stable_odelete : forall b, cl_stable (odeleteA b).
Proof. intros [p|]; [apply cl_stable_opdelete| apply cl_stable_ret]. Qed.
Lemma cl_stable_vctor : forall n, cl_stable (vctorA n).
Proof.
  intros n. unfold vctorA, vctor_model. destruct (n =? 0); [apply cl_stable_ret|].
  apply cl_stable_bind; [apply cl_stable_opnew|]. intros p. apply cl_stable_ret.
Qed.
Lemma cl_stable_assign : forall n b, cl_stable (assignA n b).
Proof.
  intros n b. unfold assignA, assign_model. destruct (ERRMSG_LEN <=? n); [apply cl_stable_ret|].
  apply cl_stable_bind; [apply cl_stable_odelete|]. intros []. apply cl_stable_bind; [apply cl_stable_opnew|]. intros p. apply cl_stable_ret.
Qed.
Lemma cl_stable_lam : forall data, cl_stable (lamA data).
Proof.
  intros data. rewrite lamA_unfold. apply cl_stable_bind; [apply cl_stable_vctor|]. intros b.
  destruct (unclosed data); [| apply cl_stable_ret].
  apply cl_stable_bind; [apply cl_stable_opnew|]. intros t.
  apply cl_stable_bind; [apply cl_stable_assign|]. intros b'.
  apply cl_stable_bind; [apply cl_stable_opdelete|]. intros []. apply cl_stable_ret.
Qed.
Lemma cl_stable_minify_call : forall data, cl_stable (minify_callA data).
Proof.
  intros data. unfold minify_callA, HarnessM.minify_call.
  apply cl_stable_bind.
  { destruct (Z.of_nat (length data) =? 0); [apply cl_stable_ret|]. apply cl_stable_bind; [apply cl_stable_opnew|]. intros p. apply cl_stable_ret. }
  intros b. destruct (unclosed data); [| apply cl_stable_odelete].
  apply cl_stable_bind; [apply cl_stable_opnew|]. intros t.
  apply cl_stable_bind.
  { destruct (ERRMSG_LEN <=? Z.of_nat (length data)); [apply cl_stable_ret|].
    apply cl_stable_bind; [apply cl_stable_odelete|]. intros []. apply cl_stable_bind; [apply cl_stable_opnew|]. intros p. apply cl_stable_ret. }
  intros b'. apply cl_stable_bind; [apply cl_stable_opdelete|]. intros []. apply cl_stable_odelete.
Qed.

(* [comment removed for export] *)
Lemma implF_mono_ret : forall {R} RNG (t : itree node R) (Q Q' : R -> footprint -> machine_state -> Prop) ms,
  implS asegs RNG t Q ms -> (forall r RNG' ms', may_ret t r -> Q r RNG' ms' -> Q' r RNG' ms') -> implS asegs RNG t Q' ms.
Proof.
  intros R RNG t; revert RNG. induction t as [r|n k IH]; intros RNG Q Q' ms H HQ; cbn in *.
  - eapply evtF_mono; [exact H|]. cbn. intros ms' H'. apply HQ; [reflexivity| exact H'].
  - eapply evtF_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp RNG' HF. eapply IH; [eapply Hk; exact HF|]. intros r RNG2 ms2 HM HQ2. apply HQ; [| exact HQ2]. exists rsp. exact HM.
Qed.

Lemma implMA_cl : forall {X} RNG (c : MA X) s (Q : X -> APS -> footprint -> machine_state -> Prop) ms,
  cl_stable c -> implMA RNG c s Q ms ->
  implMA RNG c s (fun x s' RNG' ms' => Q x s' RNG' ms' /\ aps_cl s' = aps_cl s) ms.
Proof.
  intros X RNG c s Q ms HC H. unfold implMA in *. eapply implF_mono_ret; [exact H|].
  intros [|[x s']] RNG' ms' HM HQ; cbn in *; [exact HQ|]. split; [exact HQ|]. exact (HC s x s' HM).
Qed.
End CANSEC1.
