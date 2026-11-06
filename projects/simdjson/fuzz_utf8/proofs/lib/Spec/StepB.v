(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition nf_node (n : node) : Prop :=
  match n with NMmap _ _ _ _ | NMprotect _ _ _ => True | _ => False end.

(* [comment removed for export] *)
Definition NF (n : node) (mo : Model) : Prop :=
  match n with
  | NMmap _ _ _ _ | NMprotect _ _ _ =>
      forall rsp mo' evs, nstep n mo rsp mo' evs -> errno_of (eff_ret rsp) = None
  | _ => True
  end.

Lemma NF_other : forall n mo, ~ nf_node n -> NF n mo.
Proof. intros n mo H. destruct n; cbn in *; auto; exfalso; exact (H I). Qed.

Definition nstepB (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs
  /\ (vm_live_bytes (m_vmmaps mo') <= B \/ vm_live_bytes (m_vmmaps mo') <= vm_live_bytes (m_vmmaps mo))
  /\ NF n mo.

Lemma nstepB_nstep : forall B n mo rsp mo' evs, nstepB B n mo rsp mo' evs -> nstep n mo rsp mo' evs.
Proof. intros B n mo rsp mo' evs [H _]. exact H. Qed.

Lemma nstepB_NF : forall B n mo rsp mo' evs, nstepB B n mo rsp mo' evs -> NF n mo.
Proof. intros B n mo rsp mo' evs (_ & _ & H). exact H. Qed.

(* [comment removed for export] *)
Lemma nstepB_no_errno : forall B n mo rsp mo' evs,
  nf_node n -> nstepB B n mo rsp mo' evs -> errno_of (eff_ret rsp) = None.
Proof.
  intros B n mo rsp mo' evs Hn (Hst & _ & HNF). destruct n; cbn in Hn; try contradiction; exact (HNF _ _ _ Hst).
Qed.

(* [comment removed for export] *)
Lemma nstepB_same : forall B n mo rsp mo' evs,
  ~ nf_node n -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> nstepB B n mo rsp mo' evs.
Proof. intros B n mo rsp mo' evs Hn H E. split; [exact H|]. split; [right; rewrite E; lia| apply NF_other; exact Hn]. Qed.

(* [comment removed for export] *)
Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  end.

(* [comment removed for export] *)
Fixpoint tnf {R} (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => NF n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> tnf (k rsp) mo'
  end.

Lemma tnf_bind : forall {A R} (t : itree node A) (f : A -> itree node R) mo,
  tnf t mo -> (forall a mo', tnf (f a) mo') -> tnf (ITree.bind node t f) mo.
Proof.
  intros A R t. induction t as [r|n k IH]; intros f mo H Hf; cbn in *; [apply Hf|].
  destruct H as [Hn Hk]. split; [exact Hn|]. intros rsp mo' evs Hst. apply IH; [apply (Hk _ _ _ Hst)| exact Hf].
Qed.

Lemma texit_nstepB_of_tlive : forall {R} B (t : itree node R) mo tr,
  tlive B t mo -> tnf t mo -> texit nstep nexit t mo tr -> texit (nstepB B) nexit t mo tr.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo tr Hl Hn Hx; [destruct Hx|].
  cbn [texit] in *. destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & Hst & Hx & ->)].
  - left. exists code, mo'. auto.
  - right. destruct (Hl _ _ _ Hst) as [Hb Hl']. cbn in Hn. destruct Hn as [HNF Hn'].
    exists rsp, mo', evs, tr'. split; [split; [exact Hst| split; [left; exact Hb| exact HNF]]|].
    split; [apply IH; [assumption| apply (Hn' _ _ _ Hst)| assumption]| reflexivity].
Qed.

Lemma texit_nstep_of_nstepB : forall {R} B (t : itree node R) mo tr,
  texit (nstepB B) nexit t mo tr -> texit nstep nexit t mo tr.
Proof.
  intros R B t. induction t as [r|n k IH]; intros mo tr Hx; [destruct Hx|].
  cbn [texit] in *. destruct Hx as [(code & mo' & Hex & ->)|(rsp & mo' & evs & tr' & [Hst _] & Hx & ->)].
  - left. exists code, mo'. auto.
  - right. exists rsp, mo', evs, tr'. split; [exact Hst|]. split; [apply IH; assumption| reflexivity].
Qed.

Lemma tpath_nstep_of_nstepB : forall {R} B (t : itree node R) mo tr r mo',
  tpath (nstepB B) t mo tr r mo' -> tpath nstep t mo tr r mo'.
Proof.
  intros R B t. induction t as [x|n k IH]; intros mo tr r mo' Hp; cbn [tpath] in *; [exact Hp|].
  destruct Hp as (rsp & mo1 & evs & tr' & [Hst _] & Hp & ->). exists rsp, mo1, evs, tr'. split; [exact Hst|]. split; [apply IH; exact Hp| reflexivity].
Qed.
