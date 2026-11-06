(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad MSafe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tsil {R : Type} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => nsafe n mo
      /\ (forall code mo', ~ nexit n mo code mo')
      /\ (forall rsp mo' evs, nstep n mo rsp mo' evs -> evs = [] /\ tsil (k rsp) mo' P)
  end.

Lemma tsil_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
  tsil t mo P -> (forall r mo', P r mo' -> P' r mo') -> tsil t mo P'.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P P' H HP; cbn in *.
  - apply HP. exact H.
  - destruct H as (Hsafe & Hnx & Hk). split; [exact Hsafe|]. split; [exact Hnx|].
    intros rsp mo' evs Hst. split; [exact (proj1 (Hk rsp mo' evs Hst))|].
    eapply IH; [exact (proj2 (Hk rsp mo' evs Hst)) | exact HP].
Qed.

Lemma tsil_twf : forall {R} (t : itree node R) mo P, tsil t mo P -> twf t mo P.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P H; cbn in *; [exact H|].
  destruct H as (Hsafe & _ & Hk). split; [exact Hsafe|]. intros rsp mo' evs Hst. apply IH. exact (proj2 (Hk _ _ _ Hst)).
Qed.

(* [comment removed for export] *)
Definition kind_mm (n : node) : Prop :=
  match n with
  | NBrk _ | NMmap _ _ _ _ | NMunmap _ _ | NMprotect _ _ _ | NMremap _ _ _ _ => True
  | _ => False
  end.

Lemma kind_mm_noexit : forall n mo code mo', kind_mm n -> ~ nexit n mo code mo'.
Proof. intros n mo code mo' Hk Hx. destruct n; cbn in Hk, Hx; tauto. Qed.

Lemma kind_mm_evs : forall n mo rsp mo' evs, kind_mm n -> nstep n mo rsp mo' evs -> evs = [].
Proof. intros n mo rsp mo' evs Hk Hst. destruct n; cbn in Hk; try contradiction; cbn in Hst; tauto. Qed.

(* [comment removed for export] *)
Fixpoint tmm {R : Type} (t : itree node R) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => kind_mm n /\ forall rsp, tmm (k rsp)
  end.

Theorem twf_tsil : forall {R} (t : itree node R) mo P, twf t mo P -> tmm t -> tsil t mo P.
Proof.
  intros R t; induction t as [r | n k IH]; intros mo P H Hm; cbn in *; [exact H|].
  destruct H as [Hsafe Hk]. destruct Hm as [Hn Hmk]. split; [exact Hsafe|]. split.
  - intros code mo'. apply kind_mm_noexit. exact Hn.
  - intros rsp mo' evs Hst. split; [exact (kind_mm_evs _ _ _ _ _ Hn Hst)|]. apply IH; [exact (Hk _ _ _ Hst)| apply Hmk].
Qed.

Lemma tmm_bind : forall {A B} (t : itree node A) (f : A -> itree node B),
  tmm t -> (forall a, tmm (f a)) -> tmm (ITree.bind node t f).
Proof.
  intros A B t; induction t as [r | n k IH]; intros f Ht Hf; cbn in *; [apply Hf|].
  destruct Ht as [Hn Hk]. split; [exact Hn|]. intros rsp. apply IH; [apply Hk| exact Hf].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TMM.
Context {St : Type}.
Local Notation MS := (Monad.M St).

Lemma tmm_mret : forall {A} (a : A) (s : St), tmm (mret a s).
Proof. intros. exact I. Qed.
Lemma tmm_munr : forall {A} (s : St), tmm (munr (A:=A) s).
Proof. intros. exact I. Qed.
Lemma tmm_mget : forall (s : St), tmm (mget s).
Proof. intros. exact I. Qed.
Lemma tmm_mput : forall (s s' : St), tmm (mput s' s).
Proof. intros. exact I. Qed.
Lemma tmm_mupd : forall f (s : St), tmm (mupd f s).
Proof. intros. exact I. Qed.
Lemma tmm_mbind : forall {A B} (m : MS A) (f : A -> MS B) (s : St),
  tmm (m s) -> (forall a s', tmm (f a s')) -> tmm (mbind m f s).
Proof.
  intros A B m f s Hm Hf. unfold mbind, ebind. apply tmm_bind; [exact Hm|]. intros [|[a s']]; [exact I| apply Hf].
Qed.
Lemma tmm_msys : forall {A} n (dec : resp -> option A) (s : St), kind_mm n -> tmm (msys n dec s).
Proof. intros A n dec s Hn. unfold msys, enode. cbn. split; [exact Hn|]. intros rsp. destruct (dec rsp); exact I. Qed.
Lemma tmm_mif : forall {A} (b : bool) (m1 m2 : MS A) (s : St), tmm (m1 s) -> tmm (m2 s) -> tmm ((if b then m1 else m2) s).
Proof. intros A b m1 m2 s H1 H2. destruct b; assumption. Qed.

(* [comment removed for export] *)
Lemma mspec_tsil : forall {A} (P : assn St) (m : MS A) (Q : A -> assn St) s mo,
  mspec P m Q -> P s mo -> tmm (m s) ->
  tsil (m s) mo (fun p mo' => match p with Unr => False | Ok x => Q (fst x) (snd x) mo' end).
Proof. intros A P m Q s mo Hm HP Ht. apply twf_tsil; [exact (Hm s mo HP)| exact Ht]. Qed.

End TMM.
