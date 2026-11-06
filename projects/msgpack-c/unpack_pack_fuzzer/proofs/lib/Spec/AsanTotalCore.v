(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
Unset Nia Cache. Unset Nra Cache.

Unset Lia Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section Core.
Variable atop : Z.
Variable step2 : node -> Model -> resp -> Model -> list event -> Prop.

Variable aok : aev -> Model -> Prop.
Variable apost : aev -> Model -> Z -> Model -> Prop.

Definition aev_node (e : aev) : option (node * (resp -> option Z)) :=
  match e with
  | AMmap a l p f => Some (NMmap a l p f, adec_mmap atop l p)
  | AMunmap a l => Some (NMunmap a l, adec_munmap a l)
  | AMprotect a l p => Some (NMprotect a l p, adec_mprotect a l)
  | ABrk req => Some (NBrk req, adec_raw)
  | ASetTid _ => Some (NSetTid, adec_raw)
  | AMadvise a l => Some (NMadvise a l, adec_madvise a l)
  | AMmapT l => Some (NMmap 0 l PROT_RW F_ANON, adec_mmap_tol atop l)
  | AUndef _ => None
  end.

Lemma aev_tree_node : forall e,
  aev_tree atop e = match aev_node e with Some (n, d) => enode n d | None => Ret Unr end.
Proof. destruct e; reflexivity. Qed.

Definition node_sound : Prop :=
  forall e mo, aok e mo ->
    exists n d, aev_node e = Some (n, d)
    /\ (forall rsp mo' evs, step2 n mo rsp mo' evs -> evs = [] /\ exists z, d rsp = Some z /\ apost e mo z mo')
    /\ (exists rsp mo' evs, step2 n mo rsp mo' evs)
    /\ (forall code mo', ~ nexit n mo code mo').

Fixpoint atotal {R} (t : AM R) (mo : Model) (Post : R -> Model -> Prop) {struct t} : Prop :=
  match t with
  | SRet r => Post r mo
  | SVis e k => aok e mo /\ forall z mo', apost e mo z mo' -> atotal (k z) mo' Post
  end.

Lemma atotal_ret : forall {R} (r : R) mo Post, Post r mo -> atotal (SRet r) mo Post.
Proof. intros. exact H. Qed.

Lemma atotal_vis : forall {R} e (k : Z -> AM R) mo Post,
  aok e mo -> (forall z mo', apost e mo z mo' -> atotal (k z) mo' Post) -> atotal (SVis e k) mo Post.
Proof. intros. cbn. auto. Qed.

Lemma atotal_mono : forall {R} (t : AM R) mo (P Q : R -> Model -> Prop),
  (forall r mo', P r mo' -> Q r mo') -> atotal t mo P -> atotal t mo Q.
Proof.
  intros R t. induction t as [r|e k IH]; intros mo P Q HPQ H; cbn in *.
  - auto.
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact HPQ| exact (Hk _ _ Hp)].
Qed.

Lemma atotal_sbind : forall {A B} (t : AM A) (f : A -> AM B) mo (P : A -> Model -> Prop) (Q : B -> Model -> Prop),
  atotal t mo P -> (forall a mo', P a mo' -> atotal (f a) mo' Q) -> atotal (sbind t f) mo Q.
Proof.
  intros A B t. induction t as [r|e k IH]; intros f mo P Q Ht Hf; cbn in *.
  - exact (Hf _ _ Ht).
  - destruct Ht as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp. eapply IH; [exact (Hk _ _ Hp)| exact Hf].
Qed.

End Core.
