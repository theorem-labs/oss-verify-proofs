(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import ExecA ITreeA NodesA MonadA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section ImplX.
  Variable segs : list Segment.
  Variable P : acc -> Prop.
  Local Notation IMPL := (implA segs (at_nodeA segs) P).

  Lemma implA_bind_cong : forall {A B} (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> machine_state -> Prop) ms,
    (forall r ms', IMPL (k1 r) Q ms' -> IMPL (k2 r) Q ms') ->
    IMPL (ITree.bind node t k1) Q ms -> IMPL (ITree.bind node t k2) Q ms.
  Proof.
    intros A B t. induction t as [r|n k IH]; intros k1 k2 Q ms HK H; cbn [ITree.bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. eapply IH; [exact HK| apply Hk].
  Qed.

  Lemma implA_bind_assoc : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    IMPL (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms -> IMPL (ITree.bind node (ITree.bind node t g) f) Q ms.
  Proof.
    intros A B C t. induction t as [r|n k IH]; intros g f Q ms H; cbn [ITree.bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
      intros rsp. apply IH. apply Hk.
  Qed.

  Context {St : Type}.
  Local Notation IM := (implMA (St:=St) segs P).

  Lemma implMA_bind_assoc : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    IM (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms ->
    IM (Monad.mbind (Monad.mbind m g) f) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implMA, Monad.mbind, ebind in *.
    apply implA_bind_assoc. eapply implA_bind_cong; [| exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  Lemma implMA_retb : forall {A B} (a : A) (f : A -> @M St B) (s : St) Q ms,
    IM (f a) s Q ms -> IM (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof. intros A B a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma implMA_sysk : forall {A B} (n : node) (dec : resp -> option A) (k : A -> @M St B) (s : St) Q ms,
    evtA segs P (fun ms1 => at_nodeA segs P n ms1 /\
                         (forall rsp a, dec rsp = Some a -> IM (k a) s Q (nret ms1 rsp))) ms ->
    IM (Monad.mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B n dec k s Q ms H. unfold implMA, Monad.mbind, msys, ebind, enode in *. cbn [ITree.bind implA].
    eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply implA_ret_unr.
  Qed.

  Lemma implMA_sys_ret : forall {A} (n : node) (dec : resp -> option A) (s0 : St)
      (Q : unit -> St -> machine_state -> Prop) ms,
    evtA segs P (fun ms1 : machine_state => at_nodeA segs P n ms1 /\
                 (forall (rsp : resp) (a : A), dec rsp = Some a -> evtA segs P (Q tt s0) (nret ms1 rsp))) ms ->
    IM (Monad.mbind (msys n dec) (fun _ => Monad.mret tt)) s0 Q ms.
  Proof.
    intros A n dec s0 Q ms H. apply implMA_sysk. eapply evtA_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp a E. apply implMA_ret. exact (Hk rsp a E).
  Qed.

  Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  Lemma implMA_rdso : forall {A} (f : stdout_st -> @M St A) (s : St) Q ms,
    IM (f (get_so s)) s Q ms -> IM (Monad.mbind (rd_so get_so) f) s Q ms.
  Proof. intros A f s Q ms H. exact H. Qed.
  Lemma implMA_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> @M St A) (s : St) Q ms,
    IM (f tt) (set_so (g (get_so s)) s) Q ms -> IM (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
  Proof. intros A g f s Q ms H. exact H. Qed.
  Lemma implMA_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
    Q tt (set_so (g (get_so s)) s) ms -> IM (upd_so get_so set_so g) s Q ms.
  Proof. intros g s Q ms H. apply implMA_upd. apply evtA_done. exact H. Qed.

  (* [comment removed for export] *)
  Lemma implMA_from_evtA : forall {A} (c : @M St A) s Q ms,
    evtA segs P (fun ms' => IM c s Q ms') ms -> IM c s Q ms.
  Proof. intros A c s Q ms H. eapply implMA_evtA; [exact H|]. intros ms' H'; exact H'. Qed.
End ImplX.
End RC__1.
