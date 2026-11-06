(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StdioOld.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplX.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  #[using="Type"] Lemma impl_bind_cong : forall {A B} (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> machine_state -> Prop) ms,
    (forall r ms', impl segs (at_node segs) (npeek segs) (k1 r) Q ms' -> impl segs (at_node segs) (npeek segs) (k2 r) Q ms') ->
    impl segs (at_node segs) (npeek segs) (ITree.bind node t k1) Q ms -> impl segs (at_node segs) (npeek segs) (ITree.bind node t k2) Q ms.
  Proof. intros A B t k1 k2 Q ms HK H. eapply ITree.impl_bind_cong; [exact HK|exact H]. Qed.

  #[using="Type"] Lemma impl_bind_assoc : forall {A B C} (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) Q ms,
    impl segs (at_node segs) (npeek segs) (ITree.bind node t (fun x => ITree.bind node (g x) f)) Q ms ->
    impl segs (at_node segs) (npeek segs) (ITree.bind node (ITree.bind node t g) f) Q ms.
  Proof. intros A B C t g f Q ms H. apply ITree.impl_bind_assoc. exact H. Qed.

  Context {St : Type}.

  #[using="Type"] Lemma implM_bind_assoc : forall {A B C} (m : @M St A) (g : A -> @M St B) (f : B -> @M St C) s Q ms,
    implM segs (Monad.mbind m (fun a => Monad.mbind (g a) f)) s Q ms ->
    implM segs (Monad.mbind (Monad.mbind m g) f) s Q ms.
  Proof.
    intros A B C m g f s Q ms H. unfold implM, Monad.mbind, ebind in *.
    apply impl_bind_assoc. eapply impl_bind_cong; [| exact H].
    intros [|[a s']] ms'; cbn [ITree.bind fst snd]; intros H'; exact H'.
  Qed.

  #[using="Type"] Lemma implM_retb : forall {A B} (a : A) (f : A -> @M St B) (s : St) Q ms,
    implM segs (f a) s Q ms -> implM segs (Monad.mbind (Monad.mret a) f) s Q ms.
  Proof. intros A B a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implM_sysk : forall {A B} (n : node) (dec : resp -> option A) (k : A -> @M St B) (s : St) Q ms,
    evt segs (fun ms1 => at_node segs n ms1 /\
                         (forall rsp a, dec rsp = Some a -> implM segs (k a) s Q (nret ms1 rsp))) ms ->
    implM segs (Monad.mbind (msys n dec) k) s Q ms.
  Proof.
    intros A B n dec k s Q ms H. unfold implM, Monad.mbind, msys, ebind, enode in *. cbn [ITree.bind].
    apply impl_vis. eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
    intros rsp. destruct (dec rsp) as [a|] eqn:E; cbn [ITree.bind fst snd].
    - exact (Hk rsp a E).
    - apply impl_ret_unr.
  Qed.

  Context (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).

  #[using="Type"] Lemma implM_rdso : forall {A} (f : stdout_st -> @M St A) (s : St) Q ms,
    implM segs (f (get_so s)) s Q ms -> implM segs (Monad.mbind (rd_so get_so) f) s Q ms.
  Proof. intros A f s Q ms H. exact H. Qed.
  #[using="Type"] Lemma implM_updso : forall {A} (g : stdout_st -> stdout_st) (f : unit -> @M St A) (s : St) Q ms,
    implM segs (f tt) (set_so (g (get_so s)) s) Q ms -> implM segs (Monad.mbind (upd_so get_so set_so g) f) s Q ms.
  Proof. intros A g f s Q ms H. exact H. Qed.
  #[using="Type"] Lemma implM_updso_last : forall (g : stdout_st -> stdout_st) (s : St) (Q : unit -> St -> machine_state -> Prop) ms,
    Q tt (set_so (g (get_so s)) s) ms -> implM segs (upd_so get_so set_so g) s Q ms.
  Proof. intros g s Q ms H. apply implM_upd. apply evt_done. exact H. Qed.
End ImplX.
