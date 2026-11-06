(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AcctCore ExecF ITreeA RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim PcapPrelim PcapTypes Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module MonadGX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AProto.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import MonadG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplFX.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> footprint -> machine_state -> Prop.
  Variable sil : footprint -> machine_state -> machine_state -> Prop.
  Variable npeek : node -> option (machine_state -> resp).
  Variable fstep : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF' := (@implF node segs at_node sil npeek fstep).

  #[using="Type"] Lemma implF_bind_cong : forall {A B} RNG (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> footprint -> machine_state -> Prop) ms,
    (forall r RNG' ms', implF' RNG' (k1 r) Q ms' -> implF' RNG' (k2 r) Q ms') ->
    implF' RNG (bind node t k1) Q ms -> implF' RNG (bind node t k2) Q ms.
  Proof.
    intros A B RNG t; revert RNG. induction t as [r|n k IH]; intros RNG k1 k2 Q ms HK H; cbn [bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; [exact HK| exact (Hk rsp RNG' HF)].
      + right. exists g. split; [exact Hg|]. intros RNG' HF. eapply IH; [exact HK| exact (Hk RNG' HF)].
  Qed.

  #[using="Type"] Lemma implF_bind_assoc : forall {A B C} RNG (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) (Q : C -> footprint -> machine_state -> Prop) ms,
    implF' RNG (bind node t (fun x => bind node (g x) f)) Q ms -> implF' RNG (bind node (bind node t g) f) Q ms.
  Proof.
    intros A B C RNG t; revert RNG. induction t as [r|n k IH]; intros RNG g f Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. exact (Hk rsp RNG' HF).
      + right. exists h. split; [exact Hh|]. intros RNG' HF. apply IH. exact (Hk RNG' HF).
  Qed.
End ImplFX.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMGX.
  Context {St : Type}.
  Local Notation M := (Monad.M St).

  #[using="Type"] Lemma implMG_bind_assoc : forall {A B C} RNG (m : M A) (g : A -> M B) (f : B -> M C) s Q ms,
    implMG RNG (mbind m (fun a => mbind (g a) f)) s Q ms -> implMG RNG (mbind (mbind m g) f) s Q ms.
  Proof.
    intros A B C RNG m g f s Q ms H. unfold implMG, mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [bind fst snd]; intros H'; exact H'.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_mget : forall {A} RNG (k : St -> M A) s Q ms, implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros A RNG k s Q ms H. exact H. Qed.
  #[using="Type"] Lemma implMG_retb : forall {A B} RNG (a : A) (f : A -> M B) s Q ms, implMG RNG (f a) s Q ms -> implMG RNG (mbind (mret a) f) s Q ms.
  Proof. intros A B RNG a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_pure : forall {A} RNG (c : M A) s (Q : A -> St -> footprint -> machine_state -> Prop) ms r s1,
    c s = Ret (Ok (r, s1)) -> evtF asegs RNG (Q r s1 RNG) ms -> implMG RNG c s Q ms.
  Proof. intros A RNG c s Q ms r s1 E H. unfold implMG. rewrite E. apply implF_ret_ok. exact H. Qed.
  #[using="Type"] Lemma implMG_pure_k : forall {A B} RNG (c : M A) (k : A -> M B) s Q ms r s1,
    c s = Ret (Ok (r, s1)) -> implMG RNG (k r) s1 Q ms -> implMG RNG (mbind c k) s Q ms.
  Proof. intros A B RNG c k s Q ms r s1 E H. unfold implMG, mbind in *. rewrite E. exact H. Qed.
End ImplMGX.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.AcctCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Section ImplFX.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> footprint -> machine_state -> Prop.
  Variable sil : footprint -> machine_state -> machine_state -> Prop.
  Variable npeek : node -> option (machine_state -> resp).
  Variable fstep : node -> resp -> footprint -> footprint -> Prop.
  Local Notation implF' := (@implF node segs at_node sil npeek fstep).

  #[using="Type"] Lemma implF_bind_cong : forall {A B} RNG (t : itree node A) (k1 k2 : A -> itree node B) (Q : B -> footprint -> machine_state -> Prop) ms,
    (forall r RNG' ms', implF' RNG' (k1 r) Q ms' -> implF' RNG' (k2 r) Q ms') ->
    implF' RNG (bind node t k1) Q ms -> implF' RNG (bind node t k2) Q ms.
  Proof.
    intros A B RNG t; revert RNG. induction t as [r|n k IH]; intros RNG k1 k2 Q ms HK H; cbn [bind] in *.
    - apply HK. exact H.
    - cbn in H |- *. eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(g & Hg & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. eapply IH; [exact HK| exact (Hk rsp RNG' HF)].
      + right. exists g. split; [exact Hg|]. intros RNG' HF. eapply IH; [exact HK| exact (Hk RNG' HF)].
  Qed.

  #[using="Type"] Lemma implF_bind_assoc : forall {A B C} RNG (t : itree node A) (g : A -> itree node B) (f : B -> itree node C) (Q : C -> footprint -> machine_state -> Prop) ms,
    implF' RNG (bind node t (fun x => bind node (g x) f)) Q ms -> implF' RNG (bind node (bind node t g) f) Q ms.
  Proof.
    intros A B C RNG t; revert RNG. induction t as [r|n k IH]; intros RNG g f Q ms H; cbn [bind] in *.
    - exact H.
    - cbn in H |- *. eapply evtS_mono; [exact H|]. intros ms1 [[Hat Hk]|(h & Hh & Hk)].
      + left. split; [exact Hat|]. intros rsp RNG' HF. apply IH. exact (Hk rsp RNG' HF).
      + right. exists h. split; [exact Hh|]. intros RNG' HF. apply IH. exact (Hk RNG' HF).
  Qed.
End ImplFX.

Section CANSEC1. Context {rc : runConstT}.
Section ImplMGX.
  Context {St : Type}.
  Local Notation M := (Monad.M St).

  #[using="Type"] Lemma implMG_bind_assoc : forall {A B C} RNG (m : M A) (g : A -> M B) (f : B -> M C) s Q ms,
    implMG RNG (mbind m (fun a => mbind (g a) f)) s Q ms -> implMG RNG (mbind (mbind m g) f) s Q ms.
  Proof.
    intros A B C RNG m g f s Q ms H. unfold implMG, mbind, ebind in *.
    apply implF_bind_assoc. eapply implF_bind_cong; [| exact H].
    intros [|[a s']] RNG' ms'; cbn [bind fst snd]; intros H'; exact H'.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_mget : forall {A} RNG (k : St -> M A) s Q ms, implMG RNG (k s) s Q ms -> implMG RNG (mbind mget k) s Q ms.
  Proof. intros A RNG k s Q ms H. exact H. Qed.
  #[using="Type"] Lemma implMG_retb : forall {A B} RNG (a : A) (f : A -> M B) s Q ms, implMG RNG (f a) s Q ms -> implMG RNG (mbind (mret a) f) s Q ms.
  Proof. intros A B RNG a f s Q ms H. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma implMG_pure : forall {A} RNG (c : M A) s (Q : A -> St -> footprint -> machine_state -> Prop) ms r s1,
    c s = Ret (Ok (r, s1)) -> evtF asegs RNG (Q r s1 RNG) ms -> implMG RNG c s Q ms.
  Proof. intros A RNG c s Q ms r s1 E H. unfold implMG. rewrite E. apply implF_ret_ok. exact H. Qed.
  #[using="Type"] Lemma implMG_pure_k : forall {A B} RNG (c : M A) (k : A -> M B) s Q ms r s1,
    c s = Ret (Ok (r, s1)) -> implMG RNG (k r) s1 Q ms -> implMG RNG (mbind c k) s Q ms.
  Proof. intros A B RNG c k s Q ms r s1 E H. unfold implMG, mbind in *. rewrite E. exact H. Qed.
End ImplMGX.
End CANSEC1.
End TwB.
End MonadGX.

(* [comment removed for export] *)
Module TracesA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapPrelim PcapTypes Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
Record tparams := mkTP { tp_cpc : Z; tp_rpc : Z; tp_fopen : alayout -> Z -> list Z -> Prop; tp_fclose : alayout -> Z -> list Z -> Prop }.
Definition depth_pcap_freecode : nat := 0%nat.
Definition frames_pcap_freecode : list fframe := [].
Definition traces_pcap_freecode (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AFREE_PC :: 0x858a4 :: []) (al_U L).

Definition depth_sf_cleanup : nat := 0%nat.
Definition frames_sf_cleanup : list fframe := [].
Definition traces_sf_cleanup (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fclose TP L 0x84c9c [] /\
    In (AFREE_PC :: 0x84cbc :: []) (al_U L) /\
    traces_pcap_freecode TP L ra trC.

Definition depth_ng_cleanup : nat := 0%nat.
Definition frames_ng_cleanup : list fframe := [].
Definition traces_ng_cleanup (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AFREE_PC :: 0x8dca0 :: []) (al_U L) /\
    traces_sf_cleanup TP L ra trC.

Definition depth_pcap_close : nat := 0%nat.
Definition frames_pcap_close : list fframe := [].
Definition traces_pcap_close (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_sf_cleanup TP L 0x85c70 [] /\
    traces_ng_cleanup TP L 0x85c70 [] /\
    In (AFREE_PC :: 0x85c90 :: []) (al_U L) /\
    In (AFREE_PC :: ra :: trC) (al_U L).

Definition depth_pcap_strerror : nat := 0%nat.
Definition frames_pcap_strerror : list fframe := [].
Definition traces_pcap_strerror (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_fmt_errmsg : nat := 1%nat.
Definition frames_fmt_errmsg : list fframe := [FF_FMT_ERRMSG].
Definition traces_fmt_errmsg (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_strerror TP L 0x86120 (ra :: trC).

Definition depth_open_offline_common : nat := 1%nat.
Definition frames_open_offline_common : list fframe := [FF_FMT_ERRMSG].
Definition traces_open_offline_common (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (tp_cpc TP :: 0x85d04 :: []) (al_U L) /\
    traces_fmt_errmsg TP L 0x85dd0 [].

Definition depth_sf_stats : nat := 0%nat.
Definition frames_sf_stats : list fframe := [].
Definition traces_sf_stats (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_pcap_stats : nat := 0%nat.
Definition frames_pcap_stats : list fframe := [].
Definition traces_pcap_stats (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_sf_stats TP L ra trC.

Definition depth_oneshot : nat := 0%nat.
Definition frames_oneshot : list fframe := [].
Definition traces_oneshot (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_linktype_to_dlt : nat := 0%nat.
Definition frames_linktype_to_dlt : list fframe := [].
Definition traces_linktype_to_dlt (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_max_snaplen : nat := 0%nat.
Definition frames_max_snaplen : list fframe := [].
Definition traces_max_snaplen (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_adjust_snapshot : nat := 0%nat.
Definition frames_adjust_snapshot : list fframe := [].
Definition traces_adjust_snapshot (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_max_snaplen TP L ra trC.

Definition depth_isochronous : nat := 0%nat.
Definition frames_isochronous : list fframe := [].
Definition traces_isochronous (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_post_process : nat := 0%nat.
Definition frames_post_process : list fframe := [].
Definition traces_post_process (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_isochronous TP L 0x8a068 [].

Definition depth_read_bytes : nat := 1%nat.
Definition frames_read_bytes : list fframe := [FF_FMT_ERRMSG].
Definition traces_read_bytes (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8bad4 [].

Definition depth_read_block : nat := 2%nat.
Definition frames_read_block : list fframe := [FF_READ_BLOCK; FF_FMT_ERRMSG].
Definition traces_read_block (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8bd68 (ra :: trC) /\
    In (tp_rpc TP :: 0x8bed0 :: (ra :: trC)) (al_U L).

Definition depth_add_interface : nat := 0%nat.
Definition frames_add_interface : list fframe := [].
Definition traces_add_interface (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AMALLOC_PC :: 0x8c2b0 :: []) (al_U L) /\
    In (tp_rpc TP :: 0x8c7ec :: []) (al_U L).

Definition depth_pcap_check_header : nat := 2%nat.
Definition frames_pcap_check_header : list fframe := [FF_CHECK_HEADER; FF_FMT_ERRMSG].
Definition traces_pcap_check_header (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8795c (ra :: trC) /\
    traces_open_offline_common TP L 0x87b4c (ra :: trC) /\
    traces_linktype_to_dlt TP L 0x87bb8 (ra :: trC) /\
    traces_adjust_snapshot TP L 0x87c0c (ra :: trC) /\
    In (AFREE_PC :: 0x87d24 :: (ra :: trC)) (al_U L) /\
    In (AMALLOC_PC :: 0x87ecc :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x87f30 :: (ra :: trC)) (al_U L).

Definition depth_pcap_ng_check_header : nat := 3%nat.
Definition frames_pcap_ng_check_header : list fframe := [FF_NG_CHECK_HEADER; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_pcap_ng_check_header (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8aecc (ra :: trC) /\
    traces_fmt_errmsg TP L 0x8af3c (ra :: trC) /\
    traces_open_offline_common TP L 0x8b054 (ra :: trC) /\
    In (AMALLOC_PC :: 0x8b14c :: (ra :: trC)) (al_U L) /\
    traces_read_bytes TP L 0x8b210 (ra :: trC) /\
    traces_read_block TP L 0x8b330 (ra :: trC) /\
    In (AFREE_PC :: 0x8b398 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b3d0 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b45c :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b474 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b47c :: (ra :: trC)) (al_U L) /\
    traces_add_interface TP L 0x8b604 (ra :: trC) /\
    traces_linktype_to_dlt TP L 0x8b61c (ra :: trC) /\
    traces_adjust_snapshot TP L 0x8b650 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b698 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b6d4 (ra :: trC).

Definition depth_pcap_next_packet : nat := 2%nat.
Definition frames_pcap_next_packet : list fframe := [FF_NEXT_PACKET; FF_FMT_ERRMSG].
Definition traces_pcap_next_packet (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x88498 (ra :: trC) /\
    traces_max_snaplen TP L 0x88640 (ra :: trC) /\
    In (tp_rpc TP :: 0x886e4 :: (ra :: trC)) (al_U L) /\
    traces_max_snaplen TP L 0x88800 (ra :: trC) /\
    In (tp_rpc TP :: 0x88898 :: (ra :: trC)) (al_U L) /\
    traces_post_process TP L 0x88960 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x889e8 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x88aa8 (ra :: trC).

Definition depth_pcap_ng_next_packet : nat := 2%nat.
Definition frames_pcap_ng_next_packet : list fframe := [FF_READ_BLOCK; FF_FMT_ERRMSG].
Definition traces_pcap_ng_next_packet (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_read_block TP L 0x8cc90 trC /\
    traces_read_block TP L 0x8cc90 [] /\
    traces_adjust_snapshot TP L 0x8ce9c [] /\
    traces_add_interface TP L 0x8ceb8 [] /\
    traces_post_process TP L 0x8d8d0 [].

Definition depth_offline_read : nat := 3%nat.
Definition frames_offline_read : list fframe := [FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_offline_read (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_next_packet TP L 0x85650 (ra :: trC) /\
    traces_pcap_ng_next_packet TP L 0x85650 (ra :: trC) /\
    traces_oneshot TP L 0x85650 (ra :: trC) /\
    traces_pcap_next_packet TP L 0x85694 (ra :: trC) /\
    traces_pcap_ng_next_packet TP L 0x85694 (ra :: trC) /\
    traces_oneshot TP L 0x85694 (ra :: trC).

Definition depth_pcap_next_ex : nat := 4%nat.
Definition frames_pcap_next_ex : list fframe := [FF_NEXT_EX; FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_pcap_next_ex (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_offline_read TP L 0x85af8 (ra :: trC) /\
    traces_offline_read TP L 0x85b38 (ra :: trC).

Definition depth_fopen_offline : nat := 4%nat.
Definition frames_fopen_offline : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_fopen_offline (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_check_header TP L 0x84fd4 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x8521c (ra :: trC) /\
    traces_pcap_ng_check_header TP L 0x85240 (ra :: trC).

Definition depth_open_offline_wtp : nat := 4%nat.
Definition frames_open_offline_wtp : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_open_offline_wtp (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fopen TP L 0x84d64 [] /\
    traces_fopen_offline TP L 0x84d7c [] /\
    tp_fclose TP L 0x84da8 [] /\
    traces_fmt_errmsg TP L 0x84df4 [].

Definition depth_pcap_open_offline : nat := 4%nat.
Definition frames_pcap_open_offline : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_pcap_open_offline (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_open_offline_wtp TP L ra trC.

Definition depth_fuzz_one : nat := 5%nat.
Definition frames_fuzz_one : list fframe := [FF_FUZZ_ONE_INPUT; FF_NEXT_EX; FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK; FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_NG_CHECK_HEADER].
Definition traces_fuzz_one (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fopen TP L 0x848b4 (ra :: trC) /\
    tp_fopen TP L 0x84924 (ra :: trC) /\
    tp_fclose TP L 0x8494c (ra :: trC) /\
    traces_pcap_open_offline TP L 0x84964 (ra :: trC) /\
    traces_pcap_next_ex TP L 0x84984 (ra :: trC) /\
    traces_pcap_next_ex TP L 0x849e0 (ra :: trC) /\
    traces_pcap_stats TP L 0x84a58 (ra :: trC) /\
    traces_pcap_close TP L 0x84a7c (ra :: trC).

  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition depth_next_packet_op (ng : bool) : nat := if ng then depth_pcap_ng_next_packet else depth_pcap_next_packet.
Definition depth_check_header (ng : bool) : nat := if ng then depth_pcap_ng_check_header else depth_pcap_check_header.
Definition depth_open_offline (ENTRY : Z) : nat := depth_open_offline_wtp.
Definition frames_next_packet_op (ng : bool) := if ng then frames_pcap_ng_next_packet else frames_pcap_next_packet.
Definition frames_check_header (ng : bool) := if ng then frames_pcap_ng_check_header else frames_pcap_check_header.
Definition frames_open_offline (ENTRY : Z) := frames_open_offline_wtp.
Definition traces_next_packet_op (TP : tparams) (ng : bool) := if ng then traces_pcap_ng_next_packet TP else traces_pcap_next_packet TP.
Definition traces_check_header (TP : tparams) (ng : bool) := if ng then traces_pcap_ng_check_header TP else traces_pcap_check_header TP.
Definition traces_open_offline (TP : tparams) (ENTRY : Z) := if ENTRY =? 0x84ce8 then traces_open_offline_wtp TP else traces_pcap_open_offline TP.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
Record tparams := mkTP { tp_cpc : Z; tp_rpc : Z; tp_fopen : alayout -> Z -> list Z -> Prop; tp_fclose : alayout -> Z -> list Z -> Prop }.
Definition depth_pcap_freecode : nat := 0%nat.
Definition frames_pcap_freecode : list fframe := [].
Definition traces_pcap_freecode (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AFREE_PC :: 0x859cc :: []) (al_U L).

Definition depth_sf_cleanup : nat := 0%nat.
Definition frames_sf_cleanup : list fframe := [].
Definition traces_sf_cleanup (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fclose TP L 0x84d34 [] /\
    In (AFREE_PC :: 0x84d54 :: []) (al_U L) /\
    traces_pcap_freecode TP L ra trC.

Definition depth_ng_cleanup : nat := 0%nat.
Definition frames_ng_cleanup : list fframe := [].
Definition traces_ng_cleanup (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AFREE_PC :: 0x8e080 :: []) (al_U L) /\
    traces_sf_cleanup TP L ra trC.

Definition depth_pcap_close : nat := 0%nat.
Definition frames_pcap_close : list fframe := [].
Definition traces_pcap_close (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_sf_cleanup TP L 0x85dcc [] /\
    traces_ng_cleanup TP L 0x85dcc [] /\
    In (AFREE_PC :: 0x85dec :: []) (al_U L) /\
    In (AFREE_PC :: ra :: trC) (al_U L).

Definition depth_pcap_strerror : nat := 0%nat.
Definition frames_pcap_strerror : list fframe := [].
Definition traces_pcap_strerror (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_fmt_errmsg : nat := 1%nat.
Definition frames_fmt_errmsg : list fframe := [FF_FMT_ERRMSG].
Definition traces_fmt_errmsg (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_strerror TP L 0x862c8 (ra :: trC).

Definition depth_open_offline_common : nat := 1%nat.
Definition frames_open_offline_common : list fframe := [FF_FMT_ERRMSG].
Definition traces_open_offline_common (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (tp_cpc TP :: 0x85e68 :: trC) (al_U L) /\
    traces_fmt_errmsg TP L 0x85f3c [].

Definition depth_sf_stats : nat := 0%nat.
Definition frames_sf_stats : list fframe := [].
Definition traces_sf_stats (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_pcap_stats : nat := 0%nat.
Definition frames_pcap_stats : list fframe := [].
Definition traces_pcap_stats (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_sf_stats TP L ra trC.

Definition depth_oneshot : nat := 0%nat.
Definition frames_oneshot : list fframe := [].
Definition traces_oneshot (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_linktype_to_dlt : nat := 0%nat.
Definition frames_linktype_to_dlt : list fframe := [].
Definition traces_linktype_to_dlt (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_max_snaplen : nat := 0%nat.
Definition frames_max_snaplen : list fframe := [].
Definition traces_max_snaplen (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_adjust_snapshot : nat := 0%nat.
Definition frames_adjust_snapshot : list fframe := [].
Definition traces_adjust_snapshot (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_max_snaplen TP L ra trC.

Definition depth_isochronous : nat := 0%nat.
Definition frames_isochronous : list fframe := [].
Definition traces_isochronous (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    True.

Definition depth_post_process : nat := 0%nat.
Definition frames_post_process : list fframe := [].
Definition traces_post_process (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_isochronous TP L 0x89b48 [].

Definition depth_read_bytes : nat := 1%nat.
Definition frames_read_bytes : list fframe := [FF_FMT_ERRMSG].
Definition traces_read_bytes (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8ba7c [].

Definition depth_read_block : nat := 2%nat.
Definition frames_read_block : list fframe := [FF_READ_BLOCK; FF_FMT_ERRMSG].
Definition traces_read_block (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8bd28 (ra :: trC) /\
    In (tp_rpc TP :: 0x8be9c :: (ra :: trC)) (al_U L).

Definition depth_add_interface : nat := 0%nat.
Definition frames_add_interface : list fframe := [].
Definition traces_add_interface (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    In (AMALLOC_PC :: 0x8c3d4 :: []) (al_U L) /\
    In (tp_rpc TP :: 0x8c970 :: []) (al_U L).

Definition depth_pcap_check_header : nat := 2%nat.
Definition frames_pcap_check_header : list fframe := [FF_CHECK_HEADER; FF_FMT_ERRMSG].
Definition traces_pcap_check_header (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x87e34 (ra :: trC) /\
    traces_open_offline_common TP L 0x8801c (ra :: trC) /\
    traces_linktype_to_dlt TP L 0x88094 (ra :: trC) /\
    traces_adjust_snapshot TP L 0x880e8 (ra :: trC) /\
    In (AFREE_PC :: 0x88234 :: (ra :: trC)) (al_U L) /\
    In (AMALLOC_PC :: 0x88358 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x883bc :: (ra :: trC)) (al_U L).

Definition depth_pcap_ng_check_header : nat := 3%nat.
Definition frames_pcap_ng_check_header : list fframe := [FF_NG_CHECK_HEADER; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_pcap_ng_check_header (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x8ae18 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x8ae94 (ra :: trC) /\
    traces_open_offline_common TP L 0x8afac (ra :: trC) /\
    In (AMALLOC_PC :: 0x8b0c4 :: (ra :: trC)) (al_U L) /\
    traces_read_bytes TP L 0x8b1b0 (ra :: trC) /\
    traces_read_block TP L 0x8b2d8 (ra :: trC) /\
    traces_add_interface TP L 0x8b3c0 (ra :: trC) /\
    traces_linktype_to_dlt TP L 0x8b3dc (ra :: trC) /\
    traces_adjust_snapshot TP L 0x8b414 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b460 (ra :: trC) /\
    traces_max_snaplen TP L 0x8b498 (ra :: trC) /\
    In (AFREE_PC :: 0x8b51c :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b554 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b5e0 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b5f8 :: (ra :: trC)) (al_U L) /\
    In (AFREE_PC :: 0x8b600 :: (ra :: trC)) (al_U L).

Definition depth_pcap_next_packet : nat := 2%nat.
Definition frames_pcap_next_packet : list fframe := [FF_NEXT_PACKET; FF_FMT_ERRMSG].
Definition traces_pcap_next_packet (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_fmt_errmsg TP L 0x88954 (ra :: trC) /\
    traces_max_snaplen TP L 0x88b54 (ra :: trC) /\
    In (tp_rpc TP :: 0x88bf4 :: (ra :: trC)) (al_U L) /\
    traces_max_snaplen TP L 0x88d08 (ra :: trC) /\
    In (tp_rpc TP :: 0x88e24 :: (ra :: trC)) (al_U L) /\
    traces_post_process TP L 0x88f00 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x89054 (ra :: trC).

Definition depth_pcap_ng_next_packet : nat := 2%nat.
Definition frames_pcap_ng_next_packet : list fframe := [FF_READ_BLOCK; FF_FMT_ERRMSG].
Definition traces_pcap_ng_next_packet (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_read_block TP L 0x8ce3c trC /\
    traces_read_block TP L 0x8ce3c [] /\
    traces_adjust_snapshot TP L 0x8d038 [] /\
    traces_add_interface TP L 0x8d054 [] /\
    traces_post_process TP L 0x8dc5c [].

Definition depth_offline_read : nat := 3%nat.
Definition frames_offline_read : list fframe := [FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_offline_read (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_next_packet TP L 0x8571c (ra :: trC) /\
    traces_pcap_ng_next_packet TP L 0x8571c (ra :: trC) /\
    traces_oneshot TP L 0x8571c (ra :: trC) /\
    traces_pcap_next_packet TP L 0x85760 (ra :: trC) /\
    traces_pcap_ng_next_packet TP L 0x85760 (ra :: trC) /\
    traces_oneshot TP L 0x85760 (ra :: trC).

Definition depth_pcap_next_ex : nat := 4%nat.
Definition frames_pcap_next_ex : list fframe := [FF_NEXT_EX; FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK].
Definition traces_pcap_next_ex (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_offline_read TP L 0x85c48 (ra :: trC) /\
    traces_offline_read TP L 0x85c84 (ra :: trC).

Definition depth_fopen_offline : nat := 4%nat.
Definition frames_fopen_offline : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_fopen_offline (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_pcap_check_header TP L 0x85088 (ra :: trC) /\
    traces_fmt_errmsg TP L 0x852e4 (ra :: trC) /\
    traces_pcap_ng_check_header TP L 0x85308 (ra :: trC).

Definition depth_open_offline_wtp : nat := 4%nat.
Definition frames_open_offline_wtp : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_open_offline_wtp (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fopen TP L 0x84e08 [] /\
    traces_fopen_offline TP L 0x84e20 [] /\
    tp_fclose TP L 0x84e4c [] /\
    traces_fmt_errmsg TP L 0x84ea4 [].

Definition depth_pcap_open_offline : nat := 4%nat.
Definition frames_pcap_open_offline : list fframe := [FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_FMT_ERRMSG; FF_NG_CHECK_HEADER; FF_READ_BLOCK].
Definition traces_pcap_open_offline (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    traces_open_offline_wtp TP L ra trC.

Definition depth_fuzz_one : nat := 5%nat.
Definition frames_fuzz_one : list fframe := [FF_FUZZ_ONE_INPUT; FF_NEXT_EX; FF_OFFLINE_READ; FF_NEXT_PACKET; FF_FMT_ERRMSG; FF_READ_BLOCK; FF_FOPEN_OFFLINE; FF_CHECK_HEADER; FF_NG_CHECK_HEADER].
Definition traces_fuzz_one (TP : tparams) (L : alayout) (ra : Z) (trC : list Z) : Prop :=
    tp_fopen TP L 0x8491c (ra :: trC) /\
    tp_fopen TP L 0x84998 (ra :: trC) /\
    tp_fclose TP L 0x849c0 (ra :: trC) /\
    traces_pcap_open_offline TP L 0x849d8 (ra :: trC) /\
    traces_pcap_next_ex TP L 0x849f8 (ra :: trC) /\
    traces_pcap_next_ex TP L 0x84a60 (ra :: trC) /\
    traces_pcap_stats TP L 0x84bf8 (ra :: trC) /\
    traces_pcap_close TP L 0x84c1c (ra :: trC).

  (* [comment removed for export] *)
(* [comment removed for export] *)
Definition depth_next_packet_op (ng : bool) : nat := if ng then depth_pcap_ng_next_packet else depth_pcap_next_packet.
Definition depth_check_header (ng : bool) : nat := if ng then depth_pcap_ng_check_header else depth_pcap_check_header.
Definition depth_open_offline (ENTRY : Z) : nat := depth_open_offline_wtp.
Definition frames_next_packet_op (ng : bool) := if ng then frames_pcap_ng_next_packet else frames_pcap_next_packet.
Definition frames_check_header (ng : bool) := if ng then frames_pcap_ng_check_header else frames_pcap_check_header.
Definition frames_open_offline (ENTRY : Z) := frames_open_offline_wtp.
Definition traces_next_packet_op (TP : tparams) (ng : bool) := if ng then traces_pcap_ng_next_packet TP else traces_pcap_next_packet TP.
Definition traces_check_header (TP : tparams) (ng : bool) := if ng then traces_pcap_ng_check_header TP else traces_pcap_check_header TP.
Definition traces_open_offline (TP : tparams) (ENTRY : Z) := if ENTRY =? 0x84d84 then traces_open_offline_wtp TP else traces_pcap_open_offline TP.
End CANSEC1.
End TwB.
End TracesA.

(* [comment removed for export] *)
Module TracesUnivA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapPrelim PcapTypes Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint tr_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && tr_eqb a' b'
  | _, _ => false
  end.
Lemma tr_eqb_eq : forall a b, tr_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; intros E; try discriminate; [reflexivity|].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. subst y. f_equal. exact (IH _ E2).
Qed.
Definition tr_mem (tr : list Z) (U : list (list Z)) : bool := existsb (tr_eqb tr) U.
Lemma tr_mem_In : forall tr U, tr_mem tr U = true -> In tr U.
Proof.
  intros tr U E. apply existsb_exists in E. destruct E as (u & IN & E). apply tr_eqb_eq in E. subst u. exact IN.
Qed.

(* [comment removed for export] *)
Definition ACALLOC_PC : Z := 0x56650.
Definition AREALLOC_PC : Z := 0x568f0.

(* [comment removed for export] *)
Definition fuzz_traces : list (list Z) :=
  [ [AMALLOC_PC; 0x99bd0] ;
    [AFREE_PC; 0x9a2ac] ;
    [AFREE_PC; 0x9a2a4] ;
    [ACALLOC_PC; 0x85d04] ;
    [AFREE_PC; 0x87d24; 0x84fd4; 0x84d7c] ;
    [AMALLOC_PC; 0x87ecc; 0x84fd4; 0x84d7c] ;
    [AFREE_PC; 0x87f30; 0x84fd4; 0x84d7c] ;
    [AMALLOC_PC; 0x8b14c; 0x85240; 0x84d7c] ;
    [AREALLOC_PC; 0x8bed0; 0x8b330; 0x85240; 0x84d7c] ;
    [AFREE_PC; 0x8b398; 0x85240; 0x84d7c] ;
    [AFREE_PC; 0x8b3d0; 0x85240; 0x84d7c] ;
    [AFREE_PC; 0x8b45c; 0x85240; 0x84d7c] ;
    [AFREE_PC; 0x8b474; 0x85240; 0x84d7c] ;
    [AFREE_PC; 0x8b47c; 0x85240; 0x84d7c] ;
    [AMALLOC_PC; 0x8c2b0] ;
    [AREALLOC_PC; 0x8c7ec] ;
    [AREALLOC_PC; 0x886e4; 0x85650; 0x85af8; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85650; 0x85af8; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x8bed0; 0x8cc90; 0x85af8; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x8bed0; 0x8cc90] ;
    [AREALLOC_PC; 0x886e4; 0x85694; 0x85af8; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85694; 0x85af8; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85650; 0x85b38; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85650; 0x85b38; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x8bed0; 0x8cc90; 0x85b38; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85694; 0x85b38; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85694; 0x85b38; 0x84984; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85650; 0x85af8; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85650; 0x85af8; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x8bed0; 0x8cc90; 0x85af8; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85694; 0x85af8; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85694; 0x85af8; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85650; 0x85b38; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85650; 0x85b38; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x8bed0; 0x8cc90; 0x85b38; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x886e4; 0x85694; 0x85b38; 0x849e0; 0x844bc] ;
    [AREALLOC_PC; 0x88898; 0x85694; 0x85b38; 0x849e0; 0x844bc] ;
    [AFREE_PC; 0x84cbc] ;
    [AFREE_PC; 0x858a4] ;
    [AFREE_PC; 0x8dca0] ;
    [AFREE_PC; 0x85c90] ;
    [AFREE_PC; 0x84a7c; 0x844bc] ].

Lemma fuzz_traces_length : length fuzz_traces = 42%nat.
Proof. reflexivity. Qed.
Lemma fuzz_traces_short : Forall (fun u : list Z => (length u <= 6)%nat) fuzz_traces.
Proof. unfold fuzz_traces. repeat constructor. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
Definition TP_real : tparams :=
  mkTP ACALLOC_PC AREALLOC_PC (fun L _ _ => In [AMALLOC_PC; 0x99bd0] (al_U L))
       (fun L _ _ => In [AFREE_PC; 0x9a2ac] (al_U L) /\ In [AFREE_PC; 0x9a2a4] (al_U L)).   (* [comment removed for export] *)
#[using="Type"] Lemma TP_real_fopen : forall L ra trC, tp_fopen TP_real L ra trC -> In [AMALLOC_PC; 0x99bd0] (al_U L).
Proof. intros L ra trC HH. exact HH. Qed.
#[using="Type"] Lemma TP_real_fclose : forall L ra trC, tp_fclose TP_real L ra trC -> In [AFREE_PC; 0x9a2ac] (al_U L) /\ In [AFREE_PC; 0x9a2a4] (al_U L).
Proof. intros L ra trC HH. exact HH. Qed.

#[using="Type"] Theorem traces_fuzz_one_univ : forall L : alayout,
  (forall tr, In tr fuzz_traces -> In tr (al_U L)) -> traces_fuzz_one TP_real L 0x844bc [].
Proof.
  intros L HU.
  assert (K : forall tr, tr_mem tr fuzz_traces = true -> In tr (al_U L)) by (intros tr E; apply HU, tr_mem_In, E).
  unfold traces_fuzz_one, traces_pcap_open_offline, traces_open_offline_wtp, traces_fopen_offline, traces_pcap_next_ex, traces_offline_read, traces_pcap_ng_next_packet, traces_pcap_next_packet, traces_pcap_ng_check_header, traces_pcap_check_header, traces_add_interface, traces_read_block, traces_read_bytes, traces_post_process, traces_isochronous, traces_adjust_snapshot, traces_max_snaplen, traces_linktype_to_dlt, traces_oneshot, traces_pcap_stats, traces_sf_stats, traces_open_offline_common, traces_fmt_errmsg, traces_pcap_strerror, traces_pcap_close, traces_ng_cleanup, traces_sf_cleanup, traces_pcap_freecode;
  cbn [tp_fopen tp_fclose tp_cpc tp_rpc TP_real].
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I | apply K; vm_compute; reflexivity ].
Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint tr_eqb (a b : list Z) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (x =? y) && tr_eqb a' b'
  | _, _ => false
  end.
Lemma tr_eqb_eq : forall a b, tr_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; cbn; intros E; try discriminate; [reflexivity|].
  apply andb_true_iff in E. destruct E as [E1 E2]. apply Z.eqb_eq in E1. subst y. f_equal. exact (IH _ E2).
Qed.
Definition tr_mem (tr : list Z) (U : list (list Z)) : bool := existsb (tr_eqb tr) U.
Lemma tr_mem_In : forall tr U, tr_mem tr U = true -> In tr U.
Proof.
  intros tr U E. apply existsb_exists in E. destruct E as (u & IN & E). apply tr_eqb_eq in E. subst u. exact IN.
Qed.

(* [comment removed for export] *)
Definition ACALLOC_PC : Z := 0x566b8.
Definition AREALLOC_PC : Z := 0x56958.

(* [comment removed for export] *)
Definition fuzz_traces : list (list Z) :=
  [ [AMALLOC_PC; 0x99fb4] ;
    [AFREE_PC; 0x9a690] ;
    [AFREE_PC; 0x9a688] ;
    [ACALLOC_PC; 0x85e68; 0x85088; 0x84e20] ;
    [AFREE_PC; 0x88234; 0x85088; 0x84e20] ;
    [AMALLOC_PC; 0x88358; 0x85088; 0x84e20] ;
    [AFREE_PC; 0x883bc; 0x85088; 0x84e20] ;
    [ACALLOC_PC; 0x85e68; 0x85308; 0x84e20] ;
    [AMALLOC_PC; 0x8b0c4; 0x85308; 0x84e20] ;
    [AREALLOC_PC; 0x8be9c; 0x8b2d8; 0x85308; 0x84e20] ;
    [AMALLOC_PC; 0x8c3d4] ;
    [AREALLOC_PC; 0x8c970] ;
    [AFREE_PC; 0x8b51c; 0x85308; 0x84e20] ;
    [AFREE_PC; 0x8b554; 0x85308; 0x84e20] ;
    [AFREE_PC; 0x8b5e0; 0x85308; 0x84e20] ;
    [AFREE_PC; 0x8b5f8; 0x85308; 0x84e20] ;
    [AFREE_PC; 0x8b600; 0x85308; 0x84e20] ;
    [AREALLOC_PC; 0x88bf4; 0x8571c; 0x85c48; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x8571c; 0x85c48; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x8be9c; 0x8ce3c; 0x85c48; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x8be9c; 0x8ce3c] ;
    [AREALLOC_PC; 0x88bf4; 0x85760; 0x85c48; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x85760; 0x85c48; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x8571c; 0x85c84; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x8571c; 0x85c84; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x8be9c; 0x8ce3c; 0x85c84; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x85760; 0x85c84; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x85760; 0x85c84; 0x849f8; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x8571c; 0x85c48; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x8571c; 0x85c48; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x8be9c; 0x8ce3c; 0x85c48; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x85760; 0x85c48; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x85760; 0x85c48; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x8571c; 0x85c84; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x8571c; 0x85c84; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x8be9c; 0x8ce3c; 0x85c84; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88bf4; 0x85760; 0x85c84; 0x84a60; 0x84524] ;
    [AREALLOC_PC; 0x88e24; 0x85760; 0x85c84; 0x84a60; 0x84524] ;
    [AFREE_PC; 0x84d54] ;
    [AFREE_PC; 0x859cc] ;
    [AFREE_PC; 0x8e080] ;
    [AFREE_PC; 0x85dec] ;
    [AFREE_PC; 0x84c1c; 0x84524] ].

Lemma fuzz_traces_length : length fuzz_traces = 43%nat.
Proof. reflexivity. Qed.
Lemma fuzz_traces_short : Forall (fun u : list Z => (length u <= 6)%nat) fuzz_traces.
Proof. unfold fuzz_traces. repeat constructor. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
Definition TP_real : tparams :=
  mkTP ACALLOC_PC AREALLOC_PC (fun L _ _ => In [AMALLOC_PC; 0x99fb4] (al_U L))
       (fun L _ _ => In [AFREE_PC; 0x9a690] (al_U L) /\ In [AFREE_PC; 0x9a688] (al_U L)).   (* [comment removed for export] *)
#[using="Type"] Lemma TP_real_fopen : forall L ra trC, tp_fopen TP_real L ra trC -> In [AMALLOC_PC; 0x99fb4] (al_U L).
Proof. intros L ra trC HH. exact HH. Qed.
#[using="Type"] Lemma TP_real_fclose : forall L ra trC, tp_fclose TP_real L ra trC -> In [AFREE_PC; 0x9a690] (al_U L) /\ In [AFREE_PC; 0x9a688] (al_U L).
Proof. intros L ra trC HH. exact HH. Qed.

#[using="Type"] Theorem traces_fuzz_one_univ : forall L : alayout,
  (forall tr, In tr fuzz_traces -> In tr (al_U L)) -> traces_fuzz_one TP_real L 0x84524 [].
Proof.
  intros L HU.
  assert (K : forall tr, tr_mem tr fuzz_traces = true -> In tr (al_U L)) by (intros tr E; apply HU, tr_mem_In, E).
  unfold traces_fuzz_one, traces_pcap_open_offline, traces_open_offline_wtp, traces_fopen_offline, traces_pcap_next_ex, traces_offline_read, traces_pcap_ng_next_packet, traces_pcap_next_packet, traces_pcap_ng_check_header, traces_pcap_check_header, traces_add_interface, traces_read_block, traces_read_bytes, traces_post_process, traces_isochronous, traces_adjust_snapshot, traces_max_snaplen, traces_linktype_to_dlt, traces_oneshot, traces_pcap_stats, traces_sf_stats, traces_open_offline_common, traces_fmt_errmsg, traces_pcap_strerror, traces_pcap_close, traces_ng_cleanup, traces_sf_cleanup, traces_pcap_freecode;
  cbn [tp_fopen tp_fclose tp_cpc tp_rpc TP_real].
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I | apply K; vm_compute; reflexivity ].
Qed.
End CANSEC1.
End TwB.
End TracesUnivA.
