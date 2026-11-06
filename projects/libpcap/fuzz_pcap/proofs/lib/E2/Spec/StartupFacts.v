(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Kernel Require Import Fork.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes RelSpec RelSpecMm Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.

(* [comment removed for export] *)
Definition floor_free (segs : list Segment) : Prop :=
  region_free (segments_reserved segs ++ []) (Z_to_bv 64 bottomup_floor) (Z_to_bv 64 4096) = true.

(* Start-up: the model records the thread descriptor block (a constant of the build, inside the image) and
   performs set_tid_address. No memory is mapped. *)
Section Startup.
  Context {St : Type} (set_tls : Z -> St -> St).
  Variables (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) (tls : Z).
  Hypothesis TLS : tls_in_image segs tls.
  Hypothesis VIN : valid_input inp.

  Notation mo0 := (mo0 segs lim en inp).
  Hypothesis CEQ : alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps mo0)).

  (* The kernel model after start-up: the initial one with the thread id set. *)
  Definition startup_mo (tb t : Z) (mo' : Model) : Prop :=
    m_vmmaps mo' = mkVmMapsFull (segments_reserved segs) [] []
                                (en_brk en) (en_brk en) lim (en_mmap_base en) (en_sp en)
    /\ m_fds mo' = m_fds mo0 /\ m_fs mo' = m_fs mo0 /\ m_halted mo' = None /\ m_stdin mo' = m_stdin mo0
    /\ m_tid mo' = Some (Z_to_bv 64 t) /\ lazyfree mo' /\ minv mo'
    /\ tls_in_image segs tb
    /\ alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps mo')).

  #[using="TLS VIN CEQ"] Lemma startup_tpath : forall s tr r mo',
    tpath nstep (startup_model set_tls tls s) mo0 tr r mo' ->
    exists tb t, r = Ok (tt, set_tls tb s) /\ tr = []
      /\ tb = tls /\ (0 < t < PID_MAX_ENVELOPE)%Z
      /\ startup_mo tb t mo'.
  Proof.
    intros s tr r mo' H.
    unfold startup_model, mbind, msys, mupd, mret, enode in H. cbn [tpath ITree.bind ebind fst snd] in H.
    destruct H as (rsp2 & mo2 & evs2 & tr2 & Hst2 & H & ->).
    pose proof (mo0_minv segs lim en inp VIN) as MI0.
    pose proof (nstep_dec_set_tid mo0 rsp2 mo2 evs2 MI0 Hst2) as (-> & t & Hdt & Ht & Hmo2).
    rewrite Hdt in H. cbn [tpath ITree.bind ebind fst snd] in H. destruct H as (<- & -> & ->).
    exists tls, t. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Ht|].
    assert (Htid0 : m_tid mo0 = None) by (unfold TopLevel.mo0; apply m_tid_init_model).
    destruct Hmo2 as [[Hc _]|[_ ->]]; [rewrite Htid0 in Hc; discriminate|].
    destruct (minv_preserved NSetTid mo0 rsp2 (with_tid (Z_to_bv 64 t) mo0) [] I MI0 (mo0_not_halted _ _ _ _) Hst2) as [HH2 MI2].
    unfold startup_mo.
    split; [rewrite m_vmmaps_with_tid; unfold TopLevel.mo0; apply m_vmmaps_init_model|].
    split; [rewrite m_fds_with_tid; reflexivity|].
    split; [rewrite m_fs_with_tid; reflexivity|].
    split; [exact HH2|].
    split; [rewrite m_stdin_with_tid; reflexivity|].
    split; [apply m_tid_with_tid|].
    split; [apply minv_lazyfree; exact MI2|]. split; [exact MI2|].
    split; [exact TLS|].
    rewrite m_vmmaps_with_tid. exact CEQ.
  Qed.

  #[using="TLS VIN CEQ"] Lemma startup_no_unr : forall s tr mo', tpath nstep (startup_model set_tls tls s) mo0 tr Unr mo' -> False.
  Proof. intros s tr mo' H. apply startup_tpath in H. destruct H as (tb & t & H & _). discriminate H. Qed.

  #[using="Type"] Lemma startup_texit : forall s tr, texit nstep nexit (startup_model set_tls tls s) mo0 tr -> False.
  Proof.
    intros s tr H.
    unfold startup_model, mbind, msys, mupd, mret, enode in H. cbn [texit ITree.bind ebind fst snd] in H.
    destruct H as [(code & mo' & Hx & _) | (rsp2 & mo2 & evs2 & tr2 & Hst2 & H & ->)]; [exact Hx|].
    destruct (dec_set_tid rsp2); cbn in H; [|exact H].
    exact H.
  Qed.

  #[using="Type"] Lemma startup_tsafe : forall s, tsafe nstep nsafe (startup_model set_tls tls s) mo0.
  Proof.
    intros s. unfold startup_model, mbind, msys, mupd, mret, enode. cbn [tsafe ITree.bind ebind fst snd].
    split; [exact I|]. intros rsp2 mo2 evs2 Hst2. destruct (dec_set_tid rsp2); cbn; exact I.
  Qed.
End Startup.

End WithCeil.
