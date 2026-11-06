(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Import GIA PcapRepA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
  (* [comment removed for export] *)
  Definition z8 : list byte := repeat (Z_to_bv 8 0) 8.
  Definition fd_pad48 : list byte := repeat (Z_to_bv 8 0) 24 ++ le4 (Z_to_bv 64 (-1)) ++ repeat (Z_to_bv 8 0) 20.
  Definition blank_cells (P : Z) : list cell :=
    [ C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 0);
      CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48;
      C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0) ].

  #[using="Type"] Lemma blank_recell : forall m P,
    rw_cells asegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
    rw_cells asegs m P (blank_cells P).
  Proof.
    intros m P Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_SF_TOTAL in C. change (Z.to_nat (664 - 188)) with 476%nat in C.
    assert (A' : rw_cells asegs m P (firstn 7 (blank_cells P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells asegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (blank_cells P))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.

  (* [comment removed for export] *)
  Definition pcells (P : Z) (sw : bool) (maj min lt ext : Z) (nxt bsz buf snapc clean hsz lsw scl : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); nxt; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z sw)); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 maj); C4 (Z_to_bv 64 min); snapc; C4 (Z_to_bv 64 lt); C4 (Z_to_bv 64 ext);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; clean; hsz; lsw; scl ].
  Definition blank_junk : pcap_junk :=
    mkPJ (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 16)
         (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 28) fd_pad48 (repeat (Z_to_bv 8 0) 304) (repeat (Z_to_bv 8 0) 72) (Z_to_bv 64 0).

  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_C4_low : forall m A pre w w' post,
    rw_cells asegs m A (pre ++ C4 w :: post) -> le4 w = le4 w' -> rw_cells asegs m A (pre ++ C4 w' :: post).
  Proof.
    intros m A pre w w' post HC E. eapply rw_cells_recell; [exact HC| |].
    - destruct HC as [[WF _] _]. apply cells_wf_app in WF as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn in W2 |- *. exact W2.
    - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
  Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
  (* [comment removed for export] *)
  Definition z8 : list byte := repeat (Z_to_bv 8 0) 8.
  Definition fd_pad48 : list byte := repeat (Z_to_bv 8 0) 24 ++ le4 (Z_to_bv 64 (-1)) ++ repeat (Z_to_bv 8 0) 20.
  Definition blank_cells (P : Z) : list cell :=
    [ C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); C4 (Z_to_bv 64 0);
      CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48;
      C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0) ].

  #[using="Type"] Lemma blank_recell : forall m P,
    rw_cells asegs m P ([CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 (-1)); CB 28 (repeat (Z_to_bv 8 0) 28);
                         C8 (Z_to_bv 64 (P + PCAP_PRIV_OFF)); CB 128 (repeat (Z_to_bv 8 0) 128); C4 (Z_to_bv 64 (-1));
                         CB (Z.to_nat (PCAP_SF_TOTAL - 188)) (repeat (Z_to_bv 8 0) (Z.to_nat (PCAP_SF_TOTAL - 188)))]) ->
    rw_cells asegs m P (blank_cells P).
  Proof.
    intros m P Hc.
    destruct (rw_cells_cut _ _ _ 3 Hc) as [A X]. destruct (rw_cells_cut _ _ _ 1 X) as [B C]. clear Hc X.
    cbn [firstn skipn cells_size csize Nat.add] in A, B, C.
    unfold PCAP_SF_TOTAL in C. change (Z.to_nat (664 - 188)) with 476%nat in C.
    assert (A' : rw_cells asegs m P (firstn 7 (blank_cells P))).
    { eapply rw_cells_recell; [exact A | cbn; repeat split; exact Logic.I | vm_compute; reflexivity]. }
    assert (C' : rw_cells asegs m (P + Z.of_nat 48 + Z.of_nat 8) (skipn 8 (blank_cells P))).
    { eapply rw_cells_recell; [exact C | cbn; repeat split; exact Logic.I | unfold fd_pad48; vm_compute; reflexivity]. }
    pose proof (rw_cells_uncut _ _ _ _ _ A' B ltac:(cbn; lia)) as AB.
    pose proof (rw_cells_uncut _ _ _ _ _ AB C' ltac:(cbn; lia)) as ABC. exact ABC.
  Qed.

  (* [comment removed for export] *)
  Definition pcells (P : Z) (sw : bool) (maj min lt ext : Z) (nxt bsz buf snapc clean hsz lsw scl : cell) : list cell :=
    [ C8 (Z_to_bv 64 0); nxt; C4 (Z_to_bv 64 (-1)); bsz; buf; CB 12 (repeat (Z_to_bv 8 0) 12); C4 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (P + 648)); C4 (Z_to_bv 64 (Z.b2z sw)); CB 4 (repeat (Z_to_bv 8 0) 4); CB 8 z8; CB 16 (repeat (Z_to_bv 8 0) 16);
      C4 (Z_to_bv 64 maj); C4 (Z_to_bv 64 min); snapc; C4 (Z_to_bv 64 lt); C4 (Z_to_bv 64 ext);
      CB 12 (repeat (Z_to_bv 8 0) 12); C8 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C4 (Z_to_bv 64 0);
      CB 48 fd_pad48; C8 (Z_to_bv 64 0); CB 304 (repeat (Z_to_bv 8 0) 304);
      C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
      CB 72 (repeat (Z_to_bv 8 0) 72); CB 8 z8; C8 (Z_to_bv 64 0); CB 8 z8; clean; hsz; lsw; scl ].
  Definition blank_junk : pcap_junk :=
    mkPJ (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 4) (repeat (Z_to_bv 8 0) 16)
         (repeat (Z_to_bv 8 0) 12) (repeat (Z_to_bv 8 0) 28) fd_pad48 (repeat (Z_to_bv 8 0) 304) (repeat (Z_to_bv 8 0) 72) (Z_to_bv 64 0).

  (* [comment removed for export] *)
  #[using="Type"] Lemma rw_cells_C4_low : forall m A pre w w' post,
    rw_cells asegs m A (pre ++ C4 w :: post) -> le4 w = le4 w' -> rw_cells asegs m A (pre ++ C4 w' :: post).
  Proof.
    intros m A pre w w' post HC E. eapply rw_cells_recell; [exact HC| |].
    - destruct HC as [[WF _] _]. apply cells_wf_app in WF as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn in W2 |- *. exact W2.
    - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite E. reflexivity.
  Qed.
End CANSEC1.
End TwB.
