(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require String ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UPcapXB.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition pcore (p : pcapT) :=
  (pc_self p, pc_rfile p, pc_swapped p, pc_version_major p, pc_version_minor p, pc_snapshot p, pc_linktype p, pc_linktype_ext p,
   pc_tstamp_precision p).
Definition pkeep (p p' : pcapT) : Prop := pcore p' = pcore p /\ pc_priv p' = pc_priv p.
(* [comment removed for export] *)
Definition isng (p : pcapT) : bool := match pc_priv p with PrivPcap _ => false | PrivNg _ _ => true end.
(* [comment removed for export] *)
Definition psim (p p' : pcapT) : Prop := pcore p' = pcore p /\ isng p' = isng p.
#[using="Type"] Lemma pkeep_psim p p' : pkeep p p' -> psim p p'.
Proof. intros [A B]. split; [exact A| unfold isng; rewrite B; reflexivity]. Qed.
#[using="Type"] Lemma psim_refl p : psim p p. Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_trans p1 p2 p3 : psim p1 p2 -> psim p2 p3 -> psim p1 p3.
Proof. intros [A1 A2] [B1 B2]. split; congruence. Qed.
#[using="Type"] Lemma psim_set_bufdata dd p : psim p (set_bufdata dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_errbuf m p : psim p (set_errbuf m p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_header h p : psim p (set_header h p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_break_loop v p : psim p (set_break_loop v p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma psim_set_ng p s i s0 i0 : pc_priv p = PrivNg s0 i0 -> psim p (set_ng s i p).
Proof. intros HS. split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]. Qed.
#[using="Type"] Lemma psim_ng p p' s i : psim p p' -> pc_priv p = PrivNg s i -> exists s' i', pc_priv p' = PrivNg s' i'.
Proof. intros [_ E] HS. unfold isng in E. rewrite HS in E. destruct (pc_priv p') as [|s' i']; [discriminate|]. exists s', i'; reflexivity. Qed.
#[using="Type"] Lemma psim_sf p p' s : psim p p' -> pc_priv p = PrivPcap s -> exists s', pc_priv p' = PrivPcap s'.
Proof. intros [_ E] HS. unfold isng in E. rewrite HS in E. destruct (pc_priv p') as [s'|]; [| discriminate]. exists s'; reflexivity. Qed.
#[using="Type"] Lemma psim_bufdata_r p q dd : psim p q -> psim p (set_bufdata dd q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_bufdata]. Qed.
#[using="Type"] Lemma psim_errbuf_r p q m : psim p q -> psim p (set_errbuf m q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_errbuf]. Qed.
#[using="Type"] Lemma psim_header_r p q h : psim p q -> psim p (set_header h q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_header]. Qed.
#[using="Type"] Lemma psim_break_r p q v : psim p q -> psim p (set_break_loop v q). Proof. intros H. eapply psim_trans; [exact H| apply psim_set_break_loop]. Qed.
(* [comment removed for export] *)
End WithCeil.

Ltac psim_tac :=
  repeat first [ apply psim_refl | assumption | (apply pkeep_psim; assumption)
               | apply psim_bufdata_r | apply psim_errbuf_r | apply psim_header_r | apply psim_break_r
               | match goal with H : psim ?a ?b |- psim ?a ?c => apply (psim_trans _ _ _ H); clear H end
               | match goal with H : pkeep ?a ?b |- psim ?a ?c => apply (psim_trans _ _ _ (pkeep_psim _ _ H)); clear H end ];
  match goal with |- psim _ _ => fail "psim_tac" | |- _ => idtac end.
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma pkeep_refl p : pkeep p p. Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_trans p1 p2 p3 : pkeep p1 p2 -> pkeep p2 p3 -> pkeep p1 p3.
Proof. intros [A1 A2] [B1 B2]. split; congruence. Qed.
#[using="Type"] Lemma pkeep_set_bufdata dd p : pkeep p (set_bufdata dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_errbuf m p : pkeep p (set_errbuf m p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_buffer b sz al dd p : pkeep p (set_buffer b sz al dd p). Proof. split; reflexivity. Qed.
#[using="Type"] Lemma pkeep_set_header h p : pkeep p (set_header h p). Proof. split; reflexivity. Qed.
End WithCeil.

#[export] Hint Resolve pkeep_refl pkeep_set_bufdata pkeep_set_errbuf pkeep_set_buffer pkeep_set_header : pk.

Section WithCeil.
(* [comment removed for export] *)
Section ReadingB.
(* [comment removed for export] *)
Variable Uk : UKit.
#[local] Notation G := (uk_G Uk).
#[local] Notation nsafeP := (uk_nsafeP Uk).
#[local] Notation gstepP := (uk_gstepP Uk).
#[local] Notation GK_safe := (uk_GK_safe Uk).
#[local] Notation GK_step := (uk_GK_step Uk).
#[local] Notation HG := (uk_HG Uk).
#[local] Notation HC := (uk_HC Uk).
#[local] Notation HOG := (uk_HOG Uk).
#[local] Notation HOC := (uk_HOC Uk).
#[local] Notation eqbG := (uk_eqbG Uk).
#[local] Notation eqbC := (uk_eqbC Uk).
#[local] Notation segs := (uk_segs Uk).
#[local] Notation hi := (uk_hi Uk).
#[local] Notation PSG := (PState (uk_HG Uk) hptr).
#[local] Notation PSC := (PState (uk_HC Uk) hptr).
#[local] Notation npk := (npeek (uk_segs Uk)).
#[local] Notation relX := (USimX.relX (uk_G Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr)).
#[local] Notation usimS := (usimX (uk_nsafeP Uk) (uk_gstepP Uk) (npeek (uk_segs Uk))).
#[local] Notation RQ := (RelX.RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX := (RelX.RX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RU := (RelX.RU (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_RQ := (RelX.RX_RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_U := (RelX.RX_U (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_G := (RelX.RQ_G (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_C := (RelX.RQ_C (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_minvX := (RelX.RQ_minvX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_halted := (RelX.RQ_halted (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc := (RelX.RQ_libc (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile := (RelX.RQ_outfile (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_mq := (RelX.RQ_mq (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_lci := (RelX.RQ_lci (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_fresh := (RelX.RQ_fresh (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_toks_below := (RelX.RQ_toks_below (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_pot := (RelX.RQ_pot (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation blk_addr_range := (RelX.blk_addr_range (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_same_heap := (RelX.RQ_same_heap (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc_upd := (RelX.RQ_libc_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile_upd := (RelX.RQ_outfile_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_xstep := (RelX.RQ_xstep (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_after := (RelX.RQ_after (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Definition ru_get := @RelX.ru_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_rd_lc := @RelX.ru_rd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_lc := @RelX.ru_upd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_outfile := @RelX.ru_upd_outfile (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_heap_op := @RelX.ru_heap_op (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
Arguments ru_heap_op {A}.
#[local] Definition ru_heap_opu := @RelX.ru_heap_opu (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pmalloc := @RelX.ru_pmalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pcalloc := @RelX.ru_pcalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_prealloc := @RelX.ru_prealloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pfree := @RelX.ru_pfree (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_sys := @RelX.ru_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
Arguments ru_sys {A}.
#[local] Definition ru_read := @RelX.ru_read (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_readv := @RelX.ru_readv (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_exit := @RelX.ru_exit (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_bind := @RelX.ru_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind {A B}.
#[local] Definition ru_bind2 := @RelX.ru_bind2 (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind2 {A B A' B'}.
#[local] Definition ru_seq := @RelX.ru_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_seq {A B A' B'}.
#[local] Definition ru_ret := @RelX.ru_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_ret {A}.
#[local] Definition ru_post := @RelX.ru_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_post {A}.
#[local] Definition ru_pre := @RelX.ru_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_pre {A B}.
#[local] Definition ru_munr := @RelX.ru_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_munr {A B}.
#[local] Definition ru_use := @RelX.ru_use (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_use {A B}.
#[local] Definition ru_bind_retl := @RelX.ru_bind_retl (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind_retl {A B}.
#[local] Definition usim_pure := @usimX_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pure {A B}.
#[local] Definition usim_exI := @usimX_exI (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_exI {A B X}.
#[local] Definition usim_ret := @usimX_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_ret {A B}.
#[local] Definition usim_get := @usimX_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_upd := @usimX_upd (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_post := @usimX_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_post {A B}.
#[local] Definition usim_pre := @usimX_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pre {A B}.
#[local] Definition usim_conseq := @usimX_conseq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_conseq {A B}.
#[local] Definition usim_munr := @usimX_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_munr {A B}.
#[local] Definition usim_false := @usimX_false (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_false {A B}.
#[local] Definition usim_if := @usimX_if (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_if {A B}.
#[local] Definition usim_pointwise := @usimX_pointwise (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pointwise {A B}.
#[local] Definition usim_sys := @usimX_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_sys {A B}.
#[local] Definition usim_of_paths := @usimX_of_paths (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_of_paths {A B}.
#[local] Definition usim_bind := @usimX_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind {A B A' B'}.
#[local] Definition usim_seq := @usimX_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_seq {A B A' B'}.
#[local] Definition usim_bind_eq := @usimX_bind_eq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind_eq {A A' B'}.
#[local] Definition usim_loopV := @usimX_loopV (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_loopV {X Y A B}.
(* [comment removed for export] *)
#[local] Notation framed I R := (framedX I R) (only parsing).
#[local] Definition usim_ND := fun A B p => @usimX_ND (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) A B p.
Arguments usim_ND {A B}.
#[local] Notation FOG := (uk_FOG Uk).
#[local] Notation FOC := (uk_FOC Uk).
#[local] Notation RQ_siteG := (RelX.RQ_siteG (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Notation finsens := (RelX.finsens (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Definition usim_fenter := @RelX.usimX_fenter (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fenter {A B}.
#[local] Definition usim_fret_of_ret := @RelX.usimX_fret_of_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fret_of_ret {A B}.
#[local] Definition finsens_RX := @RelX.finsens_RX (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_pure := @RelX.finsens_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_ex := @RelX.finsens_ex (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments finsens_ex {X}.
#[local] Definition finsens_mo := @RelX.finsens_mo (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
(* [comment removed for export] *)
Ltac fins_head t := lazymatch t with ?f _ => fins_head f | _ => t end.
Ltac fins :=
  lazymatch goal with
  | |- RelX.finsens _ _ _ _ _ _ _ _ _ ?R =>
      first [ apply finsens_RX; let s := fresh in let s' := fresh in let mo := fresh in let EL := fresh in let EO := fresh in let HU := fresh in
              intros s s' mo EL EO HU; unfold UK in *; rewrite EL, EO; exact HU
            | apply finsens_ex; intro; fins
            | apply finsens_pure; fins
            | apply finsens_mo; fins
            | let h := fins_head R in unfold h; fins ]
  end.
(* [comment removed for export] *)
Ltac xfe := try (apply usim_fenter; [solve [fins]|]).
Ltac xfr := xfe; try (apply usim_fret_of_ret; [solve [fins]|]).
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).
#[local] Notation PR_G := (prims HOG FOG stkG).
#[local] Notation PR_C := (prims HOC FOC stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).
#[local] Notation P0 := (rc_P0 rc).
#[local] Notation PA := (PA rc).

#[using="Type"] Lemma VIF_pkeep p p' : pkeep p p' -> VIF p' = VIF p.
Proof. intros [_ E]. unfold VIF. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Definition RPP nx (tm : gmap N Z) (pt : Z) (off pos : Z) : relX := RUK tm nx pt (KR_ off) Cc idl (WF oh hs (FR_ off pos)).
Definition PST {A} (Φ : A -> pcapT -> Z -> Z -> Prop) : A -> A -> relX :=
  eqpost (fun r => fun gh sG moG sC moC => exists p' tm' nx' pt' off' pos',
            Φ r p' pos' pt' /\ PI p' pos' /\ TML tm' (toks p') /\ RPP nx' tm' pt' off' pos' gh sG moG sC moC).

#[using="Type"] Lemma pp_ret {A} (Φ : A -> pcapT -> Z -> Z -> Prop) nx p tm pt off pos (r : A) :
  Φ r p pos pt -> PI p pos -> TML tm (toks p) -> usimS (RPP nx tm pt off pos) (mret r) (mret r) (PST Φ).
Proof. intros H1 H2 H3. xfr; apply ru_ret. intros gh sG moG sC moC HR. exists p, tm, nx, pt, off, pos. auto. Qed.

#[using="Type"] Lemma pp_bind {A B'} (Φ : A -> pcapT -> Z -> Z -> Prop) nx tm pt off pos (m : Monad.M PSG A) (m' : Monad.M PSC A) (k : A -> Monad.M PSG B') (k' : A -> Monad.M PSC B') Q :
  usimS (RPP nx tm pt off pos) m m' (PST Φ) ->
  (forall r p' tm' nx' pt' off' pos', Φ r p' pos' pt' -> PI p' pos' -> TML tm' (toks p') -> usimS (RPP nx' tm' pt' off' pos') (k r) (k' r) Q) ->
  usimS (RPP nx tm pt off pos) (mbind m k) (mbind m' k') Q.
Proof.
  intros H1 H2. eapply ru_bind; [exact H1|]. intros r.
  eapply usim_exI; intros p'. eapply usim_exI; intros tm'. eapply usim_exI; intros nx'. eapply usim_exI; intros pt'. eapply usim_exI; intros off'. eapply usim_exI; intros pos'.
  eapply ru_pre; [| intros ? ? ? ? ? (X1 & X2 & X3 & X4); exact (conj X1 (conj X2 (conj X3 X4)))].
  apply usim_pure; intros X1. apply usim_pure; intros X2. apply usim_pure; intros X3. exact (H2 _ _ _ _ _ _ _ X1 X2 X3).
Qed.

#[using="Type"] Lemma pp_post {A} (Φ Φ' : A -> pcapT -> Z -> Z -> Prop) R (m : Monad.M PSG A) (m' : Monad.M PSC A) :
  usimS R m m' (PST Φ) -> (forall r p pos pt, Φ r p pos pt -> PI p pos -> Φ' r p pos pt) -> usimS R m m' (PST Φ').
Proof.
  intros H HI. eapply ru_post; [exact H|]. intros r ? ? ? ? ? (p' & tm' & nx' & pt' & off' & pos' & X1 & X2 & X3 & X4). exists p', tm', nx', pt', off', pos'. auto 6.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pp_keep {A} (Φ : A -> pcapT -> Z -> Z -> Prop) nx p tm pt off pos (m : Monad.M PSG A) (m' : Monad.M PSC A) :
  usimS (RPP nx tm pt off pos) m m' (eqpost (fun r => fun gh sG moG sC moC => Φ r p pos pt /\ RPP nx tm pt off pos gh sG moG sC moC)) ->
  PI p pos -> TML tm (toks p) -> usimS (RPP nx tm pt off pos) m m' (PST Φ).
Proof.
  intros H H2 H3. eapply ru_post; [exact H|]. intros r ? ? ? ? ? [X HR]. exists p, tm, nx, pt, off, pos. auto.
Qed.

#[using="Type"] Lemma toks_set_buffer_perm p b al sz dd :
  Permutation ((b, al) :: lrm (pc_buffer p) (toks p)) (toks (set_buffer b sz al dd p)).
Proof. unfold UPcapXA.toks. rewrite lrm_head. cbn. unfold psize, ifas. cbn. reflexivity. Qed.

#[using="Type"] Lemma PI_set_buffer p pos b sz al dd : PI p pos -> 1 <= al <= BUFMAX -> 1 <= sz <= BUFMAX -> PI (set_buffer b sz al dd p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4] Hal Hsz. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_bufdata p pos dd : PI p pos -> PI (set_bufdata dd p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_errbuf p pos m : PI p pos -> PI (set_errbuf m p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_set_header p pos h : PI p pos -> PI (set_header h p) pos.
Proof. intros [P1 P2 P2' P3 P3' P4]. constructor; cbn; auto. Qed.
#[using="Type"] Lemma PI_pos_mono p pos pos' : PI p pos -> pos <= pos' <= Z.of_nat (length d) -> PI p pos'.
Proof.
  intros [P1 P2 P2' P3 P3' P4] Hp. constructor; auto; [lia|]. destruct (pc_priv p) as [|s i]; [exact P4|]. destruct P4 as (A1 & A2 & A3 & A4 & A5). split; [lia|]. split; [lia|]. exact (conj A3 (conj A4 A5)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_read_bytes (p : pcapT) (pos : Z) (pt : Z) (n : Z) (r : rb_status * list Z) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  pt' = pt /\ p' = p /\ zlength (snd r) <= n /\ pos' = pos + zlength (snd r) /\
  match fst r with RBS_Ok => zlength (snd r) = n | RBS_Eof => zlength (snd r) = 0 | RBS_Err m => mok m end /\
  snd r = dsl d pos (zlength (snd r)).

#[using="STK RCW"] Lemma pr_read_bytes nx p tm pt off pos dst n foe :
  PI p pos -> TML tm (toks p) -> rdest_ok p dst n -> 0 <= n < 2^40 ->
  usimS (RPP nx tm pt off pos) (read_bytes MOps PR_G fp dst n foe) (read_bytes MOps PR_C fp dst n foe) (PST (Q_read_bytes p pos pt n)).
Proof.
  intros HPI HT HD Hn. unfold read_bytes. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
  eapply ru_bind.
  { eapply ru_post; [apply (pr_fread Uk stkG stkC STK rc RCW nx p tm pt off pos dst n HPI HT HD Hn)|]. intros r ? ? ? ? ? X. exact X. }
  intros got. eapply usim_exI; intros off'. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4).
  assert (HPI' : PI p (pos + zlength got)).
  { apply (PI_pos_mono p pos); [exact HPI|]. pose proof (zlength_nonneg got). lia. }
  destruct (negb (zlength got =? n)) eqn:EN.
  - eapply ruk_bind with (K1 := fun _ => KR_ off') (C1 := fun _ => Cc) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (FR_ off' (pos + zlength got))); [apply (pr_ferror Uk stkG stkC rc RCW nx)|].
    intros e ->. cbn beta iota.
    destruct ((zlength got =? 0) && negb foe) eqn:EZ.
    + xfr; apply (pp_ret _ nx p tm pt off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
      apply andb_prop in EZ as [EZ _]. apply Z.eqb_eq in EZ. exact (conj EZ Q4).
    + xfr; apply (pp_ret _ nx p tm pt off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| split; [mok_tac| exact Q4]].
  - apply negb_false_iff in EN. apply Z.eqb_eq in EN.
    xfr; apply (pp_ret _ nx p tm pt off'); [| exact HPI'| exact HT]. unfold Q_read_bytes. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity| exact (conj EN Q4)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_grow (p : pcapT) (pos pt sz : Z) (r : bool * pcapT) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  p' = snd r /\ pos' = pos /\ pkeep p p' /\ (fst r = true -> pc_bufsize p' = sz /\ pc_bufalloc p' = sz) /\ pt' = pt + sz.

#[using="RCW"] Lemma pr_grow_buffer nx p tm pt off pos sz :
  PI p pos -> TML tm (toks p) -> 1 <= sz <= BUFMAX -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (grow_buffer MOps PR_G p sz) (grow_buffer MOps PR_C p sz) (PST (Q_grow p pos pt sz)).
Proof.
  intros HPI HT Hsz HPA. unfold grow_buffer. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc prims]; xfe.
  destruct (RP_budget rc RCW p pos tm sz HPI HT ltac:(lia)) as (R1 & R2 & R3).
  destruct (RP_live rc RCW p pos tm sz HPI HT ltac:(lia)) as (L1 & L2 & L3).
  destruct (PA_pot0 rc RCW p pos pt sz HPA HPI ltac:(lia)) as [V1 V2].
  eapply ru_bind.
  { apply (gr_realloc Uk tm (toks p) nx pt _ _ _ (pc_buffer p) (pc_bufalloc p) sz HT (toks_buf rc p)); [| unfold BUFMAX in Hsz; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2| exact V1| exact V2| exact L1| rewrite <- (live1_TML _ _ HT); exact L2].
    unfold UPcapXA.toks. rewrite !zlen_cons, zlen_app, zlen_cons. pose proof (rw_B _ RCW) as (BL & _). destruct (ifas_R63N rc p pos HPI) as [_ IL]. lia. }
  intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
  xfr; eapply (pp_ret _ (N.succ nx) (set_buffer nx sz sz (zfirstn sz (pc_bufdata p)) p) _ (pt + sz) off pos).
  - unfold Q_grow. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [apply pkeep_set_buffer|]. split; [intros _; split; reflexivity| reflexivity].
  - apply PI_set_buffer; [exact HPI| exact Hsz| lia].
  - eapply TML_perm; [exact HT'| apply toks_set_buffer_perm].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_read_block (p : pcapT) (pos : Z) (rb : block_result) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  pkeep p p' /\ pos <= pos' /\
  match rb with
  | RB_Ok c p'' => p'' = p' /\ (exists tl, 12 <= tl /\ pos' = pos + tl /\ cur_off c = 8 /\ cur_remaining c = tl - 12) /\ PA false p' pos' pt'
  | RB_Eof p'' => p'' = p' /\ PA true p' pos' pt'
  | RB_Err m p'' => p'' = p' /\ mok m /\ PA true p' pos' pt'
  end.

#[using="Type"] Lemma PA_keep sl sl' p p' pos pos' pt : PA sl p pos pt -> pkeep p p' -> pos <= pos' -> (sl = true -> sl' = true) -> PA sl' p' pos' pt.
Proof.
  intros H [_ E] L Hs. assert (EV : VIF p = VIF p') by (unfold VIF; rewrite E; reflexivity).
  destruct sl'; [apply PA_slack with (sl := sl)|destruct sl; [discriminate (Hs eq_refl)|]]; eapply PA_mono; eauto.
Qed.

#[using="STK RCW"] Lemma pr_read_block nx p tm pt off pos a_bhdr :
  PI p pos -> TML tm (toks p) -> rdest_ok p a_bhdr 8 -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (read_block MOps PR_G a_bhdr p) (read_block MOps PR_C a_bhdr p) (PST (Q_read_block p pos)).
Proof.
  intros HPI HT HD HPA. unfold read_block. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe. rewrite (pi_fp _ _ _ HPI).
  eapply pp_bind; [apply (pr_read_bytes nx p tm pt off pos a_bhdr 8 false HPI HT HD ltac:(lia))|].
  intros [st bh] p1 tm1 nx1 pt1 off1 pos1 (-> & -> & LB & -> & ST & CT) HPI1 HT1. cbn [fst snd] in *. pose proof (zlength_nonneg bh) as NB.
  assert (PAK : forall pos', pos <= pos' -> PA true p pos' pt) by (intros pos' L; eapply PA_keep; [exact HPA| apply pkeep_refl| exact L| discriminate]).
  destruct st as [| |m].
  2:{ xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| apply PAK; lia]]. }
  2:{ xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| split; [exact ST| apply PAK; lia]]]. }
  cbn in ST. rewrite !ST in *. cbv zeta.
  set (bt := if pc_swapped p then bswap32 (get_le32 bh 0) else get_le32 bh 0).
  set (tl := if pc_swapped p then bswap32 (get_le32 bh 4) else get_le32 bh 4).
  destruct (tl <? 12) eqn:ETL. { xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| split; [mok_tac| apply PAK; lia]]]. }
  apply Z.ltb_ge in ETL.
  destruct (negb (tl mod 4 =? 0)). { xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. split; [apply pkeep_refl|]. split; [lia| split; [reflexivity| split; [mok_tac| apply PAK; lia]]]. }
  (* [comment removed for export] *)
  eapply (pp_bind (fun r p' pos' pt' => pos' = pos + 8 /\ pkeep p p' /\ p' = snd r /\ (fst r = None -> tl <= BUFMAX) /\ (forall m, fst r = Some m -> mok m) /\ pt <= pt' <= pt + Z.min tl BUFMAX)).
  { destruct (pc_bufsize p <? tl) eqn:EBS.
    - destruct (ng_max_blocksize (ng_of p) <? tl) eqn:EM.
      + xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. cbn [fst snd]. split; [lia|]. split; [apply pkeep_refl|]. split; [reflexivity|]. split; [intros; discriminate|]. split; [intros m X; injection X as <-; mok_tac| unfold BUFMAX; lia].
      + apply Z.ltb_ge in EM.
        assert (TLB : 1 <= tl <= BUFMAX).
        { destruct HPI1 as [_ _ _ _ _ NG]. unfold ng_of in EM. destruct (pc_priv p) as [|sng i]; cbn in EM; [unfold BUFMAX; lia|]. destruct NG as (_ & _ & _ & _ & MB). lia. }
        cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_realloc prims]; xfe.
        (* [comment removed for export] *)
        destruct (RP_budget rc RCW p (pos + 8) tm1 tl HPI1 HT1 ltac:(lia)) as (R1 & R2 & R3).
        destruct (RP_live rc RCW p (pos + 8) tm1 tl HPI1 HT1 ltac:(lia)) as (L1 & L2 & L3).
        destruct (PA_pot0 rc RCW p pos pt tl HPA HPI ltac:(lia)) as [V1 V2].
        eapply ru_bind.
        { apply (gr_realloc Uk tm1 (toks p) nx1 pt _ _ _ (pc_buffer p) (pc_bufalloc p) tl HT1 (toks_buf rc p)); [| unfold BUFMAX in TLB; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT1)); exact R2| exact V1| exact V2| exact L1| rewrite <- (live1_TML _ _ HT1); exact L2].
          unfold UPcapXA.toks. rewrite !zlen_cons, zlen_app, zlen_cons. pose proof (rw_B _ RCW) as (BL & _). destruct (ifas_R63N rc p _ HPI1) as [_ IL]. lia. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        xfr; eapply (pp_ret _ (N.succ nx1) (set_buffer nx1 (pc_bufsize p) tl (zfirstn tl (pc_bufdata p)) p) _ (pt + tl) off1 (pos + 8)).
        * cbn [fst snd]. split; [lia|]. split; [apply pkeep_set_buffer|]. split; [reflexivity|]. split; [intros _; lia|]. split; [intros; discriminate| pose proof (Z.le_min_l tl BUFMAX); pose proof (Z.min_glb tl BUFMAX tl); unfold BUFMAX in *; lia].
        * apply PI_set_buffer; [exact HPI1| exact TLB| exact (pi_bsz _ _ _ HPI1)].
        * eapply TML_perm; [exact HT'| apply toks_set_buffer_perm].
    - apply Z.ltb_ge in EBS. pose proof (pi_bsz _ _ _ HPI1) as BSZ.
      xfr; apply (pp_ret _ nx1 p tm1 pt off1); [| exact HPI1| exact HT1]. cbn [fst snd]. split; [lia|]. split; [apply pkeep_refl|]. split; [reflexivity|]. split; [intros _; lia|]. split; [intros; discriminate| pose proof (Z.le_min_l tl BUFMAX); pose proof (Z.min_glb tl BUFMAX tl); unfold BUFMAX in *; lia]. }
  intros [gerr p2] p2' tm2 nx2 pt2 off2 pos2 (-> & PK2 & E2 & TLB & MOK & PT2) HPI2 HT2. cbn [fst snd] in *. subst p2'.
  (* [comment removed for export] *)
  assert (PA2 : forall sl p' pos', pkeep p p' -> pos + 8 <= pos' -> (sl = false -> tl <= 2 * (pos' - pos)) -> PA sl p' pos' pt2).
  { intros sl p' pos' [_ EP] LP Hsl. destruct HPA as [A1 A2]. assert (EV : VIF p' = VIF p) by (unfold VIF; rewrite EP; reflexivity).
    unfold UPcapXA.PA. rewrite EV. pose proof (Z.le_min_l tl BUFMAX). pose proof (Z.le_min_r tl BUFMAX). destruct sl; [split; lia|]. specialize (Hsl eq_refl). split; lia. }
  destruct gerr as [m|].
  { xfr; apply (pp_ret _ nx2 p2 tm2 pt2 off2); [| exact HPI2| exact HT2]. split; [exact PK2|]. split; [lia| split; [reflexivity| split; [exact (MOK m eq_refl)| apply PA2; [exact PK2| lia| discriminate]]]]. }
  specialize (TLB eq_refl).
  cbv zeta.
  set (p3 := set_bufdata (le_bytes 4 bt ++ le_bytes 4 tl) p2).
  assert (HPI3 : PI p3 (pos + 8)) by (apply PI_set_bufdata; exact HPI2).
  assert (HT3 : TML tm2 (toks p3)) by exact HT2.
  rewrite <- (pi_fp _ _ _ HPI2).
  replace (pc_rfile p2) with (pc_rfile p3) by reflexivity.
  rewrite (pi_fp _ _ _ HPI3).
  eapply pp_bind; [apply (pr_read_bytes nx2 p3 tm2 pt2 off2 (pos + 8) (DHeap (pc_buffer p3) 8) (tl - 8) true HPI3 HT3); [cbn; split; [reflexivity| unfold BUFMAX in TLB; lia]| unfold BUFMAX in TLB; lia]|].
  intros [st2 data] p4 tm4 nx4 pt4 off4 pos4 (-> & -> & LB2 & -> & ST2 & CT2) HPI4 HT4. cbn [fst snd] in *. pose proof (zlength_nonneg data) as ND2.
  set (p5 := set_bufdata (pc_bufdata p3 ++ data) p3).
  assert (HPI5 : PI p5 (pos + 8 + zlength data)) by (apply PI_set_bufdata; exact HPI4).
  assert (PK5 : pkeep p p5) by (eapply pkeep_trans; [exact PK2|]; split; reflexivity).
  destruct st2 as [| |m2].
  2:{ xfr; apply (pp_ret _ nx4 p5 tm4 pt2 off4); [| exact HPI5| exact HT4]. split; [exact PK5|]. split; [lia| split; [reflexivity| split; [mok_tac| apply PA2; [exact PK5| lia| discriminate]]]]. }
  2:{ xfr; apply (pp_ret _ nx4 p5 tm4 pt2 off4); [| exact HPI5| exact HT4]. split; [exact PK5|]. split; [lia| split; [reflexivity| split; [cbn in ST2; exact ST2| apply PA2; [exact PK5| lia| discriminate]]]]. }
  cbv zeta.
  set (p6 := if pc_swapped p5 then set_bufdata (swap_field 4 (tl - 4) (pc_bufdata p5)) p5 else p5).
  assert (HPI6 : PI p6 (pos + 8 + zlength data)) by (subst p6; destruct (pc_swapped p5); [apply PI_set_bufdata|]; exact HPI5).
  assert (HT6 : TML tm4 (toks p6)) by (subst p6; destruct (pc_swapped p5); exact HT4).
  assert (PK6 : pkeep p p6) by (subst p6; destruct (pc_swapped p5); [eapply pkeep_trans; [exact PK5| split; reflexivity]| exact PK5]).
  destruct (negb (tl =? get_le32 (pc_bufdata p6) (tl - 4))).
  - xfr; apply (pp_ret _ nx4 p6 tm4 pt2 off4); [| exact HPI6| exact HT6]. split; [exact PK6|]. split; [lia| split; [reflexivity| split; [mok_tac| apply PA2; [exact PK6| lia| discriminate]]]].
  - cbn in ST2. xfr; apply (pp_ret _ nx4 p6 tm4 pt2 off4); [| exact HPI6| exact HT6]. split; [exact PK6|]. split; [lia|]. split; [reflexivity|]. split.
    + exists tl. cbn. split; [lia|]. split; [lia|]. split; reflexivity.
    + apply PA2; [exact PK6| lia| intros _; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma lor_lt_pow2 a b m : 0 <= a < 2 ^ m -> 0 <= b < 2 ^ m -> 0 <= m -> 0 <= Z.lor a b < 2 ^ m.
Proof.
  intros Ha Hb Hm. pose proof (proj2 (Z.lor_nonneg a b) (conj (proj1 Ha) (proj1 Hb))) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|NA]; [rewrite Z.lor_0_l; lia|]. destruct (Z.eq_dec b 0) as [->|NB]; [rewrite Z.lor_0_r; lia|].
  assert (L : 0 < Z.lor a b). { destruct (Z.eq_dec (Z.lor a b) 0) as [E|]; [| lia]. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [exact L|]. rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

#[using="Type"] Lemma roundup_pow2_small v : 1 <= v <= 2^27 -> 1 <= roundup_pow2_u32 v <= 2^27.
Proof.
  intros Hv. unfold roundup_pow2_u32. cbv zeta.
  assert (U : forall x, 0 <= x < 2^32 -> Prelim.u32 x = x) by (intros x Hx; unfold Prelim.u32; apply Z.mod_small; lia).
  rewrite (U (v - 1)) by lia.
  assert (STEP : forall n k, 0 <= n < 2^27 -> 0 <= k -> 0 <= Z.lor n (Z.shiftr n k) < 2^27).
  { intros n k Hn Hk. apply lor_lt_pow2; [lia| | lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia. }
  pose proof (STEP (v - 1) 1 ltac:(lia) ltac:(lia)) as S1. set (n1 := Z.lor (v - 1) (Z.shiftr (v - 1) 1)) in *.
  pose proof (STEP n1 2 S1 ltac:(lia)) as S2. set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
  pose proof (STEP n2 4 S2 ltac:(lia)) as S3. set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
  pose proof (STEP n3 8 S3 ltac:(lia)) as S4. set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
  pose proof (STEP n4 16 S4 ltac:(lia)) as S5. set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
  rewrite (U (n5 + 1)); lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma roundup_pow2_le2 v : 1 <= v <= 2^27 -> roundup_pow2_u32 v <= 2 * v.
Proof.
  intros Hv. unfold roundup_pow2_u32. cbv zeta.
  assert (U : forall x, 0 <= x < 2^32 -> Prelim.u32 x = x) by (intros x Hx; unfold Prelim.u32; apply Z.mod_small; lia).
  rewrite (U (v - 1)) by lia.
  destruct (Z.eq_dec v 1) as [->|NE].
  { vm_compute. discriminate. }
  set (m := Z.log2 (v - 1) + 1).
  destruct (Z.log2_spec (v - 1) ltac:(lia)) as [LO HI]. rewrite <- Z.add_1_r in HI. fold m in HI.
  assert (Hm : 0 <= m) by (pose proof (Z.log2_nonneg (v - 1)); lia).
  assert (HM : 2 ^ m <= 2 * (v - 1)) by (unfold m; rewrite Z.pow_succ_r by (apply Z.log2_nonneg); lia).
  assert (M32 : 2 ^ m <= 2^28) by lia.
  assert (STEP : forall n k, 0 <= n < 2^m -> 0 <= k -> 0 <= Z.lor n (Z.shiftr n k) < 2^m).
  { intros n k Hn Hk. apply lor_lt_pow2; [lia| | lia]. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). nia. }
  pose proof (STEP (v - 1) 1 ltac:(lia) ltac:(lia)) as S1. set (n1 := Z.lor (v - 1) (Z.shiftr (v - 1) 1)) in *.
  pose proof (STEP n1 2 S1 ltac:(lia)) as S2. set (n2 := Z.lor n1 (Z.shiftr n1 2)) in *.
  pose proof (STEP n2 4 S2 ltac:(lia)) as S3. set (n3 := Z.lor n2 (Z.shiftr n2 4)) in *.
  pose proof (STEP n3 8 S3 ltac:(lia)) as S4. set (n4 := Z.lor n3 (Z.shiftr n3 8)) in *.
  pose proof (STEP n4 16 S4 ltac:(lia)) as S5. set (n5 := Z.lor n4 (Z.shiftr n4 16)) in *.
  rewrite (U (n5 + 1)); lia.
Qed.

(* [comment removed for export] *)
#[using="STK RCW"] Lemma pr_discard_loop nx p tm pt : forall fuel off pos caplen btd br,
  PI p pos -> TML tm (toks p) -> 0 <= btd ->
  usimS (RPP nx tm pt off pos) (discard_loop MOps PR_G fuel fp caplen btd br) (discard_loop MOps PR_C fuel fp caplen btd br)
        (PST (fun _ p' pos' pt' => p' = p /\ pos <= pos' /\ pt' = pt)).
Proof.
  induction fuel as [|fuel IH]; intros off pos caplen btd br HPI HT Hb; cbn [discard_loop]; cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
  - xfr; apply (pp_ret _ nx p tm pt off); [| exact HPI| exact HT]. split; [reflexivity| split; [lia| reflexivity]].
  - destruct (btd =? 0). { xfr; apply (pp_ret _ nx p tm pt off); [| exact HPI| exact HT]. split; [reflexivity| split; [lia| reflexivity]]. }
    set (btr := if 4096 <? btd then 4096 else btd).
    assert (Hbtr : 0 <= btr <= 4096 /\ btr <= btd) by (subst btr; destruct (4096 <? btd) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread Uk stkG stkC STK rc RCW nx p tm pt off pos (DStack SiteDiscardBuf 0) btr HPI HT); [cbn; lia| lia]|]. intros r ? ? ? ? ? X; exact X. }
    intros got. eapply usim_exI; intros off'. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4). pose proof (zlength_nonneg got) as NG.
    assert (HPI' : PI p (pos + zlength got)) by (apply (PI_pos_mono p pos); [exact HPI| lia]).
    change (RUK tm nx pt (KR_ off') Cc idl (WF oh hs (FR_ off' (pos + zlength got)))) with (RPP nx tm pt off' (pos + zlength got)).
    destruct (negb (zlength got =? btr)).
    + eapply ru_bind; [apply (pr_read_fail_msg Uk stkG stkC rc RCW nx); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. xfr; apply (pp_ret _ nx p tm pt off'); [| exact HPI'| exact HT]. split; [reflexivity| split; [lia| reflexivity]].
    + eapply pp_post; [apply (IH off' (pos + zlength got)); [exact HPI'| exact HT| lia]|]. cbn. intros ? ? ? ? (-> & LE & ->) _. split; [reflexivity| split; [lia| reflexivity]].
Qed.

Definition Q_next (p : pcapT) (pos : Z) (r : Z * pkthdr * pcapT) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (0 < fst (fst r) -> pos < pos') /\ PA (negb (0 <? fst (fst r))) p' pos' pt'.

#[using="STK RCW"] Lemma pr_pcap_next_packet nx p tm pt off pos s :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivPcap s -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (pcap_next_packet MOps PR_G p) (pcap_next_packet MOps PR_C p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HS HPA. unfold pcap_next_packet. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe. rewrite (pi_fp _ _ _ HPI).
  unfold sf_of. rewrite HS.
  (* [comment removed for export] *)
  assert (PAE : forall p' pos' pt', psim p p' -> pos <= pos' -> pt <= pt' <= pt + BUFMAX -> PA true p' pos' pt').
  { intros p' pos' pt' [_ EQ] LP PT. destruct HPA as [A1 A2]. unfold UPcapXA.PA.
    assert (EV : VIF p' = VIF p). { unfold VIF, isng in *. rewrite HS in EQ |- *. destruct (pc_priv p'); [reflexivity| discriminate EQ]. }
    rewrite EV. split; lia. }
  assert (HH : sf_hdrsize s = 16 \/ sf_hdrsize s = 24) by (pose proof (pi_ng _ _ _ HPI) as NG; rewrite HS in NG; exact NG).
  assert (HH' : 1 <= sf_hdrsize s <= 24) by lia.
  pose proof (pi_snap _ _ _ HPI) as SNAP. rewrite HS in SNAP.
  eapply ru_bind.
  { eapply ru_post; [apply (pr_fread Uk stkG stkC STK rc RCW nx p tm pt off pos (DStack SiteSfHdr 0) (sf_hdrsize s) HPI HT); [cbn; lia| lia]|]. intros r ? ? ? ? ? X; exact X. }
  intros hb. eapply usim_exI; intros off1. apply usim_pure; intros (Q1 & Q2 & Q3 & Q4). pose proof (zlength_nonneg hb) as NHB.
  assert (HPI1 : PI p (pos + zlength hb)) by (apply (PI_pos_mono p pos); [exact HPI| lia]).
  change (RUK tm nx pt (KR_ off1) Cc idl (WF oh hs (FR_ off1 (pos + zlength hb)))) with (RPP nx tm pt off1 (pos + zlength hb)).
  cbv zeta.
  destruct (negb (zlength hb =? sf_hdrsize s)) eqn:EH.
  { (* [comment removed for export] *)
    eapply ruk_bind with (K1 := fun _ => KR_ off1) (C1 := fun _ => Cc) (g1 := fun _ => idl) (W1 := fun _ => WF oh hs (FR_ off1 (pos + zlength hb))); [apply (pr_ferror Uk stkG stkC rc RCW nx)|].
    intros e ->. cbn beta iota.
    destruct (negb (zlength hb =? 0)).
    - xfr; apply (pp_ret _ nx (set_errbuf (Msg.trunc_header (sf_hdrsize s) (zlength hb)) p) tm pt off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; apply pkeep_set_errbuf| lia| unfold BUFMAX; lia].
    - xfr; apply (pp_ret _ nx p tm pt off1); [| exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_refl|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply psim_refl| lia| unfold BUFMAX; lia]. }
  apply negb_false_iff in EH. apply Z.eqb_eq in EH.
  assert (HBok : bytes_ok hb) by (rewrite Q4; apply dsl_bytes).
  assert (SWB : forall v, 0 <= v < 2^32 -> 0 <= (if pc_swapped p then bswap32 v else v) < 2^32) by (intros v Hv; destruct (pc_swapped p); [apply bswap32_range| exact Hv]).
  (* [comment removed for export] *)
  match goal with |- context [let '(caplen, len) := ?cl in _] => destruct cl as [caplen len] eqn:ECL end.
  assert (CL0 : 0 <= caplen < 2^32 /\ 0 <= len < 2^32).
  { pose proof (SWB _ (get_le32_range hb 8 HBok)) as B8. pose proof (SWB _ (get_le32_range hb 12 HBok)) as B12.
    destruct (sf_lengths_swapped s); try destruct (_ <=? _); injection ECL as E1 E2; lia. }
  cbv zeta.
  destruct (max_snaplen_for_dlt (pc_linktype p) <? caplen) eqn:EMX.
  { destruct (pc_snapshot p <? caplen).
    - xfr; apply (pp_ret _ nx (set_errbuf (Msg.invalid_caplen_snaplen caplen (pc_snapshot p)) p) tm pt off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; apply pkeep_set_errbuf| lia| unfold BUFMAX; lia].
    - xfr; apply (pp_ret _ nx (set_errbuf (Msg.invalid_caplen_maximum caplen (max_snaplen_for_dlt (pc_linktype p))) p) tm pt off1); [| apply PI_set_errbuf; exact HPI1| exact HT]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; apply pkeep_set_errbuf|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; apply pkeep_set_errbuf| lia| unfold BUFMAX; lia]. }
  apply Z.ltb_ge in EMX.
  assert (CAPB : caplen <= 2^27) by (unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN in EMX; destruct (pc_linktype p =? DLT_DBUS); [lia|]; destruct (pc_linktype p =? DLT_EBHSCR); [lia|]; destruct (pc_linktype p =? DLT_USBPCAP); lia).
  destruct (pc_snapshot p <? caplen) eqn:ESC.
  - apply Z.ltb_lt in ESC.
    (* [comment removed for export] *)
    assert (HPA1 : PA false p (pos + zlength hb) pt) by (eapply PA_mono; [exact HPA| lia| reflexivity]).
    eapply (pp_bind (fun r p' pos' pt' => pos' = pos + zlength hb /\ pkeep p p' /\ snd r = p' /\ pt <= pt' <= pt + pc_snapshot p)).
    { destruct (pc_bufsize p <? caplen).
      - eapply pp_post; [apply (pr_grow_buffer nx p tm pt off1 _ (pc_snapshot p) HPI1 HT); [unfold BUFMAX; lia| exact HPA1]|]. unfold Q_grow. cbn. intros [ok p'] ? ? ? (-> & -> & PK & _ & ->) _. split; [reflexivity|]. split; [exact PK|]. split; [reflexivity| lia].
      - xfr; apply (pp_ret _ nx p tm pt off1); [| exact HPI1| exact HT]. cbn. split; [reflexivity|]. split; [apply pkeep_refl|]. split; [reflexivity| lia]. }
    intros [ok p1] p1' tm1 nx1 pt1 off2 pos1 (-> & PK1 & E1 & PT1) HPI2 HT1. cbn [fst snd] in E1. subst p1'.
    destruct (negb ok). { xfr; apply (pp_ret _ nx1 p1 tm1 pt1 off2); [| exact HPI2| exact HT1]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; exact PK1|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; exact PK1| lia| unfold BUFMAX; lia]. }
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread Uk stkG stkC STK rc RCW nx1 p1 tm1 pt1 off2 _ (DHeap (pc_buffer p1) 0) (pc_snapshot p) HPI2 HT1); [cbn; split; [reflexivity| lia]| lia]|]. intros r ? ? ? ? ? X; exact X. }
    intros got. eapply usim_exI; intros off3. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg got) as NGT.
    set (p2 := set_bufdata got p1).
    assert (HPI3 : PI p2 (pos + zlength hb + zlength got)) by (apply PI_set_bufdata; apply (PI_pos_mono p1 (pos + zlength hb)); [exact HPI2| lia]).
    assert (HT2 : TML tm1 (toks p2)) by exact HT1.
    assert (PK2 : pkeep p p2) by (eapply pkeep_trans; [exact PK1| apply pkeep_set_bufdata]).
    change (RUK tm1 nx1 pt1 (KR_ off3) Cc idl (WF oh hs (FR_ off3 (pos + zlength hb + zlength got)))) with (RPP nx1 tm1 pt1 off3 (pos + zlength hb + zlength got)).
    destruct (negb (zlength got =? pc_snapshot p)) eqn:EGOT.
    { eapply ru_bind; [apply (pr_read_fail_msg Uk stkG stkC rc RCW nx1); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. xfr; apply (pp_ret _ nx1 (set_errbuf m p2) tm1 pt1 off3); [| apply PI_set_errbuf; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]| lia| unfold BUFMAX; lia]. }
    (* [comment removed for export] *)
    assert (HPA2 : forall p' pos', pkeep p p' -> pos + zlength hb + zlength got <= pos' -> PA false p' pos' pt1).
    { intros p' pos' [_ EP] LP. destruct HPA as [A1 A2]. unfold UPcapXA.PA. replace (VIF p') with (VIF p) by (unfold VIF; rewrite EP; reflexivity).
      apply negb_false_iff in EGOT. apply Z.eqb_eq in EGOT. split; lia. }
    eapply pp_bind; [apply (pr_discard_loop nx1 p2 tm1 pt1 _ off3 (pos + zlength hb + zlength got)); [exact HPI3| exact HT2| lia]|].
    intros r p3 tm3 nx3 pt3 off4 pos3 (-> & LE3 & ->) HPI4 HT3.
    destruct r as [m|[]].
    + xfr; apply (pp_ret _ nx3 (set_errbuf m p2) tm3 pt1 off4); [| apply PI_set_errbuf; exact HPI4| exact HT3]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; [lia|]. split; [lia|]. cbn. eapply PA_slack. apply HPA2; [eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]| lia].
    + match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
      xfr; match goal with |- usimX _ _ _ _ (mret (_, _, ?q)) _ _ => xfr; apply (pp_ret _ nx3 q tm3 pt1 off4) end; [| apply PI_set_bufdata; exact HPI4| exact HT3]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]|]. split; [lia|]. split; [lia|]. cbn. apply HPA2; [eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]| lia].
  - apply Z.ltb_ge in ESC.
    assert (HPA1 : PA false p (pos + zlength hb) pt) by (eapply PA_mono; [exact HPA| lia| reflexivity]).
    pose proof (roundup_pow2_le2 caplen) as RU2.
    eapply (pp_bind (fun r p' pos' pt' => pos' = pos + zlength hb /\ pkeep p p' /\ snd r = p' /\ pt <= pt' <= pt + Z.min (2 * caplen) (2^27))).
    { destruct (pc_bufsize p <? caplen) eqn:EBC.
      - apply Z.ltb_lt in EBC. pose proof (pi_bsz _ _ _ HPI) as BSZ.
        pose proof (roundup_pow2_small caplen ltac:(lia)) as RU. specialize (RU2 ltac:(lia)).
        eapply pp_post; [apply (pr_grow_buffer nx p tm pt off1 _ _ HPI1 HT)|].
        + destruct (pc_snapshot p <? roundup_pow2_u32 caplen) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; unfold BUFMAX; lia.
        + exact HPA1.
        + unfold Q_grow. cbn. intros [ok p'] ? ? ? (-> & -> & PK & _ & ->) _. split; [reflexivity|]. split; [exact PK|]. split; [reflexivity|].
          destruct (pc_snapshot p <? roundup_pow2_u32 caplen) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; (split; [lia| apply (proj1 (Z.add_le_mono_l _ _ _)); apply Z.min_glb; lia]).
      - xfr; apply (pp_ret _ nx p tm pt off1); [| exact HPI1| exact HT]. cbn. pose proof (Z.min_glb (2 * caplen) (2^27) 0). split; [reflexivity|]. split; [apply pkeep_refl|]. split; [reflexivity| lia]. }
    intros [ok p1] p1' tm1 nx1 pt1 off2 pos1 (-> & PK1 & E1 & PT1) HPI2 HT1. cbn [fst snd] in E1. subst p1'.
    pose proof (Z.le_min_r (2 * caplen) (2^27)) as MN1. pose proof (Z.le_min_l (2 * caplen) (2^27)) as MN2.
    destruct (negb ok). { xfr; apply (pp_ret _ nx1 p1 tm1 pt1 off2); [| exact HPI2| exact HT1]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; exact PK1|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; exact PK1| lia| unfold BUFMAX; lia]. }
    eapply ru_bind.
    { eapply ru_post; [apply (pr_fread Uk stkG stkC STK rc RCW nx1 p1 tm1 pt1 off2 _ (DHeap (pc_buffer p1) 0) caplen HPI2 HT1); [cbn; split; [reflexivity| lia]| lia]|]. intros r ? ? ? ? ? X; exact X. }
    intros got. eapply usim_exI; intros off3. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg got) as NGT.
    set (p2 := set_bufdata got p1).
    assert (HPI3 : PI p2 (pos + zlength hb + zlength got)) by (apply PI_set_bufdata; apply (PI_pos_mono p1 (pos + zlength hb)); [exact HPI2| lia]).
    assert (HT2 : TML tm1 (toks p2)) by exact HT1.
    assert (PK2 : pkeep p p2) by (eapply pkeep_trans; [exact PK1| apply pkeep_set_bufdata]).
    change (RUK tm1 nx1 pt1 (KR_ off3) Cc idl (WF oh hs (FR_ off3 (pos + zlength hb + zlength got)))) with (RPP nx1 tm1 pt1 off3 (pos + zlength hb + zlength got)).
    destruct (negb (zlength got =? caplen)) eqn:EGOT.
    { eapply ru_bind; [apply (pr_read_fail_msg Uk stkG stkC rc RCW nx1); mok_tac|].
      intros m. apply usim_pure; intros Mm. cbn beta. xfr; apply (pp_ret _ nx1 (set_errbuf m p2) tm1 pt1 off3); [| apply PI_set_errbuf; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]|]. split; [lia|]. split; [lia|]. cbn. apply PAE; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_errbuf]| lia| unfold BUFMAX; lia]. }
    match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
    xfr; match goal with |- usimX _ _ _ _ (mret (_, _, ?q)) _ _ => xfr; apply (pp_ret _ nx1 q tm1 pt1 off3) end; [| apply PI_set_bufdata; exact HPI3| exact HT2]. unfold Q_next; cbn [fst snd]. split; [reflexivity|]. split; [apply pkeep_psim; eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]|]. split; [lia|]. split; [lia|]. cbn.
    (* [comment removed for export] *)
    destruct HPA as [A1 A2]. unfold UPcapXA.PA. rewrite (VIF_pkeep p) by (eapply pkeep_trans; [exact PK2| apply pkeep_set_bufdata]).
    apply negb_false_iff in EGOT. apply Z.eqb_eq in EGOT. split; lia.
Qed.

End ReadingB.

End WithCeil.
End UPcapXB.

(* [comment removed for export] *)
Module UPcapXC.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

Section WithCeil.
(* [comment removed for export] *)
Section ReadingC.
(* [comment removed for export] *)
Variable Uk : UKit.
#[local] Notation G := (uk_G Uk).
#[local] Notation nsafeP := (uk_nsafeP Uk).
#[local] Notation gstepP := (uk_gstepP Uk).
#[local] Notation GK_safe := (uk_GK_safe Uk).
#[local] Notation GK_step := (uk_GK_step Uk).
#[local] Notation HG := (uk_HG Uk).
#[local] Notation HC := (uk_HC Uk).
#[local] Notation HOG := (uk_HOG Uk).
#[local] Notation HOC := (uk_HOC Uk).
#[local] Notation eqbG := (uk_eqbG Uk).
#[local] Notation eqbC := (uk_eqbC Uk).
#[local] Notation segs := (uk_segs Uk).
#[local] Notation hi := (uk_hi Uk).
#[local] Notation PSG := (PState (uk_HG Uk) hptr).
#[local] Notation PSC := (PState (uk_HC Uk) hptr).
#[local] Notation npk := (npeek (uk_segs Uk)).
#[local] Notation relX := (USimX.relX (uk_G Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr)).
#[local] Notation usimS := (usimX (uk_nsafeP Uk) (uk_gstepP Uk) (npeek (uk_segs Uk))).
#[local] Notation RQ := (RelX.RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX := (RelX.RX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RU := (RelX.RU (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_RQ := (RelX.RX_RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_U := (RelX.RX_U (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_G := (RelX.RQ_G (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_C := (RelX.RQ_C (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_minvX := (RelX.RQ_minvX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_halted := (RelX.RQ_halted (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc := (RelX.RQ_libc (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile := (RelX.RQ_outfile (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_mq := (RelX.RQ_mq (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_lci := (RelX.RQ_lci (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_fresh := (RelX.RQ_fresh (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_toks_below := (RelX.RQ_toks_below (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_pot := (RelX.RQ_pot (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation blk_addr_range := (RelX.blk_addr_range (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_same_heap := (RelX.RQ_same_heap (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc_upd := (RelX.RQ_libc_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile_upd := (RelX.RQ_outfile_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_xstep := (RelX.RQ_xstep (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_after := (RelX.RQ_after (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Definition ru_get := @RelX.ru_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_rd_lc := @RelX.ru_rd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_lc := @RelX.ru_upd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_outfile := @RelX.ru_upd_outfile (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_heap_op := @RelX.ru_heap_op (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
Arguments ru_heap_op {A}.
#[local] Definition ru_heap_opu := @RelX.ru_heap_opu (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pmalloc := @RelX.ru_pmalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pcalloc := @RelX.ru_pcalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_prealloc := @RelX.ru_prealloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pfree := @RelX.ru_pfree (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_sys := @RelX.ru_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
Arguments ru_sys {A}.
#[local] Definition ru_read := @RelX.ru_read (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_readv := @RelX.ru_readv (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_exit := @RelX.ru_exit (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_bind := @RelX.ru_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind {A B}.
#[local] Definition ru_bind2 := @RelX.ru_bind2 (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind2 {A B A' B'}.
#[local] Definition ru_seq := @RelX.ru_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_seq {A B A' B'}.
#[local] Definition ru_ret := @RelX.ru_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_ret {A}.
#[local] Definition ru_post := @RelX.ru_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_post {A}.
#[local] Definition ru_pre := @RelX.ru_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_pre {A B}.
#[local] Definition ru_munr := @RelX.ru_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_munr {A B}.
#[local] Definition ru_use := @RelX.ru_use (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_use {A B}.
#[local] Definition ru_bind_retl := @RelX.ru_bind_retl (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind_retl {A B}.
#[local] Definition usim_pure := @usimX_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pure {A B}.
#[local] Definition usim_exI := @usimX_exI (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_exI {A B X}.
#[local] Definition usim_ret := @usimX_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_ret {A B}.
#[local] Definition usim_get := @usimX_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_upd := @usimX_upd (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_post := @usimX_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_post {A B}.
#[local] Definition usim_pre := @usimX_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pre {A B}.
#[local] Definition usim_conseq := @usimX_conseq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_conseq {A B}.
#[local] Definition usim_munr := @usimX_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_munr {A B}.
#[local] Definition usim_false := @usimX_false (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_false {A B}.
#[local] Definition usim_if := @usimX_if (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_if {A B}.
#[local] Definition usim_pointwise := @usimX_pointwise (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pointwise {A B}.
#[local] Definition usim_sys := @usimX_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_sys {A B}.
#[local] Definition usim_of_paths := @usimX_of_paths (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_of_paths {A B}.
#[local] Definition usim_bind := @usimX_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind {A B A' B'}.
#[local] Definition usim_seq := @usimX_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_seq {A B A' B'}.
#[local] Definition usim_bind_eq := @usimX_bind_eq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind_eq {A A' B'}.
#[local] Definition usim_loopV := @usimX_loopV (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_loopV {X Y A B}.
(* [comment removed for export] *)
#[local] Notation framed I R := (framedX I R) (only parsing).
#[local] Definition usim_ND := fun A B p => @usimX_ND (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) A B p.
Arguments usim_ND {A B}.
#[local] Notation FOG := (uk_FOG Uk).
#[local] Notation FOC := (uk_FOC Uk).
#[local] Notation RQ_siteG := (RelX.RQ_siteG (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Notation finsens := (RelX.finsens (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Definition usim_fenter := @RelX.usimX_fenter (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fenter {A B}.
#[local] Definition usim_fret_of_ret := @RelX.usimX_fret_of_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fret_of_ret {A B}.
#[local] Definition finsens_RX := @RelX.finsens_RX (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_pure := @RelX.finsens_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_ex := @RelX.finsens_ex (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments finsens_ex {X}.
#[local] Definition finsens_mo := @RelX.finsens_mo (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
(* [comment removed for export] *)
Ltac fins_head t := lazymatch t with ?f _ => fins_head f | _ => t end.
Ltac fins :=
  lazymatch goal with
  | |- RelX.finsens _ _ _ _ _ _ _ _ _ ?R =>
      first [ apply finsens_RX; let s := fresh in let s' := fresh in let mo := fresh in let EL := fresh in let EO := fresh in let HU := fresh in
              intros s s' mo EL EO HU; unfold UK in *; rewrite EL, EO; exact HU
            | apply finsens_ex; intro; fins
            | apply finsens_pure; fins
            | apply finsens_mo; fins
            | let h := fins_head R in unfold h; fins ]
  end.
(* [comment removed for export] *)
Ltac xfe := try (apply usim_fenter; [solve [fins]|]).
Ltac xfr := xfe; try (apply usim_fret_of_ret; [solve [fins]|]).
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).
#[local] Notation PR_G := (prims HOG FOG stkG).
#[local] Notation PR_C := (prims HOC FOC stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP Uk rc).
#[local] Notation PST := (PST Uk rc).
#[local] Notation PA := (PA rc).
#[local] Notation Q_next := (Q_next rc).
#[local] Notation P0 := (rc_P0 rc).

(* [comment removed for export] *)
#[using="Type"] Lemma toks_ng p s i :
  pc_priv p = PrivNg s i ->
  toks p = (pc_buffer p, pc_bufalloc p) :: (pc_self p, PCAP_NG_SF_TOTAL)
           :: match i with Some q => [(q, ng_ifaces_size s * PCAP_NG_IF_SIZE)] | None => [] end ++ (fp, FILE_ALLOC) :: B.
Proof. intros HS. unfold UPcapXA.toks, psize, ifas. rewrite HS. destruct i; reflexivity. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma toks_len p : zlen (toks p) + 1 <= 9.
Proof.
  unfold UPcapXA.toks, ifas. pose proof (rw_B _ RCW) as (BL & _). unfold zlen in *. cbn [length]. rewrite length_app. cbn [length].
  destruct (pc_priv p) as [|s [q|]]; cbn [length]; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pow2_double_small k pos :
  0 <= k -> 20 * 2 ^ k <= pos - 20 -> pos < MAX_INPUT -> 2 ^ k * 2 <= IFSMAX.
Proof.
  intros Hk Hle Hp. unfold MAX_INPUT, IFSMAX in *.
  assert (LT : 2 ^ k < 2 ^ 22) by lia.
  apply Z.pow_lt_mono_r_iff in LT; [| lia| lia]. change (2 ^ 22) with (2 ^ 21 * 2).
  apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma RP_live_if p pos tm n' :
  PI p pos -> TML tm (toks p) -> 0 <= n' <= IFSMAX * PCAP_NG_IF_SIZE -> 2 * liveL (ifas p) <= IFSMAX * PCAP_NG_IF_SIZE ->
  n' <= NMAXA /\ live1 tm + n' <= LIVEMAX /\ zlen (sizes tm) + 1 <= LIVECNT.
Proof.
  intros HPI HT Hn IL. pose proof (rw_Blive _ RCW) as BL. pose proof (rw_B _ RCW) as [BL2 _]. destruct (ifas_R63N rc p pos HPI) as [_ IL2].
  pose proof (pi_buf _ _ _ HPI) as PB. rewrite (live1_TML _ _ HT), toks_liveL. rewrite (zlen_perm _ _ (TML_sizes _ _ HT)).
  assert (EZ : zlen (map snd (toks p)) = 3 + zlen (ifas p) + zlen B).
  { unfold zlen. rewrite length_map. unfold UPcapXA.toks. cbn [length app]. rewrite length_app. cbn [length]. lia. }
  rewrite EZ.
  assert (N1 : forall z, 0 <= z -> n1 z <= z + 1) by (intros; unfold n1; lia).
  pose proof (N1 (pc_bufalloc p) ltac:(lia)). pose proof (N1 (psize p) ltac:(unfold psize; destruct (pc_priv p); unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL; lia)).
  assert (psize p <= 2^20) by (unfold psize; destruct (pc_priv p); unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL; lia).
  unfold n1 at 3. unfold NMAXA, LIVEMAX, LIVECNT, BUFMAX, IFSMAX, PCAP_NG_IF_SIZE, FILE_ALLOC in *. lia.
Qed.
#[using="RCW"] Lemma PA_pot_if p pos pt n' :
  PA false p pos pt -> PI p pos -> 0 <= n' -> VIF p + n' <= 80 * IFSMAX -> 0 <= pt /\ pt + n' <= VOLMAX.
Proof.
  intros [A1 A2] HPI Hn Hv. pose proof (rw_P0 _ RCW) as [P1 [_ P2]]. pose proof (pi_pos _ _ _ HPI) as PP. pose proof (rw_d _ RCW).
  unfold V_READ, VC0, BUFMAX, IFSMAX, MAX_INPUT in *. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma PA_vif sl p p' pos pt c : PA sl p pos pt -> 0 <= c -> VIF p + c <= VIF p' -> PA sl p' pos (pt + c).
Proof. unfold UPcapXA.PA. intros [A1 A2] C D. split; lia. Qed.

(* [comment removed for export] *)
Ltac pa_keep H :=
  eapply (PA_keep _ _ _ _ _ _ _ _ H);
  [ first [apply pkeep_refl| apply pkeep_set_errbuf| apply pkeep_set_bufdata| apply pkeep_set_header| assumption
          | eapply pkeep_trans; [eassumption| first [apply pkeep_set_errbuf| apply pkeep_set_bufdata| apply pkeep_set_header]]]
  | lia
  | first [intros _; reflexivity| discriminate] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma gfbd_mok c n m : get_from_block_data c n = inl m -> mok m.
Proof. unfold get_from_block_data. destruct (cur_remaining c <? n); [| discriminate]. intros X. injection X as <-. mok_tac. Qed.
#[using="Type"] Lemma process_idb_options_loop_mok : forall fuel sw st c buf buf' m,
  process_idb_options_loop fuel sw st c buf = (buf', inl m) -> mok m.
Proof.
  induction fuel as [|fuel IH]; intros sw st c buf buf' m H; cbn [process_idb_options_loop] in H; [discriminate|].
  destruct (cur_remaining c =? 0); [discriminate|].
  unfold get_opthdr_from_block_data in H. destruct (get_from_block_data c 4) as [m1|[off c1]] eqn:E1; [injection H as _ <-; exact (gfbd_mok _ _ _ E1)|].
  cbv zeta in H. cbn [fst snd] in H.
  match type of H with context [get_optvalue_from_block_data ?cc ?ol] => unfold get_optvalue_from_block_data in H; destruct (get_from_block_data cc (((ol + 3) / 4) * 4)) as [m2|[voff c2]] eqn:E2; [injection H as _ <-; exact (gfbd_mok _ _ _ E2)|] end.
  repeat match type of H with
    | (if ?c then _ else _) = _ => destruct c
    | process_idb_options_loop _ _ _ _ _ = _ => exact (IH _ _ _ _ _ _ H)
    | (_, inl _) = (_, inl _) => injection H as _ <-; mok_tac
    | (_, inr _) = (_, inl _) => discriminate
    end.
Qed.
#[using="Type"] Lemma process_idb_options_mok sw c buf buf' m : process_idb_options sw c buf = (buf', inl m) -> mok m.
Proof. unfold process_idb_options. apply process_idb_options_loop_mok. Qed.

Definition Q_addif (p : pcapT) (pos : Z) (r : bool * cursor * pcapT * list Z) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  snd (fst r) = p' /\ pos' = pos /\ psim p p' /\ mok (snd r) /\ PA false p' pos' pt'.

#[using="RCW"] Lemma pr_add_interface nx p tm pt off pos s i idb_off c :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> 20 * (ng_ifcount s + 1) <= pos -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (add_interface MOps PR_G p idb_off c) (add_interface MOps PR_C p idb_off c) (PST (Q_addif p pos)).
Proof.
  intros HPI HT HS Hc HPA. pose proof HPI as [P1 P2 P3 P4 P5 P6]. rewrite HS in P6. destruct P6 as (N1 & N2 & N3 & N4 & N5).
  pose proof (rw_d _ RCW) as DL.
  assert (U1 : Prelim.u32 (ng_ifcount s + 1) = ng_ifcount s + 1) by (unfold Prelim.u32; apply Z.mod_small; unfold MAX_INPUT in DL; lia).
  unfold add_interface. unfold ng_of, ng_ifaces_ptr_of. rewrite HS. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_malloc e_realloc prims]; xfe. rewrite U1. cbv zeta.
  (* [comment removed for export] *)
  eapply (pp_bind Uk rc (fun r p' pos' pt' => pos' = pos /\ fst r = None /\ PA false p' pos' pt' /\ exists sz q k, snd r = p' /\
            p' = set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) sz (ng_ifaces s)) (Some q) p /\ 0 <= k /\ sz = 2 ^ k /\ sz <= IFSMAX)).
  { destruct (ng_ifaces_size s <? ng_ifcount s + 1) eqn:ELT.
    - apply Z.ltb_lt in ELT. destruct (ng_ifaces_size s =? 0) eqn:EZ.
      + (* [comment removed for export] *)
        apply Z.eqb_eq in EZ.
        assert (Hi : i = None) by (destruct i as [q|]; [destruct N4 as (k & Hk & E); pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia| reflexivity]). subst i.
        destruct (RP_budget rc RCW p pos tm PCAP_NG_IF_SIZE HPI HT ltac:(unfold PCAP_NG_IF_SIZE, BUFMAX; lia)) as (R1 & R2 & R3).
        destruct (RP_live rc RCW p pos tm (n1 PCAP_NG_IF_SIZE) HPI HT ltac:(unfold n1, PCAP_NG_IF_SIZE, BUFMAX; lia)) as (L1 & L2 & L3).
        destruct (PA_pot0 rc RCW p pos pt (n1 PCAP_NG_IF_SIZE) HPA HPI ltac:(unfold n1, PCAP_NG_IF_SIZE, BUFMAX; lia)) as [V1 V2].
        eapply ru_bind.
        { eapply (gr_malloc Uk tm (toks p) nx pt _ _ _ PCAP_NG_IF_SIZE HT); [apply toks_len| unfold PCAP_NG_IF_SIZE; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2| exact V1| exact V2| exact L1| rewrite <- (live1_TML _ _ HT); exact L2]. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        xfr; apply (pp_ret Uk rc _ (N.succ nx) (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) 1 (ng_ifaces s)) (Some nx) p) _ (pt + n1 PCAP_NG_IF_SIZE) off pos).
        * cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [apply (PA_vif false p _ pos pt _ HPA); [unfold n1, PCAP_NG_IF_SIZE; lia| unfold VIF; rewrite HS; cbn [pc_priv set_ng set_priv ng_ifaces_size]; unfold n1, PCAP_NG_IF_SIZE; lia]|]. exists 1, nx, 0. split; [reflexivity|]. split; [reflexivity|]. unfold IFSMAX. lia.
        * constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [unfold IFSMAX; lia|]. split; [exists 0; split; [lia| reflexivity]|]. exact N5.
        * eapply TML_perm; [exact HT'|]. unfold UPcapXA.toks, psize, ifas. rewrite HS. cbn.
          etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_swap.
      + (* [comment removed for export] *)
        apply Z.eqb_neq in EZ.
        destruct i as [old|]; [| lia]. destruct N4 as (k & Hk & Esz).
        assert (SZ2 : ng_ifaces_size s * 2 <= IFSMAX) by (rewrite Esz; apply (pow2_double_small k pos Hk); [rewrite <- Esz; lia| lia]).
        assert (U2 : Prelim.u32 (ng_ifaces_size s * 2) = ng_ifaces_size s * 2) by (unfold Prelim.u32; apply Z.mod_small; unfold IFSMAX in SZ2; lia).
        rewrite U2. destruct (ng_ifaces_size s * 2 <? ng_ifaces_size s) eqn:EO; [apply Z.ltb_lt in EO; lia|].
        replace (ng_ifcount s <? 2 ^ 22) with true by (symmetry; apply Z.ltb_lt; unfold MAX_INPUT in DL; lia). cbn [negb].
        destruct (RP_budget_if rc RCW p pos tm (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HPI HT ltac:(unfold PCAP_NG_IF_SIZE; lia)) as (R1 & R2 & R3).
        { unfold ifas. rewrite HS. cbn [map snd]. rewrite R63N_cons, R63N_nil.
          pose proof (bigb_le (ng_ifaces_size s * PCAP_NG_IF_SIZE) ltac:(unfold PCAP_NG_IF_SIZE; lia)). unfold IFSMAX, PCAP_NG_IF_SIZE, PGSZ in *. cbn. lia. }
        destruct (RP_live_if p pos tm (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HPI HT ltac:(unfold PCAP_NG_IF_SIZE, IFSMAX in *; lia)) as (L1 & L2 & L3).
        { unfold ifas. rewrite HS. rewrite liveL_cons. unfold liveL. cbn [map zsum fold_right]. unfold n1, IFSMAX, PCAP_NG_IF_SIZE in *. lia. }
        destruct (PA_pot_if p pos pt (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HPA HPI ltac:(unfold PCAP_NG_IF_SIZE; lia)) as [V1 V2].
        { unfold VIF. rewrite HS. unfold PCAP_NG_IF_SIZE, IFSMAX in *. lia. }
        eapply ru_bind.
        { eapply (gr_realloc Uk tm (toks p) nx pt _ _ _ old (ng_ifaces_size s * PCAP_NG_IF_SIZE) (ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) HT);
            [| apply toks_len| unfold PCAP_NG_IF_SIZE, IFSMAX in *; lia| exact R3| rewrite <- (R63N_perm _ _ (TML_sizes _ _ HT)); exact R2| exact V1| exact V2| exact L1| rewrite <- (live1_TML _ _ HT); exact L2].
          rewrite (toks_ng p s (Some old) HS). right; right. apply in_app_iff. left. left. reflexivity. }
        intros r. apply usim_pure. intros [-> HT']. cbn beta iota.
        xfr; apply (pp_ret Uk rc _ (N.succ nx) (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s * 2) (ng_ifaces s)) (Some nx) p) _ (pt + ng_ifaces_size s * 2 * PCAP_NG_IF_SIZE) off pos).
        * cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [apply (PA_vif false p _ pos pt _ HPA); [unfold PCAP_NG_IF_SIZE; lia| unfold VIF; rewrite HS; cbn [pc_priv set_ng set_priv ng_ifaces_size]; unfold PCAP_NG_IF_SIZE; lia]|]. exists (ng_ifaces_size s * 2), nx, (k + 1). split; [reflexivity|]. split; [reflexivity|].
          split; [lia|]. split; [rewrite Esz, Z.pow_add_r by lia; reflexivity| exact SZ2].
        * constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists (k + 1); split; [lia| rewrite Esz, Z.pow_add_r by lia; reflexivity]|]. exact N5.
        * eapply TML_perm; [exact HT'|]. pose proof (TML_nodup _ _ HT) as ND. unfold UPcapXA.toks, psize, ifas in ND |- *. rewrite HS in ND |- *. cbn in ND |- *.
          inversion ND as [|? ? NI1 ND1]; subst. inversion ND1 as [|? ? NI2 ND2]; subst.
          destruct (N.eqb_spec (pc_buffer p) old) as [E|_]; [exfalso; apply NI1; rewrite E; right; left; reflexivity|].
          destruct (N.eqb_spec (pc_self p) old) as [E|_]; [exfalso; apply NI2; rewrite E; left; reflexivity|].
          rewrite N.eqb_refl. etransitivity; [apply perm_swap|]. apply perm_skip. apply perm_swap.
    - apply Z.ltb_ge in ELT. destruct i as [old|]; [| lia]. destruct N4 as (k & Hk & Esz).
      xfr; apply (pp_ret Uk rc _ nx (set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) (ng_ifcount s + 1) (ng_ifaces_size s) (ng_ifaces s)) (Some old) p) tm pt off pos).
      + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [eapply PA_mono; [exact HPA| lia| unfold VIF; rewrite HS; reflexivity]|]. exists (ng_ifaces_size s), old, k. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Esz| lia].
      + constructor; cbn; auto. split; [lia|]. split; [lia|]. split; [lia|]. split; [exists k; auto|]. exact N5.
      + unfold UPcapXA.toks, psize, ifas in HT |- *. rewrite HS in HT. cbn in HT |- *. exact HT. }
  (* [comment removed for export] *)
  intros [r p1] p1' tm1 nx1 pt1 off1 pos1 (-> & Hr & PA1 & (sz & q & k & E1 & -> & Hk & Hsz & SZM)) HPI1 HT1. cbn [fst snd] in Hr, E1. subst r p1.
  cbn [ng_of ng_ifaces_ptr_of set_ng set_priv pc_priv pc_bufdata pc_swapped ng_user_tsresol ng_max_blocksize ng_ifcount ng_ifaces_size ng_ifaces
       pc_self pc_rfile pc_bufsize pc_bufalloc pc_buffer pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_break_loop pc_errbuf pc_header].
  destruct (process_idb_options (pc_swapped p) c (pc_bufdata p)) as [buf [m|[opts c']]] eqn:EPO.
  - xfr; match goal with |- usimX _ _ _ _ (mret (_, _, ?q, _)) _ _ => xfr; apply (pp_ret Uk rc _ nx1 q tm1 pt1 off1 pos) end.
    + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]| split; [exact (process_idb_options_mok _ _ _ _ _ EPO)| eapply PA_mono; [exact PA1| lia| reflexivity]]].
    + pose proof HPI1 as [X1 X2 X3 X4 X5 X6]. constructor; cbn in *; auto.
    + exact HT1.
  - cbv zeta.
    match goal with |- context [let '(scale_type, scale_factor) := ?x in _] => destruct x as [st sf] end.
    xfr; match goal with |- usimX _ _ _ _ (mret (_, _, ?q, _)) _ _ => xfr; apply (pp_ret Uk rc _ nx1 q tm1 pt1 off1 pos) end.
    + cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [split; [reflexivity| unfold isng; cbn; rewrite HS; reflexivity]| split; [apply mok_nil| eapply PA_mono; [exact PA1| lia| reflexivity]]].
    + pose proof HPI1 as [X1 X2 X3 X4 X5 X6]. constructor; cbn in *; auto.
    + exact HT1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Q_thr {A} (p : pcapT) (pos : Z) (r : (list Z + A) * pcapT) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ match fst r with inl m => mok m | inr _ => True end
  /\ PA match fst r with inl _ => true | inr _ => false end p' pos' pt'.

(* [comment removed for export] *)
Ltac q_thr_ret nx q tm pt off pos :=
  xfr; apply (pp_ret Uk rc _ nx q tm pt off pos); [cbv beta iota zeta delta [Q_thr fst snd]; split; [reflexivity|]; split; [psim_tac|]; split; [lia|]; split; [first [exact I| mok_tac]|]| | ].

#[using="Type"] Lemma gfbd_ok c n off c' : get_from_block_data c n = inr (off, c') -> n <= cur_remaining c /\ off = cur_off c /\ c' = mkCursor (cur_off c + n) (cur_remaining c - n) (cur_block_type c).
Proof. unfold get_from_block_data. destruct (cur_remaining c <? n) eqn:E; [discriminate|]. apply Z.ltb_ge in E. intros X. injection X as <- <-. auto. Qed.

#[using="STK RCW"] Lemma pr_ng_find_idb : forall fuel nx p tm pt off pos s i,
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (ng_find_idb MOps PR_G fuel p) (ng_find_idb MOps PR_C fuel p) (PST (Q_thr p pos)).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm pt off pos s i HPI HT HS HF HPA.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [ng_find_idb]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims]; xfe.
  eapply (pp_bind Uk rc); [apply (pr_read_block Uk stkG stkC STK rc RCW nx p tm pt off pos (DStack SiteBhdrCheckHeader 0) HPI HT); [cbn; lia| exact HPA]|].
  intros rb p1 tm1 nx1 pt1 off1 pos1 (PK & LE & HRB) HPI1 HT1.
  destruct rb as [p1'|m p1'|c p1'].
  { destruct HRB as [-> PA1]. q_thr_ret nx1 p1 tm1 pt1 off1 pos1; [exact PA1| exact HPI1| exact HT1]. }
  { destruct HRB as (-> & Mm & PA1). q_thr_ret nx1 p1 tm1 pt1 off1 pos1; [exact PA1| exact HPI1| exact HT1]. }
  destruct HRB as (-> & (tl & TL & -> & CO & CR) & PA1). cbv zeta. cbn beta iota.
  destruct (cur_block_type c =? BT_IDB).
  - destruct (get_from_block_data c 8) as [m|[off' c']] eqn:EG.
    + pose proof (gfbd_mok _ _ _ EG) as Mm. q_thr_ret nx1 p1 tm1 pt1 off1 (pos + tl); [pa_keep PA1| exact HPI1| exact HT1].
    + apply gfbd_ok in EG as (G1 & -> & ->).
      set (p2 := if pc_swapped p1 then set_bufdata (swap_field 4 (cur_off c + 4) (swap_field 2 (cur_off c) (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      pose proof (pi_ng _ _ _ HPI) as NG. rewrite HS in NG. destruct NG as (N1 & N2 & _).
      assert (PK12 : pkeep p1 p2) by (subst p2; destruct (pc_swapped p1); [apply pkeep_set_bufdata| apply pkeep_refl]).
      assert (PA2 : PA false p2 (pos + tl) pt1) by (pa_keep PA1).
      eapply (pp_bind Uk rc); [apply (pr_add_interface nx1 p2 tm1 pt1 off1 (pos + tl) s i (cur_off c) _ HPI2 HT2 HS2); [lia| exact PA2]|].
      intros [[[ok c2] p3] m] p3' tm3 nx3 pt3 off3 pos3 (E3 & -> & PS3 & Mm & PA3) HPI3 HT3. cbn [fst snd] in E3, Mm. subst p3'. cbn beta iota.
      destruct ok; (q_thr_ret nx3 p3 tm3 pt3 off3 (pos + tl); [pa_keep PA3| exact HPI3| exact HT3]).
  - destruct ((cur_block_type c =? BT_EPB) || (cur_block_type c =? BT_SPB) || (cur_block_type c =? BT_PB)).
    + q_thr_ret nx1 p1 tm1 pt1 off1 (pos + tl); [pa_keep PA1| exact HPI1| exact HT1].
    + destruct (psim_ng p p1 s i (pkeep_psim _ _ PK) HS) as (s1 & i1 & HS1).
      eapply (pp_post Uk rc); [apply (IH nx1 p1 tm1 pt1 off1 (pos + tl) s1 i1 HPI1 HT1 HS1); [rewrite Nat2Z.inj_succ in HF; lia| exact PA1]|].
      intros r p' pos' pt' (A1 & A2 & A3 & A4 & A5) _. split; [exact A1|]. split; [psim_tac|]. split; [lia| exact (conj A4 A5)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_scan (p : pcapT) (pos : Z) (r : (Z + ng_found) * pcapT) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (match fst r with inr _ => pos < pos' | inl st => st <= 0 end)
  /\ PA match fst r with inl _ => true | inr _ => false end p' pos' pt'.

Ltac q_scan_ret nx q tm pt off pos :=
  xfr; apply (pp_ret Uk rc _ nx q tm pt off pos); [cbv beta iota zeta delta [Q_scan fst snd]; split; [reflexivity|]; split; [psim_tac|]; split; [lia|]; split; [lia|]| | ].

#[using="STK RCW"] Lemma pr_ng_scan_blocks : forall fuel nx p tm pt off pos s i,
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (ng_scan_blocks MOps PR_G fuel p) (ng_scan_blocks MOps PR_C fuel p) (PST (Q_scan p pos)).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm pt off pos s i HPI HT HS HF HPA.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [ng_scan_blocks]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims]; xfe.
  eapply (pp_bind Uk rc); [apply (pr_read_block Uk stkG stkC STK rc RCW nx p tm pt off pos (DStack SiteBhdrNextPacket 0) HPI HT); [cbn; lia| exact HPA]|].
  intros rb p1 tm1 nx1 pt1 off1 pos1 (PK & LE & HRB) HPI1 HT1.
  destruct rb as [p1'|m p1'|c p1'].
  { destruct HRB as [-> PA1]. q_scan_ret nx1 p1 tm1 pt1 off1 pos1; [exact PA1| exact HPI1| exact HT1]. }
  { destruct HRB as (-> & _ & PA1). q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 pos1; [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1]. }
  destruct HRB as (-> & (tl & TL & -> & CO & CR) & PA1). cbv zeta. cbn beta iota.
  destruct (psim_ng p p1 s i (pkeep_psim _ _ PK) HS) as (s1 & i1 & HS1).
  assert (IHfuel : Z.of_nat (length d) < pos + tl + Z.of_nat fuel) by (rewrite Nat2Z.inj_succ in HF; lia).
  destruct (cur_block_type c =? BT_EPB).
  { destruct (get_from_block_data c 20) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 pt1 off1 (pos + tl); [pa_keep PA1| exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_SPB).
  { destruct (get_from_block_data c 4) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 pt1 off1 (pos + tl); [pa_keep PA1| exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_PB).
  { destruct (get_from_block_data c 20) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1].
    - q_scan_ret nx1 p1 tm1 pt1 off1 (pos + tl); [pa_keep PA1| exact HPI1| exact HT1]. }
  destruct (cur_block_type c =? BT_IDB).
  { destruct (get_from_block_data c 8) as [m|[off' c']] eqn:EG.
    - q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1].
    - apply gfbd_ok in EG as (G1 & -> & ->).
      set (p2 := if pc_swapped p1 then set_bufdata (swap_field 4 (cur_off c + 4) (swap_field 2 (cur_off c) (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      assert (PK12 : pkeep p1 p2) by (subst p2; destruct (pc_swapped p1); [apply pkeep_set_bufdata| apply pkeep_refl]).
      assert (PA2 : PA false p2 (pos + tl) pt1) by (pa_keep PA1).
      pose proof (pi_ng _ _ _ HPI) as NG. rewrite HS in NG. destruct NG as (N1 & N2 & _).
      destruct (negb (pc_linktype p2 =? _)).
      { q_scan_ret nx1 (set_errbuf (Msg.iface_type_differs (get_le16 (pc_bufdata p2) (cur_off c))) p2) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI2| exact HT2]. }
      destruct (negb (pc_snapshot p2 =? _)).
      { q_scan_ret nx1 (set_errbuf (Msg.iface_snaplen_differs (get_le32 (pc_bufdata p2) (cur_off c + 4))) p2) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI2| exact HT2]. }
      eapply (pp_bind Uk rc); [apply (pr_add_interface nx1 p2 tm1 pt1 off1 (pos + tl) s i (cur_off c) _ HPI2 HT2 HS2); [lia| exact PA2]|].
      intros [[[ok c2] p3] m] p3' tm3 nx3 pt3 off3 pos3 (E3 & -> & PS3 & _ & PA3) HPI3 HT3. cbn [fst snd] in E3. subst p3'. cbn beta iota.
      destruct ok.
      + destruct (psim_ng p p3 s i ltac:(psim_tac) HS) as (s3 & i3 & HS3).
        eapply (pp_post Uk rc); [apply (IH nx3 p3 tm3 pt3 off3 (pos + tl) s3 i3 HPI3 HT3 HS3 IHfuel PA3)|].
        intros [r q] p' pos' pt' (A1 & A2 & A3 & A4 & A5) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|]. split; [psim_tac|]. split; [lia|]. split; [destruct r; lia| exact A5].
      + q_scan_ret nx3 (set_errbuf m p3) tm3 pt3 off3 (pos + tl); [pa_keep PA3| apply PI_set_errbuf; exact HPI3| exact HT3]. }
  destruct (cur_block_type c =? BT_SHB).
  { destruct (get_from_block_data c 16) as [m|[off' c']].
    - q_scan_ret nx1 (set_errbuf m p1) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI1| exact HT1].
    - set (p2 := if pc_swapped p1 then set_bufdata (swap_field 2 (off' + 4) (swap_field 4 off' (pc_bufdata p1))) p1 else p1).
      assert (HPI2 : PI p2 (pos + tl)) by (subst p2; destruct (pc_swapped p1); [apply PI_set_bufdata|]; exact HPI1).
      assert (HT2 : TML tm1 (toks p2)) by (subst p2; destruct (pc_swapped p1); exact HT1).
      assert (PK2 : pkeep p p2) by (subst p2; destruct (pc_swapped p1); [eapply pkeep_trans; [exact PK| apply pkeep_set_bufdata]| exact PK]).
      assert (HS2 : pc_priv p2 = PrivNg s i) by (destruct PK2 as [_ E]; rewrite E; exact HS).
      assert (PK12 : pkeep p1 p2) by (subst p2; destruct (pc_swapped p1); [apply pkeep_set_bufdata| apply pkeep_refl]).
      assert (PA2 : PA false p2 (pos + tl) pt1) by (pa_keep PA1).
      destruct (get_le32 (pc_bufdata p2) off' =? BYTE_ORDER_MAGIC).
      + destruct (negb (get_le16 (pc_bufdata p2) (off' + 4) =? 1)).
        * q_scan_ret nx1 (set_errbuf (Msg.unknown_major (get_le16 (pc_bufdata p2) (off' + 4))) p2) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI2| exact HT2].
        * unfold ng_of, ng_ifaces_ptr_of. rewrite HS2.
          set (p3 := set_ng (mkNg (ng_user_tsresol s) (ng_max_blocksize s) 0 (ng_ifaces_size s) []) i p2).
          assert (HPI3 : PI p3 (pos + tl)).
          { pose proof HPI2 as [X1 X2 X3 X4 X5 X6]. rewrite HS2 in X6. destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). constructor; cbn; auto. split; [lia|]. split; [lia|]. auto. }
          assert (HT3 : TML tm1 (toks p3)) by (unfold UPcapXA.toks, psize, ifas in HT2 |- *; rewrite HS2 in HT2; cbn in HT2 |- *; exact HT2).
          assert (PA3' : PA false p3 (pos + tl) pt1) by (eapply PA_mono; [exact PA2| lia| unfold VIF; rewrite HS2; reflexivity]).
          eapply (pp_post Uk rc); [apply (IH nx1 p3 tm1 pt1 off1 (pos + tl) _ i HPI3 HT3 eq_refl IHfuel PA3')|].
          intros [r q] p' pos' pt' (A1 & A2 & A3 & A4 & A5) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|].
          split; [eapply psim_trans; [| exact A2]; eapply psim_trans; [apply pkeep_psim; exact PK2| apply (psim_set_ng _ _ _ _ _ HS2)]|].
          split; [lia|]. split; [destruct r; lia| exact A5].
      + destruct (get_le32 (pc_bufdata p2) off' =? BYTE_ORDER_MAGIC_SWAPPED).
        * q_scan_ret nx1 (set_errbuf Msg.sections_byte_order p2) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI2| exact HT2].
        * q_scan_ret nx1 (set_errbuf Msg.bad_byte_order_magic p2) tm1 pt1 off1 (pos + tl); [pa_keep PA1| apply PI_set_errbuf; exact HPI2| exact HT2]. }
  eapply (pp_post Uk rc); [apply (IH nx1 p1 tm1 pt1 off1 (pos + tl) s1 i1 HPI1 HT1 HS1 IHfuel PA1)|].
  intros [r q] p' pos' pt' (A1 & A2 & A3 & A4 & A5) _. unfold Q_scan. cbn [fst snd] in *. split; [exact A1|]. split; [psim_tac|]. split; [lia|]. split; [destruct r; lia| exact A5].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="STK RCW"] Lemma pr_pcap_ng_next_packet fuel nx p tm pt off pos s i :
  PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (pcap_ng_next_packet MOps PR_G fuel p) (pcap_ng_next_packet MOps PR_C fuel p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HS HF HPA. unfold pcap_ng_next_packet. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
  eapply (pp_bind Uk rc); [apply (pr_ng_scan_blocks fuel nx p tm pt off pos s i HPI HT HS HF HPA)|].
  intros [r p1] p1' tm1 nx1 pt1 off1 pos1 (E1 & PS1 & LE1 & PR1 & PA1) HPI1 HT1. cbn [fst snd] in E1, PR1, PA1. subst p1'. cbn beta iota.
  assert (RET : forall st h q, psim p1 q -> PI q pos1 -> TML tm1 (toks q) -> (0 < st -> pos < pos1) -> PA (negb (0 <? st)) q pos1 pt1 ->
            usimS (RPP nx1 tm1 pt1 off1 pos1) (mret (st, h, q)) (mret (st, h, q)) (PST (Q_next p pos))).
  { intros st h q PSq HPIq HTq Hst HPAq. xfr; apply (pp_ret Uk rc _ nx1 q tm1 pt1 off1 pos1); [| exact HPIq| exact HTq].
    unfold Q_next. cbn [fst snd]. split; [reflexivity|]. split; [eapply psim_trans; [exact PS1| exact PSq]|]. split; [lia| exact (conj Hst HPAq)]. }
  destruct r as [status|f].
  { apply RET; [apply psim_refl| exact HPI1| exact HT1| intros; lia| replace (0 <? status) with false by (symmetry; apply Z.ltb_ge; lia); exact PA1]. }
  cbv zeta.
  destruct (ng_ifcount (ng_of p1) <=? f_interface_id f).
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia| cbn; pa_keep PA1]. }
  destruct (pc_snapshot p1 <? f_caplen f).
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia| cbn; pa_keep PA1]. }
  destruct (get_from_block_data (f_cursor f) (f_caplen f)) as [m|[doff cx]].
  { apply RET; [apply psim_set_errbuf| apply PI_set_errbuf; exact HPI1| exact HT1| lia| cbn; pa_keep PA1]. }
  match goal with |- context [let '(hdr, dd) := ?x in _] => destruct x as [hdr dd] end.
  apply RET; [apply psim_set_bufdata| apply PI_set_bufdata; exact HPI1| exact HT1| lia| cbn; pa_keep PA1].
Qed.

#[using="STK RCW"] Lemma pr_next_packet_op fuel nx p tm pt off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (next_packet_op MOps PR_G fuel p) (next_packet_op MOps PR_C fuel p) (PST (Q_next p pos)).
Proof.
  intros HPI HT HF HPA. unfold next_packet_op. destruct (pc_priv p) as [sf|s i] eqn:HS.
  - apply (pr_pcap_next_packet Uk stkG stkC STK rc RCW nx p tm pt off pos sf HPI HT HS HPA).
  - apply (pr_pcap_ng_next_packet fuel nx p tm pt off pos s i HPI HT HS HF HPA).
Qed.

(* [comment removed for export] *)
Definition Q_rd (p : pcapT) (pos : Z) (r : Z * pcapT) (p' : pcapT) (pos' : Z) (pt' : Z) : Prop :=
  snd r = p' /\ psim p p' /\ pos <= pos' /\ (0 < fst r -> pos < pos') /\ PA (negb (0 <? fst r)) p' pos' pt'.

#[using="STK RCW"] Lemma pr_offline_read_1 fuel nx p tm pt off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (pcapint_offline_read_1 MOps PR_G fuel p) (pcapint_offline_read_1 MOps PR_C fuel p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT HF HPA. unfold pcapint_offline_read_1. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
  destruct (negb (pc_break_loop p =? 0)).
  { xfr; apply (pp_ret Uk rc _ nx (set_break_loop 0 p) tm pt off pos); [| destruct HPI; constructor; cbn; auto| exact HT].
    unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_set_break_loop|]. split; [lia|]. split; [lia|].
    cbn. eapply (PA_keep _ _ _ _ _ _ _ _ HPA); [split; reflexivity| lia| discriminate]. }
  eapply (pp_bind Uk rc); [apply (pr_next_packet_op fuel nx p tm pt off pos HPI HT HF HPA)|].
  intros [[st h] p1] p1' tm1 nx1 pt1 off1 pos1 (E1 & PS1 & LE1 & PR1 & PA1) HPI1 HT1. cbn [fst snd] in E1, PR1, PA1. subst p1'. cbn beta iota.
  destruct (st <? 0) eqn:E.
  { xfr; apply (pp_ret Uk rc _ nx1 p1 tm1 pt1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; [lia| exact (conj PR1 PA1)]. }
  destruct (st =? 0) eqn:E0.
  { apply Z.eqb_eq in E0. subst st. xfr; apply (pp_ret Uk rc _ nx1 p1 tm1 pt1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; [lia|]. split; [lia| exact PA1]. }
  apply Z.ltb_ge in E. apply Z.eqb_neq in E0.
  xfr; apply (pp_ret Uk rc _ nx1 (set_header h p1) tm1 pt1 off1 pos1); [| apply PI_set_header; exact HPI1| exact HT1].
  unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_header_r; exact PS1|]. split; [lia|]. split; [intros _; apply PR1; lia|].
  replace (0 <? st) with true in PA1 by (symmetry; apply Z.ltb_lt; lia). cbn in PA1 |- *. pa_keep PA1.
Qed.

#[using="STK RCW"] Lemma pr_pcap_next_ex fuel nx p tm pt off pos :
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (pcap_next_ex MOps PR_G fuel p) (pcap_next_ex MOps PR_C fuel p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT HF HPA. unfold pcap_next_ex. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
  eapply (pp_bind Uk rc); [apply (pr_offline_read_1 fuel nx p tm pt off pos HPI HT HF HPA)|].
  intros [st p1] p1' tm1 nx1 pt1 off1 pos1 (E1 & PS1 & LE1 & PR1 & PA1) HPI1 HT1. cbn [fst snd] in E1, PR1, PA1. subst p1'. cbn beta iota.
  xfr; apply (pp_ret Uk rc _ nx1 p1 tm1 pt1 off1 pos1); [| exact HPI1| exact HT1]. unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [exact PS1|]. split; [lia|].
  destruct (st =? 0) eqn:E0; [| exact (conj PR1 PA1)]. apply Z.eqb_eq in E0. subst st. cbn in PA1 |- *. split; [intros; lia| exact PA1].
Qed.

#[using="Type"] Lemma pr_pcap_stats sl nx p tm pt off pos :
  PI p pos -> TML tm (toks p) -> PA sl p pos pt ->
  usimS (RPP nx tm pt off pos) (pcap_stats MOps p) (pcap_stats MOps p) (PST (Q_rd p pos)).
Proof.
  intros HPI HT HPA. unfold pcap_stats. cbn [mo_ret MOps e_fenter e_fret prims]; xfe.
  xfr; apply (pp_ret Uk rc _ nx (set_errbuf Msg.stats_not_avail p) tm pt off pos); [| apply PI_set_errbuf; exact HPI| exact HT].
  unfold Q_rd. cbn [fst snd]. split; [reflexivity|]. split; [apply psim_set_errbuf|]. split; [lia|]. split; [intros; lia|].
  cbn. eapply (PA_keep _ _ _ _ _ _ _ _ HPA); [apply pkeep_set_errbuf| lia| intros _; reflexivity].
Qed.

End ReadingC.

End WithCeil.
End UPcapXC.

(* [comment removed for export] *)
Module UPcapXD.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

Section WithCeil.
(* [comment removed for export] *)
Section ReadingD.
(* [comment removed for export] *)
Variable Uk : UKit.
#[local] Notation G := (uk_G Uk).
#[local] Notation nsafeP := (uk_nsafeP Uk).
#[local] Notation gstepP := (uk_gstepP Uk).
#[local] Notation GK_safe := (uk_GK_safe Uk).
#[local] Notation GK_step := (uk_GK_step Uk).
#[local] Notation HG := (uk_HG Uk).
#[local] Notation HC := (uk_HC Uk).
#[local] Notation HOG := (uk_HOG Uk).
#[local] Notation HOC := (uk_HOC Uk).
#[local] Notation eqbG := (uk_eqbG Uk).
#[local] Notation eqbC := (uk_eqbC Uk).
#[local] Notation segs := (uk_segs Uk).
#[local] Notation hi := (uk_hi Uk).
#[local] Notation PSG := (PState (uk_HG Uk) hptr).
#[local] Notation PSC := (PState (uk_HC Uk) hptr).
#[local] Notation npk := (npeek (uk_segs Uk)).
#[local] Notation relX := (USimX.relX (uk_G Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr)).
#[local] Notation usimS := (usimX (uk_nsafeP Uk) (uk_gstepP Uk) (npeek (uk_segs Uk))).
#[local] Notation RQ := (RelX.RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX := (RelX.RX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RU := (RelX.RU (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_RQ := (RelX.RX_RQ (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RX_U := (RelX.RX_U (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_G := (RelX.RQ_G (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_C := (RelX.RQ_C (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_minvX := (RelX.RQ_minvX (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_halted := (RelX.RQ_halted (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc := (RelX.RQ_libc (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile := (RelX.RQ_outfile (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_mq := (RelX.RQ_mq (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_lci := (RelX.RQ_lci (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_fresh := (RelX.RQ_fresh (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_toks_below := (RelX.RQ_toks_below (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_pot := (RelX.RQ_pot (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation blk_addr_range := (RelX.blk_addr_range (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_same_heap := (RelX.RQ_same_heap (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_libc_upd := (RelX.RQ_libc_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_outfile_upd := (RelX.RQ_outfile_upd (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_xstep := (RelX.RQ_xstep (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Notation RQ_after := (RelX.RQ_after (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk)).
#[local] Definition ru_get := @RelX.ru_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_rd_lc := @RelX.ru_rd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_lc := @RelX.ru_upd_lc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_upd_outfile := @RelX.ru_upd_outfile (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_heap_op := @RelX.ru_heap_op (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
Arguments ru_heap_op {A}.
#[local] Definition ru_heap_opu := @RelX.ru_heap_opu (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pmalloc := @RelX.ru_pmalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pcalloc := @RelX.ru_pcalloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_prealloc := @RelX.ru_prealloc (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_pfree := @RelX.ru_pfree (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk).
#[local] Definition ru_sys := @RelX.ru_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
Arguments ru_sys {A}.
#[local] Definition ru_read := @RelX.ru_read (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_readv := @RelX.ru_readv (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_exit := @RelX.ru_exit (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_GK_safe Uk).
#[local] Definition ru_bind := @RelX.ru_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind {A B}.
#[local] Definition ru_bind2 := @RelX.ru_bind2 (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind2 {A B A' B'}.
#[local] Definition ru_seq := @RelX.ru_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_seq {A B A' B'}.
#[local] Definition ru_ret := @RelX.ru_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_ret {A}.
#[local] Definition ru_post := @RelX.ru_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_post {A}.
#[local] Definition ru_pre := @RelX.ru_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_pre {A B}.
#[local] Definition ru_munr := @RelX.ru_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_munr {A B}.
#[local] Definition ru_use := @RelX.ru_use (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_use {A B}.
#[local] Definition ru_bind_retl := @RelX.ru_bind_retl (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_segs Uk).
Arguments ru_bind_retl {A B}.
#[local] Definition usim_pure := @usimX_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pure {A B}.
#[local] Definition usim_exI := @usimX_exI (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_exI {A B X}.
#[local] Definition usim_ret := @usimX_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_ret {A B}.
#[local] Definition usim_get := @usimX_get (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_upd := @usimX_upd (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
#[local] Definition usim_post := @usimX_post (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_post {A B}.
#[local] Definition usim_pre := @usimX_pre (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pre {A B}.
#[local] Definition usim_conseq := @usimX_conseq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_conseq {A B}.
#[local] Definition usim_munr := @usimX_munr (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_munr {A B}.
#[local] Definition usim_false := @usimX_false (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_false {A B}.
#[local] Definition usim_if := @usimX_if (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_if {A B}.
#[local] Definition usim_pointwise := @usimX_pointwise (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_pointwise {A B}.
#[local] Definition usim_sys := @usimX_sys (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_sys {A B}.
#[local] Definition usim_of_paths := @usimX_of_paths (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)).
Arguments usim_of_paths {A B}.
#[local] Definition usim_bind := @usimX_bind (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind {A B A' B'}.
#[local] Definition usim_seq := @usimX_seq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_seq {A B A' B'}.
#[local] Definition usim_bind_eq := @usimX_bind_eq (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_bind_eq {A A' B'}.
#[local] Definition usim_loopV := @usimX_loopV (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) (npeek (uk_segs Uk)) (npk_inh (uk_segs Uk)).
Arguments usim_loopV {X Y A B}.
(* [comment removed for export] *)
#[local] Notation framed I R := (framedX I R) (only parsing).
#[local] Definition usim_ND := fun A B p => @usimX_ND (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (PState (uk_HG Uk) hptr) (PState (uk_HC Uk) hptr) A B p.
Arguments usim_ND {A B}.
#[local] Notation FOG := (uk_FOG Uk).
#[local] Notation FOC := (uk_FOC Uk).
#[local] Notation RQ_siteG := (RelX.RQ_siteG (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Notation finsens := (RelX.finsens (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk)).
#[local] Definition usim_fenter := @RelX.usimX_fenter (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fenter {A B}.
#[local] Definition usim_fret_of_ret := @RelX.usimX_fret_of_ret (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments usim_fret_of_ret {A B}.
#[local] Definition finsens_RX := @RelX.finsens_RX (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_pure := @RelX.finsens_pure (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
#[local] Definition finsens_ex := @RelX.finsens_ex (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
Arguments finsens_ex {X}.
#[local] Definition finsens_mo := @RelX.finsens_mo (uk_G Uk) (uk_nsafeP Uk) (uk_gstepP Uk) (uk_HG Uk) (uk_HC Uk) (uk_HOG Uk) (uk_HOC Uk) (uk_segs Uk) (uk_hi Uk) (uk_FOG Uk) (uk_FOC Uk) (uk_fi Uk).
(* [comment removed for export] *)
Ltac fins_head t := lazymatch t with ?f _ => fins_head f | _ => t end.
Ltac fins :=
  lazymatch goal with
  | |- RelX.finsens _ _ _ _ _ _ _ _ _ ?R =>
      first [ apply finsens_RX; let s := fresh in let s' := fresh in let mo := fresh in let EL := fresh in let EO := fresh in let HU := fresh in
              intros s s' mo EL EO HU; unfold UK in *; rewrite EL, EO; exact HU
            | apply finsens_ex; intro; fins
            | apply finsens_pure; fins
            | apply finsens_mo; fins
            | let h := fins_head R in unfold h; fins ]
  end.
(* [comment removed for export] *)
Ltac xfe := try (apply usim_fenter; [solve [fins]|]).
Ltac xfr := xfe; try (apply usim_fret_of_ret; [solve [fins]|]).
Variables (stkG stkC : stack_site -> Z).
Hypothesis STK : stk_ok stkG.
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).
#[local] Notation PR_G := (prims HOG FOG stkG).
#[local] Notation PR_C := (prims HOC FOC stkC).
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
#[local] Notation B := (rc_B rc).
#[local] Notation Kx := (rc_Kx rc).
#[local] Notation F0 := (rc_F0 rc).
#[local] Notation hs := (rc_hs rc).
#[local] Notation Cc := (rc_C rc).
#[local] Notation oh := (rc_oh rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation KR_ := (KR_ rc).
#[local] Notation FR_ := (FR_ rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP Uk rc).
#[local] Notation PST := (PST Uk rc).
#[local] Notation PA := (PA rc).
#[local] Notation P0 := (rc_P0 rc).

(* [comment removed for export] *)
Ltac case_if E := lazymatch goal with |- usimX _ _ _ _ (if ?c then _ else _) _ _ => destruct c eqn:E end.
Ltac case_ifb E := lazymatch goal with |- usimX _ _ _ _ (mbind (if ?c then _ else _) _) _ _ => destruct c eqn:E end.

(* [comment removed for export] *)
Definition L0 : list (N * Z) := (fp, FILE_ALLOC) :: B.

#[using="RCW"] Lemma L0_len : zlen L0 <= 4.
Proof. unfold L0. rewrite zlen_cons. pose proof (rw_B _ RCW) as (BL & _). lia. Qed.
#[using="Type"] Lemma L0_R63N : R63N (map snd L0) = R63N (map snd B).
Proof. unfold L0. cbn [map snd]. rewrite R63N_cons, bigb_FILE. lia. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma budget_pre tm L n :
  TML tm L -> zlen L + 1 <= 9 -> R63N (map snd L) <= R63N (map snd B) -> 0 <= n <= BUFMAX ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ bigb n <= QMAX /\ PHI P9 + R63N (map snd L) + bigb n <= BLIVE.
Proof.
  intros HT HL HR Hn. pose proof (rw_B _ RCW) as [BL BR]. pose proof (bigb_le n ltac:(lia)) as BN.
  assert (X : PHI P9 + R63N (map snd L) + bigb n <= BLIVE).
  { rewrite PHI_P9. unfold BASEB, B26, BUFMAX, BLIVE, PGSZ in *. lia. }
  destruct (budget_of_TML tm L n HT HL ltac:(lia) X) as [R1 R2].
  split; [exact R1|]. split; [exact R2|]. split; [unfold QMAX, BUFMAX, PGSZ in *; lia| exact X].
Qed.

(* [comment removed for export] *)
Definition PZ (pt : Z) : Prop := P0 <= pt <= P0 + 2^19.
(* [comment removed for export] *)
#[using="RCW"] Lemma pot_pre ptx n : P0 <= ptx -> ptx + n <= P0 + VC0 -> 0 <= n -> 0 <= ptx /\ ptx + n <= VOLMAX.
Proof. intros A1 A2 A3. pose proof (rw_P0 _ RCW) as [P1 [_ P2]]. unfold V_READ, VC0, BUFMAX, IFSMAX, MAX_INPUT in *. lia. Qed.
#[using="Type"] Lemma L0_liveL : liveL L0 = n1 FILE_ALLOC + liveL B.
Proof. unfold L0. rewrite liveL_cons. reflexivity. Qed.
#[using="RCW"] Lemma live_pre L n : liveL L <= liveL L0 + 2^20 -> 0 <= n <= 2^21 -> n1 n <= NMAXA /\ liveL L + n1 n <= LIVEMAX.
Proof. rewrite L0_liveL. intros A1 A2. pose proof (rw_Blive _ RCW) as BL. pose proof (liveL_nonneg B). unfold n1, NMAXA, LIVEMAX, FILE_ALLOC in *. lia. Qed.
(* [comment removed for export] *)
#[using="RCW"] Lemma PA_exit sl p pos pt : PA sl p pos pt -> PI p pos -> pt <= P0 + V_READ.
Proof.
  intros [A1 A2] HPI. pose proof (pi_pos _ _ _ HPI) as PP. pose proof (rw_d _ RCW) as DL.
  assert (VIF p <= 80 * IFSMAX).
  { unfold VIF. pose proof (pi_ng _ _ _ HPI) as NG. destruct (pc_priv p) as [|sng i]; [unfold IFSMAX; lia|]. destruct NG as (_ & _ & SZ & _). lia. }
  unfold V_READ, VC0, BUFMAX, MAX_INPUT in *. destruct sl; lia.
Qed.
#[using="Type"] Lemma PZ_exit pt : PZ pt -> pt <= P0 + V_READ.
Proof. unfold PZ, V_READ, VC0, BUFMAX, IFSMAX, MAX_INPUT. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="STK RCW"] Lemma pr_freadS nx L tm pt off pos site o n :
  TML tm L -> In (fp, FILE_ALLOC) L -> 0 <= pos <= Z.of_nat (length d) -> 0 <= o -> o + n <= 8192 -> 0 <= n < 2^40 ->
  usimS (RPP nx tm pt off pos) (e_fread PR_G fp (DStack site o) n) (e_fread PR_C fp (DStack site o) n)
        (eqpost (fun r => fun gh sG moG sC moC => exists off',
           (zlength r <= n /\ (zlength r < n -> pos + zlength r = Z.of_nat (length d)) /\ pos + zlength r <= Z.of_nat (length d) /\ r = dsl d pos (zlength r)) /\
           RPP nx tm pt off' (pos + zlength r) gh sG moG sC moC)).
Proof.
  intros HT HIn Hpos Ho Hon Hn. cbn [e_fread prims].
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros gh0 sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  destruct (STK site) as [S1 S2].
  eapply ru_pre; [| intros ? ? ? ? ? (-> & -> & -> & -> & ->); exact HR0].
  assert (DD : 0 <= eval_rdest HOG FOG stkG sG0 (DStack site o) /\ eval_rdest HOG FOG stkG sG0 (DStack site o) + n < 2^64).
  { unfold eval_rdest. destruct (fo_site FOG sG0 site) as [a|] eqn:ES; [destruct (RQ_siteG _ _ _ _ _ _ _ _ _ _ (proj1 HR0) ES) as [T1 T2]; lia| lia]. }
  destruct DD as [D1 D2].
  eapply ru_post; [apply (us_fread Uk tm nx pt (KR_ off) Cc oh hs (FR_ off pos) fp (kat e0 off) d pos _ _ n (KR_in rc off) (own_kat rc RCW off) (rw_hs _ RCW) (FR_in rc off pos)
                          (TML_lookup _ _ _ _ HT HIn) ltac:(lia) D1 D2)|].
  intros r gh sG moG sC moC (off' & (Q1 & Q2 & Q3 & Q4 & Q5) & H). exists off'. rewrite (KR_kset rc RCW), (FR_fupd rc RCW) in H. split; [| exact H]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_open_common nx L tm pt off pos total :
  TML tm L -> zlen L + 2 <= 9 -> R63N (map snd L) <= R63N (map snd B) -> total = PCAP_SF_TOTAL \/ total = PCAP_NG_SF_TOTAL ->
  P0 <= pt -> pt + 2^20 <= P0 + VC0 -> liveL L <= liveL L0 + 2^19 ->
  usimS (RPP nx tm pt off pos) (pcapint_open_offline_common MOps PR_G total) (pcapint_open_offline_common MOps PR_C total)
        (eqpost (fun r => fun gh sG moG sC moC => (r = inr nx /\ TML (<[nx := total]> tm) ((nx, total) :: L)) /\ RPP (N.succ nx) (<[nx := total]> tm) (pt + total) off pos gh sG moG sC moC)).
Proof.
  intros HT HL HR Htot Hp1 Hp2 HLV. unfold pcapint_open_offline_common. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_calloc prims]; xfe.
  assert (TT : 0 <= total < 2^20 /\ total * 1 < MMAP_THRESHOLD) by (unfold PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL, MMAP_THRESHOLD in *; lia).
  destruct (budget_pre tm L 0 HT ltac:(lia) HR ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & R4). rewrite bigb_small in R4 by (unfold MMAP_THRESHOLD; lia).
  assert (N1 : n1 (total * 1) = total) by (unfold n1, PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL in *; lia).
  destruct (pot_pre pt total Hp1 ltac:(lia) ltac:(lia)) as [V1 V2].
  destruct (live_pre L total ltac:(lia) ltac:(lia)) as [LV1 LV2].
  eapply ru_bind.
  { eapply (gr_calloc Uk tm L nx pt _ _ _ total 1 HT ltac:(lia) ltac:(lia) ltac:(lia) (proj2 TT)); [lia| exact V1| rewrite N1; exact V2| rewrite N1; unfold n1 in LV2; lia]. }
  intros r. apply usim_pure. intros [-> HT']. cbn beta iota. rewrite Z.mul_1_r in HT'.
  xfr; apply ru_ret. intros gh sG moG sC moC HR'. split; [split; [reflexivity| exact HT']|]. rewrite N1, Z.mul_1_r in HR'. exact HR'.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma max_snaplen_range lt : 1 <= max_snaplen_for_dlt lt <= 134217728.
Proof. unfold max_snaplen_for_dlt, MAXIMUM_SNAPLEN. destruct (lt =? DLT_DBUS); [lia|]. destruct (lt =? DLT_EBHSCR); [lia|]. destruct (lt =? DLT_USBPCAP); lia. Qed.
#[using="Type"] Lemma adjust_snapshot_range lt v : 0 <= v -> 1 <= pcapint_adjust_snapshot lt v <= INT_MAX.
Proof.
  intros Hv. unfold pcapint_adjust_snapshot. pose proof (max_snaplen_range lt).
  destruct ((v =? 0) || (INT_MAX <? v)) eqn:E.
  - unfold INT_MAX. lia.
  - apply orb_false_iff in E as [E1 E2]. apply Z.eqb_neq in E1. apply Z.ltb_ge in E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Q_check (r : check_result) (tm' : gmap N Z) (pos' : Z) : Prop :=
  match r with
  | CH_Ok p => PI p pos' /\ TML tm' (toks p)
  | CH_Err m => (TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)) /\ mok m
  | CH_NotMe => TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)
  end.
(* [comment removed for export] *)
Definition Q_pot (r : check_result) (pos' pt' : Z) : Prop :=
  match r with CH_Ok p => PA false p pos' pt' | CH_Err _ => pt' <= P0 + V_READ | CH_NotMe => PZ pt' end.
Definition PSTc : check_result -> check_result -> relX :=
  eqpost (fun r => fun gh sG moG sC moC => exists tm' nx' pt' off' pos', Q_check r tm' pos' /\ Q_pot r pos' pt' /\ RPP nx' tm' pt' off' pos' gh sG moG sC moC).

#[using="Type"] Lemma pc_ret_notok nx tm pt off pos (r : check_result) :
  match r with CH_Ok _ => False | CH_Err m => mok m | CH_NotMe => True end -> Q_pot r pos pt -> TML tm L0 -> 0 <= pos <= Z.of_nat (length d) ->
  usimS (RPP nx tm pt off pos) (mret r) (mret r) PSTc.
Proof. intros Hr HQ HT Hp. xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm, nx, pt, off, pos. split; [| exact (conj HQ HR)]. destruct r; [split; assumption| split; [split; assumption| exact Hr]| destruct Hr]. Qed.

(* [comment removed for export] *)
Ltac qpot := cbv beta iota delta [Q_pot]; first [assumption| eapply PA_exit; eassumption| (unfold PZ, V_READ, VC0, BUFMAX, IFSMAX, MAX_INPUT, PCAP_SF_TOTAL, PCAP_NG_SF_TOTAL, n1 in *; lia)].

#[using="STK RCW"] Lemma pr_pcap_check_header nx tm pt off pos magic precision :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) -> PZ pt ->
  usimS (RPP nx tm pt off pos) (pcap_check_header MOps PR_G magic fp precision) (pcap_check_header MOps PR_C magic fp precision) PSTc.
Proof.
  intros HT Hp HPZ. pose proof HPZ as [HPZ1 HPZ2]. unfold pcap_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_malloc e_free prims]; xfe.
  cbv zeta. lazymatch goal with |- usimX _ _ _ _ (match ?x with _ => _ end) _ _ => destruct x as [[ok magic_int] swapped] end. cbv beta iota zeta.
  destruct (negb ok); [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp]|].
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm pt off pos SitePcapHdrRest 0 20 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? ? X; exact X. }
  intros rest. eapply usim_exI; intros off1. apply usim_pure; intros (R1 & R2 & R3 & R4). pose proof (zlength_nonneg rest) as NR.
  assert (Hp1 : 0 <= pos + zlength rest <= Z.of_nat (length d)) by lia.
  destruct (negb (zlength rest =? 20)) eqn:E20.
  { eapply ru_bind; [apply (pr_read_fail_msg Uk stkG stkC rc RCW nx); mok_tac|]. intros m. apply usim_pure; intros Mm. cbn beta. xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp1]. }
  apply negb_false_iff in E20. apply Z.eqb_eq in E20.
  assert (RB : bytes_ok rest) by (rewrite R4; apply dsl_bytes).
  cbv zeta.
  case_if EV; [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp1]|].
  case_if ELT; [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp1]|].
  eapply ru_bind.
  { eapply ru_post; [apply (pr_open_common nx L0 tm pt off1 (pos + zlength rest) PCAP_SF_TOTAL HT); [pose proof L0_len; lia| rewrite L0_R63N; lia| left; reflexivity| lia| unfold VC0; lia| lia]|].
    intros r ? ? ? ? ? X; exact X. }
  intros r. apply usim_pure. intros [-> HT1]. cbn beta iota. cbv zeta.
  match goal with |- context [match ?x with Some scale_type => _ | None => _ end] => destruct x as [scale_type|] end.
  2:{ (* [comment removed for export] *)
    destruct (budget_pre _ _ 0 HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & X0).
    pose proof (bigb_nonneg 0) as B0.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ (N.succ nx) _ _ _ _ nx PCAP_SF_TOTAL HT1); [left; reflexivity| lia]. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT2| exact Hp1]. }
  match goal with |- context [let '(hdrsize, snapshot) := ?x in _] => destruct x as [hdrsize snapshot] eqn:EHS end. cbv zeta.
  (* [comment removed for export] *)
  assert (SNAP : 1 <= snapshot /\ (hdrsize = 16 \/ hdrsize = 24)).
  { assert (V : 0 <= (if swapped then bswap32 (get_le32 rest 12) else get_le32 rest 12)).
    { destruct swapped; [apply bswap32_range| apply get_le32_range; exact RB]. }
    pose proof (adjust_snapshot_range (linktype_to_dlt (Z.land (if swapped then bswap32 (get_le32 rest 16) else get_le32 rest 16) 65535)) _ V) as AR.
    destruct (magic_int =? KUZNETZOV_TCPDUMP_MAGIC).
    - injection EHS as E1 E2. subst hdrsize. split; [| right; reflexivity].
      destruct (_ =? DLT_EN10MB); [| subst snapshot; lia]. destruct (_ <=? INT_MAX - 14) eqn:E; subst snapshot; [lia| unfold INT_MAX; lia].
    - injection EHS as E1 E2. subst hdrsize snapshot. split; [lia| left; reflexivity]. }
  destruct SNAP as [SNAP HDR].
  set (bufsize := if 2048 <? snapshot then 2048 else snapshot).
  assert (BS : 1 <= bufsize <= 2048) by (subst bufsize; destruct (2048 <? snapshot) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
  destruct (budget_pre _ _ bufsize HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (Q1 & Q2 & Q3 & Q4).
  destruct (pot_pre (pt + PCAP_SF_TOTAL) (n1 bufsize) ltac:(unfold PCAP_SF_TOTAL; lia) ltac:(unfold n1, VC0, PCAP_SF_TOTAL; lia) ltac:(unfold n1; lia)) as [V1 V2].
  destruct (live_pre ((nx, PCAP_SF_TOTAL) :: L0) bufsize ltac:(rewrite liveL_cons; unfold n1, PCAP_SF_TOTAL; lia) ltac:(lia)) as [LV1 LV2].
  eapply ru_bind.
  { eapply (gr_malloc Uk _ _ (N.succ nx) (pt + PCAP_SF_TOTAL) _ _ _ bufsize HT1); [pose proof L0_len; rewrite zlen_cons; lia| lia| exact Q3| exact Q4| exact V1| exact V2| exact LV1| exact LV2]. }
  intros r. apply usim_pure. intros [-> HT2]. cbn beta iota.
  xfr; apply ru_ret. intros gh sG moG sC moC HR. eexists _, _, _, _, (pos + zlength rest). split; [| split; [| exact HR]]; [cbn [Q_check]; split|].
  - constructor; cbn; auto; [unfold BUFMAX; lia| unfold BUFMAX; lia].
  - unfold UPcapXA.toks, psize, ifas, L0 in *. cbn. exact HT2.
  - cbn [Q_pot]. unfold UPcapXA.PA, VIF. cbn [pc_priv]. unfold n1, VC0, PCAP_SF_TOTAL in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_ng_fail sl nx p tm pt off pos s i (m : list Z) :
  mok m -> PI p pos -> TML tm (toks p) -> pc_priv p = PrivNg s i -> PA sl p pos pt ->
  usimS (RPP nx tm pt off pos)
        (mbind (free_opt MOps PR_G (ng_ifaces_ptr_of p)) (fun _ => mbind (pfree HOG (pc_buffer p)) (fun _ => mbind (pfree HOG (pc_self p)) (fun _ => e_fret PR_G FF_NG_CHECK_HEADER (CH_Err m)))))
        (mbind (free_opt MOps PR_C (ng_ifaces_ptr_of p)) (fun _ => mbind (pfree HOC (pc_buffer p)) (fun _ => mbind (pfree HOC (pc_self p)) (fun _ => e_fret PR_C FF_NG_CHECK_HEADER (CH_Err m)))))
        PSTc.
Proof.
  intros Hm HPI HT HS HPA. cbn [e_fret prims]. pose proof (TML_nodup _ _ HT) as ND. pose proof (pi_pos _ _ _ HPI) as Hp. pose proof (PA_exit _ _ _ _ HPA HPI) as PX.
  assert (BUD : forall tm' L', TML tm' L' -> R63N (map snd L') <= R63N (map snd (toks p)) -> PHI P9 + R63N (map snd L') <= BLIVE).
  { intros tm' L' HT' HR'. destruct (RP_budget rc RCW p pos tm 0 HPI HT ltac:(unfold BUFMAX; lia)) as (_ & R2 & _).
    rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in R2. pose proof (bigb_nonneg 0). lia. }
  unfold ng_ifaces_ptr_of. rewrite HS. unfold UPcapXA.toks, psize, ifas in HT, ND, BUD. rewrite HS in HT, ND, BUD. cbn [map fst app] in ND.
  (* [comment removed for export] *)
  assert (NE12 : pc_buffer p <> pc_self p) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; left; reflexivity).
  destruct i as [q|].
  - cbn [app] in *.
    assert (NE13 : pc_buffer p <> q) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
    assert (NE23 : pc_self p <> q) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
    unfold free_opt. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_free prims]; xfe.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx _ _ _ _ q _ HT); [right; right; left; reflexivity|]. apply (BUD _ _ HT). lia. }
    intros []. apply usim_pure. intros HT1. cbn [lrm] in HT1. rewrite (proj2 (N.eqb_neq _ _) NE13), (proj2 (N.eqb_neq _ _) NE23), N.eqb_refl in HT1.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx _ _ _ _ (pc_buffer p) _ HT1); [left; reflexivity|]. apply (BUD _ _ HT1). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (ng_ifaces_size s * PCAP_NG_IF_SIZE)); lia. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx _ _ _ _ (pc_self p) _ HT2); [left; reflexivity|]. apply (BUD _ _ HT2). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (ng_ifaces_size s * PCAP_NG_IF_SIZE)); pose proof (bigb_nonneg (pc_bufalloc p)); lia. }
    intros []. apply usim_pure. intros HT3. rewrite lrm_head in HT3.
    xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT3| exact Hp].
  - cbn [app] in *. unfold free_opt. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_free prims]; xfe. xfr; apply ru_bind_retl.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx _ _ _ _ (pc_buffer p) _ HT); [left; reflexivity|]. apply (BUD _ _ HT). lia. }
    intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx _ _ _ _ (pc_self p) _ HT2); [left; reflexivity|]. apply (BUD _ _ HT2). cbn [map snd]; rewrite !R63N_cons; pose proof (bigb_nonneg (pc_bufalloc p)); lia. }
    intros []. apply usim_pure. intros HT3. rewrite lrm_head in HT3.
    xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT3| exact Hp].
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_short_notme nx tm pt off pos :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) -> PZ pt ->
  usimS (RPP nx tm pt off pos)
        (mbind (e_ferror PR_G fp) (fun e : bool => if e then mbind (errmsg_for_errno MOps PR_G "error reading dump file" []) (fun m => e_fret PR_G FF_NG_CHECK_HEADER (CH_Err m)) else e_fret PR_G FF_NG_CHECK_HEADER CH_NotMe))
        (mbind (e_ferror PR_C fp) (fun e : bool => if e then mbind (errmsg_for_errno MOps PR_C "error reading dump file" []) (fun m => e_fret PR_C FF_NG_CHECK_HEADER (CH_Err m)) else e_fret PR_C FF_NG_CHECK_HEADER CH_NotMe))
        PSTc.
Proof.
  intros HT Hp HPZ. cbn [e_fret prims]. eapply ru_bind; [apply (pr_ferror Uk stkG stkC rc RCW nx)|]. intros e. apply usim_pure. intros ->. xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp].
Qed.

#[using="Type"] Lemma MAX_BLOCKSIZE_range lt : 1 <= MAX_BLOCKSIZE_FOR_SNAPLEN (max_snaplen_for_dlt lt) <= BUFMAX.
Proof. unfold MAX_BLOCKSIZE_FOR_SNAPLEN, BUFMAX. pose proof (max_snaplen_range lt). lia. Qed.

#[using="STK RCW"] Lemma pr_pcap_ng_check_header fuel nx tm pt off pos magic precision :
  TML tm L0 -> 0 <= pos <= Z.of_nat (length d) -> Z.of_nat (length d) < Z.of_nat fuel -> PZ pt ->
  usimS (RPP nx tm pt off pos) (pcap_ng_check_header MOps PR_G fuel magic fp precision) (pcap_ng_check_header MOps PR_C fuel magic fp precision) PSTc.
Proof.
  intros HT Hp HF HPZ. pose proof HPZ as [HPZ1 HPZ2]. unfold pcap_ng_check_header. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_malloc e_free prims]; xfe. cbv zeta.
  case_if EM; [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp]|].
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm pt off pos SiteNgTotalLength 0 4 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? ? X; exact X. }
  intros tlb. eapply usim_exI; intros off1. apply usim_pure; intros (T1 & T2 & T3 & T4). pose proof (zlength_nonneg tlb) as NT.
  assert (Hp1 : 0 <= pos + zlength tlb <= Z.of_nat (length d)) by lia.
  case_if ET4; [apply (pr_short_notme nx tm pt off1 _ HT Hp1 HPZ)|]. apply Z.ltb_ge in ET4.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm pt off1 _ SiteNgByteOrderMagic 0 4 HT ltac:(left; reflexivity) Hp1); lia|]. intros r ? ? ? ? ? X; exact X. }
  intros bomb. eapply usim_exI; intros off2. apply usim_pure; intros (M1 & M2 & M3 & M4). pose proof (zlength_nonneg bomb) as NM.
  assert (Hp2 : 0 <= pos + zlength tlb + zlength bomb <= Z.of_nat (length d)) by lia.
  case_if EB4; [apply (pr_short_notme nx tm pt off2 _ HT Hp2 HPZ)|]. apply Z.ltb_ge in EB4.
  cbv zeta. lazymatch goal with |- usimX _ _ _ _ (match ?x with _ => _ end) _ _ => destruct x as [[ok swapped] TL] end. cbv beta iota zeta.
  case_if EOK; [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp2]|].
  case_if ETL; [xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT| exact Hp2]|].
  apply orb_false_iff in ETL as [ETL1 ETL2]. apply Z.ltb_ge in ETL1. apply Z.ltb_ge in ETL2. unfold BT_SHB_INSANE_MAX in ETL2.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (pr_open_common nx L0 tm pt off2 _ PCAP_NG_SF_TOTAL HT); [pose proof L0_len; lia| rewrite L0_R63N; lia| right; reflexivity| lia| unfold VC0; lia| lia]|]. intros r ? ? ? ? ? X; exact X. }
  intros r. apply usim_pure. intros [-> HT1]. cbn beta iota. cbv zeta.
  pose proof (budget_pre _ _ 0 HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (_ & _ & _ & X0).
  pose proof (bigb_nonneg 0) as B0.
  lazymatch goal with |- usimX _ _ _ _ (match ?x with _ => _ end) _ _ => destruct x as [user|] end.
  2:{ eapply ru_bind.
      { eapply (gr_free Uk _ _ (N.succ nx) _ _ _ _ nx PCAP_NG_SF_TOTAL HT1); [left; reflexivity| lia]. }
      intros []. apply usim_pure. intros HT2. rewrite lrm_head in HT2. xfr; apply pc_ret_notok; [first [exact I| mok_tac]| qpot| exact HT2| exact Hp2]. }
  cbv beta iota zeta.
  set (bufsize := if 2048 <? TL then TL else 2048).
  assert (BS : 2048 <= bufsize <= 1048576) by (subst bufsize; destruct (2048 <? TL) eqn:E; [apply Z.ltb_lt in E| apply Z.ltb_ge in E]; lia).
  destruct (budget_pre _ _ bufsize HT1 ltac:(pose proof L0_len; rewrite zlen_cons; lia) ltac:(cbn [map snd]; rewrite R63N_cons, L0_R63N, bigb_small by (unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia); lia) ltac:(unfold BUFMAX; lia)) as (Q1 & Q2 & Q3 & Q4).
  destruct (pot_pre (pt + PCAP_NG_SF_TOTAL) (n1 bufsize) ltac:(unfold PCAP_NG_SF_TOTAL; lia) ltac:(unfold n1, VC0, PCAP_NG_SF_TOTAL; lia) ltac:(unfold n1; lia)) as [V1 V2].
  destruct (live_pre ((nx, PCAP_NG_SF_TOTAL) :: L0) bufsize ltac:(rewrite liveL_cons; unfold n1, PCAP_NG_SF_TOTAL; lia) ltac:(lia)) as [LV1 LV2].
  eapply ru_bind.
  { eapply (gr_malloc Uk _ _ (N.succ nx) (pt + PCAP_NG_SF_TOTAL) _ _ _ bufsize HT1); [pose proof L0_len; rewrite zlen_cons; lia| lia| exact Q3| exact Q4| exact V1| exact V2| exact LV1| exact LV2]. }
  intros r. apply usim_pure. intros [-> HT2]. cbn beta iota. cbv zeta.
  (* [comment removed for export] *)
  set (p0 := mkPcap nx fp bufsize bufsize (N.succ nx) (le_bytes 4 (le_of_bytes magic) ++ le_bytes 4 TL ++ le_bytes 4 BYTE_ORDER_MAGIC) swapped 0 0 0 0 0 precision 0 [] hdr0
               (PrivNg (mkNg user INITIAL_MAX_BLOCKSIZE 0 0 []) None) : pcapT).
  assert (HPI0 : PI p0 (pos + zlength tlb + zlength bomb)).
  { constructor; cbn; auto; try (unfold BUFMAX; lia). unfold IFSMAX, INITIAL_MAX_BLOCKSIZE, BUFMAX. repeat split; lia. }
  assert (HT0 : TML (<[N.succ nx:=bufsize]> (<[nx:=PCAP_NG_SF_TOTAL]> tm)) (toks p0)) by (unfold UPcapXA.toks, psize, ifas, L0 in *; cbn; exact HT2).
  assert (PA0 : PA false p0 (pos + zlength tlb + zlength bomb) (pt + PCAP_NG_SF_TOTAL + n1 bufsize)).
  { unfold UPcapXA.PA, VIF. cbn [pc_priv p0 ng_ifaces_size]. unfold n1, VC0, PCAP_NG_SF_TOTAL in *. lia. }
  eapply (pp_bind Uk rc); [apply (pr_read_bytes Uk stkG stkC STK rc RCW _ p0 _ _ off2 _ (DHeap (N.succ nx) 12) (TL - 12) true HPI0 HT0); [cbn; lia| lia]|].
  intros [st data] p1 tm3 nx3 pt3 off3 pos3 (-> & -> & LB & -> & ST & CT) HPI3 HT3. cbn [fst snd] in LB, ST, CT. cbn beta iota. cbv zeta.
  set (p0' := set_bufdata (pc_bufdata p0 ++ data) p0).
  assert (HPI0' : PI p0' (pos + zlength tlb + zlength bomb + zlength data)) by (apply PI_set_bufdata; exact HPI3).
  assert (HT0' : TML tm3 (toks p0')) by exact HT3.
  assert (PA0' : PA false p0' (pos + zlength tlb + zlength bomb + zlength data) (pt + PCAP_NG_SF_TOTAL + n1 bufsize)).
  { eapply (PA_keep _ _ _ _ _ _ _ _ PA0); [apply pkeep_set_bufdata| pose proof (zlength_nonneg data); lia| discriminate]. }
  destruct st as [| |m].
  2:{ apply (pr_ng_fail false nx3 p0' tm3 _ off3 _ _ None [] mok_nil HPI0' HT0' eq_refl PA0'). }
  2:{ apply (pr_ng_fail false nx3 p0' tm3 _ off3 _ _ None m ST HPI0' HT0' eq_refl PA0'). }
  set (p0'' := if swapped then set_bufdata (swap_field 2 14 (swap_field 2 12 (pc_bufdata p0'))) p0' else p0').
  assert (HPI0'' : PI p0'' (pos + zlength tlb + zlength bomb + zlength data)) by (subst p0''; destruct swapped; [apply PI_set_bufdata|]; exact HPI0').
  assert (HT0'' : TML tm3 (toks p0'')) by (subst p0''; destruct swapped; exact HT0').
  assert (HS0'' : pc_priv p0'' = pc_priv p0) by (subst p0'' p0'; destruct swapped; reflexivity).
  assert (PA0'' : PA false p0'' (pos + zlength tlb + zlength bomb + zlength data) (pt + PCAP_NG_SF_TOTAL + n1 bufsize)).
  { eapply PA_mono; [exact PA0'| lia| unfold VIF; rewrite HS0''; reflexivity]. }
  case_if EVER; [eapply (pr_ng_fail false nx3 p0'' tm3 _ off3 (pos + zlength tlb + zlength bomb + zlength data) _ None); [mok_tac| exact HPI0''| exact HT0''| exact HS0''| exact PA0'']|].
  match goal with |- usimX _ _ _ _ (mbind (ng_find_idb _ _ _ ?q) _) _ _ => set (p2 := q) end.
  assert (HS2 : pc_priv p2 = PrivNg (mkNg user INITIAL_MAX_BLOCKSIZE 0 0 []) None) by (subst p2 p0'' p0' p0; destruct swapped; reflexivity).
  assert (HPI2 : PI p2 (pos + zlength tlb + zlength bomb + zlength data)).
  { pose proof HPI0'' as [X1 X2 X3 X4 X5 X6]. subst p2 p0'' p0' p0. destruct swapped; cbn in X2, X3, X4, X6; constructor; cbn; auto. }
  assert (HT2' : TML tm3 (toks p2)) by exact HT0''.
  assert (PA2 : PA false p2 (pos + zlength tlb + zlength bomb + zlength data) (pt + PCAP_NG_SF_TOTAL + n1 bufsize)).
  { eapply PA_mono; [exact PA0''| lia| unfold VIF; rewrite HS0'', HS2; reflexivity]. }
  eapply (pp_bind Uk rc); [apply (pr_ng_find_idb Uk stkG stkC STK rc RCW fuel nx3 p2 tm3 _ off3 _ _ None HPI2 HT2' HS2); [pose proof (zlength_nonneg data); lia| exact PA2]|].
  intros [r p3] p3' tm4 nx4 pt4 off4 pos4 (E4 & PS4 & LE4 & MM4 & PA4) HPI4 HT4. cbn [fst snd] in E4, MM4, PA4. subst p3'. cbn beta iota.
  destruct (psim_ng p2 p3 _ None PS4 HS2) as (s4 & i4 & HS4).
  destruct r as [m|idb_off].
  { apply (pr_ng_fail true nx4 p3 tm4 pt4 off4 _ _ _ m MM4 HPI4 HT4 HS4 PA4). }
  cbv zeta. unfold ng_of, ng_ifaces_ptr_of. rewrite HS4.
  xfr; apply ru_ret. intros gh sG moG sC moC HR. eexists tm4, nx4, pt4, off4, pos4. split; [| split; [| exact HR]]; [cbn [Q_check]|].
  - pose proof HPI4 as [X1 X2 X3 X4 X5 X6]. rewrite HS4 in X6. destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5).
    pose proof (MAX_BLOCKSIZE_range (linktype_to_dlt (get_le16 (pc_bufdata p3) idb_off))) as MB.
    split.
    + destruct (ng_max_blocksize s4 <? _); constructor; cbn; auto; repeat split; auto; lia.
    + unfold UPcapXA.toks, psize, ifas in HT4 |- *. rewrite HS4 in HT4. cbn in HT4 |- *. destruct (ng_max_blocksize s4 <? _); exact HT4.
  - cbn [Q_pot]. eapply PA_mono; [exact PA4| lia| unfold VIF; rewrite HS4; cbn [pc_priv]; destruct (ng_max_blocksize s4 <? _); reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition Q_open (r : list Z + pcapT) (tm' : gmap N Z) (pos' : Z) (pt' : Z) : Prop :=
  match r with
  | inr p => (PI p pos' /\ TML tm' (toks p)) /\ PA false p pos' pt'
  | inl m => ((TML tm' L0 /\ 0 <= pos' <= Z.of_nat (length d)) /\ mok m) /\ pt' <= P0 + V_READ
  end.
Definition PSTo : (list Z + pcapT) -> (list Z + pcapT) -> relX :=
  eqpost (fun r => fun gh sG moG sC moC => exists tm' nx' pt' off' pos', Q_open r tm' pos' pt' /\ RPP nx' tm' pt' off' pos' gh sG moG sC moC).

#[using="STK RCW"] Lemma pr_fopen_offline fuel nx tm pt off precision :
  TML tm L0 -> Z.of_nat (length d) < Z.of_nat fuel -> PZ pt ->
  usimS (RPP nx tm pt off 0) (pcap_fopen_offline_with_tstamp_precision MOps PR_G fuel fp precision)
        (pcap_fopen_offline_with_tstamp_precision MOps PR_C fuel fp precision) PSTo.
Proof.
  intros HT HF HPZ. unfold pcap_fopen_offline_with_tstamp_precision. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fileno prims]; xfe.
  assert (Hp : 0 <= 0 <= Z.of_nat (length d)) by lia.
  eapply ru_bind.
  { eapply ru_post; [apply (pr_freadS nx L0 tm pt off 0 SiteMagic 0 4 HT ltac:(left; reflexivity) Hp); lia|]. intros r ? ? ? ? ? X; exact X. }
  intros magic. eapply usim_exI; intros off1. apply usim_pure; intros (G1 & G2 & G3 & G4). pose proof (zlength_nonneg magic) as NM. rewrite Z.add_0_l in *.
  assert (Hp1 : 0 <= zlength magic <= Z.of_nat (length d)) by lia.
  case_if E4.
  { eapply ru_bind; [apply (pr_read_fail_msg Uk stkG stkC rc RCW nx); mok_tac|]. intros m. apply usim_pure; intros Mm. cbn beta.
    xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm, nx, pt, off1, (zlength magic). split; [| exact HR]. cbn. split; [auto| apply PZ_exit; exact HPZ]. }
  (* [comment removed for export] *)
  assert (FIN : forall (r : check_result) nx' tm' pt' off' pos', Q_check r tm' pos' -> Q_pot r pos' pt' ->
            usimS (RPP nx' tm' pt' off' pos')
                  (match r with CH_NotMe => fo_ret FOG _ FF_FOPEN_OFFLINE (inl Msg.unknown_file_format) | CH_Err m => fo_ret FOG _ FF_FOPEN_OFFLINE (inl m) | CH_Ok p => mbind (s_fileno HOG fp) (fun _ => fo_ret FOG _ FF_FOPEN_OFFLINE (inr p)) end)
                  (match r with CH_NotMe => fo_ret FOC _ FF_FOPEN_OFFLINE (inl Msg.unknown_file_format) | CH_Err m => fo_ret FOC _ FF_FOPEN_OFFLINE (inl m) | CH_Ok p => mbind (s_fileno HOC fp) (fun _ => fo_ret FOC _ FF_FOPEN_OFFLINE (inr p)) end)
                  PSTo).
  { intros [|m|p] nx' tm' pt' off' pos' Q QP; cbn in Q, QP.
    - xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm', nx', pt', off', pos'. split; [| exact HR]. split; [split; [exact Q| mok_tac]| apply PZ_exit; exact QP].
    - xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm', nx', pt', off', pos'. split; [exact (conj Q QP)| exact HR].
    - eapply ru_bind; [apply (pr_fileno Uk stkG stkC rc RCW nx')|]. intros fd. apply usim_pure. intros _.
      xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm', nx', pt', off', pos'. split; [exact (conj Q QP)| exact HR]. }
  eapply ru_bind; [apply (pr_pcap_check_header nx tm pt off1 (zlength magic) magic precision HT Hp1 HPZ)|].
  intros r1. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros off2. eapply usim_exI; intros pos1. apply usim_pure; intros Q1. apply usim_pure; intros QP1.
  destruct r1 as [|m|p]; [| apply (FIN (CH_Err m) _ _ _ _ _ Q1 QP1)| apply (FIN (CH_Ok p) _ _ _ _ _ Q1 QP1)].
  cbn in Q1, QP1. destruct Q1 as [HT1 Hp2].
  eapply ru_bind; [apply (pr_pcap_ng_check_header fuel nx1 tm1 pt1 off2 pos1 magic precision HT1 Hp2 HF QP1)|].
  intros r2. eapply usim_exI; intros tm2. eapply usim_exI; intros nx2. eapply usim_exI; intros pt2. eapply usim_exI; intros off3. eapply usim_exI; intros pos2. apply usim_pure; intros Q2. apply usim_pure; intros QP2.
  apply (FIN r2 _ _ _ _ _ Q2 QP2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition RCL (tm : gmap N Z) (nx : N) (pt : Z) : relX :=
  RUK tm nx pt Kx ((k_path e0, d) :: Cc) idl (WF oh (hrem fp hs) F0).

#[using="RCW"] Lemma kdel_KR off : kdel (k_fd e0) (KR_ off) = Kx.
Proof.
  unfold UPcapXA.KR_, kdel. rewrite filter_app. cbn [List.filter]. replace (k_fd (kat e0 off)) with (k_fd e0) by (destruct e0; reflexivity). rewrite Z.eqb_refl. cbn.
  rewrite app_nil_r. apply forallb_filter_id. rewrite forallb_forall. intros x Hx. destruct (Z.eqb_spec (k_fd x) (k_fd e0)) as [E|NE]; [exfalso; exact (rw_Kx _ RCW x Hx E)| reflexivity].
Qed.
#[using="RCW"] Lemma fdel_FR off pos : fdel fp (FR_ off pos) = F0.
Proof. unfold UPcapXA.FR_, fdel. cbn [List.filter fst]. rewrite N.eqb_refl. cbn. apply (fdel_notin fp F0). exact (rw_F0 _ RCW). Qed.
#[using="Type"] Lemma kpath_kat off : k_path (kat e0 off) = k_path e0.
Proof. destruct e0; reflexivity. Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_fclose_buf nx tm pt off pos buf ba self ps :
  TML tm ((buf, ba) :: (self, ps) :: (fp, FILE_ALLOC) :: B) -> 0 <= pos <= Z.of_nat (length d) -> 0 <= ba <= BUFMAX -> 0 <= ps < MMAP_THRESHOLD ->
  usimS (RPP nx tm pt off pos) (mbind (s_fclose HOG fp) (fun _ => pfree HOG buf)) (mbind (s_fclose HOC fp) (fun _ => pfree HOC buf))
        (eqpost (fun _ => fun gh sG moG sC moC => TML (delete buf (delete fp tm)) ((self, ps) :: B) /\ RCL (delete buf (delete fp tm)) nx pt gh sG moG sC moC)).
Proof.
  intros HT Hp Hba Hps. pose proof (TML_nodup _ _ HT) as ND. cbn [map fst] in ND.
  assert (NE1 : buf <> fp) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
  assert (NE2 : self <> fp) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
  pose proof (rw_B _ RCW) as [BL BR]. pose proof (bigb_le ba ltac:(lia)) as BB.
  assert (BUD : PHI P9 + R63N (sizes tm) <= BLIVE).
  { rewrite (R63N_perm _ _ (TML_sizes _ _ HT)). cbn [map snd]. rewrite !R63N_cons, bigb_FILE, (bigb_small ps) by lia. rewrite PHI_P9. unfold BASEB, B26, BUFMAX, BLIVE, PGSZ in *. lia. }
  eapply ru_bind.
  { apply (us_fclose_r Uk tm nx pt (KR_ off) Cc oh hs (FR_ off pos) fp (kat e0 off) d pos FILE_ALLOC (KR_in rc off) (own_kat rc RCW off) (rw_hs _ RCW) (FR_in rc off pos) (rw_oh _ RCW)
                               (conj (TML_lookup _ _ _ _ HT ltac:(right; right; left; reflexivity)) BUD)). }
  intros []. rewrite kdel_KR, fdel_FR, kpath_kat.
  pose proof (TML_delete _ _ _ _ HT ltac:(right; right; left; reflexivity)) as HT1. cbn [lrm] in HT1.
  rewrite (proj2 (N.eqb_neq _ _) NE1), (proj2 (N.eqb_neq _ _) NE2), N.eqb_refl in HT1.
  eapply ru_post; [eapply (gr_free Uk _ _ nx _ _ _ _ buf ba HT1); [left; reflexivity|]|].
  - rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in BUD. cbn [map snd] in BUD |- *. rewrite ?R63N_cons in BUD. rewrite ?R63N_cons in BUD. rewrite ?R63N_cons. rewrite bigb_FILE in BUD. lia.
  - intros [] ? ? ? ? ? [X Y]. rewrite lrm_head in X. exact (conj X Y).
Qed.

(* [comment removed for export] *)
#[using="RCW"] Lemma pr_free_self nx tm pt self ps :
  TML tm ((self, ps) :: B) -> 0 <= ps < MMAP_THRESHOLD ->
  usimS (RCL tm nx pt) (pfree HOG self) (pfree HOC self)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm', TML tm' B /\ RCL tm' nx pt gh sG moG sC moC)).
Proof.
  intros HT Hps. pose proof (rw_B _ RCW) as [BL BR].
  eapply ru_post; [eapply (gr_free Uk _ _ nx _ _ _ _ self ps HT); [left; reflexivity|]|].
  - cbn [map snd]. rewrite R63N_cons, (bigb_small ps) by lia. rewrite PHI_P9. unfold BASEB, B26, BLIVE, PGSZ in *. lia.
  - intros [] ? ? ? ? ? [X Y]. rewrite lrm_head in X. exists (delete self tm). exact (conj X Y).
Qed.

#[using="RCW"] Lemma pr_pcap_close nx p tm pt off pos :
  PI p pos -> TML tm (toks p) ->
  usimS (RPP nx tm pt off pos) (pcap_close MOps PR_G p) (pcap_close MOps PR_C p)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm', TML tm' B /\ RCL tm' nx pt gh sG moG sC moC)).
Proof.
  intros HPI HT. pose proof HPI as [P1 P2 P3 P4 P5 P6].
  unfold pcap_close, pcap_ng_cleanup, pcapint_sf_cleanup. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_free e_fclose prims]; xfe. rewrite P4.
  unfold UPcapXA.toks, psize, ifas in HT. destruct (pc_priv p) as [sf|s [q|]] eqn:HS; cbn [app] in HT.
  - eapply ru_bind; [apply (pr_fclose_buf nx tm pt off pos _ _ _ _ HT P1 ltac:(lia)); unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia|].
    intros []. apply usim_pure. intros HT1. apply (pr_free_self nx _ _ _ _ HT1). unfold PCAP_SF_TOTAL, MMAP_THRESHOLD; lia.
  - (* [comment removed for export] *)
    pose proof (TML_nodup _ _ HT) as ND. cbn [map fst] in ND.
    assert (NE13 : pc_buffer p <> q) by (inversion ND as [|? ? NI ND1]; subst; intros E; apply NI; rewrite E; right; left; reflexivity).
    assert (NE23 : pc_self p <> q) by (inversion ND as [|? ? NI ND1]; subst; inversion ND1 as [|? ? NI2 ND2]; subst; intros E; apply NI2; rewrite E; left; reflexivity).
    eapply ru_bind.
    + eapply ru_bind.
      * unfold free_opt, ng_ifaces_ptr_of. rewrite HS. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_free prims]; xfe.
        eapply (gr_free Uk _ _ nx _ _ _ _ q _ HT); [right; right; left; reflexivity|].
        destruct (RP_budget rc RCW p pos tm 0 HPI ltac:(unfold UPcapXA.toks, psize, ifas; rewrite HS; exact HT) ltac:(unfold BUFMAX; lia)) as (_ & R2 & _).
        rewrite (R63N_perm _ _ (TML_sizes _ _ HT)) in R2. pose proof (bigb_nonneg 0). lia.
      * intros []. apply usim_pure. intros HT1. cbn [lrm] in HT1. rewrite (proj2 (N.eqb_neq _ _) NE13), (proj2 (N.eqb_neq _ _) NE23), N.eqb_refl in HT1.
        apply (pr_fclose_buf nx _ _ off pos _ _ _ _ HT1 P1 ltac:(lia)). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
    + intros []. apply usim_pure. intros HT2. apply (pr_free_self nx _ _ _ _ HT2). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
  - (* [comment removed for export] *)
    eapply ru_bind.
    + unfold free_opt, ng_ifaces_ptr_of. rewrite HS. cbn [mo_ret MOps e_fenter e_fret prims]; xfe. xfr; apply ru_bind_retl.
      apply (pr_fclose_buf nx tm pt off pos _ _ _ _ HT P1 ltac:(lia)). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
    + intros []. apply usim_pure. intros HT2. apply (pr_free_self nx _ _ _ _ HT2). unfold PCAP_NG_SF_TOTAL, MMAP_THRESHOLD; lia.
Qed.

End ReadingD.

End WithCeil.
End UPcapXD.
