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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA UPcapXE.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require HeapDrive HeapSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ITreeA RunConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX AIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UMainX.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA UPcapXE. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
Definition V_MAIN : Z := READALL_V + RUNV.
Section WithCeil.

#[using="Type"] Lemma RUNV_nonneg : 0 <= RUNV.
Proof. unfold RUNV, V_ONE, V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX, FILE_ALLOC. lia. Qed.

Section UMainX.
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
#[local] Notation framed := framedX (only parsing).
#[local] Notation framed_exI := (framedX_exI (uk_nsafeP Uk) (uk_gstepP Uk) _ (npeek (uk_segs Uk))) (only parsing).
#[local] Notation framed_pure := (framedX_pure (uk_nsafeP Uk) (uk_gstepP Uk) _ (npeek (uk_segs Uk))) (only parsing).
#[local] Notation framed_use := (framedX_use (uk_nsafeP Uk) (uk_gstepP Uk) _ (npeek (uk_segs Uk))) (only parsing).
#[local] Notation framed_pre := (framedX_pre (uk_nsafeP Uk) (uk_gstepP Uk) _ (npeek (uk_segs Uk))) (only parsing).
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
#[local] Notation W0 := (WF None [] []).

(* [comment removed for export] *)
#[using="STK"] Theorem us_prog_main nx pt argv (Q : Empty_set -> Empty_set -> relX) :
  Forall (fun a => zlength a <= ARGMAX) argv -> pot_ok (pt + V_MAIN) ->
  usimS (RUK ∅ nx pt [] [] idl W0) (prog_main HOG (uk_FOG Uk) stkG argv) (prog_main HOC (uk_FOC Uk) stkC argv) Q.
Proof.
  intros Hargv HOK. unfold prog_main, V_MAIN in *. rewrite Z.add_assoc in HOK.
  eapply usim_bind; [apply (us_main_prog Uk stkG stkC RUNV RUNV_nonneg (us_run Uk stkG stkC STK) nx pt argv Hargv HOK)|].
  intros codeG codeC. apply usim_pure; intros <-.
  eapply usim_exI; intros tm'. eapply usim_exI; intros nx'. eapply usim_exI; intros pt'. eapply usim_exI; intros K'. eapply usim_exI; intros C'.
  eapply usim_exI; intros oh'. eapply usim_exI; intros hs'. eapply usim_exI; intros F'.
  apply usim_pure; intros XK. apply (us_exit_model Uk). exact XK.
Qed.
End UMainX.
End WithCeil.
End UMainX.

(* [comment removed for export] *)
Module TopX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.KPin OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UNodes__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UPcapB__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UPcapB__Equiv.UMain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA RunConst NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA UPcapXE. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX AIface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.ProgT OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXE OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UMainX__EquivA.UMainX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.HeapI_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.HeapI_SA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma FI_std segs lim en inp mo nx : m_fds mo = m_fds (mo0 segs lim en inp) -> FI nx [] [] libc_init mo.
Proof.
  intros EF. apply FI_init; rewrite EF; unfold mo0; rewrite m_fds_init_model.
  - cbn. assert (D : forall a b, Z_to_bv 64 a = Z_to_bv 64 b -> 0 <= a < 3 -> 0 <= b < 3 -> a = b).
    { intros a b E Ha Hb. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E. }
    constructor. { intros [H|[H|[]]]; [pose proof (D _ _ H ltac:(lia) ltac:(lia))| pose proof (D _ _ H ltac:(lia) ltac:(lia))]; lia. }
    constructor. { intros [H|[]]. pose proof (D _ _ H ltac:(lia) ltac:(lia)). lia. }
    constructor. { intros []. } constructor.
  - intros k en0 Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; eexists; (split; [reflexivity| rewrite unsigned_lit by lia; lia]).
Qed.

(* [comment removed for export] *)
Lemma etwfX_leavesX {G} (nsafeP : node -> G -> Model -> Prop) (gstepP : node -> resp -> G -> G) {A} (t : itree node (exc A)) g mo :
  etwfX nsafeP gstepP t g mo (fun _ _ _ => False) -> leaves_unreachable_m nstep t mo.
Proof.
  intros H tr r mo' Hp. destruct (tpath_tpathX gstepP t g mo tr r mo' Hp) as [g' Hp'].
  pose proof (twfX_tpathX _ _ _ _ _ _ _ _ _ _ H Hp') as HP. destruct r; exact HP.
Qed.

Lemma minvX_of_minv mo : minv mo -> minvX mo.
Proof.
  intros H. unfold minvX. replace (lf mo) with mo; [exact H|]. destruct (minv_lazyfree mo H) as [E1 E2].
  destruct mo as [fd [vmm lz mat] io fs pr lm tm]. cbn in E1, E2. subst. reflexivity.
Qed.

Section TopX.
Context {rc : runConstT}.
Context {CES : CEIL}.
Variable NMAX : nat.
Variable site_frame : Pcap.stack_site -> option (Pcap.fframe * Z).
Variable AH : AHalves NMAX site_frame.
(* [comment removed for export] *)
Variables (segsS : list Segment) (limS : Z) (enS : ExecEntry) (inp : ProcInput) (tbS : Z) (stkS : stack_site -> Z) (secS : Z).
Hypothesis IOS : image_ok segsS limS.
Hypothesis BRKS : valid_brk segsS (en_brk enS).
Hypothesis TLSS : tls_in_image segsS tbS.
Hypothesis STKS : stk_ok stkS.
Hypothesis ARGV : Forall (fun a => zlength a <= ARGMAX) (argv_Z (in_argv inp)).
Hypothesis VIN : valid_input inp.
Hypothesis CEQS : alloc_ceiling (CEIL:=CES) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segsS limS enS inp))).
Hypothesis SECS : 0 <= secS < 2^64.
(* [comment removed for export] *)
Variables (segsA : list Segment) (stkA : stack_site -> Z) (sA : PState aheap hptr) (moA : Model) (g0 : alw).
Hypothesis STKA : stk_ok stkA.
Hypothesis AHM : aG NMAX site_frame AH ∅ 0%N 0 g0 sA moA.
Hypothesis ALC : ps_libc sA = libc_init.
Hypothesis AOF : ps_outfile sA = None.
Hypothesis AMX : minvX moA.
Hypothesis AFDS : m_fds moA = m_fds (mo0 segsS limS enS inp).
Hypothesis AFS : m_fs moA = m_fs (mo0 segsS limS enS inp).
Hypothesis AHALT : m_halted moA = None.

#[local] Notation HOS := (full_ops (CE:=CES)).
#[local] Notation HOA := (asan_ops (CE:=ceil_of_rc)).
#[local] Notation FOA := (asan_fo site_frame).
#[local] Notation sS0 := (ps_init (fheap_init secS (reservedZ segsS))).
#[local] Notation moS0 := (mo0 segsS limS enS inp).
#[local] Notation argv := (argv_Z (in_argv inp)).
#[local] Notation KSA := (UK_SA NMAX site_frame AH segsA).
#[local] Notation KAS := (UK_AS NMAX site_frame AH segsS).
(* [comment removed for export] *)
Definition TREE_S : itree node (exc unit) := prog_itree HOS tbS (fheap_init secS (reservedZ segsS)) fo_nop stkS (in_argv inp).
Definition TREE_A : itree node (exc unit) := prog_main_itree HOA FOA stkA (in_argv inp) sA.

#[using="secS SECS"] Lemma V_MAIN_ok : pot_ok (0 + V_MAIN).
Proof. unfold pot_ok, V_MAIN, READALL_V, RUNV, V_ONE, V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX, FILE_ALLOC, VOLMAX. lia. Qed.

(* [comment removed for export] *)
#[using="IOS BRKS SECS"] Lemma ShiQ_main tb t moS1 : startup_mo (CE:=CES) segsS limS enS inp tb t moS1 -> ShiQ (CE:=CES) ∅ 0%N 0 (set_tls_pin HOS tb sS0) moS1.
Proof.
  intros SM. split; [exact (HQ_main (CE:=CES) inp segsS limS enS secS tb t moS1 IOS BRKS SECS SM)|].
  split; [cbn; unfold tok_szmap; cbn; apply fmap_empty|]. split; [reflexivity|]. unfold pot_ok, VOLMAX. lia.
Qed.

(* [comment removed for export] *)
#[using="IOS BRKS SECS g0 AHM ALC AOF AFDS AFS AHALT"] Lemma R_SA tb t moS1 : startup_mo (CE:=CES) segsS limS enS inp tb t moS1 ->
  RelX.RX unsafeS ugstepS HOS HOA segsA (HeapI_SA NMAX site_frame AH segsA) ∅ 0%N 0 (UK 0%N [] [] (fun l => l) (WF None [] []))
          tt (set_tls_pin HOS tb sS0) moS1 sA moA.
Proof.
  intros SM. pose proof SM as (_ & EF & ES & EH & _ & _ & _ & MI & _).
  split; [| split; [exact (FI_main (CE:=CES) _ _ _ _ _ _ _ 0%N SM)| split; [reflexivity|]; split; [constructor|]; split; [intros ? []| intros ? ? ? []]]].
  split; [exact (ShiQ_main tb t moS1 SM)|]. split; [exists g0; exact AHM|]. split; [exact (minvX_of_minv _ MI)|]. split; [exact EH|].
  split; [cbn; exact ALC|]. split; [cbn; exact AOF|]. split; [| cbn; apply LCI_init].
  unfold mqX. rewrite AFDS, AFS, AHALT, EF, ES, EH. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="IOS BRKS SECS AHM ALC AOF AMX AFDS AFS AHALT"] Lemma R_AS tb t moS1 : startup_mo (CE:=CES) segsS limS enS inp tb t moS1 ->
  RelX.RX (nsafePA NMAX) gstepA HOA HOS segsS (HeapI_AS NMAX site_frame AH segsS) ∅ 0%N 0 (UK 0%N [] [] (fun l => l) (WF None [] []))
          g0 sA moA (set_tls_pin HOS tb sS0) moS1.
Proof.
  intros SM. pose proof SM as (_ & EF & ES & EH & _ & _ & _ & MI & _).
  split; [| split; [rewrite ALC; exact (FI_std segsS limS enS inp moA 0%N AFDS)| rewrite ALC, AOF; split; [reflexivity|]; split; [constructor|]; split; [intros ? []| intros ? ? ? []]]].
  split; [exact AHM|]. split; [exact (ShiQ_main tb t moS1 SM)|]. split; [exact AMX|]. split; [exact AHALT|].
  split; [cbn; symmetry; exact ALC|]. split; [cbn; symmetry; exact AOF|]. split; [| rewrite ALC; apply LCI_init].
  unfold mqX. rewrite AFDS, AFS, AHALT, EF, ES, EH. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="NMAX AH IOS BRKS TLSS STKS ARGV VIN CEQS SECS g0 AHM ALC AOF AFDS AFS AHALT"] Theorem sim_SA full : texit nstep nexit TREE_S moS0 full -> wexit (npeek segsA) nstep nexit TREE_A moA (eq full).
Proof.
  intros HX. unfold TREE_S, prog_itree in HX. rewrite (prog_split HOS) in HX. unfold mbind in HX.
  apply texit_ebind in HX as [HX|(tr1 & [e s'] & mo1 & tr2 & _ & HX & _)]; [| destruct e].
  apply texit_ebind in HX as [HX|(tr1 & [[] s1] & moS1 & tr2 & HP & HX & ->)].
  { exfalso. exact (startup_texit (set_tls_pin HOS) segsS limS enS inp tbS sS0 full HX). }
  destruct (startup_tpath (CE:=CES) (set_tls_pin HOS) segsS limS enS inp tbS TLSS VIN CEQS sS0 tr1 _ moS1 HP) as (tb & t & E & -> & _ & Ht & SM).
  injection E as Es. subst s1. cbn [fst snd app] in HX |- *.
  pose proof (us_prog_main KSA stkS stkA STKS 0%N 0 argv (fun _ _ => fun _ _ _ _ _ => True) ARGV V_MAIN_ok) as U.
  destruct (U tt (set_tls_pin HOS tb sS0) moS1 sA moA (R_SA tb t moS1 SM)) as (_ & HE & _).
  unfold TREE_A, prog_main_itree. apply wexit_ebind_l. exact (HE _ HX).
Qed.

(* [comment removed for export] *)
#[using="NMAX AH IOS BRKS TLSS ARGV VIN CEQS SECS g0 STKA AHM ALC AOF AMX AFDS AFS AHALT"] Theorem sim_AS full : texit nstep nexit TREE_A moA full -> wexit (npeek segsS) nstep nexit TREE_S moS0 (eq full).
Proof.
  intros HX. unfold TREE_A, prog_main_itree in HX.
  apply texit_ebind in HX as [HX|(tr1 & [e s'] & mo1 & tr2 & _ & HX & _)]; [| destruct e].
  destruct (startup_exists (CEC:=CES) segsS limS enS inp tbS IOS TLSS VIN CEQS secS secS SECS SECS sS0 1 ltac:(unfold Fork.PID_MAX_ENVELOPE; lia)) as (tb & moS1 & TP & SM).
  pose proof (us_prog_main KAS stkA stkS STKA 0%N 0 argv (fun _ _ => fun _ _ _ _ _ => True) ARGV V_MAIN_ok) as U.
  destruct (U g0 sA moA (set_tls_pin HOS tb sS0) moS1 (R_AS tb 1 moS1 SM)) as (_ & HE & _).
  unfold TREE_S, prog_itree. rewrite (prog_split HOS). unfold mbind. apply wexit_ebind_l. apply wexit_ebind_r.
  eapply wreach_mono; [exact (tpath_wreach _ _ _ _ _ _ _ _ (startup_npfree segsS (CE:=CES) tbS sS0) TP)|].
  intros tr r mo' (-> & -> & ->). eexists. split; [reflexivity|]. cbn [fst snd app]. exact (HE _ HX).
Qed.

(* [comment removed for export] *)
#[using="CES AH segsS limS enS tbS stkS secS IOS BRKS TLSS ARGV VIN CEQS SECS STKA AHM ALC AOF AMX AFDS AFS AHALT"] Theorem safe_A : leaves_unreachable_m nstep TREE_A moA
  /\ tsafeA nstepA (nsafeA NMAX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.ASHM0) ProtoS.fstepS NMAX (RNGof g0 moA) g0 TREE_A moA.
Proof.
  destruct (startup_exists (CEC:=CES) segsS limS enS inp tbS IOS TLSS VIN CEQS secS secS SECS SECS sS0 1 ltac:(unfold Fork.PID_MAX_ENVELOPE; lia)) as (tb & moS1 & TP & SM).
  pose proof (us_prog_main KAS stkA stkS STKA 0%N 0 argv (fun _ _ => fun _ _ _ _ _ => True) ARGV V_MAIN_ok) as U.
  pose proof (usimX_safe _ _ _ _ _ _ _ g0 sA moA (set_tls_pin HOS tb sS0) moS1 U (R_AS tb 1 moS1 SM)) as SAFE.
  assert (W : etwfX (nsafePA NMAX) gstepA TREE_A g0 moA (fun _ _ _ => False)).
  { unfold TREE_A, prog_main_itree. apply etwfX_ebind. eapply etwfX_mono; [exact SAFE|]. intros [e s'] g1 mo1 _. destruct e. }
  split; [exact (etwfX_leavesX _ _ _ _ _ W)|].
  eapply TS_tsafeA. eapply (twfX_TS NMAX TREE_A g0 moA _ (fun _ _ _ _ => True)); [exact W|].
  intros [|a] A' mo' HF; destruct HF.
Qed.
End TopX.
End TopX.
