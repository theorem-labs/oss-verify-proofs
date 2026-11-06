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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require AcctCore ExecF ITreeA NodesAS ProtoS RunConst RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed AsanCtrlProps AsanInv AsanBudget.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeAlloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require SizeHist.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX AIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UDriverX.
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).

(* [comment removed for export] *)
Section WithCeil.
(* [comment removed for export] *)
Definition ARGMAX : Z := 131071.

(* [comment removed for export] *)
Definition READALL_V : Z := 2^28 + 2^17.

Section UDriver.
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
Variables (stkG stkC : stack_site -> Z).
#[local] Notation RUK tm nx pt K C g W := (RX tm nx pt (UK nx K C g W)).
#[local] Notation W0 := (WF None [] []).
#[local] Notation FOG := (uk_FOG Uk).
#[local] Notation FOC := (uk_FOC Uk).
#[local] Notation runG := (Prog.run HOG FOG stkG).
#[local] Notation runC := (Prog.run HOC FOC stkC).
(* [comment removed for export] *)
Variable RUNV : Z.
Hypothesis RUNV0 : 0 <= RUNV.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition exit_ok (K : list kfe) : Prop := forall e h, In e K -> k_own e = Some h -> k_kind e = KNull /\ k_data e = None.

(* [comment removed for export] *)
Hypothesis us_run : forall tm nx pt config payload,
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> live1 tm <= MAX_INPUT -> zlength payload < MAX_INPUT ->
  pot_ok (pt + RUNV) ->
  usimS (RUK tm nx pt [] [] idl W0) (runG config payload) (runC config payload)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' K' C' oh' hs' F',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\ pt' <= pt + RUNV /\
                   RUK tm' nx' pt' K' C' idl (WF oh' hs' F') gh sG moG sC moC)).

(* [comment removed for export] *)
#[using="Type"] Lemma RUK_lift tm nb nx' pt K C g W gh sG moG sC moC :
  RX tm nx' pt (UK nb K C g W) gh sG moG sC moC -> (nb <= nx')%N -> RX tm nx' pt (UK nx' K C g W) gh sG moG sC moC.
Proof. intros [HR [HF HW]] LE. split; [exact HR|]. split; [exact (FI_mono_nx _ _ _ _ _ _ LE HF)| exact HW]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma Forall_lt_of_le B (ps : list (list Z)) : B < 2^61 -> Forall (fun p => zlength p <= B) ps -> Forall (fun p => zlength p < 2^61) ps.
Proof. intros HB H. eapply Forall_impl; [| exact H]. cbn. intros; lia. Qed.

#[using="Type"] Lemma us_diag tm nx pt K C oh hs F d :
  match d with DUsage a | DCannotOpen a | DReadError a => zlength a <= ARGMAX | _ => True end ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (Prog.diag d : Monad.M PSG unit) (Prog.diag d) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  intros Hd. destruct d; cbn [Prog.diag]; unfold diag_usage, diag_cannot_open, diag_read_error, diag_oom, diag_too_big, diag_short_hdr, diag_cfg_overrun.
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_usage. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_cannot_open. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_eprintf. apply (Forall_lt_of_le ARGMAX); [unfold ARGMAX; lia|]. unfold pieces_read_error. apply pieces_small; [unfold ARGMAX; lia| items_small_tac| args_small_tac].
  - apply us_efwrite. vm_compute. reflexivity.
  - apply us_eprintf. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_too_big. apply pieces_small; [lia| items_small_tac| args_small_tac].
  - apply us_efwrite. vm_compute. reflexivity.
  - apply us_efwrite. vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma us_emit_d tm nx pt K C oh hs F rc :
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (emit_d ps_libc set_libc rc : Monad.M PSG unit) (emit_d ps_libc set_libc rc) (eqpost (fun _ => RUK tm nx pt K C idl (WF oh hs F))).
Proof.
  unfold emit_d. apply us_printf. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_emit_d. apply pieces_small; [lia| items_small_tac| args_small_tac].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[local] Notation read_loop_bodyG := (read_loop_body (@Prog.diag _ hptr) (pmalloc HOG) (pfree HOG) (stkG SiteReadStage)).
#[local] Notation read_loop_bodyC := (read_loop_body (@Prog.diag _ hptr) (pmalloc HOC) (pfree HOC) (stkC SiteReadStage)).
#[local] Notation read_allG := (read_all (@Prog.diag _ hptr) (pmalloc HOG) (pfree HOG) (stkG SiteReadStage)).
#[local] Notation read_allC := (read_all (@Prog.diag _ hptr) (pmalloc HOC) (pfree HOC) (stkC SiteReadStage)).

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_useR {A} tm nx pt K C W (m : Monad.M PSG A) (m' : Monad.M PSC A) Q :
  (forall gh sG moG sC moC, RQ tm nx pt gh sG moG sC moC -> usimS (RUK tm nx pt K C idl W) m m' Q) -> usimS (RUK tm nx pt K C idl W) m m' Q.
Proof. intros H. apply ru_use. intros ? ? ? ? ? [HR _]. exact (H _ _ _ _ _ HR). Qed.

(* [comment removed for export] *)
Definition rd_pot (pt0 : Z) (st : @rd_st hptr) (pt : Z) : Prop := pt0 <= pt <= pt0 + 4 * rd_cap st - 3 * 65536.

Definition RDpostU (e : kfe) (pt0 : Z) (st : @rd_st hptr) (r : @rd_st hptr + @rd_result hptr) : relX := fun gh sG moG sC moC =>
  exists tm' nx' pt', RUK tm' nx' pt' [e] [] idl W0 gh sG moG sC moC /\
  match r with
  | inl st' => RD st' tm' /\ rd_len st < rd_len st' /\ rd_pot pt0 st' pt'
  | inr RdExit => pt0 <= pt' <= pt0 + READALL_V
  | inr (RdDone buf content) => (exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT) /\ pt0 <= pt' <= pt0 + READALL_V
  end.

#[using="Type"] Lemma rd_pot_final pt0 st pt : rd_pot pt0 st pt -> rd_cap st <= MAX_INPUT -> pt0 <= pt <= pt0 + READALL_V.
Proof. unfold rd_pot, READALL_V, MAX_INPUT. lia. Qed.

#[using="Type"] Lemma us_read_loop_body e path nx st tm pt0 pt :
  k_own e = None -> k_data e = None -> zlength path <= ARGMAX ->
  RD st tm -> rd_pot pt0 st pt -> pot_ok (pt0 + READALL_V) ->
  usimS (RUK tm nx pt [e] [] idl W0) (read_loop_bodyG (k_fd e) path st) (read_loop_bodyC (k_fd e) path st) (eqpost (RDpostU e pt0 st)).
Proof.
  intros Ho ED Hpath HRD HPOT HOK. pose proof HRD as (Etm & Hcap & Hlen & Hcont & kc & Hk & Ek). unfold read_loop_body. cbv zeta.
  apply ruk_useR. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (RQ_fresh tm nx pt _ _ _ _ _ HR0) as FR. pose proof (RQ_pot tm nx pt _ _ _ _ _ HR0) as POK. unfold pot_ok in POK. clear HR0 gh0 sG0 moG0 sC0 moC0.
  assert (NEb : rd_buf st <> nx) by (intros E; rewrite <- E, Etm in FR; apply lookup_singleton_None in FR; exact (FR eq_refl)).
  pose proof (rd_pot_final pt0 st pt HPOT ltac:(lia)) as PF.
  (* [comment removed for export] *)
  eapply ru_bind2 with (Q1 := fun g g' => fun gh sG moG sC moC => g = g' /\ exists tm' nx' pt',
      RUK tm' nx' pt' [e] [] idl W0 gh sG moG sC moC /\ pt0 <= pt' <= pt0 + READALL_V /\
      match g with None => True | Some st1 => RD st1 tm' /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1 /\ rd_pot pt0 st1 pt' end).
  { destruct (rd_len st =? rd_cap st) eqn:EL.
    - apply Z.eqb_eq in EL. destruct (MAX_INPUT <=? rd_cap st) eqn:EM.
      + eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
        apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm, nx, pt. split; [exact HR|]. split; [exact PF| exact I].
      + apply Z.leb_gt in EM. destruct (cap_double _ _ Hk Ek EM) as [C2 E2].
        destruct (RD_budget st tm (rd_cap st * 2) HRD ltac:(lia)) as (R1 & R2 & R3).
        unfold rd_pot in HPOT.
        assert (PM : pre_malloc tm pt (rd_cap st * 2)).
        { split; [lia|]. split; [unfold size_overflows; apply Z.leb_gt; unfold MAX_INPUT in *; lia|]. split; [exact R3|]. split; [exact R1|]. split; [exact R2|].
          rewrite n1_id by lia. unfold apre. rewrite Etm. unfold live1. rewrite sizes_single. cbn [map zsum fold_right]. rewrite n1_id by lia. rewrite zlen_cons, zlen_nil.
          unfold pot_ok, READALL_V, NMAXA, LIVEMAX, LIVECNT, VOLMAX, MAX_INPUT in *. lia. }
        eapply ru_bind2; [apply (ru_pmalloc tm nx pt _ _ (rd_cap st * 2) (UK_stable _ _ _ _ _) PM)|].
        intros a b. apply usim_pure; intros <-. apply usim_pure; intros ->.
        assert (Hold : <[nx := rd_cap st * 2]> tm !! rd_buf st = Some (rd_cap st)).
        { rewrite lookup_insert_ne by (intros E; exact (NEb (eq_sym E))). rewrite Etm. apply lookup_singleton_eq. }
        eapply ru_bind2.
        { apply (ru_pfree _ (N.succ nx) _ _ _ (rd_buf st) (rd_cap st) (UK_stable _ _ _ _ _)).
          split; [exact Hold|].
          rewrite (R63N_insert tm nx _ FR). rewrite PHI_P9. rewrite Etm, sizes_single. unfold R63N. cbn [zsum map fold_right].
          pose proof (bigb_B26 (rd_cap st) ltac:(lia)). pose proof (bigb_B26 (rd_cap st * 2) ltac:(lia)). unfold B26, BLIVE, PGSZ in *. lia. }
        intros [] []. cbn beta. apply usim_pure; intros _. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|].
        exists (delete (rd_buf st) (<[nx := rd_cap st * 2]> tm)), (N.succ nx), (pt + n1 (rd_cap st * 2)).
        split; [exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ _ _ HR ltac:(lia))|].
        rewrite n1_id by lia. split; [unfold READALL_V, MAX_INPUT in *; lia|].
        assert (EC : rd_content (mkRd nx (rd_cap st * 2) (rd_len st) (rd_chunks st)) = rd_content st) by reflexivity.
        unfold RD, rd_pot. cbn [rd_buf rd_cap rd_len rd_chunks]. rewrite EC.
        split; [| split; [lia| split; [lia| split; [reflexivity| split; lia]]]].
        split; [| split; [lia| split; [lia| split; [exact Hcont| exists (kc + 1); split; [lia| exact E2]]]]].
        rewrite delete_insert_ne by exact NEb. rewrite Etm. rewrite delete_singleton_eq. reflexivity.
    - apply Z.eqb_neq in EL. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm, nx, pt. split; [exact HR|]. split; [exact PF|]. split; [exact HRD|]. unfold rd_pot in *. repeat split; lia.
  }
  intros g g'. apply usim_pure; intros <-. destruct g as [st1|].
  2:{ apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros pt'. eapply ru_pre; [| intros ? ? ? ? ? [H [HP _]]; exact (conj HP H)].
      apply usim_pure; intros HP'. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm', nx', pt'. split; [exact HR| exact HP']. }
  apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros pt1.
  eapply (ru_pre _ (fun gh sG moG sC moC => (RD st1 tm1 /\ rd_len st1 = rd_len st /\ rd_len st1 < rd_cap st1 /\ rd_content st1 = rd_content st /\ rd_cap st <= rd_cap st1 /\ rd_pot pt0 st1 pt1) /\ RUK tm1 nx1 pt1 [e] [] idl W0 gh sG moG sC moC));
    [| intros ? ? ? ? ? [H1 [_ H2]]; split; [exact H2| exact H1]].
  apply usim_pure. intros (HRD1 & EL1 & LT1 & EC1 & LC1 & HPOT1). pose proof HRD1 as (Etm1 & Hcap1 & Hlen1 & Hcont1 & k1 & Hk1 & Ek1).
  pose proof (rd_pot_final pt0 st1 pt1 HPOT1 ltac:(lia)) as PF1.
  (* [comment removed for export] *)
  eapply ru_bind2; [apply ru_get|]. intros sG sC. apply usim_pointwise. intros ? ? ? ? ? (-> & -> & EL & EO & HRQ).
  eapply ru_pre; [| intros ? ? ? ? ? (-> & -> & -> & -> & ->); exact HRQ]. cbv zeta.
  set (want := if READ_CHUNK <? rd_cap st1 - rd_len st then READ_CHUNK else rd_cap st1 - rd_len st) in *.
  assert (Hwant : 0 <= want <= rd_cap st1 - rd_len st) by (subst want; unfold READ_CHUNK; destruct (65536 <? rd_cap st1 - rd_len st) eqn:E'; [apply Z.ltb_lt in E'| apply Z.ltb_ge in E']; lia).
  eapply ru_bind.
  { eapply ru_post; [apply ru_read; eapply (unode_lift _ _ (FI nx1 [e] []) _ idl W0); apply (fn_read nx1 [e] [] e _ want ltac:(left; reflexivity)); unfold MAX_INPUT in *; lia|].
    intros a ? ? ? ? ? [HR [RP HW]]. instantiate (1 := fun a => fun gh sG moG sC moC => match a with RdErr _ => True | RdData bs => Z.of_nat (length bs) <= want end /\ RUK tm1 nx1 pt1 [e] [] idl W0 gh sG moG sC moC).
    cbn beta. destruct a as [err|bs]; cbn in RP.
    - split; [exact I|]. split; [exact HR|]. split; [exact (proj2 RP)| exact HW].
    - destruct RP as (_ & LEB & RP). rewrite ED in RP. split; [exact LEB|]. split; [exact HR|]. split; [exact RP| exact HW]. }
  intros a. cbv beta. apply usim_pure. intros HL0.
  destruct a as [err|bs].
  - eapply ru_bind2; [apply us_diag; exact Hpath|]. intros [] []. apply usim_pure; intros _.
    apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1, pt1. split; [exact HR| exact PF1].
  - assert (HL : zlength (of_bytes bs) = Z.of_nat (length bs)) by (unfold zlength, of_bytes; rewrite length_map; reflexivity).
    assert (HLb : zlength bs = Z.of_nat (length bs)) by reflexivity.
    destruct (length bs =? 0)%nat eqn:EB.
    + apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1, pt1. split; [exact HR|]. split; [| exact PF1]. exists (rd_cap st1). split; [exact Etm1| rewrite Hcont1; lia].
    + apply Nat.eqb_neq in EB. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm1, nx1, pt1. split; [exact HR|]. split; [| split; [cbn [rd_len]; lia|]].
      * unfold RD. cbn [rd_cap rd_len rd_buf rd_chunks]. split; [exact Etm1|]. split; [lia|].
        split; [lia|]. split; [rewrite rd_content_app, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.zlength_app, Hcont1; lia| exists k1; auto].
      * unfold rd_pot in *. cbn [rd_cap]. lia.
Qed.

(* [comment removed for export] *)
Definition RLpostU (e : kfe) (pt0 : Z) (r : @rd_result hptr) : relX := fun gh sG moG sC moC =>
  exists tm' nx' pt', RUK tm' nx' pt' [e] [] idl W0 gh sG moG sC moC /\ pt0 <= pt' <= pt0 + READALL_V /\
  match r with
  | RdExit => True
  | RdDone buf content => exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

(* [comment removed for export] *)
Definition RApostU (pt0 : Z) (r : @rd_result hptr) : relX := fun gh sG moG sC moC =>
  exists tm' nx' pt' K', exit_ok K' /\ RUK tm' nx' pt' K' [] idl W0 gh sG moG sC moC /\ pt0 <= pt' <= pt0 + READALL_V /\
  match r with
  | RdExit => True
  | RdDone buf content => K' = [] /\ exists cap, tm' = {[ buf := cap ]} /\ zlength content < cap <= MAX_INPUT
  end.

#[using="Type"] Lemma us_read_all nx pt path :
  zlength path <= ARGMAX -> pot_ok (pt + READALL_V) ->
  usimS (RUK ∅ nx pt [] [] idl W0) (read_allG path) (read_allC path) (eqpost (RApostU pt)).
Proof.
  intros Hpath HOK. unfold read_all.
  (* [comment removed for export] *)
  eapply ru_bind.
  { eapply ru_post; [apply (ruk_node Uk ∅ nx pt [] [] idl W0 (NOpen (to_bytes path)) dec_open _ I (fn_open nx [] [] (to_bytes path) ltac:(intros ? [])))|].
    intros r ? ? ? ? ? [HR [X HW]].
    instantiate (1 := fun r => fun gh sG moG sC moC => match r with
      | SErr _ => RUK ∅ nx pt [] [] idl W0 gh sG moG sC moC
      | SVal fd => 3 <= fd <= 4096 /\ exists kd, kd <> KW /\ RUK ∅ nx pt [mkKfe fd kd (to_bytes path) None None 0] [] idl W0 gh sG moG sC moC end).
    cbn beta. destruct r as [err|fd].
    - split; [exact HR|]. split; [exact (proj1 X)| exact HW].
    - destruct X as (R & kd & NK & HF). split; [exact R|]. exists kd. split; [exact NK|]. split; [exact HR|]. split; [cbn in HF; unfold cdel in HF; cbn in HF; exact HF| exact HW]. }
  assert (XK0 : exit_ok []) by (intros ? ? [] _).
  assert (PLE0 : pt <= pt <= pt + READALL_V) by (unfold READALL_V; lia).
  intros r. cbv beta. destruct r as [err|fd].
  - eapply ru_bind2; [apply us_diag; exact Hpath|]. intros [] []. apply usim_pure; intros _.
    apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists ∅, nx, pt, []. split; [exact XK0|]. split; [exact HR|]. split; [exact PLE0| exact I].
  - apply usim_pure. intros Hfd. apply usim_exI. intros kd. apply usim_pure. intros NK.
    set (e := mkKfe fd kd (to_bytes path) None None 0).
    assert (XK1 : exit_ok [e]) by (intros x h [<-|[]] Ho; cbn in Ho; discriminate).
    apply ruk_useR. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (RQ_pot _ _ _ _ _ _ _ _ HR0) as POK. unfold pot_ok in POK. clear HR0 gh0 sG0 moG0 sC0 moC0.
    assert (PM : pre_malloc ∅ pt 65536).
    { split; [lia|]. split; [reflexivity|]. split; [unfold bigb, MMAP_THRESHOLD, QMAX; cbn; lia|]. split; [| split].
      - apply (ROOMN_of_len P9). intros c. rewrite sizes_empty. unfold zlen, P9. cbn. lia.
      - rewrite sizes_empty, PHI_P9. unfold R63N, bigb, MMAP_THRESHOLD, BLIVE. cbn. lia.
      - unfold apre. rewrite live1_empty, sizes_empty, zlen_nil. unfold pot_ok, n1, READALL_V, NMAXA, LIVEMAX, LIVECNT, VOLMAX in *. lia. }
    eapply ru_bind2; [apply (ru_pmalloc ∅ nx pt _ _ 65536 (UK_stable _ _ _ _ _) PM)|].
    intros b b'. apply usim_pure; intros <-. apply usim_pure; intros ->.
    eapply ru_bind2.
    { eapply usim_pre.
      - eapply usim_post.
        + apply (usim_loopV
                 (fun (x y : @rd_st hptr) => fun gh sG moG sC moC => y = x /\ exists tm1 nx1 pt1, RD x tm1 /\ rd_pot pt x pt1 /\ RUK tm1 nx1 pt1 [e] [] idl W0 gh sG moG sC moC)
                 (fun x n => (Z.to_nat (MAX_INPUT - rd_len x) < n)%nat)
                 (fun (a b : @rd_result hptr) => fun gh sG moG sC moC => b = a /\ RLpostU e pt a gh sG moG sC moC)).
          * intros x y n HV. apply usim_pure; intros ->. apply usim_exI; intros tm1. apply usim_exI; intros nx1. apply usim_exI; intros pt1. apply usim_pure; intros HRD. apply usim_pure; intros HPOT.
            pose proof HRD as (_ & HcapX & HlenX & _).
            eapply usim_post; [apply (us_read_loop_body e path nx1 x tm1 pt pt1 eq_refl eq_refl Hpath HRD HPOT HOK)|].
            intros [x'|a] [y'|b'] ? ? ? ? ? [E H]; try discriminate E.
            -- injection E as <-. destruct H as (tm' & nx' & pt' & HR & HRD' & LT & HPOT'). pose proof HRD' as (_ & Hcap' & Hlen' & _).
               split; [lia|]. split; [reflexivity|]. exists tm', nx', pt'. split; [exact HRD'|]. split; assumption.
            -- injection E as <-. split; [reflexivity|]. destruct H as (tm' & nx' & pt' & HR & HP). exists tm', nx', pt'. split; [exact HR|].
               destruct a; [split; [exact HP| exact I]| exact (conj (proj2 HP) (proj1 HP))].
          * intros x H. lia.
          * unfold READ_FUEL, MAX_INPUT. cbn [rd_len]. lia.
        + intros a b' ? ? ? ? ? HH. exact HH.
      - intros ? ? ? ? ? HR. split; [reflexivity|]. exists (<[nx := 65536]> ∅), (N.succ nx), (pt + n1 65536). split; [| split; [| exact (RUK_lift _ _ _ _ _ _ _ _ _ _ _ _ _ HR ltac:(lia))]].
        { unfold RD. cbn [rd_buf rd_cap rd_len rd_chunks]. split; [rewrite insert_empty; reflexivity|]. unfold MAX_INPUT, rd_content, zlength. cbn. repeat split; try lia. exists 0. split; [lia| reflexivity]. }
        unfold rd_pot, n1. cbn [rd_cap]. lia. }
    intros res res'. cbv beta. apply usim_pure; intros ->. destruct res as [|buf' content].
    + apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros pt'. eapply ru_pre; [| intros ? ? ? ? ? [H [HP _]]; exact (conj HP H)].
      apply usim_pure; intros HP'. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm', nx', pt', [e]. split; [exact XK1|]. split; [exact HR|]. split; [exact HP'| exact I].
    + apply usim_exI; intros tm'. apply usim_exI; intros nx'. apply usim_exI; intros pt'.
      eapply (ru_pre _ (fun gh sG moG sC moC => ((exists cap, tm' = {[buf' := cap]} /\ zlength content < cap <= MAX_INPUT) /\ pt <= pt' <= pt + READALL_V) /\ RUK tm' nx' pt' [e] [] idl W0 gh sG moG sC moC));
        [| intros ? ? ? ? ? (H1 & H2 & H3); split; [exact (conj H3 H2)| exact H1]].
      apply usim_pure; intros [HC HP'].
      change fd with (k_fd e).
      eapply (ruk_bind Uk tm' nx' pt' [e] [] idl W0 (fun _ => True) (fun _ => []) (fun _ => []) (fun _ => idl) (fun _ => W0)).
      { eapply ruk_nodeK; [exact I| apply (fn_close nx' [e] [] e ltac:(left; reflexivity))|].
        intros r l mo [_ HF]. split; [exact I|]. unfold lrem, cclose in HF. cbn in HF. rewrite Z.eqb_refl in HF. cbn in HF. exact HF. }
      intros r _. cbn beta. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm', nx', pt', []. split; [exact XK0|]. split; [exact HR|]. split; [exact HP'|]. split; [reflexivity| exact HC].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="RUNV0 us_run"] Theorem us_main_prog nx pt argv :
  Forall (fun a => zlength a <= ARGMAX) argv ->
  pot_ok (pt + READALL_V + RUNV) ->
  usimS (RUK ∅ nx pt [] [] idl W0) (main_prog HOG FOG stkG argv) (main_prog HOC FOC stkC argv)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' K' C' oh' hs' F', exit_ok K' /\ RUK tm' nx' pt' K' C' idl (WF oh' hs' F') gh sG moG sC moC)).
Proof.
  intros Hargv HOK. unfold main_prog, main_model.
  assert (A0 : zlength (nth 0 argv []) <= ARGMAX).
  { destruct argv as [|a0 ?]; cbn; [unfold zlength, ARGMAX; cbn; lia|]. apply Forall_cons_iff in Hargv as [H _]. exact H. }
  assert (A1 : zlength (nth 1 argv []) <= ARGMAX).
  { destruct argv as [|a0 [|a1 ?]]; cbn; [unfold zlength, ARGMAX; cbn; lia| unfold zlength, ARGMAX; cbn; lia|].
    apply Forall_cons_iff in Hargv as [_ H]. apply Forall_cons_iff in H as [H _]. exact H. }
  assert (XK0 : exit_ok []) by (intros ? ? [] _).
  apply ruk_useR. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (RQ_pot _ _ _ _ _ _ _ _ HR0) as POK. unfold pot_ok in POK. clear HR0 gh0 sG0 moG0 sC0 moC0.
  assert (HOK1 : pot_ok (pt + READALL_V)) by (unfold pot_ok, READALL_V in *; lia).
  destruct (negb (Z.of_nat (length argv) =? 2)).
  { eapply ru_bind2; [apply us_diag; exact A0|]. intros [] []. apply usim_pure; intros _. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists ∅, nx, pt, [], [], None, [], []. exact (conj XK0 HR). }
  eapply ru_bind; [apply us_read_all; [exact A1| exact HOK1]|]. intros ra.
  eapply usim_exI; intros tm. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros K1. apply usim_pure; intros XK1.
  destruct ra as [|buf content].
  { eapply ru_pre; [| intros ? ? ? ? ? [H _]; exact H]. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists tm, nx1, pt1, K1, [], None, [], []. exact (conj XK1 HR). }
  eapply (ru_pre _ (fun gh sG moG sC moC => (pt <= pt1 <= pt + READALL_V /\ K1 = [] /\ exists cap, tm = {[buf := cap]} /\ zlength content < cap <= MAX_INPUT) /\ RUK tm nx1 pt1 K1 [] idl W0 gh sG moG sC moC));
    [| intros ? ? ? ? ? (H1 & H2 & H3); split; [exact (conj H2 H3)| exact H1]].
  apply usim_pure. intros (HP1 & -> & cap & -> & Hcap). cbv zeta.
  pose proof (bigb_B26 cap) as HB26.
  assert (BUD : zlen (sizes {[buf := cap]}) <= 1 /\ R63N (sizes {[buf := cap]}) <= B26 /\ PHI P9 + R63N (sizes {[buf := cap]}) <= BLIVE /\ live1 {[buf := cap]} <= MAX_INPUT).
  { rewrite sizes_single. unfold zlen, R63N, live1. rewrite sizes_single. cbn [length zsum map fold_right Z.of_nat]. rewrite PHI_P9.
    pose proof (zlen_nonneg content). specialize (HB26 ltac:(unfold zlength in *; lia)). rewrite n1_id by (unfold zlength in *; lia). unfold B26, BLIVE, PGSZ in *. repeat split; lia. }
  destruct BUD as (BUD1 & BUD2 & BUD3 & BUD4).
  (* [comment removed for export] *)
  assert (HOK2 : pot_ok (pt1 + RUNV)) by (unfold pot_ok, READALL_V in *; lia).
  assert (FREE : forall tm' nx' pt' K' C' oh' hs' F', EXT {[buf := cap]} tm' -> PHI P9 + R63N (sizes tm') <= BLIVE ->
            usimS (RUK tm' nx' pt' K' C' idl (WF oh' hs' F')) (pfree HOG buf) (pfree HOC buf) (eqpost (fun _ => RUK (delete buf tm') nx' pt' K' C' idl (WF oh' hs' F')))).
  { intros tm' nx' pt' K' C' oh' hs' F' HE HB.
    apply (ru_pfree tm' nx' pt' _ _ buf cap (UK_stable _ _ _ _ _)). split; [apply HE; apply lookup_singleton_eq| exact HB]. }
  destruct (zlength content <? HDR_MIN).
  { eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
    eapply ru_bind; [apply (FREE _ nx1 pt1 [] [] None [] []); [intros k n H; exact H| exact BUD3]|]. intros []. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists (delete buf {[buf := cap]}), nx1, pt1, [], [], None, [], []. exact (conj XK0 HR). }
  destruct (zlength content <? HDR_MIN + Z.land (le16 content) 32767).
  { eapply ru_bind2; [apply us_diag; exact I|]. intros [] []. apply usim_pure; intros _.
    eapply ru_bind; [apply (FREE _ nx1 pt1 [] [] None [] []); [intros k n H; exact H| exact BUD3]|]. intros []. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists (delete buf {[buf := cap]}), nx1, pt1, [], [], None, [], []. exact (conj XK0 HR). }
  eapply ru_bind.
  { apply us_run; [exact BUD1| exact BUD2| exact BUD4| | exact HOK2]. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.zlength_skipn (Z.to_nat (6 + Z.land (le16 content) 32767)) content). lia. }
  intros status. eapply usim_exI; intros tm'. eapply usim_exI; intros nx'. eapply usim_exI; intros pt'. eapply usim_exI; intros K'. eapply usim_exI; intros C'.
  eapply usim_exI; intros oh'. eapply usim_exI; intros hs'. eapply usim_exI; intros F'.
  eapply (ru_pre _ (fun gh sG moG sC moC => (EXT {[buf := cap]} tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\ pt' <= pt1 + RUNV) /\ RUK tm' nx' pt' K' C' idl (WF oh' hs' F') gh sG moG sC moC));
    [| intros ? ? ? ? ? (H1 & H2 & H3 & H4 & H5); split; [exact (conj H1 (conj H2 (conj H3 H4)))| exact H5]].
  apply usim_pure. intros (HE & HB & XK & HP').
  eapply ru_bind; [apply (FREE _ nx' pt' K' C' oh' hs' F' HE HB)|]. intros []. apply usim_ret. intros ? ? ? ? ? HR. split; [reflexivity|]. exists (delete buf tm'), nx', pt', K', C', oh', hs', F'. exact (conj XK HR).
Qed.
End UDriver.

End WithCeil.
End UDriverX.

(* [comment removed for export] *)
Module HeapI_A.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require HeapFull Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ITreeA NodesA NodesAS ProtoS RunConst RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed AsanCtrlProps AsanInv AsanBudget. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeAlloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require SizeHist. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanBudget OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotalCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanTotal OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanOps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.ATsafeEv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeAlloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.SizeHist.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX AIface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.HeapI_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Local Notation atot := (atotal (aok ATOP) (apost ATOP)).

#[using="Type"] Lemma HAT0 : atop_ok ATOP.
Proof. unfold atop_ok, AsanInv.ACEIL, AsanInv.ATOP_MAX; atop_facts; lia. Qed.
Definition NS0 := asan_node_sound (CE:=ceil_of_rc) ATOP HAT0 eq_refl.

(* [comment removed for export] *)
#[using="Type"] Lemma aembed_wreach : forall npk, NPKonly npk -> forall {R} (t : AM R) mo Post,
  atot t mo Post -> wreach npk nstep (aembed ATOP t) mo (fun tr r mo' => tr = [] /\ exists a, r = Ok a /\ Post a mo').
Proof.
  intros npk NPK R t. induction t as [r0|e k IH]; intros mo Post Ht; cbn [atotal] in Ht.
  - rewrite aembed_ret. apply wreach_ret. split; [reflexivity|]. exists r0. auto.
  - destruct Ht as [Hok Hk]. destruct (NS0 e mo Hok) as (n & d & He & Hall & (rsp & mo1 & evs & Hst) & _).
    destruct (Hall _ _ _ Hst) as (-> & z & Hd & Hpost).
    rewrite aembed_vis, (aev_tree_node ATOP), He. unfold ebind, enode. cbn [ITree.bind].
    assert (HN : npk n = None).
    { pose proof (NPK n) as X. destruct e; cbn [aev_node] in He; try discriminate He; injection He as <- _; exact X. }
    eapply wreach_vis; [exact HN| exact Hst|]. rewrite Hd. cbn [ITree.bind app].
    exact (IH z mo1 Post (Hk _ _ Hpost)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma apost_vmo : forall e mo z mo', apost ATOP e mo z mo' -> vm_only mo mo'.
Proof.
  intros e mo z mo' H. destruct e as [t|b|addr len prot flags|addr len|a l p|w]; cbn [OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanNodeSem.apost] in H; try contradiction.
  - destruct (addr =? 0).
    + destruct H as (_ & _ & _ & _ & ->). unfold grant_model, vm_only. destruct mo as [fd vm io fs pr lm tm]. cbn. repeat split; reflexivity.
    + destruct H as (_ & ->). unfold fixed_model, with_mmap_replacement, with_mmap_backing, vm_only. destruct (mmap_noreserve_b _); destruct mo as [fd vm io fs pr lm tm]; cbn; repeat split; reflexivity.
  - destruct H as (_ & ->). unfold munmap_model, with_mmap_destroyed, vm_only. destruct mo as [fd vm io fs pr lm tm]. cbn. repeat split; reflexivity.
Qed.

#[using="Type"] Lemma atotal_vmo : forall {R} (t : AM R) mo (Post : R -> Model -> Prop),
  atot t mo Post -> atot t mo (fun r mo' => Post r mo' /\ vm_only mo mo').
Proof.
  intros R t. induction t as [r|e k IH]; intros mo Post H; cbn in *.
  - split; [exact H| apply vm_only_refl].
  - destruct H as [Hok Hk]. split; [exact Hok|]. intros z mo' Hp.
    eapply atotal_mono; [| apply IH; exact (Hk _ _ Hp)]. cbv beta. intros r mo'' [HP HF]. split; [exact HP|].
    eapply vm_only_trans; [apply (apost_vmo _ _ _ _ Hp)| exact HF].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma div_add_le : forall a b m, 0 < m -> a / m + b / m <= (a + b) / m.
Proof.
  intros a b m Hm. apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.mul_div_le a m ltac:(lia)). pose proof (Z.mul_div_le b m ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma pcost_sec : forall n, 64512 < n <= 2^40 -> pcost (sec_map_size n) <= n / 1024.
Proof.
  intros n Hn. pose proof (sec_map_size_bounds n Hn) as SBn. unfold pcost.
  set (s := sec_map_size n) in *.
  pose proof (Z.div_le_mono s (n + 12296) 4096 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono s (n + 12296) 32768 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 4096 ltac:(lia)).
  pose proof (Z.div_mod (n + 12296) 32768 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 12296) 32768 ltac:(lia)).
  pose proof (Z.div_mod n 1024 ltac:(lia)). pose proof (Z.mod_pos_bound n 1024 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma soc_le : forall c, 1 <= c <= 31 -> size_of_class c <= 65536.
Proof.
  intros c Hc. assert (H : exists k : nat, c = Z.of_nat k /\ (k <= 31)%nat) by (exists (Z.to_nat c); lia).
  destruct H as (k & -> & Hk). do 32 (destruct k as [|k]; [vm_compute; discriminate|]). lia.
Qed.

#[using="Type"] Lemma cntP_le_len : forall c L, 0 <= cntP c L <= zlen L.
Proof.
  intros c L. induction L as [|ch L IH]; [unfold cntP, zlen; cbn; lia|].
  rewrite cntP_cons. unfold zlen in *. cbn [length]. destruct (is_prim_of c ch); lia.
Qed.

#[using="Type"] Lemma secs_le_len : forall L, zlen (secs L) <= zlen L.
Proof.
  induction L as [|ch L IH]; [unfold zlen; cbn; lia|]. rewrite secs_cons. unfold zlen in *. rewrite length_app. cbn [length].
  destruct ch; cbn [sec_of length]; lia.
Qed.

#[using="Type"] Lemma secbytes_le_sum : forall L, Forall (chunk_wf ATOP) L -> 0 <= secbytes L <= zsum (map chunk_size L).
Proof.
  induction L as [|ch L IH]; intros HW; [cbn; lia|]. apply Forall_cons_iff in HW as [H1 HW]. specialize (IH HW).
  cbn [map]. rewrite zsum_cons. destruct ch as [c n|mb ms n]; cbn [secbytes chunk_size] in *; cbn in H1; lia.
Qed.

#[using="Type"] Lemma live_budget_few : forall L, Forall (chunk_wf ATOP) L -> zlen L <= 16 -> zsum (map chunk_size L) <= 2^30 -> live_budget_list L.
Proof.
  intros L HW HL HS. split; [| split].
  - intros c Hc. pose proof (soc_le c Hc). pose proof (cntP_le_len c L).
    assert (LM : 2^28 <= LMAX c) by (unfold LMAX, HB; destruct (c =? 1); [lia| destruct (c =? 2); lia]).
    assert (size_of_class c * cntP c L <= 65536 * 16); [| lia].
    assert (0 <= size_of_class c) by (unfold size_of_class; destruct (c <=? 16) eqn:E; [apply Z.leb_le in E; lia|]; destruct (c =? 31); [lia|]; cbv zeta; destruct (Z.odd (c - 16)); pose proof (Z.shiftl_nonneg 512 (Z.shiftr (c - 16) 1)); pose proof (Z.shiftr_nonneg (Z.shiftl 512 (Z.shiftr (c - 16) 1)) 1); lia).
    nia.
  - pose proof (secs_le_len L). unfold SMAX, HB. lia.
  - pose proof (secbytes_le_sum L HW). unfold LSBYTES, HB. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sizes_fmap_perm : forall (m : gmap N achunk), Permutation (ProgSim.sizes (fmap (M:=gmap N) chunk_size m)) (map chunk_size (map snd (map_to_list m))).
Proof.
  intros m. unfold ProgSim.sizes. rewrite (map_to_list_fmap chunk_size m).
  apply Permutation_refl'. induction (map_to_list m) as [|[k ch] l IH]; [reflexivity|]. cbn. f_equal. exact IH.
Qed.

#[using="Type"] Lemma zsum_map_le : forall (f g : Z -> Z) l, (forall x, f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. intros f g l H. induction l as [|x l IH]; [cbn; lia|]. cbn [map]. rewrite !zsum_cons. specialize (H x). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wreach_twfX : forall {G} (nsX : node -> G -> Model -> Prop) (gst : node -> resp -> G -> G) npk {R} (t : itree node R) mo W,
  wreach npk nstep t mo W -> forall g (P : R -> G -> Model -> Prop), twfX nsX gst t g mo P ->
  wreach npk nstep t mo (fun tr r mo' => W tr r mo' /\ exists g', P r g' mo').
Proof.
  intros G nsX gst npk R t mo W H. induction H as [r mo W HW|n k mo W rsp mo' evs Hn Hst _ IH|n k mo W f Hn _ IH]; intros g P HT; cbn in HT.
  - apply wreach_ret. split; [exact HW| exists g; exact HT].
  - destruct HT as [_ HT]. eapply wreach_vis; [exact Hn| exact Hst|]. exact (IH _ _ (HT _ _ _ Hst)).
  - destruct HT as [_ HT]. eapply wreach_peek; [exact Hn|]. intros rsp mo' evs Hst. exact (IH _ _ _ Hst _ _ (HT _ _ _ Hst)).
Qed.
#[using="Type"] Lemma wreach_tpath : forall npk {R} (t : itree node R) mo W,
  wreach npk nstep t mo W -> wreach npk nstep t mo (fun tr r mo' => W tr r mo' /\ tpath nstep t mo tr r mo').
Proof.
  intros npk R t mo W H. induction H as [r mo W HW|n k mo W rsp mo' evs Hn Hst _ IH|n k mo W f Hn _ IH].
  - apply wreach_ret. split; [exact HW| cbn; auto].
  - eapply wreach_vis; [exact Hn| exact Hst|]. eapply wreach_mono; [exact IH|]. cbv beta. intros tr r mo'' [HW HP].
    split; [exact HW|]. cbn. exists rsp, mo', evs, tr. auto.
  - eapply wreach_peek; [exact Hn|]. intros rsp mo' evs Hst. eapply wreach_mono; [exact (IH _ _ _ Hst)|]. cbv beta. intros tr r mo'' [HW HP].
    split; [exact HW|]. cbn. exists rsp, mo', evs, tr. auto.
Qed.

Definition NLK0 : Z := EAGER0 + CBM + 2^34 + 2^31.

Section Ops.
Variable NMAX : nat.
Variables SB PA : Z.
Variable Abase : alw.
Variable RESV : list (Z * Z).
Variable site_frame : Pcap.stack_site -> option (Pcap.fframe * Z).
Hypothesis SITE_OFF : forall site f off, site_frame site = Some (f, off) -> 0 <= off <= 65536.
Local Notation NMAXZ := (Z.of_nat NMAX).
Hypothesis HLIM : NLK0 + NMAXZ * 4096 <= LIMIT.
Hypothesis ABASE_SH : forall z',
  (shad SB <= z' < shad (SB + K_SPACE_SIZE) \/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> Abase (page_base_of z').
Hypothesis HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Hypothesis HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Local Notation KI := (ATsafeAlloc.KI Abase NLK0).
Local Notation INV := (AsanInv.INV RESV ATOP).
#[local] Notation PSA := (PState aheap hptr).

Definition AJ (tm : gmap N Z) (nx : N) (P : Z) (A : alw) (s : PSA) (mo : Model) : Prop :=
  let h := ps_heap s in let st := ah_st h in
  INV [] [] st mo /\ ah_resv h = RESV /\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX
  /\ a_space_beg st = SB /\ a_ptr_array st = PA
  /\ tm = chunk_size <$> a_live st /\ nx = a_next st /\ pot_ok P
  /\ (exists G k, QOK G st /\ alw_le Abase A /\ GA G A /\ abud A k /\ 0 <= k /\ k + (VOLMAX - P) / 1024 <= NMAXZ)
  /\ (forall k a, ah_addr h !! k = Some a -> 0 <= a < 2^48) /\ Forall (fun e => 0 <= snd e < 2^48) (ah_frames h).

#[using="Type"] Lemma MOK_of_AMI : forall ch st mo, AMI RESV ATOP ch st mo -> MOK mo.
Proof.
  intros ch st mo HM. pose proof (AMI_ivs_wf _ _ _ HM) as W. destruct HM as (M1 & M2 & _ & _ & _ & M6 & _ & _ & M9 & [_ M10] & _).
  split; [exact M1|]. split; [exact M2|]. split; [exact W|]. split; [exact M9| split; [exact M6| exact M10]].
Qed.

#[using="NMAX"] Lemma LW_of_AINV : forall st, AINV ATOP [] [] st -> LW (a_space_beg st) (a_ptr_array st) st.
Proof.
  intros st HA. pose proof HA as (HC & _ & _ & _ & _ & _ & Hres & _).
  split; [reflexivity|]. split; [reflexivity|]. split; [unfold K_CHUNKS_BLOCK in Hres; lia|]. split; [unfold K_CHUNKS_BLOCK, K_PTRARR_RESERVE in *; lia|].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in X. cbv zeta in X. unfold cls_lw. lia.
Qed.

#[using="NMAX"] Lemma CH_bound_AJ : forall st, AINV ATOP [] [] st -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> zsum2 (CH [] [] st) <= 2^34.
Proof.
  intros st HA Hq1 Hq2.
  destruct (CH_bounds [] [] st HA) as [_ X]; [| unfold zlen; cbn; lia| cbn; lia| exact X].
  unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hb1 & Hb2 & _). unfold Q_CACHE, Q_MAX in *. lia.
Qed.

#[using="Type"] Lemma KI_entry : forall tm nx P A s mo extra,
  AJ tm nx P A s mo -> 0 <= extra <= 2^31 ->
  exists G k, KI (PHI (ah_st (ps_heap s)) + extra) G A k mo /\ QOK G (ah_st (ps_heap s)) /\ k + (VOLMAX - P) / 1024 <= NMAXZ
              /\ LW SB PA (ah_st (ps_heap s)) /\ next_fresh (ah_st (ps_heap s)).
Proof.
  intros tm nx P A s mo extra HJ Hex. cbv zeta in HJ.
  destruct HJ as ((HA & HM) & _ & Hq1 & Hq2 & HSB' & HPA' & _ & _ & _ & (G & k & HQ & HAB & HGA & HBU & Hk & Hkv) & _).
  exists G, k.
  assert (HL : LW SB PA (ah_st (ps_heap s))) by (rewrite <- HSB', <- HPA'; apply LW_of_AINV; exact HA).
  split; [| split; [exact HQ| split; [exact Hkv| split; [exact HL| destruct HA as (_ & _ & _ & _ & _ & _ & _ & NF & _); exact NF]]]].
  pose proof (PHI_nonneg SB PA _ HL). pose proof (commit_bytes_LW SB PA _ HL).
  pose proof (AMI_nonlazy_bound _ _ _ HM (CH_wf _ _ _ HA)). pose proof (CH_bound_AJ _ HA Hq1 Hq2).
  split; [eapply MOK_of_AMI; exact HM|]. split; [lia|]. split; [unfold PHI, NLK0 in *; lia|].
  split; [exact HAB|]. split; [exact HGA|]. split; [exact HBU| exact Hk].
Qed.

#[using="HLIM"] Lemma AJ_acct : forall tm nx P A s mo, AJ tm nx P A s mo -> acct_ok NMAX (RNGof A mo) A mo.
Proof.
  intros tm nx P A s mo HJ. destruct (KI_entry tm nx P A s mo 0 HJ ltac:(lia)) as (G & k & HK & _ & Hkv & _).
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & [HP0 HP1] & _). pose proof (Z.div_pos (VOLMAX - P) 1024 ltac:(lia) ltac:(lia)).
  eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK0 HLIM); [exact HK| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AJ_lbl : forall tm nx P A s mo n,
  AJ tm nx P A s mo -> 0 <= n <= 2^29 -> live1 tm + n1 n <= LIVEMAX -> zlen (ProgSim.sizes tm) + 1 <= LIVECNT ->
  forall mb ms, live_budget_list (mkch n mb ms :: live_chunks (ah_st (ps_heap s))).
Proof.
  intros tm nx P A s mo n HJ Hn HLV HCN mb ms. cbv zeta in HJ.
  destruct HJ as ((HA & _) & _ & _ & _ & _ & _ & ETM & _).
  set (st := ah_st (ps_heap s)) in *.
  set (dummy := mkch n 70368744177664 (sec_map_size n)).
  assert (Hwf : chunk_wf ATOP dummy).
  { unfold dummy, mkch. destruct (is_primary n) eqn:Hp.
    - cbn. split; [|reflexivity]. split; [lia|]. destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia].
    - cbn. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(lia)).
      unfold KHIGH. atop_facts. repeat split; try lia. }
  apply (live_budget_list_sig dummy). { unfold dummy, mkch. destruct (is_primary n); reflexivity. }
  assert (HWL : Forall (chunk_wf ATOP) (live_chunks st)).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HWl _]. exact HWl. }
  pose proof (sizes_fmap_perm (a_live st)) as PS. rewrite <- ETM in PS. fold (live_chunks st) in PS.
  apply live_budget_few.
  - constructor; assumption.
  - unfold zlen in *. cbn [length]. rewrite <- (length_map chunk_size (live_chunks st)), <- (Permutation_length PS). unfold LIVECNT in HCN. lia.
  - cbn [map]. rewrite zsum_cons. replace (chunk_size dummy) with n by (unfold dummy, mkch; destruct (is_primary n); reflexivity).
    rewrite <- (zsum_perm _ _ PS). unfold live1 in HLV.
    pose proof (zsum_map_le (fun x => x) n1 (ProgSim.sizes tm) ltac:(intros x; unfold n1; lia)) as LE. rewrite map_id in LE.
    unfold LIVEMAX, n1 in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma peek_step : forall a mo rsp mo' evs, nstep (NPeek a) mo rsp mo' evs -> mo' = mo /\ evs = [] /\ 0 <= dec_peek rsp < 256.
Proof.
  intros a mo rsp mo' evs H. cbn [nstep] in H. destruct H as (-> & -> & v & Hv & ->). split; [reflexivity|]. split; [reflexivity|].
  rewrite dec_peek_rsp by exact Hv. exact Hv.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpeek_twfX : forall a (s : PSA) A mo (P : exc (Z * PSA) -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 256 -> P (Ok (v, s)) A mo) ->
  twfX (nsafePA NMAX) gstepA (mpeek a s) A mo P.
Proof.
  intros a s A mo P HA HP. unfold mpeek, msys, enode. cbn [twfX]. split.
  - apply nsafePA_io; [right; exists a; reflexivity| exact I| exact HA].
  - intros rsp mo' evs Hst. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv). cbn [gstepA twfX]. apply HP. exact Hv.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ebind_assoc : forall {A B C} (t : itree node (exc A)) (f : A -> itree node (exc B)) (g : B -> itree node (exc C)),
  ebind (ebind t f) g = ebind t (fun a => ebind (f a) g).
Proof.
  intros A B C t f g. induction t as [r|n k IH]; [destruct r; reflexivity|].
  unfold ebind in *. cbn [ITree.bind]. f_equal. apply FunctionalExtensionality.functional_extensionality. intros rsp. apply IH.
Qed.
#[using="Type"] Lemma mbind_assoc : forall {A B C} (m : Monad.M PSA A) (f : A -> Monad.M PSA B) (g : B -> Monad.M PSA C) s,
  mbind (mbind m f) g s = mbind m (fun a => mbind (f a) g) s.
Proof. intros. unfold mbind. rewrite ebind_assoc. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpeek_bind_etwfX : forall {X} a (k : Z -> Monad.M PSA X) (s : PSA) A mo (Q : X * PSA -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 256 -> etwfX (nsafePA NMAX) gstepA (k v s) A mo Q) ->
  etwfX (nsafePA NMAX) gstepA (mbind (mpeek a) k s) A mo Q.
Proof.
  intros X a k s A mo Q HA HK. unfold mbind. apply etwfX_ebind. unfold etwfX at 1. apply mpeek_twfX; [exact HA|].
  intros v Hv. cbn [fst snd]. exact (HK v Hv).
Qed.

(* [comment removed for export] *)
#[using="rc"] Lemma mpeek_reg48_etwfX : forall {X} r (k : Z -> Monad.M PSA X) (s : PSA) A mo (Q : X * PSA -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 2^48 -> etwfX (nsafePA NMAX) gstepA (k v s) A mo Q) ->
  etwfX (nsafePA NMAX) gstepA (mbind (mpeek_reg48 r) k s) A mo Q.
Proof.
  intros X r k s A mo Q HA HK. unfold mpeek_reg48.
  do 6 (rewrite mbind_assoc; apply mpeek_bind_etwfX; [exact HA|]; intros ? ?).
  rewrite mbind_mret. apply HK. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpeek_bind_tpath : forall {X} a (k : Z -> Monad.M PSA X) (s : PSA) mo tr res mo',
  tpath nstep (mbind (mpeek a) k s) mo tr res mo' -> exists v, 0 <= v < 256 /\ tpath nstep (k v s) mo tr res mo'.
Proof.
  intros X a k s mo tr res mo' H. unfold mbind in H. apply tpath_ebind in H.
  destruct H as [[H _]|(tr1 & [v s1] & mo1 & tr2 & H1 & H2 & ->)]; unfold mpeek, msys in *.
  - apply tpath_enode in H as (rsp & _ & E). discriminate E.
  - apply tpath_enode in H1 as (rsp & Hst & E). injection E as E1 E2. subst v s1. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv).
    exists (dec_peek rsp). split; [exact Hv| exact H2].
Qed.
#[using="Type"] Lemma mpeek_bind_texit : forall {X} a (k : Z -> Monad.M PSA X) (s : PSA) mo tr,
  texit nstep nexit (mbind (mpeek a) k s) mo tr -> exists v, 0 <= v < 256 /\ texit nstep nexit (k v s) mo tr.
Proof.
  intros X a k s mo tr H. unfold mbind in H. apply texit_ebind in H.
  destruct H as [H|(tr1 & [v s1] & mo1 & tr2 & H1 & H2 & ->)]; unfold mpeek, msys in *.
  - apply texit_enode in H as (code & mo' & Hx & _). destruct Hx.
  - apply tpath_enode in H1 as (rsp & Hst & E). injection E as E1 E2. subst v s1. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv).
    exists (dec_peek rsp). split; [exact Hv| exact H2].
Qed.
#[using="rc NMAX"] Lemma mpeek_reg48_tpath : forall {X} r (k : Z -> Monad.M PSA X) (s : PSA) mo tr res mo',
  tpath nstep (mbind (mpeek_reg48 r) k s) mo tr res mo' -> exists v, 0 <= v < 2^48 /\ tpath nstep (k v s) mo tr res mo'.
Proof.
  intros X r k s mo tr res mo' H. unfold mpeek_reg48 in H.
  do 6 (rewrite mbind_assoc in H; apply mpeek_bind_tpath in H; destruct H as (? & ? & H)).
  rewrite mbind_mret in H. eexists. split; [| exact H]. lia.
Qed.
#[using="rc NMAX"] Lemma mpeek_reg48_texit : forall {X} r (k : Z -> Monad.M PSA X) (s : PSA) mo tr,
  texit nstep nexit (mbind (mpeek_reg48 r) k s) mo tr -> exists v, 0 <= v < 2^48 /\ texit nstep nexit (k v s) mo tr.
Proof.
  intros X r k s mo tr H. unfold mpeek_reg48 in H.
  do 6 (rewrite mbind_assoc in H; apply mpeek_bind_texit in H; destruct H as (? & ? & H)).
  rewrite mbind_mret in H. eexists. split; [| exact H]. lia.
Qed.

(* [comment removed for export] *)
#[using="rc NMAX"] Lemma mpeek_bind_wreach : forall npk {X} a (k : Z -> Monad.M PSA X) (s : PSA) mo W,
  (forall v, 0 <= v < 256 -> wreach npk nstep (k v s) mo W) -> wreach npk nstep (mbind (mpeek a) k s) mo W.
Proof.
  intros npk X a k s mo W HK. unfold mbind, mpeek, msys, enode, ebind. cbn [ITree.bind].
  destruct (npk (NPeek a)) as [f|] eqn:E.
  - eapply wreach_peek; [exact E|]. intros rsp mo' evs Hst. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv).
    cbn [ITree.bind fst snd app]. exact (HK _ Hv).
  - eapply wreach_vis with (rsp := peek_rsp 0) (mo' := mo) (evs := []); [exact E| cbn [nstep]; split; [reflexivity|]; split; [reflexivity|]; exists 0; split; [lia| reflexivity]|].
    cbn [ITree.bind fst snd app]. rewrite dec_peek_rsp by lia. apply HK. lia.
Qed.
#[using="rc NMAX"] Lemma mpeek_reg48_wreach : forall npk {X} r (k : Z -> Monad.M PSA X) (s : PSA) mo W,
  (forall v, 0 <= v < 2^48 -> wreach npk nstep (k v s) mo W) -> wreach npk nstep (mbind (mpeek_reg48 r) k s) mo W.
Proof.
  intros npk X r k s mo W HK. unfold mpeek_reg48.
  do 6 (rewrite mbind_assoc; apply mpeek_bind_wreach; intros ? ?).
  rewrite mbind_mret. apply HK. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation aliftA := (alift (CE:=ceil_of_rc)).

#[using="Type"] Lemma alift_unfold : forall {R X} (t : AM R) (k : R -> Monad.M PSA X) (s : PSA),
  mbind (aliftA t) k s = ebind (aembed ATOP t) (fun r => k r s).
Proof. intros R X t k s. unfold mbind, alift. rewrite ebind_assoc. reflexivity. Qed.

#[using="HLIM ABASE_SH"] Lemma alift_bind_etwfX : forall {R X} (t : AM R) (k : R -> Monad.M PSA X) (s : PSA) A mo (Q : X * PSA -> alw -> Model -> Prop)
    (RP : list (Z * Z) -> R -> Prop) Post ga G b kk KCAP,
  atot t mo Post -> evq SB PA RP ga G b t -> KI b G A kk mo -> Forall (fun l => 0 <= l) ga -> kk + gcost ga <= KCAP -> KCAP <= NMAXZ ->
  (forall r A' mo', (exists G' b' k', RP G' r /\ Post r mo' /\ KI b' G' A' k' mo' /\ k' <= KCAP /\ incl G G') ->
     etwfX (nsafePA NMAX) gstepA (k r s) A' mo' Q) ->
  etwfX (nsafePA NMAX) gstepA (mbind (aliftA t) k s) A mo Q.
Proof.
  intros R X t k s A mo Q RP Post ga G b kk KCAP HT HE HK Hga Hk HKC HC.
  rewrite alift_unfold. apply etwfX_ebind.
  pose proof (TWF_aembed NMAX SB PA Abase NLK0 HLIM ABASE_SH t RP Post ga G b A kk KCAP mo HT HE HK Hga Hk HKC) as W.
  unfold etwfX. eapply twfX_mono; [exact W|]. intros [|r] A' mo' H; cbn in H |- *; [exact H|]. exact (HC r A' mo' H).
Qed.

#[using="Type"] Lemma alift_bind_tpath : forall {R X} (t : AM R) (k : R -> Monad.M PSA X) (s : PSA) mo Post tr res mo',
  atot t mo Post -> tpath nstep (mbind (aliftA t) k s) mo tr res mo' ->
  exists r mo1, Post r mo1 /\ tpath nstep (k r s) mo1 tr res mo'.
Proof.
  intros R X t k s mo Post tr res mo' HT H. rewrite alift_unfold in H. apply tpath_ebind in H.
  destruct H as [[H _]|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)].
  - destruct (atotal_paths ATOP nstep (aok ATOP) (apost ATOP) NS0 t mo Post tr Unr mo' HT H) as (_ & a & E & _). discriminate E.
  - destruct (atotal_paths ATOP nstep (aok ATOP) (apost ATOP) NS0 t mo Post tr1 (Ok r) mo1 HT H1) as (-> & a & E & HP). injection E as <-.
    exists r, mo1. split; [exact HP| exact H2].
Qed.

#[using="Type"] Lemma alift_bind_texit : forall {R X} (t : AM R) (k : R -> Monad.M PSA X) (s : PSA) mo Post tr,
  atot t mo Post -> texit nstep nexit (mbind (aliftA t) k s) mo tr ->
  exists r mo1, Post r mo1 /\ texit nstep nexit (k r s) mo1 tr.
Proof.
  intros R X t k s mo Post tr HT H. rewrite alift_unfold in H. apply texit_ebind in H.
  destruct H as [H|(tr1 & r & mo1 & tr2 & H1 & H2 & ->)].
  - exfalso. exact (atotal_noexit ATOP nstep (aok ATOP) (apost ATOP) NS0 t mo Post tr HT H).
  - destruct (atotal_paths ATOP nstep (aok ATOP) (apost ATOP) NS0 t mo Post tr1 (Ok r) mo1 HT H1) as (-> & a & E & HP). injection E as <-.
    exists r, mo1. split; [exact HP| exact H2].
Qed.

#[using="Type"] Lemma alift_bind_wreach : forall npk, NPKonly npk -> forall {R X} (t : AM R) (k : R -> Monad.M PSA X) (s : PSA) mo Post W,
  atot t mo Post -> (forall r mo1, Post r mo1 -> wreach npk nstep (k r s) mo1 W) -> wreach npk nstep (mbind (aliftA t) k s) mo W.
Proof.
  intros npk NPK R X t k s mo Post W HT HK. rewrite alift_unfold. unfold ebind. apply wreach_bind.
  eapply wreach_mono; [exact (aembed_wreach npk NPK t mo Post HT)|]. intros tr r mo1 (-> & a & -> & HP). cbn [app]. exact (HK a mo1 HP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tail_st (forget : gmap N Z -> gmap N Z) (st' : astate) (id : N) (v : Z) (s : PSA) : PSA :=
  set_heap (ah_set_addr (<[id := v]> (forget (ah_addr (ps_heap s)))) (ah_set_st st' (ps_heap s))) s.

#[using="Type"] Lemma tail_some_eq : forall forget st' id v (s : PSA),
  mbind (upd_heap (fun h => ah_set_addr (<[id := v]> (forget (ah_addr h))) (ah_set_st st' h))) (fun _ => mret (Some id)) s
  = Ret (Ok (Some id, tail_st forget st' id v s)).
Proof. reflexivity. Qed.

#[using="rc"] Lemma tail_etwfX : forall forget st' id (s : PSA) A mo (Q : option aptr * PSA -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 2^48 -> Q (Some id, tail_st forget st' id v s) A mo) ->
  etwfX (nsafePA NMAX) gstepA (ah_alloc_tail forget (st', Some id) s) A mo Q.
Proof.
  intros forget st' id s A mo Q HA HQ. unfold ah_alloc_tail. cbn [snd fst].
  apply mpeek_reg48_etwfX; [exact HA|]. intros v Hv. rewrite tail_some_eq. apply etwfX_ret. exact (HQ v Hv).
Qed.
#[using="rc NMAX"] Lemma tail_tpath : forall forget st' id (s : PSA) mo tr res mo',
  tpath nstep (ah_alloc_tail forget (st', Some id) s) mo tr res mo' ->
  exists v, 0 <= v < 2^48 /\ tr = [] /\ res = Ok (Some id, tail_st forget st' id v s) /\ mo' = mo.
Proof.
  intros forget st' id s mo tr res mo' H. unfold ah_alloc_tail in H. cbn [snd fst] in H.
  apply mpeek_reg48_tpath in H as (v & Hv & H). rewrite tail_some_eq in H. cbn in H. destruct H as (<- & -> & ->).
  exists v. repeat split; [lia| lia].
Qed.
#[using="rc NMAX"] Lemma tail_texit : forall forget st' id (s : PSA) mo tr, texit nstep nexit (ah_alloc_tail forget (st', Some id) s) mo tr -> False.
Proof.
  intros forget st' id s mo tr H. unfold ah_alloc_tail in H. cbn [snd fst] in H.
  apply mpeek_reg48_texit in H as (v & Hv & H). rewrite tail_some_eq in H. exact H.
Qed.
#[using="rc NMAX"] Lemma tail_wreach : forall npk forget st' id (s : PSA) mo W,
  (forall v, 0 <= v < 2^48 -> W [] (Ok (Some id, tail_st forget st' id v s)) mo) ->
  wreach npk nstep (ah_alloc_tail forget (st', Some id) s) mo W.
Proof.
  intros npk forget st' id s mo W HW. unfold ah_alloc_tail. cbn [snd fst].
  apply mpeek_reg48_wreach. intros v Hv. rewrite tail_some_eq. apply wreach_ret. exact (HW v Hv).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AJ_after_alloc : forall tm nx P A s mo n st' A' mo' G' b' k' v,
  AJ tm nx P A s mo ->
  malloc_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) n (st', Some nx) mo' ->
  RPm SB PA G' (st', Some nx) -> KI b' G' A' k' mo' ->
  k' + (VOLMAX - (P + n1 n)) / 1024 <= NMAXZ -> pot_ok (P + n1 n) -> 0 <= v < 2^48 ->
  AJ (<[nx := n]> tm) (N.succ nx) (P + n1 n) A' (tail_st (fun m => m) st' nx v s) mo'.
Proof.
  intros tm nx P A s mo n st' A' mo' G' b' k' v HJ HMP HRP HK Hcr HPO Hv. cbv zeta in HJ |- *.
  destruct HJ as (_ & ERS & Hq1 & Hq2 & _ & _ & ETM & ENX & _ & _ & HAD & HFR).
  destruct HMP as (ch & _ & HI2 & Hlive & Hnone & Hsz & Eq1 & Eq2 & _ & _ & ENX'). cbn [fst snd] in *.
  destruct HRP as [HL' HQ']. pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
  unfold tail_st. cbn [ps_heap set_heap ah_st ah_resv ah_addr ah_frames ah_set_addr ah_set_st].
  split; [exact HI2|]. split; [exact ERS|]. split; [rewrite Eq1; exact Hq1|]. split; [rewrite Eq2; exact Hq2|].
  split; [exact (proj1 HL')|]. split; [exact (proj1 (proj2 HL'))|].
  split; [rewrite Hlive, fmap_insert, Hsz, ETM, ENX; reflexivity|]. split; [rewrite ENX', ENX; reflexivity|]. split; [exact HPO|].
  split; [exists G', k'; split; [exact HQ'|]; split; [exact HAB|]; split; [exact HGA|]; split; [exact HBU|]; split; [exact Hk0| exact Hcr]|].
  split; [| exact HFR].
  intros k a Hka. unfold set_heap in Hka. cbn [ps_heap ah_addr ah_set_addr ah_set_st] in Hka. apply lookup_insert_Some in Hka as [[_ <-]|[_ Hka]]; [exact Hv| exact (HAD k a Hka)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation HOA := (asan_ops (CE:=ceil_of_rc)).

#[using="Type"] Lemma ah_malloc_unfold : forall n (s : PSA),
  ho_malloc HOA n s = mbind (aliftA (amalloc ATOP (ah_resv (ps_heap s)) (ah_st (ps_heap s)) n)) (fun x => ah_alloc_tail (fun m => m) x) s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mga (n : Z) : list Z := if is_primary n then [] else [sec_map_size n].
Definition mextra (n : Z) : Z := if is_primary n then 0 else sec_map_size n.

#[using="Type"] Lemma AJ_malloc_facts : forall tm nx P A s mo n,
  AJ tm nx P A s mo -> 0 <= n -> apre tm P (n1 n) ->
  exists G k,
    atot (amalloc ATOP RESV (ah_st (ps_heap s)) n) mo (fun r mo' => malloc_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) n r mo' /\ vm_only mo mo')
    /\ evq SB PA (RPm SB PA) (mga n) G (PHI (ah_st (ps_heap s)) + mextra n) (amalloc ATOP RESV (ah_st (ps_heap s)) n)
    /\ KI (PHI (ah_st (ps_heap s)) + mextra n) G A k mo
    /\ Forall (fun l => 0 <= l) (mga n) /\ k + gcost (mga n) + (VOLMAX - (P + n1 n)) / 1024 <= NMAXZ /\ 0 <= gcost (mga n)
    /\ nx = a_next (ah_st (ps_heap s)).
Proof.
  intros tm nx P A s mo n HJ Hn0 (HP0 & HPV & HNA & HLV & HCN). unfold NMAXA in HNA.
  assert (Hn : 0 <= n <= 2^29) by (unfold n1 in HNA; lia).
  pose proof (AJ_lbl tm nx P A s mo n HJ Hn HLV HCN) as HLB.
  assert (Hex : 0 <= mextra n <= 2^31).
  { unfold mextra. destruct (is_primary n) eqn:Hp; [lia|]. pose proof (not_primary_large n ltac:(lia) Hp). pose proof (sec_map_size_bounds n ltac:(lia)). lia. }
  destruct (KI_entry tm nx P A s mo _ HJ Hex) as (G & k & HK & HQ & Hkv & HL & HNF).
  exists G, k. cbv zeta in HJ. destruct HJ as (HI & _ & Hq1 & Hq2 & _ & _ & _ & ENX & _).
  split; [apply atotal_vmo; apply amalloc_core; assumption|].
  split; [apply evq_amalloc; [exact HL| exact HQ| exact HNF| lia]|].
  split; [exact HK|].
  assert (GC : 0 <= gcost (mga n) /\ gcost (mga n) <= n1 n / 1024).
  { unfold mga. destruct (is_primary n) eqn:Hp; cbn [gcost].
    - split; [lia|]. apply Z.div_pos; unfold n1; lia.
    - pose proof (not_primary_large n ltac:(lia) Hp). pose proof (pcost_sec n ltac:(lia)). pose proof (sec_map_size_bounds n ltac:(lia)).
      pose proof (pcost_nonneg (sec_map_size n) ltac:(lia)). replace (n1 n) with n by (unfold n1; lia). lia. }
  split; [unfold mga; destruct (is_primary n) eqn:Hp; [constructor| constructor; [|constructor];
            pose proof (not_primary_large n ltac:(lia) Hp); pose proof (sec_map_size_bounds n ltac:(lia)); lia]|].
  split; [| split; [lia| exact ENX]].
  pose proof (div_add_le (n1 n) (VOLMAX - (P + n1 n)) 1024 ltac:(lia)) as D.
  replace (n1 n + (VOLMAX - (P + n1 n))) with (VOLMAX - P) in D by lia. lia.
Qed.

#[using="HLIM ABASE_SH"] Lemma A_mallocG : forall tm nx P A s mo n, AJ tm nx P A s mo -> pre_malloc tm P n ->
  gop (nsafePA NMAX) gstepA (ho_malloc HOA n) nx s A mo (gpost AJ (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo).
Proof.
  intros tm nx P A s mo n HJ HP.
  destruct (AJ_malloc_facts tm nx P A s mo n HJ (proj1 HP) (proj2 (proj2 (proj2 (proj2 (proj2 HP)))))) as (G & k & HT & HE & HK & Hga & Hcr & GC0 & ENX).
  assert (ERS : ah_resv (ps_heap s) = RESV) by (pose proof HJ as HJ'; cbv zeta in HJ'; destruct HJ' as (_ & ERS & _); exact ERS).
  assert (HPO : pot_ok (P + n1 n)).
  { destruct HP as (_ & _ & _ & _ & _ & (HP0 & HPV & _)). unfold pot_ok, n1 in *. lia. }
  assert (HVP : 0 <= (VOLMAX - (P + n1 n)) / 1024) by (apply Z.div_pos; [unfold pot_ok in HPO; lia| lia]).
  unfold gop. rewrite ah_malloc_unfold, ERS. split; [| split].
  - eapply (alift_bind_etwfX _ _ s A mo _ (RPm SB PA) _ (mga n) G _ k (k + gcost (mga n))); [exact HT| exact HE| exact HK| exact Hga| lia| lia|].
    intros [st' o] A' mo' (G' & b' & k' & HRP & [HMP HVM] & HK' & Hk' & _).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. rewrite <- ENX in *.
    apply tail_etwfX.
    + eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK0 HLIM); [exact HK'| lia].
    + intros v Hv. cbn [fst snd]. split; [reflexivity|].
      split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| exact HVM]]]].
      eapply (AJ_after_alloc tm nx P A s mo n st' A' mo' G' b' k' v); try eassumption. lia.
  - intros tr r mo' H. destruct (alift_bind_tpath _ _ s mo _ tr r mo' HT H) as ([st' o] & mo1 & [HMP _] & H2).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. apply tail_tpath in H2 as (v & _ & -> & _). reflexivity.
  - intros tr H. destruct (alift_bind_texit _ _ s mo _ tr HT H) as ([st' o] & mo1 & [HMP _] & H2).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. exact (tail_texit _ _ _ _ _ _ H2).
Qed.


#[using="Type"] Lemma cop_of_gop : forall npk {X} (m : Monad.M PSA (option X)) res (s : PSA) g mo
    (aG : gmap N Z -> N -> Z -> alw -> PSA -> Model -> Prop) tm' nx' P',
  gop (nsafePA NMAX) gstepA m res s g mo (gpost aG tm' nx' P' s mo) ->
  wreach npk nstep (m s) mo (fun _ _ _ => True) ->
  cop npk m res s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) tm' nx' P' s mo).
Proof.
  intros npk X m res s g mo aG tm' nx' P' (HT & HS & _) HW. unfold cop.
  eapply wreach_mono; [exact (wreach_tpath npk _ _ _ (wreach_twfX _ _ npk _ _ _ HW _ _ HT))|]. cbv beta.
  intros tr r mo' [[_ (g' & HQ)] HP]. split; [exact (HS _ _ _ HP)|].
  destruct r as [|[o s']]; [contradiction|]. cbn [fst snd] in HQ. destruct HQ as [-> (HG & E1 & E2 & E3 & HV)].
  exists s'. split; [reflexivity|]. split; [exists g'; exact HG| auto].
Qed.
#[using="Type"] Lemma copu_of_gopu : forall npk (m : Monad.M PSA unit) (s : PSA) g mo
    (aG : gmap N Z -> N -> Z -> alw -> PSA -> Model -> Prop) tm' nx' P',
  gopu (nsafePA NMAX) gstepA m s g mo (gpost aG tm' nx' P' s mo) ->
  wreach npk nstep (m s) mo (fun _ _ _ => True) ->
  copu npk m s mo (cpost (fun tm nx P s mo => exists g, aG tm nx P g s mo) tm' nx' P' s mo).
Proof.
  intros npk m s g mo aG tm' nx' P' (HT & HS & _) HW. unfold copu.
  eapply wreach_mono; [exact (wreach_tpath npk _ _ _ (wreach_twfX _ _ npk _ _ _ HW _ _ HT))|]. cbv beta.
  intros tr r mo' [[_ (g' & HQ)] HP]. split; [exact (HS _ _ _ HP)|].
  destruct r as [|[[] s']]; [contradiction|]. cbn [fst snd] in HQ. destruct HQ as (HG & E1 & E2 & E3 & HV).
  exists s'. split; [reflexivity|]. split; [exists g'; exact HG| auto].
Qed.

#[using="HLIM ABASE_SH"] Lemma A_mallocC : forall npk, NPKonly npk -> forall tm nx P A s mo n, AJ tm nx P A s mo -> pre_malloc tm P n ->
  cop npk (ho_malloc HOA n) nx s mo (cpost (fun tm nx P s mo => exists g, AJ tm nx P g s mo) (<[nx := n]> tm) (N.succ nx) (P + n1 n) s mo).
Proof.
  intros npk NPK tm nx P A s mo n HJ HP. eapply cop_of_gop; [exact (A_mallocG tm nx P A s mo n HJ HP)|].
  destruct (AJ_malloc_facts tm nx P A s mo n HJ (proj1 HP) (proj2 (proj2 (proj2 (proj2 (proj2 HP)))))) as (G & k & HT & _).
  assert (ERS : ah_resv (ps_heap s) = RESV) by (pose proof HJ as HJ'; cbv zeta in HJ'; destruct HJ' as (_ & ERS & _); exact ERS).
  rewrite ah_malloc_unfold, ERS. eapply alift_bind_wreach; [exact NPK| exact HT|].
  intros [st' o] mo1 [HMP _]. pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. apply tail_wreach. intros; exact I.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="NMAX"] Lemma ah_calloc_eq : forall m n (s : PSA), 0 <= m -> 0 <= n -> m * n < TWO64 -> ho_calloc HOA m n s = ho_malloc HOA (m * n) s.
Proof.
  intros m n s Hm Hn Hmn. cbn [ho_calloc ho_malloc asan_ops]. unfold ah_calloc, ah_malloc, acalloc.
  replace (m <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (TWO64 <=? m * n) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.
#[using="rc NMAX"] Lemma pre_calloc_malloc : forall tm P m n, pre_calloc tm P m n -> pre_malloc tm P (m * n) /\ 0 <= m /\ 0 <= n /\ m * n < TWO64.
Proof.
  intros tm P m n (Hm & Hn & _ & H1 & H2 & H3 & H4 & H5). pose proof H5 as (_ & _ & HNA & _). unfold NMAXA, n1 in HNA.
  assert (0 <= m * n) by (apply Z.mul_nonneg_nonneg; lia).
  split; [exact (conj H (conj H1 (conj H2 (conj H3 (conj H4 H5)))))| unfold TWO64; lia].
Qed.
#[using="HLIM ABASE_SH"] Lemma A_callocG : forall tm nx P A s mo m n, AJ tm nx P A s mo -> pre_calloc tm P m n ->
  gop (nsafePA NMAX) gstepA (ho_calloc HOA m n) nx s A mo (gpost AJ (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo).
Proof.
  intros tm nx P A s mo m n HJ HP. destruct (pre_calloc_malloc _ _ _ _ HP) as (HPM & Hm & Hn & Hmn).
  unfold gop. rewrite (ah_calloc_eq m n s Hm Hn Hmn). exact (A_mallocG tm nx P A s mo (m * n) HJ HPM).
Qed.
#[using="HLIM ABASE_SH"] Lemma A_callocC : forall npk, NPKonly npk -> forall tm nx P A s mo m n, AJ tm nx P A s mo -> pre_calloc tm P m n ->
  cop npk (ho_calloc HOA m n) nx s mo (cpost (fun tm nx P s mo => exists g, AJ tm nx P g s mo) (<[nx := m * n]> tm) (N.succ nx) (P + n1 (m * n)) s mo).
Proof.
  intros npk NPK tm nx P A s mo m n HJ HP. destruct (pre_calloc_malloc _ _ _ _ HP) as (HPM & Hm & Hn & Hmn).
  unfold cop. rewrite (ah_calloc_eq m n s Hm Hn Hmn). exact (A_mallocC npk NPK tm nx P A s mo (m * n) HJ HPM).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition free_st (st' : astate) (p : N) (s : PSA) : PSA :=
  set_heap (ah_set_addr (delete p (ah_addr (ps_heap s))) (ah_set_st st' (ps_heap s))) s.

#[using="Type"] Lemma ah_free_unfold : forall p (s : PSA),
  ho_free HOA p s = mbind (aliftA (afree (ah_st (ps_heap s)) (Some p)))
                          (fun st' => upd_heap (fun h => ah_set_addr (delete p (ah_addr h)) (ah_set_st st' h))) s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma upd_free_eq : forall st' p (s : PSA),
  upd_heap (fun h => ah_set_addr (delete p (ah_addr h)) (ah_set_st st' h)) s = Ret (Ok (tt, free_st st' p s)).
Proof. reflexivity. Qed.

#[using="Type"] Lemma AJ_free_facts : forall tm nx P A s mo p n,
  AJ tm nx P A s mo -> tm !! p = Some n ->
  exists G k,
    atot (afree (ah_st (ps_heap s)) (Some p)) mo (fun st' mo' => free_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) p st' mo' /\ vm_only mo mo')
    /\ evq SB PA (RPst SB PA) [] G (PHI (ah_st (ps_heap s)) + 0) (afree (ah_st (ps_heap s)) (Some p))
    /\ KI (PHI (ah_st (ps_heap s)) + 0) G A k mo /\ k + (VOLMAX - P) / 1024 <= NMAXZ.
Proof.
  intros tm nx P A s mo p n HJ Hp.
  destruct (KI_entry tm nx P A s mo 0 HJ ltac:(lia)) as (G & k & HK & HQ & Hkv & HL & HNF).
  exists G, k. cbv zeta in HJ. destruct HJ as (HI & _ & Hq1 & Hq2 & _ & _ & ETM & _).
  rewrite ETM, lookup_fmap in Hp. destruct ((a_live (ah_st (ps_heap s))) !! p) as [ch|] eqn:Hl; [| discriminate Hp].
  split; [apply atotal_vmo; eapply afree_core; eassumption|].
  split; [apply evq_afree; assumption|]. split; [exact HK| exact Hkv].
Qed.

#[using="Type"] Lemma AJ_after_free : forall tm nx P A s mo p st' A' mo' G' b' k',
  AJ tm nx P A s mo -> free_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) p st' mo' ->
  RPst SB PA G' st' -> KI b' G' A' k' mo' -> k' + (VOLMAX - P) / 1024 <= NMAXZ ->
  AJ (delete p tm) nx P A' (free_st st' p s) mo'.
Proof.
  intros tm nx P A s mo p st' A' mo' G' b' k' HJ HFP HRP HK Hcr. cbv zeta in HJ |- *.
  destruct HJ as (_ & ERS & _ & _ & _ & _ & ETM & ENX & HPO & _ & HAD & HFR).
  destruct HFP as (HI2 & Hlive & ENX' & Hq1 & Hq2). destruct HRP as [HL' HQ']. pose proof HK as (_ & _ & _ & HAB & HGA & HBU & Hk0).
  unfold free_st. cbn [ps_heap set_heap ah_st ah_resv ah_addr ah_frames ah_set_addr ah_set_st].
  split; [exact HI2|]. split; [exact ERS|]. split; [exact Hq1|]. split; [exact Hq2|].
  split; [exact (proj1 HL')|]. split; [exact (proj1 (proj2 HL'))|].
  split; [rewrite Hlive, fmap_delete, ETM; reflexivity|]. split; [rewrite ENX', ENX; reflexivity|]. split; [exact HPO|].
  split; [exists G', k'; split; [exact HQ'|]; split; [exact HAB|]; split; [exact HGA|]; split; [exact HBU|]; split; [exact Hk0| exact Hcr]|].
  split; [| exact HFR].
  intros k a Hka. unfold set_heap in Hka. cbn [ps_heap ah_addr ah_set_addr ah_set_st] in Hka. apply lookup_delete_Some in Hka as [_ Hka]. exact (HAD k a Hka).
Qed.

#[using="HLIM ABASE_SH HSB HPA"] Lemma A_freeG : forall tm nx P A s mo p n, AJ tm nx P A s mo -> pre_free tm p n ->
  gopu (nsafePA NMAX) gstepA (ho_free HOA p) s A mo (gpost AJ (delete p tm) nx P s mo).
Proof.
  intros tm nx P A s mo p n HJ [Hp _].
  destruct (AJ_free_facts tm nx P A s mo p n HJ Hp) as (G & k & HT & HE & HK & Hcr).
  assert (HVP : 0 <= (VOLMAX - P) / 1024).
  { pose proof HJ as HJ'. cbv zeta in HJ'. destruct HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & [HP0 HP1] & _). apply Z.div_pos; lia. }
  unfold gopu. rewrite ah_free_unfold. split; [| split].
  - eapply (alift_bind_etwfX _ _ s A mo _ (RPst SB PA) _ [] G _ k k); [exact HT| exact HE| exact HK| constructor| cbn [gcost]; lia| lia|].
    intros st' A' mo' (G' & b' & k' & HRP & [HFP HVM] & HK' & Hk' & _).
    rewrite upd_free_eq. apply etwfX_ret. cbn [fst snd].
    split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| exact HVM]]]].
    eapply (AJ_after_free tm nx P A s mo p st' A' mo' G' b' k'); try eassumption. lia.
  - intros tr r mo' H. destruct (alift_bind_tpath _ _ s mo _ tr r mo' HT H) as (st' & mo1 & _ & H2).
    rewrite upd_free_eq in H2. cbn in H2. tauto.
  - intros tr H. destruct (alift_bind_texit _ _ s mo _ tr HT H) as (st' & mo1 & _ & H2). rewrite upd_free_eq in H2. exact H2.
Qed.
#[using="HLIM ABASE_SH HSB HPA"] Lemma A_freeC : forall npk, NPKonly npk -> forall tm nx P A s mo p n, AJ tm nx P A s mo -> pre_free tm p n ->
  copu npk (ho_free HOA p) s mo (cpost (fun tm nx P s mo => exists g, AJ tm nx P g s mo) (delete p tm) nx P s mo).
Proof.
  intros npk NPK tm nx P A s mo p n HJ HP. eapply copu_of_gopu; [exact (A_freeG tm nx P A s mo p n HJ HP)|].
  destruct HP as [Hp _]. destruct (AJ_free_facts tm nx P A s mo p n HJ Hp) as (G & k & HT & _).
  rewrite ah_free_unfold. eapply alift_bind_wreach; [exact NPK| exact HT|].
  intros st' mo1 _. rewrite upd_free_eq. apply wreach_ret. exact I.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma aembed_sbind : forall {X Y} (t : AM X) (f : X -> AM Y),
  aembed ATOP (sbind t f) = ebind (aembed ATOP t) (fun a => aembed ATOP (f a)).
Proof.
  intros X Y t f. induction t as [a|e k IH].
  - reflexivity.
  - rewrite aembed_sbind_vis, aembed_vis, ebind_assoc. f_equal. apply functional_extensionality. intros z. apply IH.
Qed.

#[using="Type"] Lemma AJ_chg : forall tm nx P A (s s' : PSA) mo,
  AJ tm nx P A s mo -> ah_st (ps_heap s') = ah_st (ps_heap s) -> ah_resv (ps_heap s') = ah_resv (ps_heap s) ->
  ah_frames (ps_heap s') = ah_frames (ps_heap s) -> (forall k a, ah_addr (ps_heap s') !! k = Some a -> 0 <= a < 2^48) ->
  AJ tm nx P A s' mo.
Proof.
  intros tm nx P A s s' mo HJ E1 E2 E3 HAD. unfold AJ in HJ |- *. cbv zeta in HJ |- *. rewrite E1, E2, E3.
  destruct HJ as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _ & H12). repeat (split; [assumption|]). assumption.
Qed.

Definition realloc_k (p : N) (x : astate * option aptr) : Monad.M PSA (option aptr) :=
  match snd x with
  | None => ah_alloc_tail (fun m => delete p m) (fst x, None)
  | Some q => mbind (aliftA (afree (fst x) (Some p))) (fun st2 => ah_alloc_tail (fun m => delete p m) (st2, Some q))
  end.

#[using="Type"] Lemma ah_realloc_unfold0 : forall p n (s : PSA),
  ho_realloc HOA p n s = mbind (aliftA (arealloc ATOP (ah_resv (ps_heap s)) (ah_st (ps_heap s)) p n)) (fun x => ah_alloc_tail (delete p) x) s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma ah_realloc_unfold : forall p n (s : PSA) chp, a_live (ah_st (ps_heap s)) !! p = Some chp ->
  ho_realloc HOA p n s = mbind (aliftA (amalloc ATOP (ah_resv (ps_heap s)) (ah_st (ps_heap s)) n)) (realloc_k p) s.
Proof.
  intros p n s chp Hp. rewrite ah_realloc_unfold0, !alift_unfold. unfold arealloc.
  match goal with |- context [match ?X with Some _ => _ | None => _ end] => replace X with (Some chp) by (symmetry; exact Hp) end.
  rewrite aembed_sbind, ebind_assoc. f_equal. apply functional_extensionality. intros [st1 [q|]]; unfold realloc_k; cbn [fst snd].
  - rewrite alift_unfold, aembed_sbind, ebind_assoc. f_equal.
  - reflexivity.
Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma realloc_mid : forall tm nx P A s mo p n n' st1 A1 mo1 G1 b1 k1,
  AJ tm nx P A s mo -> tm !! p = Some n -> 1 <= n' -> pot_ok (P + n') ->
  malloc_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) n' (st1, Some nx) mo1 -> RPm SB PA G1 (st1, Some nx) -> KI b1 G1 A1 k1 mo1 ->
  k1 + (VOLMAX - (P + n')) / 1024 <= NMAXZ ->
  AJ (<[nx := n']> tm) (N.succ nx) (P + n') A1 (tail_st (fun m => m) st1 nx 0 s) mo1 /\ (<[nx := n']> tm) !! p = Some n /\ p <> nx.
Proof.
  intros tm nx P A s mo p n n' st1 A1 mo1 G1 b1 k1 HJ Hp Hn' HPO HMP HRP HK Hcr.
  assert (E1 : n1 n' = n') by (unfold n1; lia).
  assert (NE : p <> nx).
  { intros ->. pose proof HJ as HJ'. cbv zeta in HJ'. destruct HJ' as (_ & _ & _ & _ & _ & _ & ETM & ENX & _).
    destruct HMP as (ch & _ & _ & _ & Hnone & _). rewrite ETM, ENX, lookup_fmap, Hnone in Hp. discriminate Hp. }
  split; [| split; [rewrite lookup_insert_ne by (intros E; apply NE; symmetry; exact E); exact Hp| exact NE]].
  pose proof (AJ_after_alloc tm nx P A s mo n' st1 A1 mo1 G1 b1 k1 0 HJ HMP HRP HK) as X. rewrite E1 in X. apply X; [exact Hcr| exact HPO| lia].
Qed.

#[using="Type"] Lemma realloc_free_tot : forall tm nx P A s mo p n n' st1 mo1,
  AJ tm nx P A s mo -> tm !! p = Some n ->
  malloc_post (RESV:=RESV) (ATOP:=ATOP) (ah_st (ps_heap s)) n' (st1, Some nx) mo1 ->
  atot (afree st1 (Some p)) mo1 (fun st2 mo2 => free_post (RESV:=RESV) (ATOP:=ATOP) st1 p st2 mo2 /\ vm_only mo1 mo2).
Proof.
  intros tm nx P A s mo p n n' st1 mo1 HJ Hp HMP. cbv zeta in HJ.
  destruct HJ as (_ & _ & Hq1 & Hq2 & _ & _ & ETM & ENX & _).
  destruct HMP as (ch & _ & HI1 & Hlive & Hnone & _ & Eq1 & Eq2 & _). cbn [fst snd] in *.
  rewrite ETM, lookup_fmap in Hp. destruct ((a_live (ah_st (ps_heap s))) !! p) as [chp|] eqn:Hl; [| discriminate Hp].
  assert (Hl1 : (a_live st1) !! p = Some chp).
  { rewrite Hlive. rewrite lookup_insert_ne; [exact Hl|]. intros E. rewrite E in Hnone. rewrite Hnone in Hl. discriminate Hl. }
  apply atotal_vmo. eapply afree_core; [exact HI1| rewrite Eq1; exact Hq1| rewrite Eq2; exact Hq2| exact Hl1].
Qed.

#[using="Type"] Lemma AJ_live : forall tm nx P A s mo p n, AJ tm nx P A s mo -> tm !! p = Some n -> exists chp, (a_live (ah_st (ps_heap s))) !! p = Some chp.
Proof.
  intros tm nx P A s mo p n HJ Hp. cbv zeta in HJ. destruct HJ as (_ & _ & _ & _ & _ & _ & ETM & _).
  rewrite ETM, lookup_fmap in Hp. destruct ((a_live (ah_st (ps_heap s))) !! p) as [chp|]; [exists chp; reflexivity| discriminate Hp].
Qed.

#[using="HLIM ABASE_SH"] Lemma A_reallocG : forall tm nx P A s mo p n n', AJ tm nx P A s mo -> pre_realloc tm P p n n' ->
  gop (nsafePA NMAX) gstepA (ho_realloc HOA p n') nx s A mo (gpost AJ (<[nx := n']> (delete p tm)) (N.succ nx) (P + n') s mo).
Proof.
  intros tm nx P A s mo p n n' HJ (Hp & Hn' & _ & _ & _ & _ & _ & HAP).
  assert (E1 : n1 n' = n') by (unfold n1; lia).
  assert (HAP1 : apre tm P (n1 n')) by (rewrite E1; exact HAP).
  destruct (AJ_malloc_facts tm nx P A s mo n' HJ ltac:(lia) HAP1) as (G & k & HT & HE & HK & Hga & Hcr & GC0 & ENX). rewrite E1 in Hcr.
  destruct (AJ_live _ _ _ _ _ _ _ _ HJ Hp) as (chp & Hl).
  assert (ERS : ah_resv (ps_heap s) = RESV) by (pose proof HJ as HJ'; cbv zeta in HJ'; destruct HJ' as (_ & ERS & _); exact ERS).
  assert (HAD : forall k a, ah_addr (ps_heap s) !! k = Some a -> 0 <= a < 2^48)
    by (pose proof HJ as HJ'; cbv zeta in HJ'; destruct HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAD & _); exact HAD).
  assert (HPO : pot_ok (P + n')) by (destruct HAP as (HP0 & HPV & _); unfold pot_ok; lia).
  assert (HVP : 0 <= (VOLMAX - (P + n')) / 1024) by (apply Z.div_pos; [unfold pot_ok in HPO; lia| lia]).
  unfold gop. rewrite (ah_realloc_unfold p n' s chp Hl), ERS. split; [| split].
  - eapply (alift_bind_etwfX _ _ s A mo _ (RPm SB PA) _ (mga n') G _ k (k + gcost (mga n'))); [exact HT| exact HE| exact HK| exact Hga| lia| lia|].
    intros [st1 o] A1 mo1 (G1 & b1 & k1 & HRP & [HMP HVM] & HK1 & Hk1 & _).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. rewrite <- ENX in *.
    destruct (realloc_mid tm nx P A s mo p n n' st1 A1 mo1 G1 b1 k1 HJ Hp Hn' HPO HMP HRP HK1 ltac:(lia)) as (HJ1 & Hp1 & NE).
    destruct (AJ_free_facts _ _ _ _ _ _ p n HJ1 Hp1) as (G2 & k2 & HT2 & HE2 & HK2 & Hcr2).
    unfold realloc_k. cbn [fst snd].
    eapply (alift_bind_etwfX _ _ s A1 mo1 _ (RPst SB PA) _ [] G2 _ k2 k2); [exact HT2| exact HE2| exact HK2| constructor| cbn [gcost]; lia| lia|].
    intros st2 A2 mo2 (G3 & b3 & k3 & HRP3 & [HFP HVM2] & HK3 & Hk3 & _).
    apply tail_etwfX; [eapply (ATsafeAlloc.KI_acct_ok NMAX Abase NLK0 HLIM); [exact HK3| lia]|].
    intros v Hv. cbn [fst snd]. split; [reflexivity|].
    split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| eapply vm_only_trans; eassumption]]]].
    pose proof (AJ_after_free _ _ _ _ _ _ p st2 A2 mo2 G3 b3 k3 HJ1 HFP HRP3 HK3 ltac:(lia)) as HJ2.
    rewrite (delete_insert_ne _ _ _ _ NE) in HJ2.
    eapply AJ_chg; [exact HJ2| reflexivity| reflexivity| reflexivity|].
    intros k0 a Hka. unfold tail_st, set_heap in Hka. cbn [ps_heap ah_addr ah_set_addr ah_set_st] in Hka.
    apply lookup_insert_Some in Hka as [[_ <-]|[_ Hka]]; [exact Hv|]. apply lookup_delete_Some in Hka as [_ Hka]. exact (HAD _ _ Hka).
  - intros tr r mo' H. destruct (alift_bind_tpath _ _ s mo _ tr r mo' HT H) as ([st1 o] & mo1 & [HMP _] & H2).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. rewrite <- ENX in *. unfold realloc_k in H2. cbn [fst snd] in H2.
    destruct (alift_bind_tpath _ _ s mo1 _ tr r mo' (realloc_free_tot tm nx P A s mo p n n' st1 mo1 HJ Hp HMP) H2) as (st2 & mo2 & _ & H3).
    apply tail_tpath in H3 as (v & _ & -> & _). reflexivity.
  - intros tr H. destruct (alift_bind_texit _ _ s mo _ tr HT H) as ([st1 o] & mo1 & [HMP _] & H2).
    pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. rewrite <- ENX in *. unfold realloc_k in H2. cbn [fst snd] in H2.
    destruct (alift_bind_texit _ _ s mo1 _ tr (realloc_free_tot tm nx P A s mo p n n' st1 mo1 HJ Hp HMP) H2) as (st2 & mo2 & _ & H3).
    exact (tail_texit _ _ _ _ _ _ H3).
Qed.

#[using="HLIM ABASE_SH"] Lemma A_reallocC : forall npk, NPKonly npk -> forall tm nx P A s mo p n n', AJ tm nx P A s mo -> pre_realloc tm P p n n' ->
  cop npk (ho_realloc HOA p n') nx s mo (cpost (fun tm nx P s mo => exists g, AJ tm nx P g s mo) (<[nx := n']> (delete p tm)) (N.succ nx) (P + n') s mo).
Proof.
  intros npk NPK tm nx P A s mo p n n' HJ HP. eapply cop_of_gop; [exact (A_reallocG tm nx P A s mo p n n' HJ HP)|].
  destruct HP as (Hp & Hn' & _ & _ & _ & _ & _ & HAP).
  assert (E1 : n1 n' = n') by (unfold n1; lia).
  assert (HAP1 : apre tm P (n1 n')) by (rewrite E1; exact HAP).
  destruct (AJ_malloc_facts tm nx P A s mo n' HJ ltac:(lia) HAP1) as (G & k & HT & _ & _ & _ & _ & _ & ENX).
  destruct (AJ_live _ _ _ _ _ _ _ _ HJ Hp) as (chp & Hl).
  assert (ERS : ah_resv (ps_heap s) = RESV) by (pose proof HJ as HJ'; cbv zeta in HJ'; destruct HJ' as (_ & ERS & _); exact ERS).
  rewrite (ah_realloc_unfold p n' s chp Hl), ERS. eapply alift_bind_wreach; [exact NPK| exact HT|].
  intros [st1 o] mo1 [HMP _]. pose proof HMP as (ch & Eo & _). cbn [snd] in Eo. subst o. rewrite <- ENX in *. unfold realloc_k. cbn [fst snd].
  eapply alift_bind_wreach; [exact NPK| exact (realloc_free_tot tm nx P A s mo p n n' st1 mo1 HJ Hp HMP)|].
  intros st2 mo2 _. apply tail_wreach. intros; exact I.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma AMI_vm_eq : forall ch st mo mo', m_vm mo' = m_vm mo -> AMI RESV ATOP ch st mo -> AMI RESV ATOP ch st mo'.
Proof. intros ch st mo mo' E H. unfold AMI, Pm, m_vmmaps, m_vm_lazy, m_vm_materialized in *. rewrite E. exact H. Qed.

#[using="Type"] Lemma AJ_heap : forall tm nx P A (s s' : PSA) mo, ps_heap s' = ps_heap s -> AJ tm nx P A s mo -> AJ tm nx P A s' mo.
Proof. intros tm nx P A s s' mo E H. unfold AJ in *. rewrite E. exact H. Qed.

#[using="Type"] Lemma AJ_step : forall tm nx P A s mo n rsp mo' evs,
  xnode n -> nstep n mo rsp mo' evs -> m_halted mo' = None -> AJ tm nx P A s mo -> AJ tm nx P (gstepA n rsp A) s mo'.
Proof.
  intros tm nx P A s mo n rsp mo' evs Hx Hst _ HJ. rewrite (gstepA_xnode n rsp A Hx).
  pose proof (xnode_nstep_vmS _ _ _ _ _ Hx Hst) as VM. unfold AJ in *. cbv zeta in *.
  destruct HJ as ([HA HM] & Hrest). split; [split; [exact HA| exact (AMI_vm_eq _ _ _ _ VM HM)]| exact Hrest].
Qed.

#[using="Type"] Lemma AJ_below : forall tm nx P A s mo k n, AJ tm nx P A s mo -> tm !! k = Some n -> (k < nx)%N.
Proof.
  intros tm nx P A s mo k n HJ Hk. cbv zeta in HJ. destruct HJ as ((HA & _) & _ & _ & _ & _ & _ & ETM & ENX & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & NF & _). rewrite ETM, lookup_fmap in Hk.
  destruct ((a_live (ah_st (ps_heap s))) !! k) as [ch|] eqn:E; [| discriminate Hk]. rewrite ENX. exact (NF _ _ E).
Qed.
#[using="Type"] Lemma AJ_fresh : forall tm nx P A s mo, AJ tm nx P A s mo -> tm !! nx = None.
Proof. intros tm nx P A s mo HJ. destruct (tm !! nx) as [n|] eqn:E; [| reflexivity]. pose proof (AJ_below _ _ _ _ _ _ _ _ HJ E). lia. Qed.
#[using="Type"] Lemma AJ_pot : forall tm nx P A s mo, AJ tm nx P A s mo -> pot_ok P.
Proof. intros tm nx P A s mo HJ. cbv zeta in HJ. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact HP. Qed.

#[using="Type"] Lemma AJ_addr : forall tm nx P A s mo k n, AJ tm nx P A s mo -> tm !! k = Some n ->
  0 <= ho_addr HOA (ps_heap s) k /\ ho_addr HOA (ps_heap s) k + n <= 2^62 /\ 0 <= n.
Proof.
  intros tm nx P A s mo k n HJ Hk. cbv zeta in HJ. destruct HJ as ((HA & _) & _ & _ & _ & _ & _ & ETM & _ & _ & _ & HAD & _).
  rewrite ETM, lookup_fmap in Hk. destruct ((a_live (ah_st (ps_heap s))) !! k) as [ch|] eqn:E; [| discriminate Hk]. cbn in Hk. injection Hk as <-.
  assert (Hwf : chunk_wf ATOP ch).
  { destruct HA as (_ & HW & _). unfold all_chunks in HW. cbn [app] in HW. apply Forall_app in HW as [HWl _].
    rewrite Forall_forall in HWl. apply HWl. unfold live_chunks. apply in_map_iff. exists (k, ch). split; [reflexivity|].
    apply list_elem_of_In. apply elem_of_map_to_list. exact E. }
  assert (Hsz : 0 <= chunk_size ch <= 2^30) by (destruct ch; cbn in Hwf |- *; lia).
  cbn [ho_addr asan_ops]. unfold ah_addr_of. destruct (ah_addr (ps_heap s) !! k) as [a|] eqn:EA.
  - pose proof (HAD _ _ EA). change (default 0 (Some a)) with a. lia.
  - change (default 0 (@None Z)) with 0. lia.
Qed.

#[using="Type"] Lemma nsafePA_x : forall n A mo, xnode n -> nsafe n mo -> acct_ok NMAX (RNGof A mo) A mo -> nsafePA NMAX n A mo.
Proof.
  intros n A mo Hx Hns HA. split; [exact HA|]. split.
  { split; [exact Hns|]. split; destruct n; cbn in Hx |- *; try contradiction; exact I. }
  intros rsp mo' evs Hst. unfold nstepA in Hst. rewrite (gstepA_xnode n rsp A Hx). split; [| apply alw_le_refl].
  assert (EL : m_vm_lazy mo' = m_vm_lazy mo) by (unfold m_vm_lazy; rewrite (xnode_nstep_vmS _ _ _ _ _ Hx Hst); reflexivity).
  unfold RNGof. rewrite EL. apply fstepS_id. destruct n; cbn in Hx |- *; try contradiction; exact I.
Qed.
#[using="HLIM"] Lemma AJ_safe : forall tm nx P n A s mo, xnode n -> AJ tm nx P A s mo -> nsafe n mo -> nsafePA NMAX n A mo.
Proof. intros tm nx P n A s mo Hx HJ Hns. apply nsafePA_x; [exact Hx| exact Hns| exact (AJ_acct _ _ _ _ _ _ HJ)]. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Notation FOA := (asan_fo site_frame).
Local Notation FRB := (fun e : Pcap.fframe * Z => 0 <= snd e < 2^48).

Definition aeqA (s s' : PSA) : Prop :=
  ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s /\ ps_tls s' = ps_tls s
  /\ ah_st (ps_heap s') = ah_st (ps_heap s) /\ ah_resv (ps_heap s') = ah_resv (ps_heap s) /\ ah_addr (ps_heap s') = ah_addr (ps_heap s)
  /\ (Forall FRB (ah_frames (ps_heap s)) -> Forall FRB (ah_frames (ps_heap s'))).

Definition enter_st (f : Pcap.fframe) (B : Z) (s : PSA) : PSA :=
  set_heap (ah_set_frames ((f, B) :: ah_frames (ps_heap s)) (ps_heap s)) s.
Definition pop_st (s : PSA) : PSA := set_heap (ah_set_frames (tl (ah_frames (ps_heap s))) (ps_heap s)) s.

#[using="Type"] Lemma aeqA_refl : forall s, aeqA s s.
Proof. intros s. unfold aeqA. repeat (split; [reflexivity|]). auto. Qed.
#[using="Type"] Lemma aeqA_enter : forall f B s, 0 <= B < 2^48 -> aeqA s (enter_st f B s).
Proof. intros f B s HB. unfold aeqA, enter_st. cbn. repeat (split; [reflexivity|]). intros HF. constructor; [exact HB| exact HF]. Qed.
#[using="Type"] Lemma aeqA_pop : forall s, aeqA s (pop_st s).
Proof.
  intros s. unfold aeqA, pop_st. cbn. repeat (split; [reflexivity|]). intros HF.
  destruct (ah_frames (ps_heap s)) as [|e l]; [exact HF| apply Forall_cons_iff in HF as [_ HF]; exact HF].
Qed.
#[using="Type"] Lemma aeqA_libc : forall s s', aeqA s s' -> ps_libc s' = ps_libc s /\ ps_outfile s' = ps_outfile s.
Proof. intros s s' (H1 & H2 & _). split; assumption. Qed.
#[using="Type"] Lemma aeqA_G : forall tm nx P g s s' mo, aeqA s s' -> AJ tm nx P g s mo -> AJ tm nx P g s' mo.
Proof.
  intros tm nx P g s s' mo (_ & _ & _ & E1 & E2 & E3 & HF) HJ. unfold AJ in *. cbv zeta in *. rewrite E1, E2, E3.
  destruct HJ as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12). repeat (split; [assumption|]). exact (HF H12).
Qed.

#[using="SITE_OFF"] Lemma A_site : forall tm nx P g s mo site a, AJ tm nx P g s mo -> fo_site FOA s site = Some a -> 0 <= a /\ a + 8192 <= 2^62.
Proof.
  intros tm nx P g s mo site a HJ E. cbv zeta in HJ. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF).
  cbn [fo_site asan_fo] in E. destruct (site_frame site) as [[f off]|] eqn:ES; [| discriminate E].
  unfold ah_frame_base in E. match type of E with context [find ?F ?L] => destruct (find F L) as [e|] eqn:EF end; [| discriminate E]. injection E as <-.
  apply find_some in EF as [Hin _]. rewrite Forall_forall in HF. pose proof (HF _ Hin) as HB. cbv beta in HB.
  pose proof (SITE_OFF _ _ _ ES). lia.
Qed.

#[using="Type"] Lemma fo_enter_unfold : forall X f (m : Monad.M PSA X) (s : PSA),
  fo_enter FOA X f m s = mbind (mpeek_reg48 REG_A0) (fun B s0 => m (enter_st f B s0)) s.
Proof. reflexivity. Qed.
#[using="Type"] Lemma fo_ret_unfold : forall X f (x : X) (s : PSA), fo_ret FOA X f x s = Ret (Ok (x, pop_st s)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mpeek_bind_tpathX : forall {X} a (k : Z -> Monad.M PSA X) (s : PSA) g mo tr res g' mo',
  tpathX gstepA (mbind (mpeek a) k s) g mo tr res g' mo' -> exists v, 0 <= v < 256 /\ tpathX gstepA (k v s) g mo tr res g' mo'.
Proof.
  intros X a k s g mo tr res g' mo' H. unfold mbind in H. apply tpathX_ebind in H.
  destruct H as [[H _]|(tr1 & [v s1] & g1 & mo1 & tr2 & H1 & H2 & ->)]; unfold mpeek, msys in *.
  - apply tpathX_enode in H as (rsp & _ & _ & E). discriminate E.
  - apply tpathX_enode in H1 as (rsp & Hst & EG & E). injection E as E1 E2. subst v s1. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv).
    cbn [gstepA] in EG. subst g1. exists (dec_peek rsp). split; [exact Hv| exact H2].
Qed.
#[using="rc NMAX"] Lemma mpeek_reg48_tpathX : forall {X} r (k : Z -> Monad.M PSA X) (s : PSA) g mo tr res g' mo',
  tpathX gstepA (mbind (mpeek_reg48 r) k s) g mo tr res g' mo' -> exists v, 0 <= v < 2^48 /\ tpathX gstepA (k v s) g mo tr res g' mo'.
Proof.
  intros X r k s g mo tr res g' mo' H. unfold mpeek_reg48 in H.
  do 6 (rewrite mbind_assoc in H; apply mpeek_bind_tpathX in H; destruct H as (? & ? & H)).
  rewrite mbind_mret in H. eexists. split; [| exact H]. lia.
Qed.
#[using="Type"] Lemma mpeek_bind_twfX : forall {X} a (k : Z -> Monad.M PSA X) (s : PSA) A mo (P : exc (X * PSA) -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 256 -> twfX (nsafePA NMAX) gstepA (k v s) A mo P) ->
  twfX (nsafePA NMAX) gstepA (mbind (mpeek a) k s) A mo P.
Proof.
  intros X a k s A mo P HA HK. unfold mbind, ebind. apply twfX_bind. apply mpeek_twfX; [exact HA|].
  intros v Hv. cbn [fst snd]. exact (HK v Hv).
Qed.
#[using="rc"] Lemma mpeek_reg48_twfX : forall {X} r (k : Z -> Monad.M PSA X) (s : PSA) A mo (P : exc (X * PSA) -> alw -> Model -> Prop),
  acct_ok NMAX (RNGof A mo) A mo -> (forall v, 0 <= v < 2^48 -> twfX (nsafePA NMAX) gstepA (k v s) A mo P) ->
  twfX (nsafePA NMAX) gstepA (mbind (mpeek_reg48 r) k s) A mo P.
Proof.
  intros X r k s A mo P HA HK. unfold mpeek_reg48.
  do 6 (rewrite mbind_assoc; apply mpeek_bind_twfX; [exact HA|]; intros ? ?).
  rewrite mbind_mret. apply HK. lia.
Qed.
#[using="rc NMAX"] Lemma mpeek_bind_wexit : forall npk {X} a (k : Z -> Monad.M PSA X) (s : PSA) mo T,
  (forall v, 0 <= v < 256 -> wexit npk nstep nexit (k v s) mo T) -> wexit npk nstep nexit (mbind (mpeek a) k s) mo T.
Proof.
  intros npk X a k s mo T HK. unfold mbind, mpeek, msys, enode, ebind. cbn [ITree.bind].
  destruct (npk (NPeek a)) as [f|] eqn:E.
  - eapply wexit_peek; [exact E|]. intros rsp mo' evs Hst. destruct (peek_step _ _ _ _ _ Hst) as (-> & -> & Hv).
    cbn [ITree.bind fst snd app]. exact (HK _ Hv).
  - eapply wexit_vis with (rsp := peek_rsp 0) (mo' := mo) (evs := []); [exact E| cbn [nstep]; split; [reflexivity|]; split; [reflexivity|]; exists 0; split; [lia| reflexivity]|].
    cbn [ITree.bind fst snd app]. rewrite dec_peek_rsp by lia. apply HK. lia.
Qed.
#[using="rc NMAX"] Lemma mpeek_reg48_wexit : forall npk {X} r (k : Z -> Monad.M PSA X) (s : PSA) mo T,
  (forall v, 0 <= v < 2^48 -> wexit npk nstep nexit (k v s) mo T) -> wexit npk nstep nexit (mbind (mpeek_reg48 r) k s) mo T.
Proof.
  intros npk X r k s mo T HK. unfold mpeek_reg48.
  do 6 (rewrite mbind_assoc; apply mpeek_bind_wexit; intros ? ?).
  rewrite mbind_mret. apply HK. lia.
Qed.

#[using="rc NMAX"] Lemma A_enter_path : forall X f (m : Monad.M PSA X) s g mo tr r g' mo',
  tpathX gstepA (fo_enter FOA X f m s) g mo tr r g' mo' -> exists s', aeqA s s' /\ tpathX gstepA (m s') g mo tr r g' mo'.
Proof.
  intros X f m s g mo tr r g' mo' H. rewrite fo_enter_unfold in H. apply mpeek_reg48_tpathX in H as (v & Hv & H).
  exists (enter_st f v s). split; [apply aeqA_enter; exact Hv| exact H].
Qed.
#[using="rc NMAX"] Lemma A_enter_exit : forall X f (m : Monad.M PSA X) s mo tr,
  texit nstep nexit (fo_enter FOA X f m s) mo tr -> exists s', aeqA s s' /\ texit nstep nexit (m s') mo tr.
Proof.
  intros X f m s mo tr H. rewrite fo_enter_unfold in H. apply mpeek_reg48_texit in H as (v & Hv & H).
  exists (enter_st f v s). split; [apply aeqA_enter; exact Hv| exact H].
Qed.
#[using="HLIM"] Lemma A_enter_safe : forall X f (m : Monad.M PSA X) tm nx Pt s g mo (P : exc (X * PSA) -> alw -> Model -> Prop),
  AJ tm nx Pt g s mo -> (forall s', aeqA s s' -> twfX (nsafePA NMAX) gstepA (m s') g mo P) ->
  twfX (nsafePA NMAX) gstepA (fo_enter FOA X f m s) g mo P.
Proof.
  intros X f m tm nx Pt s g mo P HJ HK. rewrite fo_enter_unfold. apply mpeek_reg48_twfX; [exact (AJ_acct _ _ _ _ _ _ HJ)|].
  intros v Hv. apply HK. apply aeqA_enter; exact Hv.
Qed.
#[using="Type"] Lemma A_ret : forall X f (x : X) s, exists s', aeqA s s' /\ fo_ret FOA X f x s = Ret (Ok (x, s')).
Proof. intros X f x s. exists (pop_st s). split; [apply aeqA_pop| apply fo_ret_unfold]. Qed.
#[using="rc NMAX"] Lemma A_enter_reach : forall npk, NPKonly npk -> forall X f (m : Monad.M PSA X) s mo W,
  (forall s', aeqA s s' -> wreach npk nstep (m s') mo W) -> wreach npk nstep (fo_enter FOA X f m s) mo W.
Proof.
  intros npk _ X f m s mo W HK. rewrite fo_enter_unfold. apply mpeek_reg48_wreach. intros v Hv. apply HK. apply aeqA_enter; exact Hv.
Qed.
#[using="rc NMAX"] Lemma A_enter_wexit : forall npk, NPKonly npk -> forall X f (m : Monad.M PSA X) s mo T,
  (forall s', aeqA s s' -> wexit npk nstep nexit (m s') mo T) -> wexit npk nstep nexit (fo_enter FOA X f m s) mo T.
Proof.
  intros npk _ X f m s mo T HK. rewrite fo_enter_unfold. apply mpeek_reg48_wexit. intros v Hv. apply HK. apply aeqA_enter; exact Hv.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AH_A : AHalves NMAX site_frame :=
  mkAHalves NMAX site_frame AJ aeqA AJ_heap AJ_step AJ_fresh AJ_below AJ_addr AJ_pot AJ_safe
    A_mallocG A_callocG A_reallocG A_freeG A_mallocC A_callocC A_reallocC A_freeC
    aeqA_refl aeqA_libc aeqA_G A_site A_enter_path A_enter_exit A_enter_safe A_ret A_enter_reach A_enter_wexit.

End Ops.
End CANSEC1.
End HeapI_A.

(* [comment removed for export] *)
Module HeapI_SA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad MSafe HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require Import SimW ProgSim.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA RunConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanHeap__SpecA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require ATsafeCore. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanHeap__SpecA.AsanHeap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.ATsafeCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require MSafeX USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require ATsafeX AIface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.MSafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.HeapI_S OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.ATsafeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.AIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma npeek_NPK segs : NPKonly (npeek segs).
Proof. intros n. destruct n; first [exact I| reflexivity]. Qed.

Section Kits.
Context {rc : runConstT}.
Context {CES : CEIL}.                       (* [comment removed for export] *)
Variable NMAX : nat.
Variable site_frame : Pcap.stack_site -> option (Pcap.fframe * Z).
Variable AH : AHalves NMAX site_frame.
#[local] Notation HOA := (asan_ops (CE:=ceil_of_rc)).
#[local] Notation FOA := (asan_fo site_frame).
#[local] Notation HOS := (full_ops (CE:=CES)).
#[local] Notation aC := (fun tm nx P s mo => exists g, aG NMAX site_frame AH tm nx P g s mo).

#[using="Type"] Lemma ShiQ_addr62 tm nx P s mo k n : ShiQ (CE:=CES) tm nx P s mo -> tm !! k = Some n ->
  0 <= ho_addr HOS (ps_heap s) k /\ ho_addr HOS (ps_heap s) k + n <= 2^62 /\ 0 <= n.
Proof.
  intros H Hk. destruct (ShiQ_addr tm nx P s mo k n H Hk) as (A1 & A2 & A3).
  pose proof (@alloc_ceiling_lt47 CES) as ACL. split; [lia|]. split; [| exact A3]. revert A2 ACL. generalize (@alloc_ceiling CES). intros; lia.
Qed.

(* [comment removed for export] *)
Definition HeapI_SA (segsA : list Segment) : HeapSimI unsafeS ugstepS HOS HOA (npeek segsA) :=
  mkHSI unsafeS ugstepS HOS HOA (npeek segsA)
    ShiG aC
    (fun tm nx P g s s' mo => ShiQ_heap tm nx P s s' mo)
    (fun tm nx P s s' mo E H => let '(ex_intro _ g Hg) := H in ex_intro _ g (aG_heap _ _ AH tm nx P g s s' mo E Hg))
    (fun tm nx P g s mo n rsp mo' evs => ShiQ_step tm nx P s mo n rsp mo' evs)
    (fun tm nx P s mo n rsp mo' evs Hx Hst Hh H => let '(ex_intro _ g Hg) := H in ex_intro _ (gstepA n rsp g) (aG_step _ _ AH tm nx P g s mo n rsp mo' evs Hx Hst Hh Hg))
    (fun tm nx P g s mo => ShiQ_fresh tm nx P s mo) (fun tm nx P g s mo k n => ShiQ_below tm nx P s mo k n)
    (fun tm nx P g s mo k n => ShiQ_addr62 tm nx P s mo k n) (fun tm nx P g s mo => ShiQ_pot tm nx P s mo)
    S_mallocG (fun tm nx P s mo n H => let '(ex_intro _ g Hg) := H in a_mallocC _ _ AH _ (npeek_NPK segsA) tm nx P g s mo n Hg)
    S_callocG (fun tm nx P s mo m n H => let '(ex_intro _ g Hg) := H in a_callocC _ _ AH _ (npeek_NPK segsA) tm nx P g s mo m n Hg)
    S_reallocG (fun tm nx P s mo k n n' H => let '(ex_intro _ g Hg) := H in a_reallocC _ _ AH _ (npeek_NPK segsA) tm nx P g s mo k n n' Hg)
    S_freeG (fun tm nx P s mo k n H => let '(ex_intro _ g Hg) := H in a_freeC _ _ AH _ (npeek_NPK segsA) tm nx P g s mo k n Hg).

(* [comment removed for export] *)
Definition HeapI_AS (segsS : list Segment) : HeapSimI (nsafePA NMAX) gstepA HOA HOS (npeek segsS) :=
  mkHSI (nsafePA NMAX) gstepA HOA HOS (npeek segsS)
    (aG _ _ AH) ShiQ
    (aG_heap _ _ AH) (fun tm nx P s s' mo => ShiQ_heap tm nx P s s' mo)
    (aG_step _ _ AH) (fun tm nx P s mo n rsp mo' evs => ShiQ_step tm nx P s mo n rsp mo' evs)
    (aG_fresh _ _ AH) (aG_below _ _ AH) (aG_addr _ _ AH) (aG_pot _ _ AH)
    (a_mallocG _ _ AH) (S_mallocC segsS)
    (a_callocG _ _ AH) (S_callocC segsS)
    (a_reallocG _ _ AH) (S_reallocC segsS)
    (a_freeG _ _ AH) (S_freeC segsS).

(* [comment removed for export] *)
Definition FrameI_SA (segsA : list Segment) : FrameSimI (HeapI_SA segsA) fo_nop FOA.
Proof.
  refine (mkFSI _ _ _ _ _ (HeapI_SA segsA) fo_nop FOA (fun s s' => s' = s) (aeq _ _ AH) _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - intros s. reflexivity.
  - exact (aeq_refl _ _ AH).
  - intros s s' ->. split; reflexivity.
  - exact (aeq_libc _ _ AH).
  - intros tm nx P g s s' mo -> H. exact H.
  - intros tm nx P s s' mo E [g H]. exists g. exact (aeq_G _ _ AH tm nx P g s s' mo E H).
  - intros tm nx P g s mo site a _ E. discriminate E.
  - intros A f m s g mo tr r g' mo' H. exists s. split; [reflexivity| exact H].
  - intros A f m s mo tr H. exists s. split; [reflexivity| exact H].
  - intros A f m tm nx Pt s g mo P _ H. exact (H s eq_refl).
  - intros A f x s. exists s. split; reflexivity.
  - intros A f m s mo W H. exact (a_enter_reach _ _ AH _ (npeek_NPK segsA) A f m s mo W H).
  - intros A f m s mo T H. exact (a_enter_wexit _ _ AH _ (npeek_NPK segsA) A f m s mo T H).
  - exact (a_ret _ _ AH).
Defined.

Definition FrameI_AS (segsS : list Segment) : FrameSimI (HeapI_AS segsS) FOA fo_nop.
Proof.
  refine (mkFSI _ _ _ _ _ (HeapI_AS segsS) FOA fo_nop (aeq _ _ AH) (fun s s' => s' = s) _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact (aeq_refl _ _ AH).
  - intros s. reflexivity.
  - exact (aeq_libc _ _ AH).
  - intros s s' ->. split; reflexivity.
  - exact (aeq_G _ _ AH).
  - intros tm nx P s s' mo -> H. exact H.
  - exact (a_site _ _ AH).
  - exact (a_enter_path _ _ AH).
  - exact (a_enter_exit _ _ AH).
  - exact (a_enter_safe _ _ AH).
  - exact (a_ret _ _ AH).
  - intros A f m s mo W H. exact (H s eq_refl).
  - intros A f m s mo T H. exact (H s eq_refl).
  - intros A f x s. exists s. split; reflexivity.
Defined.

(* [comment removed for export] *)
Definition UK_SA (segsA : list Segment) : UKit :=
  mkUKit unit unsafeS ugstepS UK_stepS fheap aheap HOS HOA eq_refl eq_refl segsA (HeapI_SA segsA)
         (fun tm nx P n g s mo Hx _ Hs => UK_safeS n g mo Hx Hs) fo_nop FOA (FrameI_SA segsA).
Definition UK_AS (segsS : list Segment) : UKit :=
  mkUKit alw (nsafePA NMAX) gstepA (fun n rsp g Hx => gstepA_xnode n rsp g Hx) aheap fheap HOA HOS eq_refl eq_refl segsS (HeapI_AS segsS)
         (aG_safe _ _ AH) FOA fo_nop (FrameI_AS segsS).
End Kits.
End HeapI_SA.
