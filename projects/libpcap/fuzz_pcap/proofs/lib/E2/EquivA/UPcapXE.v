(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull Fmt PcapPrelim PcapTypes PcapPure Pcap StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UFmt UFrame. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFrame.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require Import MSafeX.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require USimX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require NodeSimX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapIface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require RelX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require HeapI_S__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UStdioX. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UDriverX__EquivA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA Require UPcapXB__EquivA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.USimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.UFrameX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.DecodeX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapIface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.NodeSimX__EquivA.NodeSimX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.RelX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.HeapI_S__EquivA.UNodesX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UStdioX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UDriverX__EquivA.UDriverX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation idl := (fun l : libc_st hptr => l).
#[local] Notation pcapT := (PcapTypes.pcap hptr hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
Definition EO (out : hptr) (fdo : Z) : kfe := mkKfe fdo KNull (to_bytes DEVNULL) (Some out) None 0.
Definition KH (ho : option (hptr * Z)) : list kfe := match ho with Some (out, fdo) => [EO out fdo] | None => [] end.
Definition HSH (ho : option (hptr * Z)) : list hptr := match ho with Some (out, _) => [out] | None => [] end.
Definition FH (ho : option (hptr * Z)) : fpm := match ho with Some (out, fdo) => [(out, PW (EO out fdo) [])] | None => [] end.
Definition OH (ho : option (hptr * Z)) : option hptr := match ho with Some (out, _) => Some out | None => None end.
(* [comment removed for export] *)
Definition LH (ho : option (hptr * Z)) (LB : list (N * Z)) : list (N * Z) := match ho with Some (out, _) => (out, FILE_ALLOC) :: LB | None => LB end.
(* [comment removed for export] *)
Definition LBok (LB : list (N * Z)) : Prop := zlen LB <= 2 /\ R63N (map snd LB) <= BASEB /\ liveL LB <= 2^27 + 1.

(* [comment removed for export] *)
Definition V_ONE : Z := 3 * FILE_ALLOC + V_READ.
Definition RUNV : Z := MAX_INPUT + 4 * V_ONE.
End WithCeil.


Ltac case_if E := lazymatch goal with |- usimX _ _ _ _ (if ?c then _ else _) _ _ => destruct c eqn:E end.

Section WithCeil.
(* [comment removed for export] *)
Section Harness.
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
#[local] Notation PR_G := (prims HOG FOG stkG).
#[local] Notation PR_C := (prims HOC FOC stkC).

Definition RH (tm : gmap N Z) (nx : N) (pt : Z) (ho : option (hptr * Z)) (C : list (list byte * list byte)) : relX :=
  RUK tm nx pt (KH ho) C idl (WF (OH ho) (HSH ho) (FH ho)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma us_get_outfile tm nx pt K C oh hs F :
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (mbind mget (fun s : PSG => mret (ps_outfile s))) (mbind mget (fun s : PSC => mret (ps_outfile s)))
        (eqpost (fun r => fun gh sG moG sC moC => r = oh /\ RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC)).
Proof.
  eapply ru_bind2; [apply ru_get|]. intros a b. apply usim_pointwise. intros gh0 sG0 moG0 sC0 moC0 (-> & -> & EL & EO & HR0).
  eapply ru_pre; [| intros ? ? ? ? ? (-> & -> & -> & -> & ->); exact HR0]. rewrite EO.
  xfr; apply ru_ret. intros gh sG moG sC moC HR. split; [| exact HR]. destruct HR0 as [_ [_ [HO _]]]. exact HO.
Qed.

#[using="Type"] Lemma us_set_outfile tm nx pt K C oh hs F o :
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (mupd (set_outfile o)) (mupd (set_outfile o)) (eqpost (fun _ => RUK tm nx pt K C idl (WF o hs F))).
Proof.
  apply usim_upd. intros gh sG moG sC moC [HR [HF HW]]. split; [reflexivity|]. split; [apply RQ_outfile_upd; exact HR|].
  destruct sG; cbn in *. split; [exact HF|]. destruct HW as (_ & A & B & D). split; [reflexivity|]. exact (conj A (conj B D)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma cstr_length l : (length (cstr l) <= length l)%nat.
Proof. induction l as [|c l IH]; cbn; [lia|]. destruct (c =? 0); cbn; lia. Qed.
#[using="Type"] Lemma small_packet_length a b : Forall (fun p => zlength p < 2^61) (pieces_packet_length a b).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_packet_length. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_number_of_packets a : Forall (fun p => zlength p < 2^61) (pieces_number_of_packets a).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_number_of_packets. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_couldnt_open m : mok m -> Forall (fun p => zlength p < 2^61) (pieces_couldnt_open (cstr m)).
Proof.
  intros Hm. apply (Forall_lt_of_le 512); [lia|]. unfold pieces_couldnt_open. apply pieces_small; [lia| items_small_tac|].
  apply args_small_cons_str; [| apply args_small_nil]. unfold mok, zlength in *. pose proof (cstr_length m). lia.
Qed.
#[using="Type"] Lemma small_failed_remove e : Forall (fun p => zlength p < 2^61) (pieces_failed_remove e).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_failed_remove. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.
#[using="Type"] Lemma small_failed_open e : Forall (fun p => zlength p < 2^61) (pieces_failed_open e).
Proof. apply (Forall_lt_of_le 64); [lia|]. unfold pieces_failed_open. apply pieces_small; [lia| items_small_tac| args_small_tac]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section InCtx.
Variable rc : rctx.
Hypothesis RCW : rcwf rc.
Variables (out : hptr) (eo : kfe).
Hypothesis Hoh : rc_oh rc = Some out.
Hypothesis HF0 : rc_F0 rc = [(out, PW eo [])].
Hypothesis Heo : In eo (rc_Kx rc).
Hypothesis Heo_own : k_own eo = Some out.
Hypothesis Heo_kind : k_kind eo = KNull.
Hypothesis Heo_data : k_data eo = None.
Hypothesis Hhs : In out (rc_hs rc).
#[local] Notation fp := (rc_fp rc).
#[local] Notation e0 := (rc_e0 rc).
#[local] Notation d := (rc_d rc).
#[local] Notation toks := (toks rc).
#[local] Notation PI := (PI rc).
#[local] Notation RPP := (RPP Uk rc).
#[local] Notation PST := (PST Uk rc).
#[local] Notation PA := (PA rc).

(* [comment removed for export] *)
#[using="RCW out eo Hoh HF0 Heo Heo_own Heo_kind Heo_data Hhs"] Lemma pr_out_fprintf nx tm pt off pos ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RPP nx tm pt off pos) (with_outfile MOps PR_G (fun o => e_fprintf PR_G o ps)) (with_outfile MOps PR_C (fun o => e_fprintf PR_C o ps))
        (eqpost (fun _ => RPP nx tm pt off pos)).
Proof.
  intros Hps. unfold with_outfile. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims e_get_outfile e_fprintf prims]; xfe. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP.
  eapply ru_bind; [apply us_get_outfile|]. intros o. apply usim_pure. intros ->. rewrite Hoh.
  pose proof (rw_F0 _ RCW) as NF. rewrite HF0 in NF. cbn in NF.
  eapply ru_post.
  - apply (us_fprintf Uk tm nx pt (UPcapXA.KR_ rc off) (rc_C rc) (Some out) (rc_hs rc) (UPcapXA.FR_ rc off pos) out eo [] ps).
    + unfold UPcapXA.KR_. apply in_app_iff. left. exact Heo.
    + exact Heo_own.
    + right. exact Heo_kind.
    + exact Hhs.
    + unfold UPcapXA.FR_. rewrite HF0. right. left. reflexivity.
    + exact Hps.
    + rewrite Heo_data. exact I.
  - intros [] ? ? ? ? ? (fl & H). rewrite (kapp_data_none eo fl Heo_data) in H.
    destruct H as [HR [HF HW]]. split; [exact HR|]. split.
    + rewrite kset_self in HF; [exact HF| unfold UPcapXA.KR_; apply in_app_iff; left; exact Heo|].
      pose proof (proj1 (FI_KP _ _ _ _ _ HF)) as ND. rewrite (map_fd_kset eo (UPcapXA.KR_ rc off) (or_intror I)) in ND. exact ND.
    + destruct HW as (W1 & W2 & W3 & W4). split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      intros h P f HP Hf. assert (X : forall P', In (h, P') (fupd out (PW eo ([] ++ to_bytes (concat ps))) (UPcapXA.FR_ rc off pos)) -> P' f) by (intros P' HP'; exact (W4 h P' f HP' Hf)).
      unfold UPcapXA.FR_ in HP, X. rewrite HF0 in HP, X. unfold fupd in X. cbn [List.filter fst] in X.
      destruct (N.eqb_spec fp out) as [E|NE]; [exfalso; apply NF; left; symmetry; exact E|]. rewrite N.eqb_refl in X. cbn in X.
      destruct HP as [HP|[HP|[]]].
      * injection HP as <- <-. apply X. right. left. reflexivity.
      * injection HP as <- <-. pose proof (X _ ltac:(left; reflexivity)) as Y. unfold PW in Y |- *. rewrite Heo_data in Y |- *. exact Y.
Qed.

(* [comment removed for export] *)
#[using="STK RCW out eo Hoh HF0 Heo Heo_own Heo_kind Heo_data Hhs"] Lemma pr_packet_loop ngfuel : forall fuel nx p tm pt off pos,
  PI p pos -> TML tm (toks p) -> Z.of_nat (length d) < pos + Z.of_nat fuel -> Z.of_nat (length d) < Z.of_nat ngfuel -> PA false p pos pt ->
  usimS (RPP nx tm pt off pos) (packet_loop MOps PR_G fuel ngfuel p) (packet_loop MOps PR_C fuel ngfuel p)
        (PST (fun (r : pcapT) p' pos' pt' => r = p' /\ PA true p' pos' pt')).
Proof.
  induction fuel as [|fuel IH]; intros nx p tm pt off pos HPI HT HF HNF HPA.
  { exfalso. pose proof (pi_pos _ _ _ HPI). cbn in HF. lia. }
  cbn [packet_loop]. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims]; xfe.
  eapply (pp_bind Uk rc); [apply (pr_pcap_next_ex Uk stkG stkC STK rc RCW ngfuel nx p tm pt off pos HPI HT); [pose proof (pi_pos _ _ _ HPI); lia| exact HPA]|].
  intros [r p1] p1' tm1 nx1 pt1 off1 pos1 (E1 & PS1 & LE1 & PR1 & PA1) HPI1 HT1. cbn [fst snd] in E1, PR1, PA1. subst p1'. cbn beta iota.
  destruct (0 <? r) eqn:E; rewrite ?E in PA1; cbn in PA1.
  - apply Z.ltb_lt in E. specialize (PR1 E).
    eapply ru_bind; [apply (pr_out_fprintf nx1 tm1 pt1 off1 pos1 _ (small_packet_length _ _))|]. intros [].
    apply (IH nx1 p1 tm1 pt1 off1 pos1 HPI1 HT1); [rewrite Nat2Z.inj_succ in HF; lia| exact HNF| exact PA1].
  - xfr; apply (pp_ret Uk rc _ nx1 p1 tm1 pt1 off1 pos1); [exact (conj eq_refl PA1)| exact HPI1| exact HT1].
Qed.

End InCtx.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkrc (ho : option (hptr * Z)) (LB : list (N * Z)) (C : list (list byte * list byte)) (fp : hptr) (fd : Z) (dd : list byte) (P0 : Z) : rctx :=
  mkRC (LH ho LB) (KH ho) (FH ho) (fp :: HSH ho) (cdel (to_bytes TMPNAME) C) (OH ho) fp (mkKfe fd KR (to_bytes TMPNAME) (Some fp) (Some dd) 0) dd P0.

#[using="Type"] Lemma to_bytes_length l : length (to_bytes l) = length l.
Proof. unfold to_bytes. apply length_map. Qed.
#[using="Type"] Lemma neq_by_length {A} (a b : list A) : length a <> length b -> a <> b.
Proof. intros H E. apply H. rewrite E. reflexivity. Qed.
#[using="Type"] Lemma DEVNULL_ne_TMPNAME : to_bytes DEVNULL <> to_bytes TMPNAME.
Proof. apply neq_by_length. rewrite !to_bytes_length. vm_compute. discriminate. Qed.
#[using="Type"] Lemma TMPNAME_ne_dot : to_bytes TMPNAME <> dot_path.
Proof. apply neq_by_length. rewrite to_bytes_length. vm_compute. discriminate. Qed.
#[using="Type"] Lemma K_clear_KH ho : K_clear (KH ho) (to_bytes TMPNAME).
Proof. intros e He _. destruct ho as [[out fdo]|]; [| destruct He]. destruct He as [<-|[]]. cbn. exact DEVNULL_ne_TMPNAME. Qed.

#[using="Type"] Lemma LH_len ho LB : LBok LB -> zlen (LH ho LB) <= 3.
Proof. intros (A & _). destruct ho as [[o f]|]; cbn [LH]; rewrite ?zlen_cons; lia. Qed.
#[using="Type"] Lemma LH_liveL ho LB : liveL (LH ho LB) <= n1 FILE_ALLOC + liveL LB.
Proof. destruct ho as [[o f]|]; cbn [LH]; rewrite ?liveL_cons; unfold n1, FILE_ALLOC; lia. Qed.
#[using="Type"] Lemma LH_R63N ho LB : R63N (map snd (LH ho LB)) = R63N (map snd LB).
Proof. destruct ho as [[o f]|]; cbn [LH map snd]; rewrite ?R63N_cons, ?bigb_FILE; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma LH_budget tm ho LB n : TML tm (LH ho LB) -> LBok LB -> 0 <= n < MMAP_THRESHOLD ->
  ROOMN (sizes tm) P9 n /\ PHI P9 + R63N (sizes tm) + bigb n <= BLIVE /\ PHI P9 + R63N (map snd (LH ho LB)) <= BLIVE.
Proof.
  intros HT HL Hn. pose proof HL as (A & B & _). rewrite (bigb_small n) by lia.
  assert (X : PHI P9 + R63N (map snd (LH ho LB)) + bigb n <= BLIVE).
  { rewrite LH_R63N, (bigb_small n) by lia. rewrite PHI_P9. unfold BASEB, B26, BLIVE, PGSZ in *. lia. }
  destruct (budget_of_TML tm (LH ho LB) n HT ltac:(pose proof (LH_len ho LB HL); lia) ltac:(lia) X) as [R1 R2].
  rewrite (bigb_small n) in R2, X by lia. split; [exact R1|]. split; [lia| lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma LH_pre tm ho LB pt : TML tm (LH ho LB) -> LBok LB -> 0 <= pt -> pt + FILE_ALLOC <= VOLMAX -> pre_malloc tm pt FILE_ALLOC.
Proof.
  intros HT HL Hp1 Hp2. destruct (LH_budget tm ho LB FILE_ALLOC HT HL ltac:(unfold FILE_ALLOC, MMAP_THRESHOLD; lia)) as (R1 & R2 & R3).
  pose proof HL as (A & B & LV). pose proof (LH_liveL ho LB) as LL. pose proof (LH_len ho LB HL) as LN.
  split; [unfold FILE_ALLOC; lia|]. split; [unfold size_overflows, FILE_ALLOC; apply Z.leb_gt; lia|]. split; [rewrite bigb_FILE; unfold QMAX, PGSZ; lia|].
  split; [exact R1|]. split; [exact R2|].
  unfold apre. rewrite (live1_TML _ _ HT), (zlen_perm _ _ (TML_sizes _ _ HT)). unfold zlen in *. rewrite length_map.
  unfold n1, FILE_ALLOC, NMAXA, LIVEMAX, LIVECNT in *. repeat split; lia.
Qed.

#[using="STK"] Lemma pr_pcap_open_offline fuel tm nx pt out fdo LB C dd :
  TML tm (LH (Some (out, fdo)) LB) -> LBok LB -> clookup C (to_bytes TMPNAME) = Some dd -> Z.of_nat (length dd) < MAX_INPUT -> Z.of_nat (length dd) < Z.of_nat fuel ->
  pot_ok (pt + n1 FILE_ALLOC + V_READ) ->
  usimS (RH tm nx pt (Some (out, fdo)) C) (pcap_open_offline MOps PR_G fuel TMPNAME) (pcap_open_offline MOps PR_C fuel TMPNAME)
        (eqpost (fun r => fun gh sG moG sC moC =>
           match r with
           | inl m => mok m /\ exists tm' nx' pt' C', (TML tm' (LH (Some (out, fdo)) LB) /\ pt' <= pt + n1 FILE_ALLOC + V_READ) /\ RH tm' nx' pt' (Some (out, fdo)) C' gh sG moG sC moC
           | inr p => exists fd tm' nx' pt' off' pos', let rc := mkrc (Some (out, fdo)) LB C nx fd dd (pt + n1 FILE_ALLOC) in
                      rcwf rc /\ PI rc p pos' /\ TML tm' (toks rc p) /\ PA rc false p pos' pt' /\ RPP Uk rc nx' tm' pt' off' pos' gh sG moG sC moC
           end)).
Proof.
  intros HT HL HC HD HF HPOT. set (ho := Some (out, fdo)) in *.
  unfold pcap_open_offline, pcap_open_offline_with_tstamp_precision. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_fopen_r e_fclose prims]; xfe. unfold RH.
  apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh Uk _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  destruct HR0 as [HQ0 [HF0 _]]. pose proof (RQ_pot _ _ _ _ _ _ _ _ HQ0) as PP0. clear HQ0. unfold pot_ok in PP0, HPOT.
  pose proof (FI_owner _ _ _ _ _ HF0 (EO out fdo) out ltac:(left; reflexivity) eq_refl) as LT. clear HF0.
  assert (V0 : 0 <= V_READ) by (unfold V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX; lia).
  pose proof (LH_pre tm ho LB pt HT HL ltac:(lia) ltac:(unfold n1 in HPOT; lia)) as PM.
  eapply ru_bind.
  { apply (us_fopen_r Uk tm nx pt (KH ho) C (OH ho) (HSH ho) (FH ho) TMPNAME dd (K_clear_KH ho) HC TMPNAME_ne_dot PM). }
  intros [fp|].
  2:{ (* [comment removed for export] *)
    eapply ru_bind; [apply (pr_errmsg Uk stkG stkC)|]. intros m. apply usim_pure. intros Mm.
    xfr; apply ru_ret. intros gh sG moG sC moC HR. split; [exact Mm|]. exists tm, nx, pt, C. split; [split; [exact HT| unfold n1; lia]| exact HR]. }
  apply usim_pure. intros ->. eapply usim_exI. intros fd. apply usim_pure. intros Hfd. cbv zeta.
  set (rc := mkrc ho LB C nx fd dd (pt + n1 FILE_ALLOC)).
  assert (HT1 : TML (<[nx:=FILE_ALLOC]> tm) (L0 rc)) by (apply TML_insert; [exact HT| exact FR]).
  (* [comment removed for export] *)
  apply ru_use. intros gh1 sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1. clear HF1. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : fdo <> fd) by (inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; symmetry; exact E).
  assert (RCW : rcwf rc).
  { pose proof HL as (A1 & A2 & A3). subst rc ho. constructor; cbn [rc_B rc_Kx rc_F0 rc_hs rc_C rc_oh rc_fp rc_e0 rc_d rc_P0 mkrc LH KH FH HSH OH k_own k_kind k_data k_fd].
    - split; [rewrite zlen_cons; lia|]. cbn [map snd]; rewrite R63N_cons, bigb_FILE; lia.
    - exact FR.
    - intros x [<-|[]]. cbn. exact NEfd.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - left; reflexivity.
    - cbn. intros [E|[]]. apply (N.lt_irrefl nx). rewrite <- E at 1. exact LT.
    - cbn. intros E. injection E as E. apply (N.lt_irrefl nx). rewrite <- E at 1. exact LT.
    - exact HD.
    - rewrite liveL_cons. unfold n1 at 1. unfold FILE_ALLOC in *. lia.
    - unfold pot_ok, n1 in *. split; lia. }
  eapply ru_pre with (R' := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP Uk rc (N.succ nx) (<[nx:=FILE_ALLOC]> tm) (pt + n1 FILE_ALLOC) 0 0).
  2:{ intros ? ? ? ? ? HR. subst rc ho. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP, UPcapXA.KR_, UPcapXA.FR_. cbn [rc_Kx rc_C rc_oh rc_hs rc_F0 rc_fp rc_e0 rc_d rc_B mkrc KH FH HSH OH LH].
      unfold fupd in HR. cbn [List.filter fst KH FH HSH OH] in HR. destruct (N.eqb_spec out nx) as [E|_]; [exfalso; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT|]. cbn [negb] in HR. exact HR. }
  eapply ru_bind; [apply (pr_fopen_offline Uk stkG stkC STK rc RCW fuel (N.succ nx) _ (pt + n1 FILE_ALLOC) 0 PCAP_TSTAMP_PRECISION_MICRO HT1 HF ltac:(unfold PZ; subst rc; cbn [rc_P0 mkrc]; lia))|].
  intros r. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros off1. eapply usim_exI; intros pos1. apply usim_pure; intros Q.
  destruct r as [m|p]; cbn [Q_open] in Q.
  - destruct Q as [[[HT2 Hp2] Mm] HP2]. cbn [rc_P0 rc mkrc] in HP2.
    assert (BUD : PHI P9 + R63N (sizes tm1) <= BLIVE).
    { rewrite (R63N_perm _ _ (TML_sizes _ _ HT2)). unfold L0. cbn [map snd rc_B rc mkrc]. rewrite R63N_cons, bigb_FILE. pose proof (LH_budget tm ho LB 0 HT HL ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & _ & X). lia. }
    eapply ru_bind.
    { unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP. apply (us_fclose_r Uk tm1 nx1 pt1 (UPcapXA.KR_ rc off1) (rc_C rc) (rc_oh rc) (rc_hs rc) (UPcapXA.FR_ rc off1 pos1) nx (kat (rc_e0 rc) off1) dd pos1 FILE_ALLOC
               (KR_in rc off1) (own_kat rc RCW off1) (rw_hs _ RCW) (FR_in rc off1 pos1) (rw_oh _ RCW) (conj (TML_lookup _ _ _ _ HT2 ltac:(left; reflexivity)) BUD)). }
    intros []. rewrite (kdel_KR rc RCW), (fdel_FR rc RCW), (kpath_kat rc).
    xfr; apply ru_ret. intros gh sG moG sC moC HR. split; [exact Mm|]. exists (delete nx tm1), nx1, pt1, ((k_path (rc_e0 rc), dd) :: rc_C rc). split; [split|].
    + pose proof (TML_delete _ _ _ _ HT2 ltac:(left; reflexivity)) as X. unfold L0 in X. rewrite lrm_head in X. exact X.
    + exact HP2.
    + subst rc ho. cbn [rc_Kx rc_oh rc_hs rc_F0 mkrc hrem List.filter HSH] in HR |- *. rewrite N.eqb_refl in HR. cbn [negb] in HR.
      destruct (N.eqb_spec out nx) as [E|_]; [exfalso; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT|]. cbn [negb] in HR. exact HR.
  - destruct Q as [[HPI2 HT2] HP2]. xfr; apply ru_ret. intros gh sG moG sC moC HR. exists fd, tm1, nx1, pt1, off1, pos1. cbv zeta. split; [exact RCW|]. split; [exact HPI2|]. split; [exact HT2| exact (conj HP2 HR)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Notation NDT := (ND (to_bytes TMPNAME)).
#[local] Notation frm := (framed NDT).

#[using="Type"] Lemma nd_lift {A} (R : relX) (m : Monad.M PSG A) (m' : Monad.M PSC A) (R1 : A -> relX) :
  usimS R m m' (eqpost R1) -> usimS (frm R) m m' (eqpost (fun a => frm (R1 a))).
Proof.
  intros H. eapply usim_post; [apply (usim_ND (to_bytes TMPNAME) npk); exact H|].
  intros a b ? ? ? ? ? [[-> HR] HN]. split; [reflexivity| exact (conj HR HN)].
Qed.

#[using="Type"] Lemma fr_exI {A B X} (R : X -> relX) (m : Monad.M PSG A) (m' : Monad.M PSC B) Q :
  (forall x, usimS (frm (R x)) m m' Q) -> usimS (frm (fun gh sG moG sC moC => exists x, R x gh sG moG sC moC)) m m' Q.
Proof. apply framed_exI. Qed.

#[using="Type"] Lemma fr_pure {A B} (R : relX) (phi : Prop) (m : Monad.M PSG A) (m' : Monad.M PSC B) Q :
  (phi -> usimS (frm R) m m' Q) -> usimS (frm (fun gh sG moG sC moC => phi /\ R gh sG moG sC moC)) m m' Q.
Proof. apply framed_pure. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fr_use {A B} (R : relX) (m : Monad.M PSG A) (m' : Monad.M PSC B) Q :
  (forall gh sG moG sC moC, R gh sG moG sC moC -> usimS (frm R) m m' Q) -> usimS (frm R) m m' Q.
Proof. intros H. apply framed_use. intros gh sG moG sC moC HR _. exact (H _ _ _ _ _ HR). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ruk_bind_nd {A B} tm nx pt K C g W (phi : A -> Prop) (K1 : A -> list kfe) (C1 : A -> list (list byte * list byte)) (g1 : A -> libc_st hptr -> libc_st hptr)
      (W1 : A -> libc_st hptr -> option hptr -> Prop) (m : Monad.M PSG A) (m' : Monad.M PSC A) (k : A -> Monad.M PSG B) (k' : A -> Monad.M PSC B) Q :
  usimS (RUK tm nx pt K C g W) m m' (eqpost (fun a => fun gh sG moG sC moC => phi a /\ RUK tm nx pt (K1 a) (C1 a) (g1 a) (W1 a) gh sG moG sC moC)) ->
  (forall a, phi a -> usimS (frm (RUK tm nx pt (K1 a) (C1 a) (g1 a) (W1 a))) (k a) (k' a) Q) ->
  usimS (frm (RUK tm nx pt K C g W)) (mbind m k) (mbind m' k') Q.
Proof. intros H1 H2. eapply ru_bind; [apply nd_lift; exact H1|]. intros a. apply fr_pure. exact (H2 a). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pp_bind_nd rc {A B'} (Φ : A -> pcapT -> Z -> Z -> Prop) nx tm pt off pos (m : Monad.M PSG A) (m' : Monad.M PSC A) (k : A -> Monad.M PSG B') (k' : A -> Monad.M PSC B') Q :
  usimS (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP Uk rc nx tm pt off pos) m m' (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.PST Uk rc Φ) ->
  (forall r p' tm' nx' pt' off' pos', Φ r p' pos' pt' -> UPcapXA.PI rc p' pos' -> TML tm' (UPcapXA.toks rc p') ->
     usimS (frm (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP Uk rc nx' tm' pt' off' pos')) (k r) (k' r) Q) ->
  usimS (frm (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.EquivA.UPcapXB__EquivA.UPcapXB.RPP Uk rc nx tm pt off pos)) (mbind m k) (mbind m' k') Q.
Proof.
  intros H1 H2. eapply ru_bind; [apply nd_lift; exact H1|]. intros r.
  apply fr_exI; intros p'. apply fr_exI; intros tm'. apply fr_exI; intros nx'. apply fr_exI; intros pt'. apply fr_exI; intros off'. apply fr_exI; intros pos'.
  eapply framed_pre; [| intros ? ? ? ? ? (X1 & X2 & X3 & X4); exact (conj X1 (conj X2 (conj X3 X4)))].
  apply fr_pure; intros X1. apply fr_pure; intros X2. apply fr_pure; intros X3. exact (H2 _ _ _ _ _ _ _ X1 X2 X3).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma DEVNULL_bytes : to_bytes DEVNULL = devnull_path.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma TMPNAME_not_devnull : to_bytes TMPNAME <> devnull_path.
Proof. intros E. apply (f_equal (@length _)) in E. vm_compute in E. discriminate. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_fopen_tmp tm nx pt K C oh hs F :
  K_clear K (to_bytes TMPNAME) ->
  pre_malloc tm pt FILE_ALLOC ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fopen HOG TMPNAME true) (s_fopen HOC TMPNAME true)
        (eqpost (fun r => fun gh sG moG sC moC =>
           match r with
           | None => RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd KW (to_bytes TMPNAME) (Some nx) (Some []) 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes TMPNAME) C) idl (WF oh (nx :: hs) (fupd nx (PW e []) F))) gh sG moG sC moC
           end)).
Proof.
  intros HC PM.
  eapply ru_post; [apply (us_fopen_w Uk tm nx pt K C oh hs F TMPNAME true HC ltac:(vm_compute; reflexivity) PM)|].
  intros [p|] gh sG moG sC moC H; [| exact H]. destruct H as [-> (fd & Hfd & HR)]. split; [reflexivity|]. exists fd. split; [exact Hfd|].
  cbv zeta in HR |- *. rewrite (wkind_other _ TMPNAME_not_devnull) in HR. exact HR.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma us_fopen_devnull tm nx pt K C oh hs F :
  K_clear K (to_bytes DEVNULL) ->
  pre_malloc tm pt FILE_ALLOC ->
  usimS (RUK tm nx pt K C idl (WF oh hs F)) (s_fopen HOG DEVNULL true) (s_fopen HOC DEVNULL true)
        (eqpost (fun r => fun gh sG moG sC moC =>
           match r with
           | None => RUK tm nx pt K C idl (WF oh hs F) gh sG moG sC moC
           | Some p => p = nx /\ exists fd, 3 <= fd <= 4096 /\
               let e := mkKfe fd KNull (to_bytes DEVNULL) (Some nx) None 0 in
               RX (<[nx := FILE_ALLOC]> tm) (N.succ nx) (pt + n1 FILE_ALLOC) (UK (N.succ nx) (K ++ [e]) (cdel (to_bytes DEVNULL) C) idl (WF oh (nx :: hs) (fupd nx (PW e []) F))) gh sG moG sC moC
           end)).
Proof.
  intros HC PM.
  eapply ru_post; [apply (us_fopen_w Uk tm nx pt K C oh hs F DEVNULL false HC ltac:(vm_compute; reflexivity) PM)|].
  intros [p|] gh sG moG sC moC H; [| exact H]. destruct H as [-> (fd & Hfd & HR)]. split; [reflexivity|]. exists fd. split; [exact Hfd|].
  cbv zeta in HR |- *. rewrite DEVNULL_bytes, wkind_devnull in HR. rewrite DEVNULL_bytes. exact HR.
Qed.

#[using="Type"] Lemma filter_idem {A} (f : A -> bool) l : List.filter f (List.filter f l) = List.filter f l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. destruct (f x) eqn:E; cbn; [rewrite E, IH; reflexivity| exact IH]. Qed.
#[using="Type"] Lemma fdel_fupd h P F : fdel h (fupd h P F) = fdel h F.
Proof. unfold fdel, fupd. cbn. rewrite N.eqb_refl. cbn. apply filter_idem. Qed.
#[using="Type"] Lemma hrem_hd h l : hrem h (h :: l) = hrem h l.
Proof. unfold hrem. cbn. rewrite N.eqb_refl. reflexivity. Qed.
#[using="Type"] Lemma hrem_notin h l : ~ In h l -> hrem h l = l.
Proof.
  induction l as [|x l IH]; intros NI; [reflexivity|]. unfold hrem in *. cbn. destruct (N.eqb_spec x h) as [->|NE]; [exfalso; apply NI; left; reflexivity|].
  cbn. rewrite IH; [reflexivity|]. intros X; apply NI; right; exact X.
Qed.

#[using="Type"] Lemma kdel_snoc_EO out fdo e : k_fd e <> fdo -> kdel (k_fd e) ([EO out fdo] ++ [e]) = [EO out fdo].
Proof. intros NE. unfold kdel. cbn. rewrite (proj2 (Z.eqb_neq _ _) (not_eq_sym NE)), Z.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma pr_bufferToFile tm nx pt out fdo LB C data :
  TML tm (LH (Some (out, fdo)) LB) -> LBok LB -> zlength data < MAX_INPUT -> pot_ok (pt + n1 FILE_ALLOC) ->
  usimS (frm (RH tm nx pt (Some (out, fdo)) C)) (bufferToFile MOps PR_G TMPNAME data) (bufferToFile MOps PR_C TMPNAME data)
        (eqpost (fun r => fun gh sG moG sC moC => exists tm' nx' pt' C',
           TML tm' (LH (Some (out, fdo)) LB) /\ (0 <= r -> clookup C' (to_bytes TMPNAME) = Some (to_bytes data)) /\ pt <= pt' <= pt + n1 FILE_ALLOC /\
           frm (RH tm' nx' pt' (Some (out, fdo)) C') gh sG moG sC moC)).
Proof.
  intros HT HL HD HPOT. set (ho := Some (out, fdo)) in *. pose proof (zlength_nonneg data) as ND0.
  unfold bufferToFile. cbn [mo_bind mo_ret MOps e_fenter e_fret prims e_remove e_last_errno e_printf e_fopen_w e_fwrite e_fclose prims]; xfe. unfold RH.
  apply fr_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh Uk _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
  destruct HR0 as [HQ0 [HF0 _]]. pose proof (RQ_pot _ _ _ _ _ _ _ _ HQ0) as PP0. clear HQ0. unfold pot_ok in PP0, HPOT.
  pose proof (FI_owner _ _ _ _ _ HF0 (EO out fdo) out ltac:(left; reflexivity) eq_refl) as LT. clear HF0.
  assert (N1 : 0 <= n1 FILE_ALLOC) by (unfold n1; lia).
  assert (NEo : out <> nx) by (intros E; apply (N.lt_irrefl nx); rewrite <- E at 1; exact LT).
  (* [comment removed for export] *)
  eapply ru_bind; [apply (us_remove Uk tm nx pt (KH ho) C (OH ho) (HSH ho) (FH ho) TMPNAME (K_clear_KH ho))|].
  intros r0. apply usim_pure. intros Hr0. set (C1 := if r0 =? 0 then cdel (to_bytes TMPNAME) C else C).   (* [comment removed for export] *)
  assert (RET : forall (z : Z) tm' nx' pt' C', z < 0 -> TML tm' (LH ho LB) -> pt <= pt' <= pt + n1 FILE_ALLOC ->
            usimS (frm (RUK tm' nx' pt' (KH ho) C' idl (WF (OH ho) (HSH ho) (FH ho)))) (mret z) (mret z)
                  (eqpost (fun r => fun gh sG moG sC moC => exists tm'' nx'' pt'' C'', TML tm'' (LH ho LB) /\ (0 <= r -> clookup C'' (to_bytes TMPNAME) = Some (to_bytes data)) /\
                                                        pt <= pt'' <= pt + n1 FILE_ALLOC /\
                                                        frm (RUK tm'' nx'' pt'' (KH ho) C'' idl (WF (OH ho) (HSH ho) (FH ho))) gh sG moG sC moC))).
  { intros z tm' nx' pt' C' Hz HT' HB. xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm', nx', pt', C'. split; [exact HT'|]. split; [intros; lia| exact (conj HB HR)]. }
  eapply (ruk_bind_nd tm nx pt (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
  { destruct (negb (r0 =? 0)).
    - eapply (ruk_bind Uk tm nx pt (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_get_errno|]. intros ? ? ? ? ? ? H; exact (conj I H). }
      intros e _. case_if EE.
      + eapply (ruk_bind Uk tm nx pt (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
        { eapply ru_post; [apply us_printf; apply small_failed_remove|]. intros ? ? ? ? ? ? H; exact (conj I H). }
        intros [] _. xfr; apply ruk_ret. exact I.
      + xfr; apply ruk_ret. exact I.
    - xfr; apply ruk_ret. exact I. }
  intros k _. destruct (negb k); [apply (RET (-1) tm nx pt C1 ltac:(lia) HT ltac:(lia))|].
  (* [comment removed for export] *)
  destruct (LH_budget tm ho LB FILE_ALLOC HT HL ltac:(unfold FILE_ALLOC, MMAP_THRESHOLD; lia)) as (R1 & R2 & R3).
  pose proof (LH_pre tm ho LB pt HT HL ltac:(lia) ltac:(unfold n1 in HPOT; lia)) as PM.
  eapply ru_bind; [apply nd_lift; apply (us_fopen_tmp tm nx pt (KH ho) C1 (OH ho) (HSH ho) (FH ho) (K_clear_KH ho) PM)|].
  intros [fd1|].
  2:{ eapply (ruk_bind_nd tm nx pt (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_get_errno|]. intros ? ? ? ? ? ? H; exact (conj I H). }
      intros e _. eapply (ruk_bind_nd tm nx pt (KH ho) C1 idl _ (fun _ => True) (fun _ => KH ho) (fun _ => C1) (fun _ => idl) (fun _ => WF (OH ho) (HSH ho) (FH ho))).
      { eapply ru_post; [apply us_printf; apply small_failed_open|]. intros ? ? ? ? ? ? H; exact (conj I H). }
      intros [] _. apply (RET (-2) tm nx pt C1 ltac:(lia) HT ltac:(lia)). }
  apply fr_pure. intros ->. apply fr_exI. intros fd. apply fr_pure. intros Hfd. cbv zeta.
  set (e1 := mkKfe fd KW (to_bytes TMPNAME) (Some nx) (Some []) 0).
  assert (HT1 : TML (<[nx:=FILE_ALLOC]> tm) ((nx, FILE_ALLOC) :: LH ho LB)) by (apply TML_insert; [exact HT| exact FR]).
  (* [comment removed for export] *)
  apply fr_use. intros gh1 sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1. clear HF1. subst ho. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : k_fd e1 <> fdo) by (cbn; inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; exact E).
  (* [comment removed for export] *)
  eapply ru_bind.
  { apply nd_lift. apply (us_fwrite Uk _ (N.succ nx) _ (KH (Some (out, fdo)) ++ [e1]) (cdel (to_bytes TMPNAME) C1) (OH (Some (out, fdo))) (nx :: HSH (Some (out, fdo))) (fupd nx (PW e1 []) (FH (Some (out, fdo)))) nx e1 [] data).
    - apply in_app_iff. right. left. reflexivity.
    - reflexivity.
    - left. split; [reflexivity| discriminate].       (* [comment removed for export] *)
    - left. reflexivity.
    - left. reflexivity.
    - unfold MAX_INPUT in HD. lia.
    - cbn. unfold FLEN, MAX_INPUT in *. lia. }
  intros n. apply fr_exI. intros fl. apply fr_pure. intros ->.
  (* [comment removed for export] *)
  assert (BUD : PHI P9 + R63N (sizes (<[nx:=FILE_ALLOC]> tm)) <= BLIVE).
  { rewrite (R63N_perm _ _ (TML_sizes _ _ HT1)). cbn [map snd]. rewrite R63N_cons, bigb_FILE. lia. }
  eapply ru_bind.
  { apply nd_lift. apply (us_fclose_w Uk _ (N.succ nx) _ _ _ _ _ _ nx (kapp e1 fl) ([] ++ to_bytes data) FILE_ALLOC).
    - apply (In_kset_new _ _ e1); [apply in_app_iff; right; left; reflexivity| reflexivity].
    - reflexivity.
    - reflexivity.
    - left. reflexivity.
    - left. reflexivity.
    - cbn. intros E. injection E as E. exact (NEo E).
    - split; [apply (TML_lookup _ _ _ _ HT1); left; reflexivity| exact BUD].
    - cbn. rewrite to_bytes_length. unfold FLEN, MAX_INPUT, zlength in *. lia. }
  intros []. rewrite kdel_kset. replace (k_fd (kapp e1 fl)) with (k_fd e1) by reflexivity. change (KH (Some (out, fdo))) with [EO out fdo] at 1.
  rewrite (kdel_snoc_EO out fdo e1 NEfd). subst e1. cbn [k_data kapp kmove k_fd k_path k_off].
  rewrite Z.eqb_refl. cbn [negb].
  eapply ru_pre with (R' := frm (RUK (delete nx (<[nx:=FILE_ALLOC]> tm)) (N.succ nx) (pt + n1 FILE_ALLOC) (KH (Some (out, fdo))) ((to_bytes TMPNAME, [] ++ to_bytes data) :: cdel (to_bytes TMPNAME) C1) idl
                               (WF (OH (Some (out, fdo))) (HSH (Some (out, fdo))) (FH (Some (out, fdo)))))).
  2:{ intros ? ? ? ? ? [HR HN]. split; [| exact HN]. rewrite !fdel_fupd, hrem_hd in HR. cbn [HSH FH] in HR. rewrite (hrem_notin nx [out]) in HR by (intros [E|[]]; exact (NEo E)).
      rewrite (fdel_notin nx) in HR by (intros [E|[]]; exact (NEo E)). exact HR. }
  xfr; apply ru_ret. intros gh sG moG sC moC HR. exists (delete nx (<[nx:=FILE_ALLOC]> tm)), (N.succ nx), (pt + n1 FILE_ALLOC), ((to_bytes TMPNAME, [] ++ to_bytes data) :: cdel (to_bytes TMPNAME) C1).
  split; [pose proof (TML_delete _ _ _ _ HT1 ltac:(left; reflexivity)) as X; rewrite lrm_head in X; exact X|].
  split; [intros _; cbn [clookup app]; rewrite path_eqb_refl; reflexivity| split; [lia| exact HR]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma seal_TEMPLATE : seal_name TEMPLATE = Some TMPNAME.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pr_h_fprintf tm nx pt out fdo C ps :
  Forall (fun p => zlength p < 2^61) ps ->
  usimS (RH tm nx pt (Some (out, fdo)) C) (with_outfile MOps PR_G (fun o => e_fprintf PR_G o ps)) (with_outfile MOps PR_C (fun o => e_fprintf PR_C o ps))
        (eqpost (fun _ => RH tm nx pt (Some (out, fdo)) C)).
Proof.
  intros Hps. unfold with_outfile, RH. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims e_get_outfile e_fprintf prims KH OH HSH FH]; xfe.
  eapply ru_bind; [apply us_get_outfile|]. intros o. apply usim_pure. intros ->.
  eapply ru_post.
  - apply (us_fprintf Uk tm nx pt [EO out fdo] C (Some out) [out] [(out, PW (EO out fdo) [])] out (EO out fdo) [] ps); [left; reflexivity| reflexivity| right; reflexivity| left; reflexivity| left; reflexivity| exact Hps| exact I].
  - intros [] ? ? ? ? ? (fl & H). rewrite (kapp_data_none (EO out fdo) fl eq_refl) in H. destruct H as [HR [HF HW]]. split; [exact HR|]. split.
    + unfold kset in HF. cbn [map k_fd EO] in HF. rewrite Z.eqb_refl in HF. exact HF.
    + destruct HW as (W1 & W2 & W3 & W4). split; [exact W1|]. split; [exact W2|]. split; [exact W3|].
      intros h P f [HP|[]] Hf. injection HP as <- <-. pose proof (W4 out _ f ltac:(left; reflexivity) Hf) as Y. unfold PW in Y |- *. cbn [k_data EO] in Y |- *. exact Y.
Qed.

#[using="STK"] Lemma pr_fuzz_one tm nx pt ho C LB data :
  TML tm (LH ho LB) -> LBok LB -> zlength data < MAX_INPUT -> pt + V_ONE <= VOLMAX ->
  usimS (RH tm nx pt ho C) (LLVMFuzzerTestOneInput MOps PR_G data) (LLVMFuzzerTestOneInput MOps PR_C data)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' ho' C', (TML tm' (LH ho' LB) /\ pt' <= pt + V_ONE) /\ RH tm' nx' pt' ho' C' gh sG moG sC moC)).
Proof.
  intros HT HL HD HPOT. pose proof (zlength_nonneg data) as ND0.
  assert (V0 : 0 <= V_READ) by (unfold V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX; lia).
  assert (N1 : n1 FILE_ALLOC = 1264) by reflexivity. assert (F1 : FILE_ALLOC = 1264) by reflexivity. unfold V_ONE in HPOT |- *.
  unfold LLVMFuzzerTestOneInput. cbn [mo_bind mo_ret mo_unr MOps e_fenter e_fret prims e_get_outfile e_set_outfile e_fopen_w e_mkstemp e_close_fd e_unlink prims]; xfe.
  unfold RH. apply ru_use. intros gh0 sG0 moG0 sC0 moC0 [HQ0 _]. pose proof (RQ_pot _ _ _ _ _ _ _ _ HQ0) as PP0. clear HQ0 gh0 sG0 moG0 sC0 moC0. unfold pot_ok in PP0.
  eapply ru_bind; [apply us_get_outfile|]. intros o0. apply usim_pure. intros ->.
  (* [comment removed for export] *)
  eapply (ru_bind _ _ _ _ (fun o => fun gh sG moG sC moC => exists tm1 nx1 pt1 ho1 C1, (TML tm1 (LH ho1 LB) /\ o = OH ho1 /\ pt <= pt1 <= pt + n1 FILE_ALLOC) /\ RUK tm1 nx1 pt1 (KH ho1) C1 idl (WF (OH ho1) (HSH ho1) (FH ho1)) gh sG moG sC moC)).
  { destruct ho as [[out fdo]|]; cbn [OH].
    - xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm, nx, pt, (Some (out, fdo)), C. split; [split; [exact HT| split; [reflexivity| lia]]| exact HR].
    - cbn [KH HSH FH].
      apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh Uk _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR. clear HR0.
      pose proof (LH_pre tm None LB pt HT HL ltac:(lia) ltac:(lia)) as PM.
      eapply ru_bind; [apply (us_fopen_devnull tm nx pt [] C None [] [] ltac:(intros e []) PM)|].
      intros [fp|].
      + apply usim_pure. intros ->. eapply usim_exI. intros fd. apply usim_pure. intros Hfd. cbv zeta. cbn [app fupd List.filter].
        eapply ru_bind; [apply us_set_outfile|]. intros [].
        xfr; apply ru_ret. intros gh sG moG sC moC HR. exists (<[nx:=FILE_ALLOC]> tm), (N.succ nx), (pt + n1 FILE_ALLOC), (Some (nx, fd)), (cdel (to_bytes DEVNULL) C).
        split; [split; [cbn [LH]; apply TML_insert; [exact HT| exact FR]| split; [reflexivity| lia]]| exact HR].
      + eapply ru_bind; [apply us_set_outfile|]. intros [].
        xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm, nx, pt, None, C. split; [split; [exact HT| split; [reflexivity| lia]]| exact HR]. }
  intros o. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros ho1. eapply usim_exI; intros C1. apply usim_pure. intros (HT1 & -> & HB1).
  destruct ho1 as [[out fdo]|]; cbn [OH].
  2:{ xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm1, nx1, pt1, None, C1. split; [split; [exact HT1| lia]| exact HR]. }
  clear tm nx ho C HT. set (ho := Some (out, fdo)).
  (* [comment removed for export] *)
  eapply ru_bind; [apply (us_mkstemp Uk tm1 nx1 pt1 (KH ho) C1 (OH ho) (HSH ho) (FH ho) TEMPLATE TMPNAME false seal_TEMPLATE (K_clear_KH ho) TMPNAME_not_devnull)|].
  intros [filename fd]. apply usim_pure. intros Hname. apply usim_pure. intros Hfd. cbn [fst snd] in Hname, Hfd. subst filename. cbn beta iota.
  case_if Efd.
  { xfr; apply ru_ret. intros gh sG moG sC moC [HR _]. apply Z.ltb_lt in Efd. assert (E : fd = -1) by lia. rewrite E in HR. cbn in HR.
    exists tm1, nx1, pt1, ho, C1. split; [split; [exact HT1| lia]| exact HR]. }
  apply Z.ltb_ge in Efd. assert (NE1 : fd <> -1) by lia. rewrite (proj2 (Z.eqb_neq _ _) NE1).
  set (et := mkKfe fd KW (to_bytes TMPNAME) None None 0).
  (* [comment removed for export] *)
  eapply ru_pre with (R' := frm (RUK tm1 nx1 pt1 (KH ho ++ [et]) (cdel (to_bytes TMPNAME) C1) idl (WF (OH ho) (HSH ho) (FH ho))));
    [| intros ? ? ? ? ? [HR HN]; exact (conj HR (HN NE1))].
  apply fr_use. intros gh1 sG1 moG1 sC1 moC1 [_ [HF1 _]]. pose proof (proj1 (FI_KP _ _ _ _ _ HF1)) as ND1.
  pose proof (FI_owner _ _ _ _ _ HF1 (EO out fdo) out ltac:(apply in_app_iff; left; left; reflexivity) eq_refl) as LT. clear HF1. subst ho. cbn [map app k_fd KH EO] in ND1.
  assert (NEfd : k_fd et <> fdo) by (cbn; inversion ND1 as [|? ? NI _]; subst; intros E; apply NI; left; exact E).
  assert (NEo : out <> nx1) by (intros E; apply (N.lt_irrefl nx1); rewrite <- E at 1; exact LT).
  (* [comment removed for export] *)
  eapply ru_bind; [apply nd_lift; apply (us_close Uk tm1 nx1 pt1 (KH (Some (out, fdo)) ++ [et]) (cdel (to_bytes TMPNAME) C1) _ _ _ et ltac:(apply in_app_iff; right; left; reflexivity) eq_refl)|].
  intros r0. apply fr_pure. intros _. change (KH (Some (out, fdo))) with [EO out fdo] at 1. rewrite (kdel_snoc_EO out fdo et NEfd). cbn [cclose k_data k_kind et].
  (* [comment removed for export] *)
  eapply ru_bind; [apply (pr_bufferToFile tm1 nx1 pt1 out fdo LB _ data HT1 HL HD ltac:(unfold pot_ok; lia))|].
  intros r. eapply usim_exI; intros tm2. eapply usim_exI; intros nx2. eapply usim_exI; intros pt2. eapply usim_exI; intros C2. apply usim_pure; intros HT2. apply usim_pure; intros HC2. apply usim_pure; intros HB2.
  case_if Er.
  { eapply ru_bind; [apply (us_unlink Uk tm2 nx2 pt2 _ C2 _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. xfr; apply ru_ret. intros gh sG moG sC moC HR. eexists tm2, nx2, pt2, (Some (out, fdo)), _. split; [split; [exact HT2| lia]| exact (proj1 HR)]. }
  apply Z.ltb_ge in Er. specialize (HC2 Er).
  (* [comment removed for export] *)
  eapply ru_bind; [apply nd_lift; apply (pr_pcap_open_offline (S (length data)) tm2 nx2 pt2 out fdo LB C2 (to_bytes data) HT2 HL HC2);
    [rewrite to_bytes_length; unfold zlength in HD; lia| rewrite to_bytes_length; unfold zlength in HD; lia| unfold pot_ok; lia]|].
  intros [m|p].
  - apply fr_pure. intros Mm. apply fr_exI; intros tm3. apply fr_exI; intros nx3. apply fr_exI; intros pt3. apply fr_exI; intros C3. apply fr_pure. intros [HT3 HB3].
    eapply ru_bind; [apply nd_lift; apply (pr_h_fprintf tm3 nx3 pt3 out fdo C3 _ (small_couldnt_open m Mm))|]. intros [].
    eapply ru_bind; [apply (us_unlink Uk tm3 nx3 pt3 _ C3 _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. xfr; apply ru_ret. intros gh sG moG sC moC HR. eexists tm3, nx3, pt3, (Some (out, fdo)), _. split; [split; [exact HT3| lia]| exact (proj1 HR)].
  - apply fr_exI; intros fd2. apply fr_exI; intros tm3. apply fr_exI; intros nx3. apply fr_exI; intros pt3. apply fr_exI; intros off3. apply fr_exI; intros pos3.
    cbv zeta. apply fr_pure; intros RCW. apply fr_pure; intros HPI3. apply fr_pure; intros HT3. apply fr_pure; intros PA3.
    set (rc := mkrc (Some (out, fdo)) LB C2 nx2 fd2 (to_bytes data) (pt2 + n1 FILE_ALLOC)) in *.
    pose proof (pi_pos _ _ _ HPI3) as Hp3. cbn [rc_d rc mkrc] in Hp3. rewrite to_bytes_length in Hp3.
    eapply (pp_bind_nd rc).
    { apply (pr_packet_loop rc RCW out (EO out fdo) eq_refl eq_refl ltac:(left; reflexivity) eq_refl eq_refl eq_refl ltac:(right; left; reflexivity) (S (length data)) (S (length data)) nx3 p tm3 pt3 off3 pos3 HPI3 HT3);
        [cbn [rc_d rc mkrc]; rewrite to_bytes_length; lia| cbn [rc_d rc mkrc]; rewrite to_bytes_length; lia| exact PA3]. }
    intros p1 p1' tm4 nx4 pt4 off4 pos4 [E4 PA4] HPI4 HT4. subst p1.
    eapply (pp_bind_nd rc); [apply (pr_pcap_stats Uk rc true nx4 _ tm4 pt4 off4 pos4 HPI4 HT4 PA4)|].
    intros [sr p2] p2' tm5 nx5 pt5 off5 pos5 (E5 & PS5 & LE5 & PR5 & PA5) HPI5 HT5. cbn [fst snd] in E5, PA5. subst p2'. cbn beta iota.
    pose proof (PA_exit rc RCW _ _ _ _ PA5 HPI5) as PX5. cbn [rc_P0 rc mkrc] in PX5.
    eapply ru_bind.
    { apply nd_lift. destruct (sr =? 0); [apply (pr_out_fprintf rc RCW out (EO out fdo) eq_refl eq_refl ltac:(left; reflexivity) eq_refl eq_refl eq_refl ltac:(right; left; reflexivity)); apply small_number_of_packets|].
      xfr; apply ru_ret. intros ? ? ? ? ? HR. exact HR. }
    intros []. eapply ru_bind; [apply nd_lift; apply (pr_pcap_close Uk stkG stkC rc RCW nx5 p2 tm5 pt5 off5 pos5 HPI5 HT5)|].
    intros []. apply fr_exI; intros tm6. apply fr_pure; intros HT6.
    unfold RCL. cbn [rc_Kx rc_e0 rc_d rc_C rc_oh rc_hs rc_fp rc_F0 rc_B rc mkrc k_path] in HT6 |- *. rewrite hrem_hd. cbn [HSH]. rewrite (hrem_notin nx2 [out]) by (intros [E|[]]; pose proof (rw_oh _ RCW) as X; cbn in X; apply X; rewrite E; reflexivity).
    eapply ru_bind; [apply (us_unlink Uk tm6 nx5 pt5 _ _ _ _ _ TMPNAME (K_clear_KH (Some (out, fdo))))|].
    intros r1. apply usim_pure. intros _. xfr; apply ru_ret. intros gh sG moG sC moC HR. eexists tm6, nx5, pt5, (Some (out, fdo)), _. split; [split; [exact HT6| lia]| exact (proj1 HR)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Notation emit_dG := (@emit_d PSG hptr ps_libc set_libc).
#[local] Notation emit_dC := (@emit_d PSC hptr ps_libc set_libc).

#[using="STK"] Lemma pr_call_loop LB data : forall n tm nx pt ho C rc0,
  TML tm (LH ho LB) -> LBok LB -> zlength data < MAX_INPUT -> pt + Z.of_nat n * V_ONE <= VOLMAX ->
  usimS (RH tm nx pt ho C) (call_loop emit_dG (harness_call HOG FOG stkG) n data rc0) (call_loop emit_dC (harness_call HOC FOC stkC) n data rc0)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' ho' C', (TML tm' (LH ho' LB) /\ pt' <= pt + Z.of_nat n * V_ONE) /\ RH tm' nx' pt' ho' C' gh sG moG sC moC)).
Proof.
  assert (V1 : 0 <= V_ONE) by (unfold V_ONE, V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX, FILE_ALLOC; lia).
  induction n as [|n IH]; intros tm nx pt ho C rc0 HT HL HD HPOT; cbn [call_loop].
  - xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm, nx, pt, ho, C. split; [split; [exact HT| lia]| exact HR].
  - rewrite Nat2Z.inj_succ in HPOT |- *.
    assert (E1 : Z.succ (Z.of_nat n) * V_ONE = Z.of_nat n * V_ONE + V_ONE) by lia. rewrite E1 in HPOT |- *.
    pose proof (Z.mul_nonneg_nonneg (Z.of_nat n) V_ONE ltac:(lia) V1) as NN.
    unfold harness_call at 1 2. cbn [mo_bind mo_ret MOps e_fenter e_fret prims]; xfe.
    eapply (ru_bind _ _ _ _ (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' ho' C', (TML tm' (LH ho' LB) /\ pt' <= pt + V_ONE) /\ RH tm' nx' pt' ho' C' gh sG moG sC moC)).
    { eapply ru_bind; [apply (pr_fuzz_one tm nx pt ho C LB data HT HL HD ltac:(lia))|]. intros []. xfr; apply ru_ret. intros ? ? ? ? ? HR. exact HR. }
    intros rc. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros ho1. eapply usim_exI; intros C1. apply usim_pure; intros [HT1 HB1].
    unfold RH. eapply ru_bind; [apply us_emit_d|]. intros [].
    eapply ru_post; [apply (IH tm1 nx1 pt1 ho1 C1 _ HT1 HL HD ltac:(lia))|].
    intros ? ? ? ? ? ? (tm' & nx' & pt' & ho' & C' & [HT' HB'] & HR'). exists tm', nx', pt', ho', C'. split; [split; [exact HT'| lia]| exact HR'].
Qed.

#[using="Type"] Lemma EXT_of_TML tm tm' L L' : TML tm L -> TML tm' L' -> (forall x, In x L -> In x L') -> EXT tm tm'.
Proof.
  intros HT HT' HI k n Hk. apply (TML_lookup _ _ _ _ HT'). apply HI.
  apply elem_of_map_to_list in Hk. unfold TML in HT. rewrite HT in Hk. apply list_elem_of_In in Hk. exact Hk.
Qed.
#[using="Type"] Lemma exit_ok_KH ho : exit_ok (KH ho).
Proof. intros e h He Ho. destruct ho as [[o f]|]; [| destruct He]. destruct He as [<-|[]]. split; reflexivity. Qed.
#[using="Type"] Lemma In_LH x ho LB : In x LB -> In x (LH ho LB).
Proof. intros H. destruct ho as [[o f]|]; cbn [LH]; [right|]; exact H. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma calls_le4 c : 0 <= Z.of_nat (Z.to_nat (1 + Z.land c 3)) <= 4.
Proof.
  assert (H : 0 <= Z.land c 3 <= 3).
  { change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (Z.ones 2) with 3. pose proof (Z.mod_pos_bound c (2 ^ 2) ltac:(lia)). lia. }
  rewrite Z2Nat.id; lia.
Qed.

(* [comment removed for export] *)
#[using="STK"] Theorem us_run tm nx pt config payload :
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> live1 tm <= MAX_INPUT -> zlength payload < MAX_INPUT -> pot_ok (pt + RUNV) ->
  usimS (RUK tm nx pt [] [] idl (WF None [] [])) (Prog.run HOG FOG stkG config payload) (Prog.run HOC FOC stkC config payload)
        (eqpost (fun _ => fun gh sG moG sC moC => exists tm' nx' pt' K' C' oh' hs' F',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ exit_ok K' /\ pt' <= pt + RUNV /\
                   RUK tm' nx' pt' K' C' idl (WF oh' hs' F') gh sG moG sC moC)).
Proof.
  intros HL1 HL2 HLV HD HPOT. set (LB := map_to_list tm).
  assert (HT : TML tm LB) by (unfold TML; reflexivity).
  assert (EL : zlen LB = zlen (sizes tm)) by (unfold sizes, zlen; rewrite length_map; reflexivity).
  assert (ER : R63N (map snd LB) = R63N (sizes tm)) by reflexivity.
  assert (ELV : liveL LB = live1 tm) by reflexivity.
  assert (B26p : 0 <= B26) by (unfold B26, PGSZ; lia).
  assert (HLB : LBok LB) by (split; [lia| split; [unfold BASEB; lia| unfold MAX_INPUT in HLV; lia]]).
  pose proof (zlength_nonneg payload) as NP.
  assert (V1 : 0 <= V_ONE) by (unfold V_ONE, V_READ, VC0, MAX_INPUT, IFSMAX, BUFMAX, FILE_ALLOC; lia).
  unfold pot_ok, RUNV in HPOT.
  (* [comment removed for export] *)
  assert (FIN : forall tm' nx' pt' ho' C' (z : Z), TML tm' (LH ho' LB) -> pt' <= pt + RUNV ->
            usimS (RH tm' nx' pt' ho' C') (mret z) (mret z)
                  (eqpost (fun _ => fun gh sG moG sC moC => exists tm'' nx'' pt'' K' C'' oh' hs' F',
                     EXT tm tm'' /\ PHI P9 + R63N (sizes tm'') <= BLIVE /\ exit_ok K' /\ pt'' <= pt + RUNV /\ RUK tm'' nx'' pt'' K' C'' idl (WF oh' hs' F') gh sG moG sC moC))).
  { intros tm' nx' pt' ho' C' z HT' HB'. xfr; apply ru_ret. intros gh sG moG sC moC HR. exists tm', nx', pt', (KH ho'), C', (OH ho'), (HSH ho'), (FH ho').
    split; [exact (EXT_of_TML _ _ _ _ HT HT' (fun x Hx => In_LH x ho' LB Hx))|].
    split; [destruct (LH_budget tm' ho' LB 0 HT' HLB ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & X & _); pose proof (bigb_nonneg 0); lia|].
    split; [apply exit_ok_KH| exact (conj HB' HR)]. }
  unfold Prog.run, target_run. cbv zeta. change (RUK tm nx pt [] [] idl (WF None [] [])) with (RH tm nx pt None []).
  match goal with |- context [call_loop _ _ (Z.to_nat ?cz) _ _] => pose proof (calls_le4 (match config with [] => 0 | b :: _ => b end)) as CL; set (calls := Z.to_nat cz) in * end.
  assert (CB : 0 <= Z.of_nat calls * V_ONE <= 4 * V_ONE) by nia.
  destruct (length payload =? 0)%nat eqn:EP.
  - xfr; apply ru_bind_retl. eapply ru_bind; [apply (pr_call_loop LB payload calls tm nx pt None [] false HT HLB HD ltac:(lia))|].
    intros rc. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros ho1. eapply usim_exI; intros C1. apply usim_pure; intros [HT1 HB1].
    xfr; apply ru_bind_retl. apply (FIN _ _ _ _ _ _ HT1). unfold RUNV. lia.
  - apply Nat.eqb_neq in EP.
    unfold RH. apply ru_use. intros gh0 sG0 moG0 sC0 moC0 HR0. pose proof (TML_fresh Uk _ _ _ _ _ _ _ _ _ _ _ _ HT HR0) as FR.
    pose proof (RQ_pot _ _ _ _ _ _ _ _ (proj1 HR0)) as PP0. unfold pot_ok in PP0. clear HR0.
    pose proof (bigb_le (zlength payload) NP) as BP.
    assert (NQ : n1 (zlength payload) <= MAX_INPUT) by (unfold n1, MAX_INPUT in *; lia).
    eapply (ru_bind _ _ _ _ (fun owned => fun gh sG moG sC moC => (owned = Some (Some nx) /\ TML (<[nx:=zlength payload]> tm) ((nx, zlength payload) :: LB)) /\
                                    RUK (<[nx := zlength payload]> tm) (N.succ nx) (pt + n1 (zlength payload)) [] [] idl (WF None [] []) gh sG moG sC moC)).
    { eapply ru_bind.
      { eapply (gr_malloc Uk tm LB nx pt [] [] _ (zlength payload) HT); [lia| unfold MAX_INPUT in HD; lia| unfold QMAX, MAX_INPUT, PGSZ in *; lia| | lia| unfold MAX_INPUT in *; lia| unfold NMAXA, MAX_INPUT in *; lia| unfold LIVEMAX, MAX_INPUT in *; lia].
        rewrite ER, PHI_P9. unfold B26, MAX_INPUT, BLIVE, PGSZ in *. lia. }
      intros q. apply usim_pure. intros [-> HT1]. xfr; apply ru_ret. intros gh sG moG sC moC HR. split; [split; [reflexivity| exact HT1]| exact HR]. }
    intros owned. apply usim_pure. intros [-> HT1].
    assert (HLB1 : LBok ((nx, zlength payload) :: LB)).
    { split; [rewrite zlen_cons; lia|]. split; [cbn [map snd]; rewrite R63N_cons; unfold BASEB, B26, MAX_INPUT in *; lia|]. rewrite liveL_cons. unfold MAX_INPUT in *. lia. }
    change (RUK (<[nx:=zlength payload]> tm) (N.succ nx) (pt + n1 (zlength payload)) [] [] idl (WF None [] [])) with (RH (<[nx:=zlength payload]> tm) (N.succ nx) (pt + n1 (zlength payload)) None []).
    eapply ru_bind; [apply (pr_call_loop _ payload calls _ (N.succ nx) (pt + n1 (zlength payload)) None [] false HT1 HLB1 HD ltac:(lia))|].
    intros rc. eapply usim_exI; intros tm1. eapply usim_exI; intros nx1. eapply usim_exI; intros pt1. eapply usim_exI; intros ho1. eapply usim_exI; intros C1. apply usim_pure; intros [HT2 HB2].
    unfold RH. pose proof (TML_nodup _ _ HT2) as ND2.
    eapply ru_bind.
    { eapply (gr_free Uk _ _ nx1 _ _ _ _ nx (zlength payload) HT2); [apply In_LH; left; reflexivity|].
      destruct (LH_budget tm1 ho1 _ 0 HT2 HLB1 ltac:(unfold MMAP_THRESHOLD; lia)) as (_ & _ & X). exact X. }
    intros []. apply usim_pure. intros HT3.
    assert (HT4 : TML (delete nx tm1) (LH ho1 LB)).
    { destruct ho1 as [[o f]|]; cbn [LH lrm] in HT3 |- *.
      - cbn [LH map fst] in ND2. inversion ND2 as [|? ? NI _]; subst.
        destruct (N.eqb_spec o nx) as [E|NE]; [exfalso; apply NI; left; symmetry; exact E|]. rewrite N.eqb_refl in HT3. exact HT3.
      - rewrite N.eqb_refl in HT3. exact HT3. }
    change (RUK (delete nx tm1) nx1 pt1 (KH ho1) C1 idl (WF (OH ho1) (HSH ho1) (FH ho1))) with (RH (delete nx tm1) nx1 pt1 ho1 C1).
    apply (FIN _ _ _ _ _ _ HT4). unfold RUNV. lia.
Qed.

End Harness.

End WithCeil.
