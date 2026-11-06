(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocBlocks MallocHINV MallocFacts_inv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RBand MallocMF_klink MallocMF_model MallocMF.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require RMalloc_iface_stmt F_opnew RF_aligned_alloc_stmt RF_aligned_alloc.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach SReachTree SReachCjNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref8MallocMF~~~~~~0h1aligned16_sr_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~l3h7aligned_alloc16_mf_stmt03HMF" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem aligned16_sr : ltac2:(zQ "10!jf@2$0?5HCEIL?4HSEC").
Proof. apply aligned16_sr_mf. apply RF_aligned_alloc.raligned16_spec. Qed.

Theorem aligned_alloc16_mf : ltac2:(zQ "20!p5!r0@2$0?5HCEIL@2$1?5HCEIL?4HSEC").
Proof.
  unfold HeapMF_iface.aligned_alloc16_mf_stmt.
  cbn [HeapMF_iface.hs_SR HeapMF_iface.hs_KREL HeapMF_iface.hs_MPRES HeapMF_iface.hs_RHEAP HeapMF_iface.hs_rauxv_ok HeapMF_iface.hs_lb_remove HMF].
  intros until mo. intros HR KM AUX HB ST CLO LO ERR MI TP REPL A0 A1 N.
  eapply sreach_mono.
  - eapply (aligned16_sr ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB n lo B errv mo);
      eauto; try (unfold RF_aligned_alloc_stmt.RALIGNED_STACK, RMalloc_iface_stmt.RMALLOC_STACK in *; lia).
  - intros c HQ. exact HQ.
Qed.

End HCW.
