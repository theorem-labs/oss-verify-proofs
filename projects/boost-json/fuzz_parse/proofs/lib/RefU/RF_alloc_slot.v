(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocTree MallocFacts_A MallocHINV Malloc_fp MallocFacts_AS ASlot_I ASlot_M0 MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMalloc_fp RAllocSlot_iface RASlot_I RF_am_P RF_alloc_meta RASlot_M6.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RBand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require MallocFacts_inv4.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z02le37Corelib4Init5Logichc3and37Corelib7Numbers7BinNumsj61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~l3cref_reserved02lt37Corelib4Init9Datatypesq84listj61N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~sbbAREACH_fromsb5block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_A~~~~~~hi68MFACTS_g79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8RASlot_I~~~~~~hn88ras_pre279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hs44FUELhs46mstatehs46s_tickhs48set_tickhs4asize_class46Stdlib6NArith6BinNat1Nij82lt03add03mul03pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7ASlot_I~~~~~~im57as_inv279OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh0RAllocSlot_iface~~~~~~ir0h0ralloc_slot_stmt" s.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma ras_pre2_intro : ltac2:(zQ "h40!h8!j0!kf!p5!q4!s0!s7!hh0!hhe!hmc!hr8!ig2!iga!ih4!ihe!iia!il0!il6!ilb!im0>2st$c>2LB@1$5$8>1t$6>2sc$2>1n$2>0@4$7?4HSEC@1$3?5HCEIL^5^4>0@3$9@1$3?5HCEIL^6^5>0@2$h0@1$d^7^5>0@2$1@2$0Z^5@2$4^5+j0>0@2$1@2$0Z^5@2$4^5@2$h3+2+i0>0@2$0@2$h1^6+4@2$h2+h0@1$f^7@7$a?5HCEIL?4HSEC^b@2$e^9^b^8^7$b").
Proof. try hcb. try hsb.
  intros st LB t sc n AR MF TT SC N FIT. split; [| split; [| split; [| repeat split; lia]]].
  - exists LB. split; [exact AR| apply ist_top; exact TT].
  - apply ER_refl_tick.
  - apply ALLC_tick; [| exact TT]. exact (mf_cell_ticks _ _ MF).
Qed.

Theorem ralloc_slot_spec : ltac2:(zQ "30!iq5!hr8!iv9@4$2?5HCEIL?4HSEC@2$1?5HCEIL?4HSEC$0").
Proof. try hcb. try hsb.
  unfold ralloc_slot_stmt. intros fuel.
  exact (ralloc_slot_ok ram_pre ralloc_meta_spec MallocFacts_inv4.ist_ampre_proof fuel).
Qed.

End HCW.

