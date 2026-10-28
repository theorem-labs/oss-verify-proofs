(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel BReach BazyRestrict BazyLedger BazySR BazyNodes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsDriverLaws BsSR BsChain BakeStackRep BllocWf BllocKit BllocRep BllocRepFacts BllocRepX BecLazy BsDepotInv BsDepotHash BG_Malloc2 BG_MallocLarge3 BG_MallocAll BS_InstDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BS_InstLaws2 LbB_Own LbB_RtOwn.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Own.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.

  Theorem inst_rt_own : rt_own (KHp p).
  Proof.
    intros x LB m R. unfold lb_own. apply Forall_forall. intros b Hb.
    pose proof (irheap_arheap p _ _ _ R) as (HA & ND & EQ).
    pose proof (lbp_In _ _ Hb) as INp. apply EQ in INp.
    destruct (alb_In _ _ _ INp) as (ch & Hch & ST & U0 & N0).
    pose proof HA as (_ & _ & _ & _ & _ & _ & _ & CH & _).
    pose proof (CH ch Hch) as (_ & _ & W & _). rewrite ST in W. destruct W as [W _].
    rewrite U0, N0 in W. exact W.
  Qed.
End Own.
