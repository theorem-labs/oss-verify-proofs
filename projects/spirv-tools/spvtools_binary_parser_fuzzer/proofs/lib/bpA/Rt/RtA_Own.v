(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require AW_0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HImage HZBridge HSysStep HSFModel CellsX HArr TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll AS_InstDefs.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AS_InstLaws2 LbA_Own LbA_RtOwn.
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
