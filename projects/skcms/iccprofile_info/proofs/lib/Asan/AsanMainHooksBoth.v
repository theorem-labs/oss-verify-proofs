(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require BoBase.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanNodesArg AsanNodesIO AsanNodesRP AsanNodesY AsanNodesSL AsanSpec AsanNodesPF.
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesXLib AsanNodesGen.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import KInvTable DepotNodeBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanMainLib AsanNodesXLib DepotNodeBoth.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Module XLNB.
Definition abi_of (A : atable) : AsFuzzContract.as_abi := BoBase.both_abi.
End XLNB.

Section Hooks.
  Variables (segs : list Segment) (A : atable) (nx0 : nat) (RP : RPN.rptab) (T : ION.iotab).
  Definition XNm (id : nat) (args : list expr) (cs : acs) : option acs :=
    if (id <? 10)%nat then AN.xn segs A nx0 id args cs
    else if (id <? 25)%nat then ION.xn segs T id args cs
    else if (id <? 40)%nat then YN.xn segs A id args cs                (* [comment removed for export] *)
    else if (id <? 100)%nat then ION.xn segs T id args cs
    else if (id =? 105)%nat then SLN.xn segs nx0 (SLN.sltab_of A) id args cs   (* [comment removed for export] *)
    else if (id =? 106)%nat then SLN.xn segs nx0 (SLN.sltab_of A) id args cs   (* [comment removed for export] *)
    else if (id <? 110)%nat then RPN.xn segs nx0 RP id args cs
    (* [comment removed for export] *)
    else if (id =? 112)%nat then XDP.xn nx0 args cs   (* [comment removed for export] *)
    else if ((id =? 120) || (id =? 121))%nat then GN.xn nx0 id args cs   (* [comment removed for export] *)
    else XLN.xn (XLNB.abi_of A) segs A nx0 id args cs.   (* [comment removed for export] *)
  Definition XEm (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := AN.xe segs A nx0 id args cs.
  Definition XBm (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := ION.xb segs nx0 T id args cs.
End Hooks.
