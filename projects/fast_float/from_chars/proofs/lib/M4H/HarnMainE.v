(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HarnKind HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnJoin HarnJoinN HarnJoinM HarnFcdT HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23 HarnS HarnSub HarnBudget HarnReent HarnEnt HarnPost HarnMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition STOPS_EQ : list Z := STOPS_H ++ [0x606b0; 0x90444; 0x8fe64; 0x681cc; 0x683ac].
Definition P_EQ : plan := PRun F60000 STOPS_EQ [].
(* [comment removed for export] *)
Definition SEGQ (t : nat) (k : MCH) : MCH := MSegK 20 P_EQ (KCons 0x606b0 0 (OBJSH_T t (NODE HQSM k)) KNil).
Definition REFRONT_E (k : MCH) : MCH := FRONT_AT (fun S => oshadow (FS2A S)) (FRONT_AT FS2A k).
Definition FIN_E : MCH := MSegK 20 P_EQ (KCons 0x90444 0 (REGROUP (EXIT7 (MSegK 20 P_EQ (KCons 0x8fe64 0 (UDONE (REFRONT_E MEnd)) KNil)))) KNil).
Definition HARN_E_CLASS : MCH := UDONE (ENTRY2 (SEGQ 0 (SEGQ 1 (SEGQ 2 FIN_E)))).
(* [comment removed for export] *)
Definition HARN_PREP_E : MCH := SEPS0 (HINTS (FKPREP (UDONE (REFRONT_E MEnd)))).
(* [comment removed for export] *)
Definition HARN_E_ALL4 (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 (CLASSK HARN_E_CLASS HARN_E_CLASS) (CLASSK HARN_E_CLASS HARN_E_CLASS)) 0x8fe64 MEnd.
(* [comment removed for export] *)
Definition HARN_E_ALL2 (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 HARN_E_CLASS HARN_E_CLASS) 0x8fe64 MEnd.
(* [comment removed for export] *)
Definition HARN_E_ALL := HARN_E_ALL2.
