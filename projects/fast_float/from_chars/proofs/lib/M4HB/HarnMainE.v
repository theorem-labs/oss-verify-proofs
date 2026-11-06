(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HarnKind HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnJoin HarnJoinN HarnJoinM HarnFcdT HarnDev HarnLong HarnSSO HarnLongL HarnCR HarnCR2 HarnSP HarnK23 HarnS HarnSub HarnCls0 HarnBudget HarnReent HarnEnt HarnPost HarnMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_EQ : list Z := STOPS_H ++ [0x606a4; 0x90528; 0x8fe58; 0x681c0; 0x683a0; 0x90784; 0x90788; 0x90a54].
(* [comment removed for export] *)
Definition P_EQ : plan := PRun F60000 STOPS_EQ [].
(* [comment removed for export] *)
Definition SEGQ (t : nat) (k : MCH) : MCH :=
  MSegK 20 P_EQ (KCons 0x90784 0 (SM0 P_EQ
    (MSegK 20 P_EQ (KCons 0x606a4 0 (OBJSH_T t (NODE HQSM (MSegK 20 P_EQ (KCons 0x90a54 0 (EXIT0 k) KNil)))) KNil))) KNil).
Definition REFRONT_E (k : MCH) : MCH := FRONT_AT (fun S => oshadow (FS2A S)) (FRONT_AT FS2A k).
Definition FIN_E : MCH := MSegK 20 P_EQ (KCons 0x90528 0 (REGROUP (EXIT7 (MSegK 20 P_EQ (KCons 0x8fe58 0 (UDONE (REFRONT_E MEnd)) KNil)))) KNil).
Definition HARN_E_CLASS : MCH := UDONE (MJoinG genF0 (ENTRY2 MEnd) 0x900e8 (SEGQ 0 (SEGQ 1 (SEGQ 2 FIN_E)))).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition HARN_PREP_E : MCH := SEPS0 (HINTS (FKPREP (UDONE (REFRONT_E MEnd)))).      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition HARN_E_ALL4 (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 (CLASSK HARN_E_CLASS HARN_E_CLASS) (CLASSK HARN_E_CLASS HARN_E_CLASS)) 0x8fe58 MEnd.
(* [comment removed for export] *)
Definition HARN_E_ALL2 (gen : list (sst * smodel) -> list (list lin) -> option (sst * smodel * list lin)) : MCH :=
  MJoinG gen (MSplitB (lvar 4) 0 0 HARN_E_CLASS HARN_E_CLASS) 0x8fe58 MEnd.
(* [comment removed for export] *)
Definition HARN_E_ALL := HARN_E_ALL2.      (* [comment removed for export] *)
(* [comment removed for export] *)
