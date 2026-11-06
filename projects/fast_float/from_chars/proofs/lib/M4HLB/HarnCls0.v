(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HLB Require Import HarnLoop HarnSite HarnFk HarnChain HarnCR2 HarnSub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition Y0 (S : sst) : lin := HINTof S 0.
Definition CARVE0 (k : MCH) : MCH := SURG (SSplit (fk_carve_fl 0 Y0)) (SURG (SSplit (fk_carve_ar 0 Y0)) (SURG (SSplit (fk_carve_sh 0 Y0)) k)).
Definition PROMZ0 (k : MCH) : MCH := NODE (HPROMZ (fun S => idx_at S (oshadow (rgk S 10)))) k.
Definition PC_SM0_CALL : Z := 0x90784.
Definition PC_SM0_RET : Z := 0x90788.
Definition PC_RETIRE0 : Z := 0x90a54.
(* [comment removed for export] *)
Definition SM0 (P : plan) (k : MCH) : MCH :=
  TRY (HIXF (fun S => Some (Y0 S))) (CARVE0 (MJoinG genF0 (MSegK 20 P (KCons PC_SM0_RET 0 MEnd KNil)) PC_SM0_RET (PROMZ0 k))).
(* [comment removed for export] *)
Definition EXIT0 (k : MCH) : MCH :=
  SURG (SSteps (fk_drop (fun S => rgk S 12))) (SURG (SMerge (fk_mrg3 (fun S => rgk S 12)))
  (SURG (SSteps (fk_drop (fun S => rgk S 11))) (NODE (HIXF (fun S => Some (rgk S 11))) (SURG (SMerge (fk_mrg3 (fun S => rgk S 11)))
  (TRY (HUNZ (fk_unz (fun S => rgk S 10))) (TRY (HPROMZ (fk_unz (fun S => rgk S 10))) (NODE (HIXF (fun S => Some (rgk S 10)))
  (SURG (SMerge (fk_mrg3 (fun S => rgk S 10))) k)))))))).
