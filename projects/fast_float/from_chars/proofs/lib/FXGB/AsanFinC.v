(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXGB Require Import AsanTbl AsanEntry AsanPlan AsanStart.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition RESC : option (list (sst * smodel)) := startup_res (S0c 176 4080 5) TBLd IMGd.
Definition RESA : option (list (sst * smodel)) := startup_res (S0c 4096 4176 67) TBLd IMGd.
Definition RESB : option (list (sst * smodel)) := startup_res (S0c 4192 4256 68) TBLd IMGd.
Definition FINC : list (sst * smodel) := Eval vm_compute in list_of RESC.
Definition FINA : list (sst * smodel) := Eval vm_compute in list_of RESA.
Definition FINB : list (sst * smodel) := Eval vm_compute in list_of RESB.
(* [comment removed for export] *)
Lemma startup_ok_res : (some_nonempty RESC && some_nonempty RESA && some_nonempty RESB)%bool = true.
Proof. vm_cast_no_check (eq_refl true). Time Qed.
(* [comment removed for export] *)
Lemma finals_res_eq : list_of RESC ++ list_of RESA ++ list_of RESB = FINC ++ FINA ++ FINB.
Proof. vm_cast_no_check (eq_refl (FINC ++ FINA ++ FINB)). Time Qed.
(* [comment removed for export] *)
