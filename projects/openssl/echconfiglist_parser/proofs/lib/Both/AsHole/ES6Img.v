(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrGen.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Pcs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition IM : fimage := odflt [] (mk_fimage ASEGS).
Definition code : itrie finstr := odflt iempty (build_code ASEGS s6_pcs).

Lemma IM_eq : mk_fimage ASEGS = Some IM.
Proof. vm_cast_no_check (eq_refl (Some IM)). Qed.
Lemma code_eq : build_code ASEGS s6_pcs = Some code.
Proof. vm_cast_no_check (eq_refl (Some code)). Qed.
