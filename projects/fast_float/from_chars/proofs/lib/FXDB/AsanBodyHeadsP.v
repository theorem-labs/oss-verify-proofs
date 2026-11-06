(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyCertDefs.

Module AsanBodyCertS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition certS_all : bool := (certS 1 && certS 2 && certS 3 && certS 4)%bool.
Lemma certS14 : certS_all = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
End AsanBodyCertS.

Module AsanBodyHeadsE.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition certHE_all : bool := (certHE 1 && certHE 2 && certHE 3 && certHE 4)%bool.
Lemma certHE14 : certHE_all = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
End AsanBodyHeadsE.

Module AsanBodyHeadsL.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanBodyCertDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition certHL_all : bool := (certHL 1 && certHL 2 && certHL 3 && certHL 4)%bool.
Lemma certHL14 : certHL_all = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
End AsanBodyHeadsL.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition certHP_all : bool := (certHP 1 && certHP 2 && certHP 3 && certHP 4)%bool.
Lemma certHP14 : certHP_all = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
(* [comment removed for export] *)
