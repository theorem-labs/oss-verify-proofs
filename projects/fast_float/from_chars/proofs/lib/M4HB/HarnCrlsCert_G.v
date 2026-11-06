(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnChain HarnSubCh HarnCertLib HPT_G.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnSubCh OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnCertLib OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HPT_G OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HPFH_G OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HPFS_G OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTP.HPF26_G.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition CRLS_FINS_G : list (sst * smodel * ast) :=
  [(HPFH_G_S, HPFH_G_M, HPFH_G_A); (HPFS_G_S, HPFS_G_M, HPFS_G_A); (HPF26_G_S, HPF26_G_M, HPF26_G_A)].
Definition NCACHE_G : nat := Eval vm_compute in ncache_of HPT_G_S HPT_G_M HPT_G_A.
Definition CRLS_CH_G : MCH :=
  CRLS_SUB6K NCACHE_G (genK HPF26_G_S HPF26_G_M (alins_a HPF26_G_A)) (genK HPFS_G_S HPFS_G_M (alins_a HPFS_G_A)) (genK HPFH_G_S HPFH_G_M (alins_a HPFH_G_A)).
Definition crls_res_G : option (list (sst * smodel * ast)) := PCHK [] CRLS_CH_G HPT_G_S HPT_G_M HPT_G_A.
Lemma crls_cert_G : PCHK [] CRLS_CH_G HPT_G_S HPT_G_M HPT_G_A = Some CRLS_FINS_G.      (* [comment removed for export] *)
Proof. vm_cast_no_check (eq_refl (Some CRLS_FINS_G)). Qed.
(* [comment removed for export] *)
