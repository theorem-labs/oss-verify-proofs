(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VCert_ub VDriver VGenv_ub FContract VTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cert_ub_ok : check_cert (genv_ub true) cert_ub = ROk.
Proof.
  vm_cast_no_check (@eq_refl res ROk).
Qed.

Lemma roots_ub_ok : roots_ok FP_ub cert_ub = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
