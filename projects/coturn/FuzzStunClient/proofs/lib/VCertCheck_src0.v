(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VCert_src0 VDriver VGenv_src0 FContract VTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cert_src0_ok : check_cert (genv_src0 true) cert_src0 = ROk.
Proof.
  vm_cast_no_check (@eq_refl res ROk).
Qed.

Lemma roots_src0_ok : roots_ok FP_src0 cert_src0 = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
