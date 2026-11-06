(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VState2 VCert2 VCertDecode2
     VItab VItab_both VDriver2 VDriver2L FPA_both VGenv_both VTopAsan VCertT_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma cert_both_ok : (let cs := chunks_both_t tt in check_chunks2b_l (genv_both true) nil cs && roots_ok2 FPA_both (concat cs)) = true.
Proof.
  vm_cast_no_check (@eq_refl bool true).
Qed.
