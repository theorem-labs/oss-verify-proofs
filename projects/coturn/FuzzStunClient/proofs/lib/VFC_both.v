(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VState2 VCert2 VCertDecode2
     VItab VItab_both VDriver2 VDriver2L FPA_both VGenv_both VSoundAll2 VContractATab_both VTopAsan VTopAsan_both VCertT_both VCertCheck_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Theorem fc_both : F_contract_asan SEGSB FPA_both.
Proof.
  pose proof cert_both_ok as H. cbv zeta in H. rewrite check_chunks2b_l_eq in H. apply andb_prop in H as [HC HR].
  apply (F_contract_asan_of_chunksb [chunks_both_t tt]).
  - exact ctab_ok2_both.
  - apply Forall_cons; [exact HC|]. apply Forall_nil.
  - cbn [map concat]. rewrite app_nil_r. exact HR.
Qed.
