(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import FContractAsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VState2 VCert2 VCertDecode2
     VItab VItab_asan VDriver2 VDriver2L FPA_asan VGenv_asan VSoundAll2 VContractATab_asan VTopAsan VTopAsan_asan VCertT_asan VCertCheck_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Theorem fc_asan : F_contract_asan SEGSA FPA_asan.
Proof.
  pose proof cert_asan_ok as H. cbv zeta in H. rewrite check_chunks2b_l_eq in H. apply andb_prop in H as [HC HR].
  apply (F_contract_asan_of_chunksb [chunks_asan_t tt]).
  - exact ctab_ok2_asan.
  - apply Forall_cons; [exact HC|]. apply Forall_nil.
  - cbn [map concat]. rewrite app_nil_r. exact HR.
Qed.
