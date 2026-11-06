(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VState2 VCert2 VCertDecode VCertDecode2 VCertS_both_p00 VCertS_both_p01 VCertS_both_p02 VCertS_both_p03 VCertS_both_p04 VCertS_both_p05 VCertS_both_p06.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition chunks_both_t (u : unit) : list (list vunit2) := let T := decode_dict2 cert_both_dict in [decode_cert2_d T cert_both_s01; decode_cert2_d T cert_both_s02; decode_cert2_d T cert_both_s03; decode_cert2_d T cert_both_s04; decode_cert2_d T cert_both_s05; decode_cert2_d T cert_both_s06]%list.
