(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VCert VCertDecode VCertS_ub_p01 VCertS_ub_p02.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition cert_ub : vcert := (decode_cert cert_ub_s01 ++ decode_cert cert_ub_s02)%list.
