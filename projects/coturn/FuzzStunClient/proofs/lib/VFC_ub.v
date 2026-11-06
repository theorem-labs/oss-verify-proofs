(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract VTop VTop_ub VCtabOk_ub VCert_ub VCertCheck_ub.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fc_ub : F_contract Ubsan.M.loaded_segments FP_ub :=
  F_contract_ub_of cert_ub ctab_ok_ub cert_ub_ok roots_ub_ok.
