(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import FContract VTop VTop_src0 VCtabOk_src0 VCert_src0 VCertCheck_src0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition fc_src0 : F_contract Plain.M.loaded_segments FP_src0 :=
  F_contract_src0_of cert_src0 ctab_ok_src0 cert_src0_ok roots_src0_ok.
