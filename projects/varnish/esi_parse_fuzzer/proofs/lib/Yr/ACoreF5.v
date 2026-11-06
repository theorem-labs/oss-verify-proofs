(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ACoresk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ACoreF4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRI3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRI3 AFreptn.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2.ACoreF OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF4.ACoreF3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACoreF4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI3.AFreeRI2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreptn.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CoreF5.
Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Theorem restF1R_closed : restF1R_stmt.
  Proof. exact (restF1R_ok step_pdm_ok step_sec_ok step_bdm_ok). Qed.

  (* [comment removed for export] *)
  Theorem dealloc_core_restF_of_F2F0 : restF2_stmt -> restF0_stmt -> dealloc_core_restF.
  Proof. intros RF2 RF0. exact (dealloc_core_restF_of restF1R_closed RF2 RF0). Qed.

  Theorem dealloc_core_of_F2F0 : restF2_stmt -> restF0_stmt -> dealloc_core_cps.
  Proof.
    intros RF2 RF0.
    exact (dealloc_core_of_restF step_pdm_ok step_sec_ok step_bdm_ok (dealloc_core_restF_of_F2F0 RF2 RF0)).
  Qed.
End CoreF5.
