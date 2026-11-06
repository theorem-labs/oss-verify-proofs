(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks Zkt Zm2 RT_rep Zjb Zi7 Zkl
  Zbo I_qck R_m2s Zn9 Zbx Zko Zbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_memmove2 : memmove_icontract2 RTA.
Proof. exact (memmove2_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
