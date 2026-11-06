(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s R_isPoisoned I_lift3 RT_iclifts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_asan_memmove : memmove_icontract RTA.
Proof. exact (asan_memmove_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.
