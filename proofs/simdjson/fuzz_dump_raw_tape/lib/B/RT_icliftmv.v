(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_state RT_rep RT_facts RT_artfacts RT_icfacts I_consts I_qck R_m2s R_isPoisoned I_lift3 RT_iclifts I_liftmv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Theorem rta_memmove2 : memmove_icontract2 RTA.
Proof. exact (memmove2_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.

End GWIN.
