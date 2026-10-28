(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_state RT_rep RT_facts RT_artfacts RT_icfacts. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_consts I_qck R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_isPoisoned I_lift3 RT_iclifts I_liftmv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Theorem rta_memmove2 : memmove_icontract2 RTA.
Proof. exact (memmove2_lift RTA rta_art_facts rip_proof rta_ic rta_shw). Qed.

End GWIN.
