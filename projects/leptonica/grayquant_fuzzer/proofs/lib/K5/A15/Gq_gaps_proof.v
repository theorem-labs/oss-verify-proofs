(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.A15 Require Import ImageA RT_iface RT_rep RT_artfacts RT_gaps_iface Gq_numa Gq_gaps RT_stackmallocF RT_atof RT_strchr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rta_gq_gaps : gq_gaps RTA.
Proof. exact (mkGqGaps RTA rta_stack_malloc_1F (atof_ok RTA rta_art_facts) rta_strchr). Qed.
