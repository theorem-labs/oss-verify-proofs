(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan MainItabBoth ArgFragsBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition main_toolong : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr_long_both))))).
Definition main_noent : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] frag_operr_both))).
Definition main_noent0 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr0_both))))).
(* [comment removed for export] *)
Definition main_noent_1_62 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr_1_62_both))))).
Definition main_noent_63_63 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr_63_63_both))))).
Definition main_noent_64_64 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr_64_64_both))))).
Definition main_noent_65_4095 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_B (PExt 10 [] (PKeepOnly KEEP_operr_bs_both KEEP_operr_rs_both (frag_operr_65_4095_both))))).
