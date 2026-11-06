(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan MainItab ArgFragsAsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition main_toolong : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr_long_asan))))).
Definition main_noent : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] frag_operr_asan))).
Definition main_noent0 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr0_asan))))).
(* [comment removed for export] *)
Definition main_noent_1_62 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr_1_62_asan))))).
Definition main_noent_63_63 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr_63_63_asan))))).
Definition main_noent_64_64 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr_64_64_asan))))).
Definition main_noent_65_4095 : plan := PBump HO_NXT (PX XLayout [ELit 1] (PRun AL_STOPS_A (PExt 10 [] (PKeepOnly KEEP_operr_bs_asan KEEP_operr_rs_asan (frag_operr_65_4095_asan))))).
