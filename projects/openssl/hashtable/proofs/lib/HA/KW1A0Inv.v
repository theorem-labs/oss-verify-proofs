(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KPA0Lit KW1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1a0_S_ (_ : unit) : acs := kcompact kpa0_hs101.
Abbreviation kw1a0_S := (kw1a0_S_ tt).
Definition kw1a0_pl_ (_ : unit) : plan := (kw1a_plan (kn0 kw1a0_S) (kvp kw1a0_S) (kvb kw1a0_S) (kvl kw1a0_S) kw1a0_S PNext).
Abbreviation kw1a0_pl := (kw1a0_pl_ tt).
