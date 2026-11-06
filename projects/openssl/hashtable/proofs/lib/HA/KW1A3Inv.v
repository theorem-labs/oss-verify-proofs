(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KPA3Lit KW1b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1a3_S_ (_ : unit) : acs := kcompact kpa3_hs101.
Abbreviation kw1a3_S := (kw1a3_S_ tt).
Definition kw1a3_pl_ (_ : unit) : plan := (kw1b_plan (kn0 kw1a3_S) (kvp kw1a3_S) (kvb kw1a3_S) (kvl kw1a3_S) kw1a3_S PNext).
Abbreviation kw1a3_pl := (kw1a3_pl_ tt).
