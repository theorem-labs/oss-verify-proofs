(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW1B1Lit KW2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw2b1_S_ (_ : unit) : acs := kcompact kw1b1_hs102.
Abbreviation kw2b1_S := (kw2b1_S_ tt).
Definition kw2b1_pl_ (_ : unit) : plan := (kw2a_plan (kn0 kw2b1_S) (kvp kw2b1_S) (kvb kw2b1_S) (kvl kw2b1_S) kw2b1_S PNext).
Abbreviation kw2b1_pl := (kw2b1_pl_ tt).
