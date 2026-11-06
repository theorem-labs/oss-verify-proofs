(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KPB2Lit KW1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1b2_S_ (_ : unit) : acs := kcompact kpb2_hs101.
Abbreviation kw1b2_S := (kw1b2_S_ tt).
Definition kw1b2_pl_ (_ : unit) : plan := (kw1a_plan (kn0 kw1b2_S) (kvp kw1b2_S) (kvb kw1b2_S) (kvl kw1b2_S) kw1b2_S PNext).
Abbreviation kw1b2_pl := (kw1b2_pl_ tt).
