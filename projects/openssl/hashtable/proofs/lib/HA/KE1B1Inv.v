(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KPB1Lit KE1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1b1_S_ (_ : unit) : acs := kcompact kpb1_hs101.
Abbreviation ke1b1_S := (ke1b1_S_ tt).
Definition ke1b1_pl_ (_ : unit) : plan := (ke1a_plan (kn0 ke1b1_S) (kvp ke1b1_S) (kvb ke1b1_S) (kvl ke1b1_S) ke1b1_S PNext).
Abbreviation ke1b1_pl := (ke1b1_pl_ tt).
