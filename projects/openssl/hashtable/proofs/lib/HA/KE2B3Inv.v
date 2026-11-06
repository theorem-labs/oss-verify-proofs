(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW1B3Lit KE2b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke2b3_S_ (_ : unit) : acs := kcompact kw1b3_hs102.
Abbreviation ke2b3_S := (ke2b3_S_ tt).
Definition ke2b3_pl_ (_ : unit) : plan := (ke2b_plan (kn0 ke2b3_S) (kvp ke2b3_S) (kvb ke2b3_S) (kvl ke2b3_S) ke2b3_S PNext).
Abbreviation ke2b3_pl := (ke2b3_pl_ tt).
