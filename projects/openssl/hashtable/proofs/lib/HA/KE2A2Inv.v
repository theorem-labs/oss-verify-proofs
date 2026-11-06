(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW1A2Lit KE2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke2a2_S_ (_ : unit) : acs := kcompact kw1a2_hs102.
Abbreviation ke2a2_S := (ke2a2_S_ tt).
Definition ke2a2_pl_ (_ : unit) : plan := (ke2a_plan (kn0 ke2a2_S) (kvp ke2a2_S) (kvb ke2a2_S) (kvl ke2a2_S) ke2a2_S PNext).
Abbreviation ke2a2_pl := (ke2a2_pl_ tt).
