(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KE4B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc4b3_S_ (_ : unit) : acs := kcompact ke4b3_hs204.
Abbreviation kc4b3_S := (kc4b3_S_ tt).
Definition kc4b3_pl_ (_ : unit) : plan := (PCompact (PHandoff 304)).
Abbreviation kc4b3_pl := (kc4b3_pl_ tt).
