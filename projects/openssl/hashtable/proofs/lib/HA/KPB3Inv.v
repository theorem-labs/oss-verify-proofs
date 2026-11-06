(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv C3B3Lit C3B3LitK C4B3Lit C4e KPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kpb3_S_ (_ : unit) : acs := kcompact c3b3_hs98k.
Abbreviation kpb3_S := (kpb3_S_ tt).
Definition kpb3_pl_ (_ : unit) : plan := (PX XLayout [ELit 1] (kpb_plan 574 235 0 0)).
Abbreviation kpb3_pl := (kpb3_pl_ tt).
