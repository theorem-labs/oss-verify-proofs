(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW2A3Lit KW3b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw3a3_S_ (_ : unit) : acs := kcompact kw2a3_hs103.
Abbreviation kw3a3_S := (kw3a3_S_ tt).
(* [comment removed for export] *)
Definition kw3a3_inv_ (_ : unit) : acs :=
  kinv kw3a3_S (kn0 kw3a3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 50) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (ELit 262144)))
    [(KRange (EVar 50) 524288 67108864)]
    [49]%nat.
Abbreviation kw3a3_inv := (kw3a3_inv_ tt).
Definition kw3a3_pl_ (_ : unit) : plan := (kw3b_plan (kn0 kw3a3_S) (kvp kw3a3_S) (kvb kw3a3_S) (kvl kw3a3_S) kw3a3_inv PNext).
Abbreviation kw3a3_pl := (kw3a3_pl_ tt).
