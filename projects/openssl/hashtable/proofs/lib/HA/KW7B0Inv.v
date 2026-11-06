(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW6B0Lit KW7a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw7b0_S_ (_ : unit) : acs := kcompact kw6b0_hs107.
Abbreviation kw7b0_S := (kw7b0_S_ tt).
(* [comment removed for export] *)
Definition kw7b0_inv_ (_ : unit) : acs :=
  kinv kw7b0_S (kn0 kw7b0_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 50) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (ELit 4194304)))
    [(KRange (EVar 50) 8388608 67108864)]
    [65]%nat.
Abbreviation kw7b0_inv := (kw7b0_inv_ tt).
Definition kw7b0_pl_ (_ : unit) : plan := (kw7a_plan (kn0 kw7b0_S) (kvp kw7b0_S) (kvb kw7b0_S) (kvl kw7b0_S) kw7b0_inv PNext).
Abbreviation kw7b0_pl := (kw7b0_pl_ tt).
