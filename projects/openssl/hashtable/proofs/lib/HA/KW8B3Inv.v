(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW7B3Lit KW8b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw8b3_S_ (_ : unit) : acs := kcompact kw7b3_hs108.
Abbreviation kw8b3_S := (kw8b3_S_ tt).
(* [comment removed for export] *)
Definition kw8b3_inv_ (_ : unit) : acs :=
  kinv kw8b3_S (kn0 kw8b3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 50) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (ELit 8388608)))
    [(KRange (EVar 50) 16777216 67108864)]
    [65]%nat.
Abbreviation kw8b3_inv := (kw8b3_inv_ tt).
Definition kw8b3_pl_ (_ : unit) : plan := (kw8b_plan (kn0 kw8b3_S) (kvp kw8b3_S) (kvb kw8b3_S) (kvl kw8b3_S) kw8b3_inv PNext).
Abbreviation kw8b3_pl := (kw8b3_pl_ tt).
