(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW4A0Lit KW5a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw5a0_S_ (_ : unit) : acs := kcompact kw4a0_hs105.
Abbreviation kw5a0_S := (kw5a0_S_ tt).
(* [comment removed for export] *)
Definition kw5a0_inv_ (_ : unit) : acs :=
  kinv kw5a0_S (kn0 kw5a0_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 50) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (ELit 1048576)))
    [(KRange (EVar 50) 2097152 67108864)]
    [58]%nat.
Abbreviation kw5a0_inv := (kw5a0_inv_ tt).
Definition kw5a0_pl_ (_ : unit) : plan := (kw5a_plan (kn0 kw5a0_S) (kvp kw5a0_S) (kvb kw5a0_S) (kvl kw5a0_S) kw5a0_inv PNext).
Abbreviation kw5a0_pl := (kw5a0_pl_ tt).
