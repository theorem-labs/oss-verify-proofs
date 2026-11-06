(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW6B2Lit KE7a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke7b2_S_ (_ : unit) : acs := kcompact kw6b2_hs107.
Abbreviation ke7b2_S := (ke7b2_S_ tt).
(* [comment removed for export] *)
Definition ke7b2_inv_ (_ : unit) : acs :=
  kinv ke7b2_S (kn0 ke7b2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (ELit 4194304)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) 4194304 8388607);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EAlu ALU_ADD (EVar 66) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 8388601);
     (KRange (EVar 66) 0 65535);
     (KRange (EVar 65) 64 127);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) 4194304 8388607);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [65; 92; 130; 168; 203; 238; 273; 490; 491]%nat.
Abbreviation ke7b2_inv := (ke7b2_inv_ tt).
Definition ke7b2_pl_ (_ : unit) : plan := (ke7a_plan (kn0 ke7b2_S) (kvp ke7b2_S) (kvb ke7b2_S) (kvl ke7b2_S) ke7b2_inv PNext).
Abbreviation ke7b2_pl := (ke7b2_pl_ tt).
