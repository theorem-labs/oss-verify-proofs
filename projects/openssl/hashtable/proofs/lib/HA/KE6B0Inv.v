(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW5B0Lit KE6a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke6b0_S_ (_ : unit) : acs := kcompact kw5b0_hs106.
Abbreviation ke6b0_S := (ke6b0_S_ tt).
(* [comment removed for export] *)
Definition ke6b0_inv_ (_ : unit) : acs :=
  kinv ke6b0_S (kn0 ke6b0_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (ELit 2097152)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) 2097152 4194303);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EAlu ALU_ADD (EVar 65) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 4194297);
     (KRange (EVar 65) 0 65535);
     (KRange (EVar 64) 32 63);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) 2097152 4194303);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [65; 92; 130; 165; 200; 235; 451; 452]%nat.
Abbreviation ke6b0_inv := (ke6b0_inv_ tt).
Definition ke6b0_pl_ (_ : unit) : plan := (ke6a_plan (kn0 ke6b0_S) (kvp ke6b0_S) (kvb ke6b0_S) (kvl ke6b0_S) ke6b0_inv PNext).
Abbreviation ke6b0_pl := (ke6b0_pl_ tt).
