(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW9B3Lit KE10b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke10b3_S_ (_ : unit) : acs := kcompact kw9b3_hs110.
Abbreviation ke10b3_S := (ke10b3_S_ tt).
(* [comment removed for export] *)
Definition ke10b3_inv_ (_ : unit) : acs :=
  kinv ke10b3_S (kn0 ke10b3_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 70)) (ELit 33554432)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) 33554432 67108863);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EAlu ALU_ADD (EVar 69) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 67108857);
     (KRange (EVar 69) 0 65535);
     (KRange (EVar 68) 512 1023);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) 33554432 67108863);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [65; 92; 130; 168; 206; 244; 282; 317; 352; 387; 598; 599]%nat.
Abbreviation ke10b3_inv := (ke10b3_inv_ tt).
Definition ke10b3_pl_ (_ : unit) : plan := (ke10b_plan (kn0 ke10b3_S) (kvp ke10b3_S) (kvb ke10b3_S) (kvl ke10b3_S) ke10b3_inv PNext).
Abbreviation ke10b3_pl := (ke10b3_pl_ tt).
