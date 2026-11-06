(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO KInv KW4B2Lit KE5a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke5b2_S_ (_ : unit) : acs := kcompact kw4b2_hs105.
Abbreviation ke5b2_S := (ke5b2_S_ tt).
(* [comment removed for export] *)
Definition ke5b2_inv_ (_ : unit) : acs :=
  kinv ke5b2_S (kn0 ke5b2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (EVar 64)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (ELit 1048576)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (EVar 64)) 1048576 2097151);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (EAlu ALU_ADD (EVar 64) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 2097145);
     (KRange (EVar 64) 0 65535);
     (KRange (EVar 63) 16 31);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (EVar 64)) 1048576 2097151);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [58; 85; 120; 155; 190; 412; 413]%nat.
Abbreviation ke5b2_inv := (ke5b2_inv_ tt).
Definition ke5b2_pl_ (_ : unit) : plan := (ke5a_plan (kn0 ke5b2_S) (kvp ke5b2_S) (kvb ke5b2_S) (kvl ke5b2_S) ke5b2_inv PNext).
Abbreviation ke5b2_pl := (ke5b2_pl_ tt).
