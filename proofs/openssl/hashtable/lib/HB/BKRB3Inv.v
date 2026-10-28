(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW9B3Lit BKRb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition krb3_S_ (_ : unit) : acs := kcompact kw9b3_hs110.
Abbreviation krb3_S := (krb3_S_ tt).
(* [comment removed for export] *)
Definition krb3_inv_ (_ : unit) : acs :=
  kinv krb3_S (kn0 krb3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 59) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (ELit 33554432)))
    [(KRange (EVar 59) 67108864 67108864)]
    [69]%nat.
Abbreviation krb3_inv := (krb3_inv_ tt).
Definition krb3_pl_ (_ : unit) : plan := (krb_plan (kn0 krb3_S) (kvp krb3_S) (kvb krb3_S) (kvl krb3_S) krb3_inv PNext).
Abbreviation krb3_pl := (krb3_pl_ tt).
