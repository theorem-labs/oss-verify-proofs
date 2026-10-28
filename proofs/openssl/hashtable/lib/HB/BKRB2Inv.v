(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW9B2Lit BKRa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition krb2_S_ (_ : unit) : acs := kcompact kw9b2_hs110.
Abbreviation krb2_S := (krb2_S_ tt).
(* [comment removed for export] *)
Definition krb2_inv_ (_ : unit) : acs :=
  kinv krb2_S (kn0 krb2_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 59) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (ELit 33554432)))
    [(KRange (EVar 59) 67108864 67108864)]
    [69]%nat.
Abbreviation krb2_inv := (krb2_inv_ tt).
Definition krb2_pl_ (_ : unit) : plan := (kra_plan (kn0 krb2_S) (kvp krb2_S) (kvb krb2_S) (kvl krb2_S) krb2_inv PNext).
Abbreviation krb2_pl := (krb2_pl_ tt).
