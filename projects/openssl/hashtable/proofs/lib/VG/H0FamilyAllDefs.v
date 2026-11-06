(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan H0Sel H0TgtGlue.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import D10BS0 D10GS0 D3BS0 D3GS0 D4BS0 D4GS0 D5BS0 D5GS0 D6BS0 D6GS0 D7BS0 D7GS0 D8BS0 D8GS0 D9BS0 D9GS0 K0AS0 K0BS0 R1BS0 R1GS0 R2BS0 R2GS0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import CAP.
Open Scope Z_scope.
Definition HASHF : kentry := KRange (esub (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (EMd Instr.M_MUL (ELit 1099511628211) (EAlu Instr.ALU_XOR (ELit 14695981039346656037) (EExt false 0 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (EExt false 1 1 (EAlu Instr.ALU_ADD (EBlob false 3 1 1) (EMd Instr.M_MUL (ELit 256) (EBlob false 3 2 1)))))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (ELit 0))) (EVar 11)) 0 0.
(* [comment removed for export] *)
Definition CSL (k : Z) : list acs :=
  if k =? 0 then [K0A_cs; K0B_cs] else if k =? 1 then [R1G_cs; R1B_cs] else if k =? 2 then [R2G_cs; R2B_cs] else if k =? 3 then [D3G_cs; D3B_cs] else if k =? 4 then [D4G_cs; D4B_cs] else if k =? 5 then [D5G_cs; D5B_cs] else if k =? 6 then [D6G_cs; D6B_cs] else if k =? 7 then [D7G_cs; D7B_cs] else if k =? 8 then [D8G_cs; D8B_cs] else if k =? 9 then [D9G_cs; D9B_cs] else if k =? 10 then [D10G_cs; D10B_cs] else [].
Definition EOKc (k : Z) (content : list byte) (CS : acs) (E : env) : Prop :=
  tin_ok k (tin_of content)
  /\ (k = 0 -> CS = K0A_cs -> eokx 56 55 57 58 HASHF (tin_of content) E)
  /\ (k = 0 -> CS = K0B_cs -> eokx 57 56 58 59 HASHF (tin_of content) E)
  /\ (k = 1 -> CS = R1G_cs -> eokx 57 56 58 59 HASHF (tin_of content) E)
  /\ (k = 1 -> CS = R1B_cs -> eokx 58 57 59 60 HASHF (tin_of content) E)
  /\ (k = 2 -> CS = R2G_cs -> eokx 57 56 58 59 HASHF (tin_of content) E)
  /\ (k = 2 -> CS = R2B_cs -> eokx 58 57 59 60 HASHF (tin_of content) E)
  /\ (k = 3 -> CS = D3G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 3 -> CS = D3B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 4 -> CS = D4G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 4 -> CS = D4B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 5 -> CS = D5G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 5 -> CS = D5B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 6 -> CS = D6G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 6 -> CS = D6B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 7 -> CS = D7G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 7 -> CS = D7B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 8 -> CS = D8G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 8 -> CS = D8B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 9 -> CS = D9G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 9 -> CS = D9B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
  /\ (k = 10 -> CS = D10G_cs -> eokx 59 58 60 61 HASHF (tin_of content) E)
  /\ (k = 10 -> CS = D10B_cs -> eokx 60 59 61 62 HASHF (tin_of content) E)
.
