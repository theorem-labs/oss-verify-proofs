(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX CutCertA CutHeapA CutAutoXA.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSOK.

Definition KOBJ : list kentry :=
  [KImg (1388760) (1392480);
   KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1427904) 4 (ELit 1);
   KZero (SA (ELit 0) 2147621501) (ELit 1);
   KZero (SA (ELit 0) 2147621539) (ELit 1);
   KZero (SA (ELit 0) 2147621545) (ELit 1);
   KZero (SA (ELit 0) 2147621546) (ELit 1);
   KImg (1363488) (1365344);
   KImg (146104) (148664);
   KWr (SA (EVar 10) (0)) (ELit (272));
   KRange (EVar 10) (7024640) (140737479966448);
   KAlign (EVar 10) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 10) (0)) (ELit (272));
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit 1);
   KZero (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit 1);
   KWord (SA (EVar 11) (0)) 8 (ELit (1365216));
   KRange (EVar 11) (7024640) (140737479966672);
   KAlign (EVar 11) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (0)) (ELit (8));
   KWr (SA (EVar 12) (0)) (ELit (16));
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar 12) (7024640) (140737479966704);
   KAlign (EVar 12) (8);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar 33) (0) (67108863);
   KRange (EVar 2) (140735332493568) (140737488355328);
   KAlign (EVar 2) (32);
   KWr (SA (EVar 2) (-10496)) (ELit (10496));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 11) (8)) (ELit (40))].
Definition PCONST : list kentry :=
  [KWord (SA (EVar 10) (0)) 8 (ELit (1363968));
   KWord (SA (EVar 10) (8)) 4 (ELit (1024));
   KWord (SA (EVar 10) (12)) 1 (ELit (0));
   KWord (SA (EVar 10) (13)) 1 (ELit (1));
   KWord (SA (EVar 10) (14)) 1 (ELit (0));
   KWord (SA (EVar 10) (15)) 1 (ELit (1));
   KWord (SA (EVar 10) (16)) 1 (ELit (0));
   KWord (SA (EVar 10) (17)) 1 (ELit (0));
   KWord (SA (EVar 10) (18)) 1 (ELit (0));
   KWord (SA (EVar 10) (24)) 1 (ELit (0));
   KWord (SA (EVar 10) (48)) 1 (ELit (0));
   KWord (SA (EVar 10) (72)) 1 (ELit (0));
   KWord (SA (EVar 10) (96)) 8 (ELit (1364920));
   KWord (SA (EVar 10) (213)) 1 (ELit (1));
   KWord (SA (EVar 10) (216)) 4 (ELit (0));
   KWord (SA (EVar 10) (128)) 8 (APC.eaddz (EVar 10) (96))].
Definition STRANGES : list kentry := [KRange (EVar 48) (0) (255);
   KRange (EVar 49) (0) (255);
   KRange (EVar 50) (0) (255);
   KRange (EVar 52) (0) (1)].
Definition WIN_KN : list kentry :=
  [KBlob (SA (EVar 36) (0)) (EVar 32) 1;
   KUnk (SA (EVar 36) (0)) (EVar 32);
   KRange (EVar 32) (0) (16384);
   KRange (EVar 36) (4096) (140737479966720);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 36) (0)) (EVar 32);
   KRange (EVar 34) (4096) (140737479950336);
   KAlign (EVar 34) (16);
   KZero (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35);
   KRange (EVar 35) (2048) (2048);
   KRange (APC.esub (EVar 36) (EVar 34)) (0) (16384);
   KRange (APC.esub (APC.eadd (APC.esub (EVar 36) (EVar 34)) (EVar 32)) (ELit (0))) (0) (16384);
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 36) (0)) (EVar 32);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar 36) (0)) (EVar 32);
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar 36) (0)) (EVar 32);
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6883756) (ELit 4)].
Definition SURV_N : list kentry :=
  [KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40))].
Definition SURV_S : list kentry :=
  [KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40))].
Definition SURV_L : list kentry :=
  [KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (ELit 0) 6877256) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (ELit 0) 7015072) (ELit (544));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (ELit 0) 6883756) (ELit (4));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (EVar 11) (8)) (ELit (40))].
Definition FRAMEKN : list kentry :=
  [KRange (EVar 65) (7024640) (140737479965696);
   KAlign (EVar 65) (64);
   KUnk (SA (EVar 65) (24)) (ELit (992));
   KWr (SA (EVar 65) (0)) (ELit (1024));
   KWord (SA (EVar 65) (1016)) 8 (EVar 60);
   KWr (SA (EVar 60) (0)) (ELit (1));
   KRange (EVar 60) (7024640) (140737479966719);
   KWr (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) (2147450880)) (ELit (128));
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 65) (0)) (ELit 1024);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar 60) (0)) (ELit 1);
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 65) (0)) (ELit (1024));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar 60) (0)) (ELit (1));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 60) (0)) (ELit (1));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar 36) (0)) (EVar 32);
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar 10) (0)) (ELit (272));
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar 12) (0)) (ELit (16));
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar 11) (0)) (ELit (8));
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar 11) (8)) (ELit (40));
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar 36) (0)) (EVar 32);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1))].
Definition SLOTKN : list kentry :=
  [KWord (SA (EVar 2) (-648)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 672));
   KWord (SA (EVar 2) (-640)) 8 (ELit 3);
   KWord (SA (EVar 2) (-632)) 8 (ELit 0);
   KWord (SA (EVar 2) (-624)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 608));
   KWord (SA (EVar 2) (-616)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 592));
   KWord (SA (EVar 2) (-608)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 576));
   KWord (SA (EVar 2) (-600)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 336));
   KWord (SA (EVar 2) (-592)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 528));
   KWord (SA (EVar 2) (-584)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 512));
   KWord (SA (EVar 2) (-576)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 320));
   KWord (SA (EVar 2) (-568)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 432));
   KWord (SA (EVar 2) (-560)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 12));
   KWord (SA (EVar 2) (-552)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 224));
   KWord (SA (EVar 2) (-544)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 208));
   KWord (SA (EVar 2) (-536)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 192));
   KWord (SA (EVar 2) (-528)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 176));
   KWord (SA (EVar 2) (-520)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 160));
   KWord (SA (EVar 2) (-512)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 144));
   KWord (SA (EVar 2) (-504)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 128));
   KWord (SA (EVar 2) (-496)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 112));
   KWord (SA (EVar 2) (-488)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 96));
   KWord (SA (EVar 2) (-480)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 80));
   KWord (SA (EVar 2) (-472)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 544));
   KWord (SA (EVar 2) (-464)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 304));
   KWord (SA (EVar 2) (-456)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 288));
   KWord (SA (EVar 2) (-448)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 256));
   KWord (SA (EVar 2) (-440)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 240));
   KWord (SA (EVar 2) (-432)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 480));
   KWord (SA (EVar 2) (-424)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 416));
   KWord (SA (EVar 2) (-416)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 368));
   KWord (SA (EVar 2) (-408)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 464));
   KWord (SA (EVar 2) (-400)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 400));
   KWord (SA (EVar 2) (-392)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 220));
   KWord (SA (EVar 2) (-384)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 209));
   KWord (SA (EVar 2) (-376)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 232));
   KWord (SA (EVar 2) (-368)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 240));
   KWord (SA (EVar 2) (-360)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 248));
   KWord (SA (EVar 2) (-352)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 210));
   KWord (SA (EVar 2) (-344)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 64));
   KWord (SA (EVar 2) (-336)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 48));
   KWord (SA (EVar 2) (-328)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 32));
   KWord (SA (EVar 2) (-320)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 225));
   KWord (SA (EVar 2) (-312)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 224));
   KWord (SA (EVar 2) (-304)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 184));
   KWord (SA (EVar 2) (-296)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 212));
   KWord (SA (EVar 2) (-288)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 13));
   KWord (SA (EVar 2) (-280)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 352));
   KWord (SA (EVar 2) (-272)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 272));
   KWord (SA (EVar 2) (-264)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 624));
   KWord (SA (EVar 2) (-256)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 176));
   KWord (SA (EVar 2) (-248)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 160));
   KWord (SA (EVar 2) (-240)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 496));
   KWord (SA (EVar 2) (-232)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 448));
   KWord (SA (EVar 2) (-224)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 560));
   KWord (SA (EVar 2) (-216)) 8 (EAlu Instr.ALU_ADD (EVar 65) (ELit 384));
   KWord (SA (EVar 2) (-208)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 144));
   KWord (SA (EVar 2) (-200)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 213));
   KWord (SA (EVar 2) (-192)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 128));
   KWord (SA (EVar 2) (-184)) 8 (EAlu Instr.ALU_ADD (EVar 10) (ELit 211));
   KWord (SA (EVar 2) (-176)) 8 (EVar 12);
   KWord (SA (EVar 2) (-168)) 8 (EVar 65);
   KWord (SA (EVar 2) (-160)) 8 (EAlu Instr.ALU_ADD (EAlu Instr.ALU_SRL (EAlu Instr.ALU_ADD (EVar 10) (ELit 211)) (ELit 3)) (ELit 2147450880));
   KWord (SA (EVar 2) (-152)) 8 (EVar 11);
   KWord (SA (EVar 2) (-144)) 8 (ELit 146132);
   KWord (SA (EVar 2) (-136)) 8 (EAlu Instr.ALU_ADD (EVar 32) (EVar 36));
   KWord (SA (EVar 2) (-120)) 8 (EVar 65);
   KWord (SA (EVar 2) (-104)) 8 (EVar 27);
   KWord (SA (EVar 2) (-96)) 8 (EVar 26);
   KWord (SA (EVar 2) (-88)) 8 (EVar 25);
   KWord (SA (EVar 2) (-80)) 8 (EVar 24);
   KWord (SA (EVar 2) (-72)) 8 (EVar 23);
   KWord (SA (EVar 2) (-64)) 8 (EVar 22);
   KWord (SA (EVar 2) (-56)) 8 (EVar 21);
   KWord (SA (EVar 2) (-48)) 8 (EVar 20);
   KWord (SA (EVar 2) (-40)) 8 (EVar 19);
   KWord (SA (EVar 2) (-32)) 8 (EVar 18);
   KWord (SA (EVar 2) (-24)) 8 (EVar 9);
   KWord (SA (EVar 2) (-16)) 8 (EVar 8);
   KWord (SA (EVar 2) (-8)) 8 (EVar 1);
   KUnk (SA (EVar 2) (-10496)) (ELit (9824));
   KWr (SA (EVar 2) (-10496)) (ELit (10496))].
Definition STATICS_UAR : list kentry := [KImg (1388760) (1392480);
   KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1427904) 4 (ELit 1)].
Definition STATICS_ISH : list kentry := [KImg (1388760) (1392480);
   KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 1427904) 4 (ELit 1);
   KZero (SA (ELit 0) 2147621501) (ELit 1);
   KZero (SA (ELit 0) 2147621539) (ELit 1);
   KZero (SA (ELit 0) 2147621545) (ELit 1);
   KZero (SA (ELit 0) 2147621546) (ELit 1)].
Definition ISH : list kentry := [KZero (SA (ELit 0) 2147621501) (ELit 1);
   KZero (SA (ELit 0) 2147621539) (ELit 1);
   KZero (SA (ELit 0) 2147621545) (ELit 1);
   KZero (SA (ELit 0) 2147621546) (ELit 1)].
Definition BSHZ : list kentry := [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)].

Definition PSTATE (xlevel xwend xwptr xst xsst xnst xmore xdone xk xsize xp xsb xslen xscap : expr) : list kentry :=
  [KWord (SA (EVar 10) (144)) 4 xlevel;
   KWord (SA (EVar 10) (192)) 8 xwend;
   KWord (SA (EVar 10) (200)) 8 xwptr;
   KWord (SA (EVar 10) (208)) 1 xst;
   KWord (SA (EVar 10) (209)) 1 xsst;
   KWord (SA (EVar 10) (210)) 1 xnst;
   KWord (SA (EVar 10) (211)) 1 xmore;
   KWord (SA (EVar 10) (212)) 1 xdone;
   KWord (SA (EVar 10) (224)) 8 (APC.eaddz (APC.escale (2) xk) (1));
   KWord (SA (EVar 10) (232)) 8 xsize;
   KWord (SA (EVar 10) (240)) 8 xp;
   KWord (SA (EVar 10) (248)) 8 xsb;
   KWord (SA (EVar 10) (256)) 8 (APC.eadd xsb xslen);
   KWord (SA (EVar 10) (264)) 8 (APC.eadd xsb xscap);
   KUnk (SA (EVar 10) (148)) (ELit (44));
   KUnk (SA (EVar 10) (220)) (ELit (4))].
Definition BLOCKS_KN (xk xsize xp xsb xslen xscap xlevel : expr) : list kentry :=
  [KRange xk (132) (67108864);
   KRange (APC.esub (APC.eaddz (APC.escale (2) xk) (-1)) xsize) (0) (140737488355328);
   KAlign (APC.escale (2) xk) (8);
   KRange xsize (0) (67108863);
   KWord (SA (APC.eadd xsize xp) (0)) 1 (ELit (0));
   KWr (SA xp (0)) (APC.escale (2) xk);
   KRange xp (4096) (140737479966720);
   KAlign xp (16);
   KZero (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA xp (0)) (APC.escale (2) xk);
   KUnk (SA xsb (0)) xscap;
   KWr (SA xsb (0)) xscap;
   KRange xsb (4096) (140737479966720);
   KAlign xsb (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA xsb (0)) xscap;
   KRange xslen (1) (1027);
   KRange xscap (66) (1056);
   KRange (APC.esub xscap xslen) (0) (1056);
   KRange xlevel (0) (4294967295);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA xsb (0)) xscap;
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 65536) (ELit 6959104);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 65536) (ELit 6959104);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (EVar 12) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit (33)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 11) (8)) (ELit (40)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 11) (8)) (ELit (40)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA xsb (0)) xscap].
Definition BLOCKS_KN0 (xk xsize xp xsb xslen xscap xlevel : expr) : list kentry :=
  [KRange xk (132) (67108864);
   KRange (APC.esub (APC.eaddz (APC.escale (2) xk) (-1)) xsize) (0) (140737488355328);
   KAlign (APC.escale (2) xk) (8);
   KRange xsize (0) (67108863);
   KWord (SA (APC.eadd xsize xp) (0)) 1 (ELit (0));
   KWr (SA xp (0)) (APC.escale (2) xk);
   KRange xp (4096) (140737479966720);
   KAlign xp (16);
   KZero (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA xp (0)) (APC.escale (2) xk);
   KUnk (SA xsb (0)) xscap;
   KWr (SA xsb (0)) xscap;
   KRange xsb (4096) (140737479966720);
   KAlign xsb (8);
   KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA xsb (0)) xscap;
   KRange xslen (1) (1027);
   KRange xscap (66) (1056);
   KRange (APC.esub xscap xslen) (0) (1056);
   KRange xlevel (0) (4294967295);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA xsb (0)) xscap;
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 65536) (ELit 6959104);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 65536) (ELit 6959104);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA xp (0)) (APC.escale (2) xk) (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA xsb (0)) xscap (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (EVar 12) (0)) (ELit 16);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 6877256) (ELit 2);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 7015072) (ELit 544);
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33) (SA (ELit 0) 6883756) (ELit 4);
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit (33)) (SA (EAlu Instr.ALU_SRL xsb (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz xscap (7)) (ELit 3));
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 11) (8)) (ELit (40)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 10) (0)) (ELit (272)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 12) (0)) (ELit (16)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 11) (0)) (ELit (8)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 11) (8)) (ELit (40)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 36) (0)) (EVar 32) (SA xsb (0)) xscap].
Definition BLOCKS_KDISJ_F (xp xk xsb xscap : expr) : list kentry :=
  [KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA xsb (0)) xscap;
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA xp (0)) (APC.escale (2) xk);
   KDisj (SA (EVar 60) (0)) (ELit (1)) (SA xsb (0)) xscap;
   KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL xp (ELit 3)) 2147450880) (ELit 33)].

Definition WE : expr := (APC.eadd (EVar 36) (EVar 32)).
Definition KN_COMMON : list kentry := KOBJ ++ [KWord (SA (EVar 12) (0)) 4 (ELit (0))] ++ PCONST ++ BLOCKS_KN0 (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59) (EVar 53) ++ STRANGES.
Definition KN0S : list kentry := KN_COMMON ++ SURV_S ++ PSTATE (EVar 53) WE (APC.esub (APC.eadd (EVar 36) (EVar 32)) (EVar 46)) (EVar 48) (EVar 49) (EVar 50) (ELit (1)) (EVar 52) (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59) ++ WIN_KN
  ++ [KRange (EVar 46) (0) (16384);
   KRange (APC.esub (EVar 32) (EVar 46)) (0) (0);
   KRange (APC.esub (EVar 33) (APC.eadd (EVar 55) (EVar 46))) (0) (67108864);
   KUnk (SA (EVar 2) (-10496)) (ELit (10496))].
Definition KN0N : list kentry := KN_COMMON ++ SURV_N ++ PSTATE (EVar 53) WE (APC.esub (APC.eadd (EVar 36) (EVar 32)) (EVar 46)) (EVar 48) (EVar 49) (EVar 50) (ELit (1)) (EVar 52) (EVar 54) (EVar 55) (EVar 56) (EVar 57) (EVar 58) (EVar 59)
  ++ [KRange (EVar 36) (0) (0);
   KRange (EVar 32) (0) (0);
   KRange (EVar 46) (0) (0);
   KRange (APC.esub (EVar 33) (EVar 55)) (0) (67108864);
   KUnk (SA (EVar 2) (-10496)) (ELit (10496))].

Definition MEASNEWS (cells : list kentry) : list kentry := (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells).
Definition FLAGC (cells : list kentry) : list kentry :=
  match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end.
Definition WFACTS_same (regs : list expr) (cells : list kentry) (g : nat) : list kentry := [KRange (APC.esub (EVar 33) (APC.eadd (EVar (g + 9)) (APC.esub (APC.eadd (EVar 36) (EVar 32)) (match CAX.cell_at cells (EVar 10) 200 8 with Some e => e | None => ELit 0 end)))) (0) (67108864)].
Definition PNEWS_same (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  PCONST ++ PSTATE (EVar (g + 7)) WE (match CAX.cell_at cells (EVar 10) 200 8 with Some e => e | None => ELit 0 end) (EVar (g + 2)) (EVar (g + 3)) (EVar (g + 4)) (EVar (g + 5)) (EVar (g + 6)) (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13))
  ++ WFACTS_same regs cells g ++ BLOCKS_KN (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13)) (EVar (g + 7)) ++ BLOCKS_KDISJ_F (EVar (g + 10)) (EVar (g + 8)) (EVar (g + 11)) (EVar (g + 13))
  ++ [KWord (SA (EVar 12) (0)) 4 (EVar g);
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar g) (0) (31);
   KRange (EVar (g + 2)) (0) (255);
   KRange (EVar (g + 3)) (0) (255);
   KRange (EVar (g + 4)) (0) (255);
   KRange (EVar (g + 5)) (0) (1);
   KRange (EVar (g + 6)) (0) (1)].
Definition WFACTS_condBm (regs : list expr) (cells : list kentry) (g : nat) : list kentry := [KRange (EVar (g + 1)) (0) (32768);
   KRange (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)) (0) (16384);
   KRange (APC.esub (EVar 32) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g))) (0) (16384);
   KRange (APC.esub (EVar 33) (APC.eadd (EVar (g + 9)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)))) (0) (67108864)].
Definition PNEWS_condBm (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  PCONST ++ PSTATE (EVar (g + 7)) WE (match CAX.cell_at cells (EVar 10) 200 8 with Some e => e | None => ELit 0 end) (EVar (g + 2)) (EVar (g + 3)) (EVar (g + 4)) (EVar (g + 5)) (EVar (g + 6)) (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13))
  ++ WFACTS_condBm regs cells g ++ BLOCKS_KN (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13)) (EVar (g + 7)) ++ BLOCKS_KDISJ_F (EVar (g + 10)) (EVar (g + 8)) (EVar (g + 11)) (EVar (g + 13))
  ++ [KWord (SA (EVar 12) (0)) 4 (EVar g);
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar g) (0) (31);
   KRange (EVar (g + 2)) (0) (255);
   KRange (EVar (g + 3)) (0) (255);
   KRange (EVar (g + 4)) (0) (255);
   KRange (EVar (g + 5)) (0) (1);
   KRange (EVar (g + 6)) (0) (1)].
Definition WFACTS_condB (regs : list expr) (cells : list kentry) (g : nat) : list kentry := [KRange (EVar (g + 1)) (0) (32768);
   KRange (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)) (0) (16384);
   KRange (APC.esub (EVar 32) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g))) (0) (16384);
   KRange (APC.esub (EVar 33) (APC.eadd (EVar (g + 9)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)))) (0) (67108864)].
Definition PNEWS_condB (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  PCONST ++ PSTATE (EVar (g + 7)) WE (APC.esub (APC.eadd (EVar 36) (EVar 32)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g))) (EVar (g + 2)) (EVar (g + 3)) (EVar (g + 4)) (EVar (g + 5)) (EVar (g + 6)) (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13))
  ++ WFACTS_condB regs cells g ++ BLOCKS_KN (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13)) (EVar (g + 7)) ++ BLOCKS_KDISJ_F (EVar (g + 10)) (EVar (g + 8)) (EVar (g + 11)) (EVar (g + 13))
  ++ [KWord (SA (EVar 12) (0)) 4 (EVar g);
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar g) (0) (31);
   KRange (EVar (g + 2)) (0) (255);
   KRange (EVar (g + 3)) (0) (255);
   KRange (EVar (g + 4)) (0) (255);
   KRange (EVar (g + 5)) (0) (1);
   KRange (EVar (g + 6)) (0) (1)].
Definition WFACTS_a1m (regs : list expr) (cells : list kentry) (g : nat) : list kentry := [KRange (APC.esub (APC.esub (APC.eadd (EVar 36) (EVar 32)) (nth 11 regs (ELit 0))) (EVar (g + 1))) (0) (16415);
   KRange (EVar (g + 1)) (0) (16384);
   KRange (APC.esub (EVar 32) (EVar (g + 1))) (0) (16384);
   KRange (APC.esub (EVar 33) (APC.eadd (EVar (g + 9)) (EVar (g + 1)))) (0) (67108864)].
Definition PNEWS_a1m (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  PCONST ++ PSTATE (EVar (g + 7)) WE (match CAX.cell_at cells (EVar 10) 200 8 with Some e => e | None => ELit 0 end) (EVar (g + 2)) (EVar (g + 3)) (EVar (g + 4)) (EVar (g + 5)) (EVar (g + 6)) (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13))
  ++ WFACTS_a1m regs cells g ++ BLOCKS_KN (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13)) (EVar (g + 7)) ++ BLOCKS_KDISJ_F (EVar (g + 10)) (EVar (g + 8)) (EVar (g + 11)) (EVar (g + 13))
  ++ [KWord (SA (EVar 12) (0)) 4 (EVar g);
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar g) (0) (31);
   KRange (EVar (g + 2)) (0) (255);
   KRange (EVar (g + 3)) (0) (255);
   KRange (EVar (g + 4)) (0) (255);
   KRange (EVar (g + 5)) (0) (1);
   KRange (EVar (g + 6)) (0) (1)].
Definition WFACTS_cell1 (regs : list expr) (cells : list kentry) (g : nat) : list kentry := [KRange (APC.esub (APC.esub (APC.eadd (EVar 36) (EVar 32)) (match CAX.cell_at cells (EVar 10) 200 8 with Some e => e | None => ELit 0 end)) (EVar (g + 1))) (1) (16415);
   KRange (EVar (g + 1)) (0) (16384);
   KRange (APC.esub (EVar 32) (EVar (g + 1))) (0) (16384);
   KRange (APC.esub (EVar 33) (APC.eadd (EVar (g + 9)) (EVar (g + 1)))) (0) (67108864)].
Definition PNEWS_cell1 (regs : list expr) (cells : list kentry) (g : nat) : list kentry :=
  PCONST ++ PSTATE (EVar (g + 7)) WE (APC.esub (APC.eadd (EVar 36) (EVar 32)) (EVar (g + 1))) (EVar (g + 2)) (EVar (g + 3)) (EVar (g + 4)) (EVar (g + 5)) (EVar (g + 6)) (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13))
  ++ WFACTS_cell1 regs cells g ++ BLOCKS_KN (EVar (g + 8)) (EVar (g + 9)) (EVar (g + 10)) (EVar (g + 11)) (EVar (g + 12)) (EVar (g + 13)) (EVar (g + 7)) ++ BLOCKS_KDISJ_F (EVar (g + 10)) (EVar (g + 8)) (EVar (g + 11)) (EVar (g + 13))
  ++ [KWord (SA (EVar 12) (0)) 4 (EVar g);
   KUnk (SA (EVar 12) (0)) (ELit (16));
   KRange (EVar g) (0) (31);
   KRange (EVar (g + 2)) (0) (255);
   KRange (EVar (g + 3)) (0) (255);
   KRange (EVar (g + 4)) (0) (255);
   KRange (EVar (g + 5)) (0) (1);
   KRange (EVar (g + 6)) (0) (1)].
Definition XS_SKIPSP : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 780684 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_cell1 regs cells g ++ [KRange (EVar g) 0 0] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PNULL : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 793496 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_condB regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_BOBJ : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 781384 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_BARR : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 782284 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_EOBJ : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 797332 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_EARR : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 798824 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_BMEMBER : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 800308 9792 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PTRUE : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 794796 9792 14%nat (fun regs g => Some (APC.esub (APC.eadd (EVar 36) (EVar 32)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)))) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_condBm regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PFALSE : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 796028 9792 14%nat (fun regs g => Some (APC.esub (APC.eadd (EVar 36) (EVar 32)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)))) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_condBm regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PSTRING : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 783228 9792 14%nat (fun regs g => Some (APC.esub (APC.eadd (EVar 36) (EVar 32)) (APC.eadd (APC.esub (APC.eaddz (EVar 46) (-1)) (EVar (g + 1))) (EVar g)))) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_condBm regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PNUMBER : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 789464 9792 14%nat (fun regs g => Some (APC.esub (APC.eadd (EVar 36) (EVar 32)) (EVar (g + 1)))) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((ELit 0), 6883756, ELit 4); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_a1m regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_ENDINT : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 778024 9280 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_ENDFRAC : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 778200 9280 14%nat (fun _ _ => None) (fun regs => [((EVar 10), 0, ELit 272); ((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544); ((ELit 0), 6883756, ELit 4); ((EVar 11), 8, ELit 40)]) (fun _ _ => []) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ PNEWS_same regs cells g ++ [] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, [((EVar (g + 10)), APC.escale 2 (EVar (g + 8))); ((EVar (g + 11)), (EVar (g + 13)))])) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_ERRH : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 822600 16 1%nat (fun regs g => Some (EVar g)) (fun regs => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ (match (match nth 11 regs (ELit 0) with EAlu Instr.ALU_ADD b (ELit k) => CAX.cell_at cells b k 4 | e => CAX.cell_at cells e 0 4 end) with Some (ELit 24) => [KRange (EVar g) 1 1] | Some (ELit _) => [KRange (EVar g) 0 0] | _ => [] end) ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 10), (211), ELit 1)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_SETEC : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 747008 1024 0%nat (fun regs g => Some (EVar 12)) (fun regs => [((EVar 12), 0, ELit 16); ((ELit 0), 6877256, ELit 2); ((ELit 0), 7015072, ELit 544)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KUnk (SA (EVar 12) 0) (ELit 16)] ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 10), (211), ELit 1)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PARENT : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 800992 640 1%nat (fun regs g => Some (EVar g)) (fun regs => []) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KRange (EVar g) 0 255] ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_VPUSH : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 807200 8240 3%nat (fun _ _ => None) (fun regs => [((EVar 10), 248, ELit 24)]) (fun _ BL => firstn 1 BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KWord (SA (EVar 10) (248)) 8 (EVar g); KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar g) (EVar (g + 2))); KWord (SA (EVar 10) (264)) 8 (APC.eadd (EVar g) (EVar (g + 1))); KUnk (SA (EVar g) (0)) (EVar (g + 1)); KWr (SA (EVar g) (0)) (EVar (g + 1)); KRange (EVar g) (4096) (140737479966720); KAlign (EVar g) (8); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar g) (0)) (EVar (g + 1)) (SA (ELit 0) 65536) (ELit 6959104); KRange (EVar (g + 2)) (1) (1027); KRange (EVar (g + 1)) (66) (1056); KRange (APC.esub (EVar (g + 1)) (EVar (g + 2))) (0) (1056); KDisj (SA (EVar 56) (0)) (APC.escale (2) (EVar 54)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 36) (0)) (EVar 32) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar 11) (8)) (ELit (40)) (SA (EVar g) (0)) (EVar (g + 1)); KDisj (SA (EVar g) (0)) (EVar (g + 1)) (SA (ELit 0) 6877256) (ELit 2); KDisj (SA (EVar g) (0)) (EVar (g + 1)) (SA (ELit 0) 7015072) (ELit 544); KDisj (SA (EVar g) (0)) (EVar (g + 1)) (SA (ELit 0) 6883756) (ELit 4); KDisj (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) 2147450880) (ELit (34)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) 2147450880) (ELit (2)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) 2147450880) (EVar 35) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) 2147450880) (ELit (1)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit (33)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit (128)) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar (g + 1)) (7)) (ELit 3)); KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, (BLk ++ [((EVar g), (EVar (g + 1)))]))) (fun F => F)) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_PUSHB : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 985020 4368 2%nat (fun _ _ => None) (fun regs => [((EVar 10), 224, ELit 24)]) (fun _ BL => skipn 1 BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KWord (SA (EVar g) (0)) 1 (nth 11 regs (ELit 0)); KWord (SA (EVar 10) (224)) 8 (APC.eaddz (APC.escale (2) (EVar (g + 1))) (1)); KWord (SA (EVar 10) (232)) 8 (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1)); KWord (SA (EVar 10) (240)) 8 (EVar g); KRange (EVar (g + 1)) (132) (67108864); KRange (APC.esub (APC.eaddz (APC.escale (2) (EVar (g + 1))) (-1)) (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1))) (0) (140737488355328); KAlign (APC.escale (2) (EVar (g + 1))) (8); KWord (SA (APC.eadd (APC.eaddz (match CAX.cell_at cells (EVar 10) 232 8 with Some e => e | None => ELit 0 end) (1)) (EVar g)) (0)) 1 (ELit (0)); KWr (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KRange (EVar g) (4096) (140737479966720); KAlign (EVar g) (16); KZero (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 65536) (ELit 6959104); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (EVar 57) (0)) (EVar 59); KDisj (SA (EVar 2) (-10496)) (ELit (10496)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 10) (0)) (ELit (272)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 12) (0)) (ELit (16)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 11) (0)) (ELit (8)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 11) (8)) (ELit (40)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 65) (0)) (ELit (1024)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 60) (0)) (ELit (1)) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar 36) (0)) (EVar 32) (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 6877256) (ELit 2); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 7015072) (ELit 544); KDisj (SA (EVar g) (0)) (APC.escale (2) (EVar (g + 1))) (SA (ELit 0) 6883756) (ELit 4); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (6877256)) (ELit (2)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (7015072)) (ELit (544)); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (ELit (0)) (6883756)) (ELit (4)); KDisj (SA (EAlu Instr.ALU_SRL (EVar 65) (ELit 3)) 2147450880) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33); KDisj (SA (EAlu Instr.ALU_SRL (EVar g) (ELit 3)) 2147450880) (ELit 33) (SA (EAlu Instr.ALU_SRL (EVar 57) (ELit 3)) 2147450880) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 59) (7)) (ELit 3))] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, (((EVar g), (APC.escale (2) (EVar (g + 1)))) :: BLk))) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_VNULL : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 829996 2624 0%nat (fun regs g => Some (ELit 1)) (fun regs => [((EVar 11), 8, ELit 40)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_VBOOL : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 830164 2624 0%nat (fun regs g => Some (ELit 1)) (fun regs => [((EVar 11), 8, ELit 40)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F)) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_POPST : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 779788 4240 2%nat (fun regs g => Some (EVar g)) (fun regs => [((EVar 10), 256, ELit 8); ((EAlu Instr.ALU_SRL (EVar 57) (ELit 3)), 2147450880, (EAlu Instr.ALU_SRL (APC.eaddz (EVar 59) (7)) (ELit 3)))]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1)] ++ (flat_map (fun X : kentry => match X with KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 64) (EVar 46)) (ELit c)) 0 4611686018427387904 => [KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 1 4611686018427387904; KRange (APC.eaddz (APC.escale 64 (EVar 46)) (c - 1)) 0 4611686018427387904] | _ => [] end) cells) ++ [KWord (SA (EVar 10) (256)) 8 (APC.eadd (EVar 57) (EVar (g + 1))); KRange (EVar g) 0 255; KRange (EVar (g + 1)) 1 1027; KRange (APC.esub (EVar 59) (EVar (g + 1))) (0) (1056); KRange (EVar g) 1 16] ++ [KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)] ++ match CAX.cell_at cells (EVar 65) 1016 8 with Some fl => [KWord (SA (EVar 65) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => [((EVar 2), (-10496), ELit 10496); ((EVar 65), (0), ELit 24); ((EVar 65), (32), ELit 984); ((EAlu Instr.ALU_SRL (EVar 65) (ELit 3)), (2147450880), ELit 128); ((EVar 10), (148), ELit 44); ((EVar 10), (200), ELit 16); ((EVar 10), (220), ELit 4); ((EVar 10), (232), ELit 8)])) (fun regs => [((EVar 65), 4, -672)]).
Definition XS_SM4 : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 413936 512 1%nat (fun _ _ => None) (fun _ => []) (fun _ BL => BL) (fun _ _ g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1); KRange (EVar (g + 5)) 7024640 140737479965696; KAlign (EVar (g + 5)) 64; KUnk (SA (EVar (g + 5)) 0) (ELit 1024); KWr (SA (EVar (g + 5)) 0) (ELit 1024); KZero (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128); KWr (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128); KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar (g + 5)) 0) (ELit 1024); KDisj (SA (EVar 2) (-10496)) (ELit 10496) (SA (EVar (g + 5)) 0) (ELit 1024); KWord (SA (EVar (g + 5)) 1016) 8 (EVar g); KWr (SA (EVar g) 0) (ELit 1); KRange (EVar g) 7024640 140737479966719; KDisj (SA (ELit 0) 2147446784) (ELit 17592186048512) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar 2) (-10496)) (ELit 10496) (SA (EVar g) 0) (ELit 1); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 10) (0)) (ELit (272)); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 12) (0)) (ELit (16)); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (0)) (ELit (8)); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 11) (8)) (ELit (40)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 11) (8)) (ELit (40)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 10) (ELit 3)) (2147450880)) (ELit (34)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 12) (ELit 3)) (2147450880)) (ELit (2)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 11) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 36) (0)) (EVar 32); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 36) (0)) (EVar 32); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 34) (ELit 3)) (2147450880)) (EVar 35); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 56) (0)) (APC.escale (2) (EVar 54)); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 56) (0)) (APC.escale (2) (EVar 54)); KDisj (SA (EVar (g + 5)) 0) (ELit 1024) (SA (EVar 57) (0)) (EVar 59); KDisj (SA (EVar g) 0) (ELit 1) (SA (EVar 57) (0)) (EVar 59); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) (2147450880)) (ELit (33)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (EVar 57) (ELit 3)) (2147450880)) (EAlu Instr.ALU_SRL (APC.eaddz (EVar 59) (7)) (ELit 3)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (209)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (210)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (211)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (212)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (213)) (ELit 3)) (2147450880)) (ELit (1)); KDisj (SA (EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)) (2147450880)) (ELit 128) (SA (EAlu Instr.ALU_SRL (APC.eaddz (EVar 10) (220)) (ELit 3)) (2147450880)) (ELit (1)); KZero (SA (ELit 0) 2147621501) (ELit 1); KZero (SA (ELit 0) 2147621539) (ELit 1); KZero (SA (ELit 0) 2147621545) (ELit 1); KZero (SA (ELit 0) 2147621546) (ELit 1); KZero (SA (EAlu Instr.ALU_SRL (EVar 56) (ELit 3)) 2147450880) (ELit 33)], BLk)) (fun F => let g := 60%nat in (F ++ [((EVar (g + 5)), 0, ELit 24); ((EVar (g + 5)), 32, ELit 984); ((EAlu Instr.ALU_SRL (EVar (g + 5)) (ELit 3)), 2147450880, ELit 128)]))) (fun _ => []).
Definition XS_SETSH : CAXA.xsumA :=
  CAXA.XSA (CAX.XSUM 535276 256 0%nat (fun _ _ => None) (fun regs => [((EAlu Instr.ALU_SRL (nth 18 regs (ELit 0)) (ELit 3)), 2147450880, ELit 128)]) (fun _ BL => BL) (fun regs cells g BLk => ([KImg (1388760) (1392480); KWord (SA (ELit 0) 1427896) 8 (ELit 2147450880); KWord (SA (ELit 0) 1427904) 4 (ELit 1)] ++ [] ++ match CAX.cell_at cells (nth 18 regs (ELit 0)) 1016 8 with Some fl => [KWord (SA (nth 18 regs (ELit 0)) 1016) 8 fl; KWr (SA fl 0) (ELit 1)] | None => [] end, BLk)) (fun F => F ++ [((EVar 60), 0, ELit 1)])) (fun regs => [((nth 18 regs (ELit 0)), 4, -672)]).

Definition x_of (xa : CAXA.xsumA) : CAX.xsum := CAXA.xa_x xa.
Definition news_of (xa : CAXA.xsumA) (regs : list expr) (cells : list kentry) (g : nat) (BLk : CA.blocks) : list kentry := fst (CAX.xs_new (x_of xa) regs cells g BLk).
Definition blk_of (xa : CAXA.xsumA) (regs : list expr) (cells : list kentry) (g : nat) (BLk : CA.blocks) : CA.blocks := snd (CAX.xs_new (x_of xa) regs cells g BLk).

Definition XS_TAB : list (Z * CAXA.xsumA) :=
  [(780684, XS_SKIPSP); (793496, XS_PNULL); (781384, XS_BOBJ); (782284, XS_BARR); (797332, XS_EOBJ); (798824, XS_EARR); (800308, XS_BMEMBER); (794796, XS_PTRUE); (796028, XS_PFALSE); (783228, XS_PSTRING); (789464, XS_PNUMBER); (778024, XS_ENDINT); (778200, XS_ENDFRAC); (822600, XS_ERRH); (747008, XS_SETEC); (800992, XS_PARENT); (807200, XS_VPUSH); (985020, XS_PUSHB); (779788, XS_POPST); (413936, XS_SM4); (535276, XS_SETSH); (829996, XS_VNULL); (830164, XS_VBOOL)].
Definition xs_at (pc : Z) : option CAXA.xsumA := match find (fun e => Z.eqb (fst e) pc) XS_TAB with Some (_, x) => Some x | None => None end.
End PSOK.
