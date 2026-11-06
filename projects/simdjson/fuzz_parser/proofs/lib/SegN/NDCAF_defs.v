(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition NDCAF_IT : itab := APC.mk_itab_ranges SG [(0xc5040, 607%nat)].
Definition V (n : nat) : expr := EVar n.
Definition add (a b : expr) : expr := EAlu ALU_ADD a b.
Definition sub (a b : expr) : expr := EAlu ALU_SUB a b.
Definition mul (k : Z) (a : expr) : expr := EMd M_MUL (ELit k) a.
Definition vRA := V 0.
Definition vSP := V 1.
Definition vGP := V 2.
Definition vTP := V 3.
Definition vS0 := V 4.
Definition vS1 := V 5.
Definition vS2 := V 6.
Definition vS3 := V 7.
Definition vS4 := V 8.
Definition vS5 := V 9.
Definition vS6 := V 10.
Definition vS7 := V 11.
Definition vS8 := V 12.
Definition vS9 := V 13.
Definition vS10 := V 14.
Definition vS11 := V 15.
Definition vX8 := V 16.
Definition vXH := V 17.
Definition vM := V 18.
Definition vP2 := V 19.
Definition vRE := V 20.
Definition vF10 := V 21.
Definition vFLG := V 22.
Definition vX := mul 8 vX8.
Definition vF := mul 1024 vF10.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (V 26); (V 27); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (vF); ((V 25)); (V 40); ((V 24)); (V 41); (V 42);
   (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49); (V 50)].
Definition T0_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KRange vFLG 0x665000 0x7fffff7fffff;
   KWr (SA vFLG 0) (ELit 1);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vFLG 0) (ELit 1);
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFLG 0) (ELit 1);
   KDisj (SA vFLG 0) (ELit 1) (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KWord (SA vSP (-80)) 8 vS8;
   KWord (SA vSP (-88)) 8 vS9;
   KWord (SA vSP (-96)) 8 vS10;
   KWord (SA vSP (-104)) 8 vS11;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425360 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4624)) (ELit 4624);
   KUnk (SA vSP (-4624)) (ELit 4624);
   KRange vX8 0xcca04 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19940 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange vP2 0 0xffffffff;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xc58dc T0_regs T0_kn 51%nat (ELit 1) 0%nat.

(* [comment removed for export] *)
Definition XRF_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 26); (V 27); (V 28);
   vS0; vS1; ((V 24)); ((V 25)); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 35); (V 36); (V 37); (V 38)].
Definition XRF_kn : list kentry :=
  [KZero (SA vX8 2147450880) (ELit 63);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KZero (SA vFLG 0) (ELit 1)].
Definition XRF : ST.tmpl := ST.TM 0xc5938 XRF_regs XRF_kn 39%nat (ELit 0) 0%nat.

Definition NDCAF : SP.prog := SP.PGCA 23 [T0] [XRF] [(vSP, -4624, ELit 4624); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (vFLG, 0, ELit 1)] [] [] [(vSP, -4624, ELit 4624); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4); (vF, 0, ELit 1024); (vFLG, 0, ELit 1)].
