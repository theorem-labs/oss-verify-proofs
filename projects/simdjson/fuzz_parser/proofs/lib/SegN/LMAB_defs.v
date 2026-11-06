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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition LMAB_IT : itab := APC.mk_itab_ranges SG [(0xc5c3c, 1065%nat)].
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
Definition vF11 := V 18.
Definition vFLG := V 19.
Definition vL0 := V 20.
Definition vSPA := V 21.
Definition vX := mul 8 vX8.
Definition vF := mul 2048 vF11.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (ELit 0xc5cb4); (vSPA); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vSP); (vSPA); (vF); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); vS2; vS3; vS4; (ELit 175424); vS6; vS7;
   vS8; (ELit 5); (ELit 2147450880); vS11; (V 32); (V 33); (V 34); (V 35)].
Definition T0_kn : list kentry :=
  [KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KZero (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 vL0;
   KRange vL0 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xc5cb4 T0_regs T0_kn 36%nat (ELit 6940667150336) 0%nat.

(* [comment removed for export] *)
Definition C1_regs : list expr :=
  [ELit 0; (V 22); (vSPA); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vSP); (vSPA); (ELit 62); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vF); (add (mul 256 vF11) (ELit 2147450880)); (vL0); (ELit 175424); (V 33); (V 34);
   (V 35); (ELit 5); (ELit 2147450880); (V 36); (V 37); (vX); (add vF (ELit 32)); (V 38)].
Definition C1_kn : list kentry :=
  [KRange vL0 1 62;
   KWord (SA vF 528) 2 (ELit 0);
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 vL0;
   KRange vL0 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition C1 : ST.tmpl := ST.TM 0xc60b8 C1_regs C1_kn 39%nat (add (ELit 6803228196864) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xc60c8); (vSPA); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vSP); (vSPA); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vF); (add (mul 256 vF11) (ELit 2147450880)); (vL0); (ELit 175424); (V 33); (V 34);
   (V 35); (ELit 5); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39); (V 40)].
Definition R1_kn : list kentry :=
  [KRange vL0 1 62;
   KWord (SA vF 528) 2 (ELit 0);
   KUnk (SA vF 32) (mul 8 vL0);
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 vL0;
   KRange vL0 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R1 : ST.tmpl := ST.TM 0xc60c8 R1_regs R1_kn 41%nat (add (ELit 6734508720128) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SM1_regs : list expr :=
  [ELit 0; (V 23); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (add vX (mul 8 (sub vL0 (V 22)))); (V 27); (V 28); (add (add vX8 (sub vL0 (V 22))) (ELit 2147450880)); (add vX (mul 8 (sub vL0 (V 22)))); ((V 22));
   (V 29); (V 30); (vF); (add (mul 256 vF11) (ELit 2147450880)); (vL0); (ELit 175424); (V 31); (V 32);
   (V 33); (ELit 5); (ELit 2147450880); (V 34); (V 35); (vX); (add vF (ELit 32)); (V 36)].
Definition SM1_kn : list kentry :=
  [KRange (V 22) 1 62;
   KRange (sub vL0 (V 22)) 0 61;
   KUnk (SA vF 32) (mul 8 vL0);
   KWord (SA vF 528) 2 vL0;
   KRange vL0 0 62;
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KWord (SA vSPA 88) 8 (vL0);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 vL0;
   KRange vL0 1 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition SM1 : ST.tmpl := ST.TM 0xc611c SM1_regs SM1_kn 37%nat (add (ELit 6665789243392) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition OL_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (ELit 175424); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 37); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition OL_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 62;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition OL : ST.tmpl := ST.TM 0xc63b4 OL_regs OL_kn 38%nat (add (sub (ELit 4054449127424) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition C2_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (ELit 175424); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 37); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition C2_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 62;
   KRange (V 24) 1 62;
   KWord (SA vF 1104) 2 (ELit 0);
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition C2 : ST.tmpl := ST.TM 0xc64dc C2_regs C2_kn 38%nat (add (sub (ELit 3985729650688) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xc64f0); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); ((V 23)); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 37); (V 38); (V 39); (V 40)].
Definition R2_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 62;
   KRange (V 24) 1 62;
   KWord (SA vF 1104) 2 (ELit 0);
   KUnk (SA vF 608) (mul 8 (V 24));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R2 : ST.tmpl := ST.TM 0xc64f0 R2_regs R2_kn 41%nat (add (sub (ELit 3917010173952) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SM2_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (add (add vF (ELit 608)) (mul 8 (sub (V 24) (V 25)))); ((V 24)); (V 29); ((V 24)); (mul 281474976710656 (V 24)); (add (add vF (ELit 608)) (mul 8 (sub (V 24) (V 25))));
   (add (add (mul 256 vF11) (sub (V 24) (V 25))) (ELit 2147450956)); ((V 25)); (V 30); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (V 31); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 32); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition SM2_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 62;
   KRange (V 24) 1 62;
   KRange (V 25) 1 62;
   KRange (sub (V 24) (V 25)) 0 61;
   KWord (SA vF 1104) 2 (V 24);
   KUnk (SA vF 608) (mul 8 (V 24));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition SM2 : ST.tmpl := ST.TM 0xc6530 SM2_regs SM2_kn 33%nat (add (sub (ELit 3848290697216) (mul 687194767360 (V 22))) (V 25)) 0%nat.

(* [comment removed for export] *)
Definition C3_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); ((V 26)); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (mul 281474976710656 (V 25)); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); ((V 25)); (ELit 2147450880); (ELit (-8)); (V 38); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition C3_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 61;
   KRange (V 24) 0 62;
   KRange (V 25) 0 62;
   KRange (sub (V 26) (add (V 22) (V 25))) 0 0;
   KRange (V 26) 1 62;
   KRange (sub (V 26) (V 23)) 1 62;
   KUnk (SA vF 608) (mul 8 (V 25));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition C3 : ST.tmpl := ST.TM 0xc65e0 C3_regs C3_kn 39%nat (add (sub (ELit 3779571220480) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0xc65f8); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); ((V 26)); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (mul 281474976710656 (V 25)); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); ((V 25)); (ELit 2147450880); (ELit (-8)); (V 38); (V 39); (V 40); (V 41)].
Definition R3_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 61;
   KRange (V 24) 0 62;
   KRange (V 25) 0 62;
   KRange (sub (V 26) (add (V 22) (V 25))) 0 0;
   KRange (V 26) 1 62;
   KRange (sub (V 26) (V 23)) 1 62;
   KUnk (SA vF 608) (mul 8 (V 25));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R3 : ST.tmpl := ST.TM 0xc65f8 R3_regs R3_kn 42%nat (add (sub (ELit 3710851743744) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition LAD1_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (add vX (mul 8 (sub (add (V 22) (V 25)) (V 26)))); (add (add vF (ELit 608)) (mul 8 (sub (V 25) (V 26)))); (V 30); (add vX (mul 8 (sub (add (V 22) (V 25)) (V 26)))); (add (add vF (ELit 608)) (mul 8 (sub (V 25) (V 26)))); ((V 26));
   (V 31); (V 32); (V 33); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (V 34); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); ((V 25)); (ELit 2147450880); (ELit (-8)); (V 35); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition LAD1_kn : list kentry :=
  [KRange (add (mul 8 (V 22)) (add (mul 8 (V 25)) (mul (-8) (V 26)))) 0 488;
   KRange (V 22) 1 4;
   KRange (V 24) 0 62;
   KRange (V 25) 1 62;
   KRange (V 26) 1 62;
   KRange (sub (V 25) (V 26)) 0 61;
   KRange (sub (add (V 22) (V 25)) (V 26)) 0 61;
   KRange (sub (V 23) (add (V 22) (V 25))) 0 61;
   KRange (V 23) 2 62;
   KUnk (SA vF 608) (mul 8 (V 25));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition LAD1 : ST.tmpl := ST.TM 0xc6638 LAD1_regs LAD1_kn 36%nat (add (sub (ELit 3642132267008) (mul 687194767360 (V 22))) (V 26)) 0%nat.

(* [comment removed for export] *)
Definition LAD2_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (add vX (mul 8 (V 25))); (sub (V 23) (V 25)); (add vX (mul 8 (V 25))); (V 29); (V 30); (V 31);
   (V 32); (V 33); (V 34); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (ELit 175424); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 35); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition LAD2_kn : list kentry :=
  [KRange (V 25) 1 61;
   KRange (V 22) 1 4;
   KRange (V 24) 0 62;
   KRange (sub (V 23) (V 25)) 1 61;
   KRange (V 23) 2 62;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition LAD2 : ST.tmpl := ST.TM 0xc66e4 LAD2_regs LAD2_kn 36%nat (add (sub (ELit 3573412790272) (mul 687194767360 (V 22))) (sub (V 23) (V 25))) 0%nat.

(* [comment removed for export] *)
Definition NX_regs : list expr :=
  [ELit 0; ((V 23)); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (add (mul 256 vF11) (ELit 2147450880)); (add vX (mul 8 (V 22))); (ELit 175424); (sub (ELit 1) (V 22)); (add vX (mul 8 (V 22)));
   ((V 22)); (ELit 5); (ELit 2147450880); (ELit (-8)); (V 37); (vX); (add vF (ELit 32)); (add vF (ELit 608))].
Definition NX_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 23) 0 62;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 16) 8 (ELit 1);
   KWord (SA vSPA 24) 8 (add (mul 256 vF11) (ELit 2147450956));
   KWord (SA vSPA 32) 8 (mul 8 (V 24));
   KWord (SA vSPA 40) 8 (add vF (ELit 608));
   KWord (SA vSPA 48) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 56) 8 (ELit 5);
   KWord (SA vSPA 64) 8 (ELit 175424);
   KWord (SA vSPA 88) 8 ((V 24));
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition NX : ST.tmpl := ST.TM 0xc62a4 NX_regs NX_kn 38%nat (add (sub (ELit 3504693313536) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition NM_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); ((V 22)); (ELit 1); (V 29); (add vX (ELit 496)); (add vX8 (ELit 2147450942));
   (V 30); (V 31); (V 32); (add (mul 256 vF11) (ELit 2147450880)); (V 33); (V 34); (ELit 1); (V 35);
   (V 36); (V 37); (ELit 2147450880); (V 38); (V 39); (vX); (V 40); (V 41)].
Definition NM_kn : list kentry :=
  [KRange (V 22) 1 62;
   KRange (V 23) 0 62;
   KWord (SA vF 528) 2 (V 23);
   KUnk (SA vF 32) (mul 8 (V 23));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 72) 8 (vF);
   KWord (SA vSPA 144) 8 (vF);
   KWord (SA vSPA 96) 8 (add vF (ELit 32));
   KWord (SA vSPA 104) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 112) 8 (add vX (ELit 496));
   KWord (SA vSPA 80) 8 (vF);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 (V 22);
   KRange (V 22) 1 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition NM : ST.tmpl := ST.TM 0xc61c0 NM_regs NM_kn 42%nat (add (ELit 343597383680) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition XSF_regs : list expr :=
  [ELit 0; (ELit 0xc6bf4); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (vF); (ELit 1184); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (add (mul 256 vF11) (ELit 2147450880)); (V 34); (V 35); ((V 23)); (V 36);
   (V 37); (V 38); (ELit 2147450880); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition XSF_kn : list kentry :=
  [KRange (V 23) 0 1;
   KWord (SA vF 0) 8 (ELit 0x45e0360e);
   KWord (SA vF 2040) 8 vFLG;
   KRange vF11 0xcca 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 256)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4352);
   KUnk (SA vSPA (-4096)) (ELit 4352);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-256)) (ELit 256);
   KDisj (SA vSPA 0) (ELit 152) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4384)) (ELit 4384) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 120) 8 vX;
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
   KWord (SA vX 496) 2 (V 22);
   KRange (V 22) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition XSF : ST.tmpl := ST.TM 0x50a40 XSF_regs XSF_kn 44%nat (ELit 0) 0%nat.

Definition LMAB : SP.prog := SP.PGCA 22 [T0; C1; R1; SM1; OL; C2; R2; SM2; C3; R3; LAD1; LAD2; NX; NM] [XSF] [(vSP, -4384, ELit 4384); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (vF, 0, ELit 2048); (mul 256 vF11, 2147450880, ELit 256); (vSPA, -4096, ELit 4352)] [] [(AMH.MCAH 0xc60c8); (AMH.MCAH 0xc64f0); (AMH.MSAH 0 0xc65f8)] [(vSP, -4384, ELit 4384); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4); (vF, 0, ELit 2048); (mul 256 vF11, 2147450880, ELit 256); (vSPA, -4096, ELit 4352)].
