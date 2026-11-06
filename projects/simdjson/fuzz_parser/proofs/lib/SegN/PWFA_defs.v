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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition PWFA_IT : itab := APC.mk_itab_ranges SG [(0x96638, 841%nat); (0xc2be8, 1%nat)].
Definition V (n : nat) : expr := EVar n.
Definition add (a b : expr) : expr := EAlu ALU_ADD a b.
Definition sub (a b : expr) : expr := EAlu ALU_SUB a b.
Definition mul (k : Z) (a : expr) : expr := EMd M_MUL (ELit k) a.
Definition vRA := V 0.
Definition vSP16 := V 1.
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
Definition vF8 := V 16.
Definition vFO := V 17.
Definition vN := V 18.
Definition vFG := V 19.
Definition vSP := mul 16 vSP16.
Definition vF := add (mul 8 vF8) vFO.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vF); (add vF vN); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x96638 T0_regs T0_kn 33%nat (ELit 83886080) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (V 24); (ELit 10); (ELit 9);
   (vS0); (vS1); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (V 20)); (add vF8 (add (V 22) (ELit 2147450880)));
   (V 25); (ELit 2147450880); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition IL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (V 21) 0 1;
   KRange (V 22) 0 1;
   KRange (sub (add vFO (V 21)) (mul 8 (V 22))) 0 7;
   KRange (sub (V 20) (V 21)) 5 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition IL : ST.tmpl := ST.TM 0x967e4 IL_regs IL_kn 30%nat (add (ELit 79691776) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (V 24); (sub (V 20) (V 21)); (V 25);
   (vS0); (vS1); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (V 26); (add vF8 (add (V 22) (ELit 2147450880)));
   (V 27); (ELit 2147450880); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition J1_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 0 1048576;
   KRange (V 21) 0 1;
   KRange (V 22) 0 1;
   KRange (sub (add vFO (V 21)) (mul 8 (V 22))) 0 7;
   KRange (sub (V 20) (V 21)) 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition J1 : ST.tmpl := ST.TM 0x9683c J1_regs J1_kn 32%nat (ELit 75497472) 0%nat.

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (ELit 0x5f5e100); (ELit 0xff000000ff); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (add (V 20) (ELit 7))); (V 27);
   (V 28); (ELit 2147450880); (ELit 0xf424000000064); (ELit 0x4646464646464646); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x271000000001); (ELit 7); (V 29);
   (V 30); (V 31); (V 32); (V 33); (sub vN (V 20)); (ELit 10); (add vF8 (add (V 22) (ELit 2147450880))); (ELit 0x8080808080808080)].
Definition SW_kn : list kentry :=
  [KRange (V 20) 1 1048576;
   KRange (sub vN (V 20)) 8 1048576;
   KRange (sub vN (V 21)) 1 1048576;
   KRange (V 22) 0 0x200000;
   KRange (sub (add vFO (V 20)) (mul 8 (V 22))) 0 7;
   KRange (V 21) 0 1;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition SW : ST.tmpl := ST.TM 0x968f4 SW_regs SW_kn 34%nat (add (ELit 71303168) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (V 22); (spo (-128)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (V 20)); (ELit 9);
   (V 28); (ELit 2147450880); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (ELit 10); (V 39); (V 40); (V 41)].
Definition FL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (sub vN (V 21)) 1 1048576;
   KRange (V 21) 0 1;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition FL : ST.tmpl := ST.TM 0x96ac4 FL_regs FL_kn 42%nat (add (ELit 67108864) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 22); (spo (-128)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (V 28); (V 29);
   (V 30); (ELit 2147450880); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J2_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (V 21) 0 1;
   KRange (sub vN (V 21)) 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition J2 : ST.tmpl := ST.TM 0x96b20 J2_regs J2_kn 45%nat (ELit 62914560) 0%nat.

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 22); (spo (-128)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (V 20)); (V 28);
   (V 29); (ELit 2147450880); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (ELit 9); (ELit 10); (ELit 0x10000000)].
Definition EL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (V 21) 0 1;
   KRange (sub vN (V 21)) 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition EL : ST.tmpl := ST.TM 0x96bd0 EL_regs EL_kn 41%nat (add (ELit 58720256) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (vF); (add vF vN); (add vF (V 20)); (V 27); (V 28); (V 29);
   (V 30); (ELit 2147450880); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J3_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (sub vN (V 20)) 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition J3 : ST.tmpl := ST.TM 0x96c1c J3_regs J3_kn 45%nat (ELit 54525952) 0%nat.

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (ELit 46);
   (V 24); (V 25); (vF); (add vF vN); (add vF (V 20)); (add vF (V 20)); (ELit 48); (V 26);
   (V 27); (ELit 2147450880); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition ZS_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition ZS : ST.tmpl := ST.TM 0x96c4c ZS_regs ZS_kn 42%nat (add (ELit 50331648) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (vF); (add vF vN); (V 27); (V 28); (V 29); ((V 20));
   (V 30); (ELit 2147450880); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J4_kn : list kentry :=
  [KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition J4 : ST.tmpl := ST.TM 0x96c84 J4_regs J4_kn 45%nat (ELit 46137344) 0%nat.

(* [comment removed for export] *)
Definition CF_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); (add (V 20) (ELit (-342)));
   (V 32); (ELit 2147450880); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition CF_kn : list kentry :=
  [KRange (V 20) 0 650;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CF : ST.tmpl := ST.TM 0x96cc4 CF_regs CF_kn 47%nat (ELit 37748736) 0%nat.

(* [comment removed for export] *)
Definition CP_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); ((V 20));
   (V 32); (ELit 2147450880); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition CP_kn : list kentry :=
  [KRange (V 20) 0 22;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CP : ST.tmpl := ST.TM 0x96eb4 CP_regs CP_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition CM_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); ((V 20));
   (V 32); (ELit 2147450880); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition CM_kn : list kentry :=
  [KRange (V 20) 0 22;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CM : ST.tmpl := ST.TM 0x96f08 CM_regs CM_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition CN_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); (mul (-1) (V 20));
   (V 32); (ELit 2147450880); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition CN_kn : list kentry :=
  [KRange (V 20) 1 22;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CN : ST.tmpl := ST.TM 0x96fe8 CN_regs CN_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition XS_regs : list expr :=
  [ELit 0; (V 20); (spo (-128)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vF); (add vF vN); (V 26); (V 27); (V 28); (V 29);
   (V 30); (ELit 2147450880); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition XS_kn : list kentry :=
  [KRange vN 1 1048576;
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
   KWord (SA vSP (-120)) 8 (ELit 0);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KZero (SA (mul 2 vSP16) 2147450258) (ELit 622);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition XS : ST.tmpl := ST.TM 0x97048 XS_regs XS_kn 45%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (ELit 0x97068); (spo (-128)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition RS_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
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
   KUnk (SA vSP (-120)) (ELit 8);
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151607 0x80000000000;
   KWr (SA vSP (-4976)) (ELit 4976);
   KUnk (SA vSP (-4976)) (ELit 4976);
   KDisj (SA vSP (-4976)) (ELit 4976) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition RS : ST.tmpl := ST.TM 0x97068 RS_regs RS_kn 47%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition X : ST.tmpl := ST.TM 0x96fe4 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PWFA : SP.prog := SP.PGH 20 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; CF; CP; CM; CN; XS; RS] [X] [(vSP, -4976, ELit 4976)] [SX.SpHav 0x96d68 12; SX.SpHav 0x96d9c 14] [SLSA] (Some [(vSP, -4976, ELit 4976); (mul 2 vSP16, 2147450258, ELit 622); (vF, 0, vN); (vF8, 2147450880, vFG); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4)]) (Some (vSP)) [(vF, 0, vN); (vF8, 2147450880, vFG)] [].
