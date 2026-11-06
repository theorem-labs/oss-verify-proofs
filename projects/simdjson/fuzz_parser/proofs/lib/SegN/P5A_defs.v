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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import LMA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition P5A_IT : itab := APC.mk_itab_ranges SG [(0xc59bc, 160%nat); (0xc6c44, 1%nat)].
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
Definition vE0 := V 18.
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vX); (vE0); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vE0 0 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xc59bc T0_regs T0_kn 33%nat (ELit 8589934592) 0%nat.

(* [comment removed for export] *)
Definition PA_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); ((V 19)); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (ELit 175424); (ELit 2147450880); (ELit 134); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition PA_kn : list kentry :=
  [KRange (V 19) 135 2147483647;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition PA : ST.tmpl := ST.TM 0xc5a00 PA_regs PA_kn 37%nat (add (ELit 4294967296) (V 19)) 1%nat.

(* [comment removed for export] *)
Definition PR_regs : list expr :=
  [ELit 0; (ELit 0xc5a10); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); ((V 19)); ((V 21)); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 175424); (ELit 2147450880); (ELit 134); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition PR_kn : list kentry :=
  [KRange (V 19) 135 2147483647;
   KRange (V 21) 0 1;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition PR : ST.tmpl := ST.TM 0xc5a10 PR_regs PR_kn 36%nat (add (ELit 4294967296) (V 19)) 0%nat.

(* [comment removed for export] *)
Definition PB_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (ELit 1); (V 22); (V 23);
   (vX); ((V 19)); (add vX (ELit 496)); (V 24); (add vX8 (ELit 2147450942)); ((V 20)); (add vX8 (ELit 2147450880)); (ELit 7450580596923828125);
   (ELit 26); (ELit 61); (V 25); (ELit 2147450880); (V 26); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition PB_kn : list kentry :=
  [KRange (V 19) 27 2147483647;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition PB : ST.tmpl := ST.TM 0xc5a70 PB_regs PB_kn 31%nat (add (ELit 2147483648) (add (mul 1024 (V 19)) (ELit 1000))) 0%nat.

(* [comment removed for export] *)
Definition PC_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (ELit 1); (V 23); (add vX (mul 8 (sub (V 20) (V 21))));
   (vX); ((V 19)); (add vX (ELit 496)); (add vX (mul 8 (sub (V 20) (V 21)))); (add vX8 (ELit 2147450942)); ((V 20)); (add vX8 (ELit 2147450880)); (ELit 7450580596923828125);
   (ELit 26); (ELit 61); (V 24); (ELit 2147450880); (V 25); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (add (add vX8 (sub (V 20) (V 21))) (ELit 2147450880)); ((V 21)); (V 26); (V 27)].
Definition PC_kn : list kentry :=
  [KRange (V 21) 1 62;
   KRange (sub (V 20) (V 21)) 0 62;
   KRange (V 19) 27 2147483647;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition PC : ST.tmpl := ST.TM 0xc5a88 PC_regs PC_kn 28%nat (add (ELit 2147483648) (add (mul 1024 (V 19)) (V 21))) 0%nat.

(* [comment removed for export] *)
Definition PD_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (add vX (mul 8 (sub (V 20) (V 21)))); ((V 21)); (V 23);
   (vX); ((V 19)); (add vX (ELit 496)); (ELit 1); (add vX (mul 8 (sub (V 20) (V 21)))); (add vX8 (ELit 2147450942)); ((V 20)); (V 24);
   (V 25); (add (add vX8 (sub (V 20) (V 21))) (ELit 2147450880)); (V 26); (ELit 2147450880); (V 27); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition PD_kn : list kentry :=
  [KRange (V 21) 1 62;
   KRange (sub (V 20) (V 21)) 0 62;
   KRange (V 19) 1 26;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425168 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4432)) (ELit 4432);
   KUnk (SA vSP (-4432)) (ELit 4432);
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
   KDisj (SA vSP (-4432)) (ELit 4432) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition PD : ST.tmpl := ST.TM 0xc5b4c PD_regs PD_kn 32%nat ((V 21)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition XR_kn : list kentry :=
  [KRange (V 20) 0 1;
   KZero (SA vX8 2147450880) (ELit 63);
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition XR : ST.tmpl := ST.TM 0xc5be4 XR_regs XR_kn 35%nat (ELit 0) 0%nat.

Definition P5A : SP.prog := SP.PGH 19 [T0; PA; PR; PB; PC; PD] [XR] [(vSP, -4432, ELit 4432); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63)] [] [LMSA] (Some [(vSP, -4432, ELit 4432); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10358, ELit 8); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4)]) (Some (vSP)) [(vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72)] [].
