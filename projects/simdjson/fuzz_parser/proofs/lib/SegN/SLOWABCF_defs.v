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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PMA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PDCA_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NDCA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition SLOWABCF_IT : itab := APC.mk_itab_ranges SG [(0xc0ae4, 2318%nat); (0xc46c4, 1%nat); (0xc4fb8, 1%nat); (0xc5938, 1%nat)].
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
Definition vV8 := V 20.
Definition vF10 := V 21.
Definition vFLG := V 22.
Definition vPB := V 23.
Definition vSP := mul 16 vSP16.
Definition vF := add (mul 8 vF8) vFO.
Definition vV := mul 8 vV8.
Definition vFK := mul 1024 vF10.
Definition vSPA := sub (mul 16 vSP16) (add (ELit 192) (mul 16 vPB)).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (V 28); (vSPA); (vGP); (vTP); (V 29); (V 30); (V 31);
   (vSP); (vSPA); (V 32); (V 33); (ELit 1); (V 34); (V 35); (V 36);
   (V 37); (V 38); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 39); (V 40);
   (vV); (ELit 2147450880); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition T0_kn : list kentry :=
  [KWord (SA vFK 634) 1 (ELit 1);
   KWord (SA vFK 616) 8 (V 27);
   KRange (V 27) 1 9999999999999999999;
   KWord (SA vFK 640) 8 (add vF (V 26));
   KWord (SA vFK 648) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vFK 656) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vFK 664) 8 (add (add (V 24) (mul (-1) (V 25))) (ELit (-1)));
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 2 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 16) 8 (ELit 53);
   KWord (SA vSPA 24) 8 (ELit 0xa0000002e);
   KUnk (SA vSPA 32) (ELit 8);
   KWord (SA vSPA 40) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0xc21a4 T0_regs T0_kn 47%nat (ELit 125829120) 0%nat.

(* [comment removed for export] *)
Definition CF2M_regs : list expr :=
  [ELit 0; (V 31); (vSPA); (vGP); (vTP); (V 32); (V 33); (V 34);
   (vSP); (vSPA); (V 35); ((V 27)); (add (V 27) (ELit 1)); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 41); ((V 29));
   (vV); (ELit 2147450880); ((V 28)); ((V 30)); (V 42); (V 43); (V 44); (V 45)].
Definition CF2M_kn : list kentry :=
  [KRange (add (V 28) (ELit 9223372036854775808)) 9223372036854775466 9223372036854776116;
   KRange (V 27) 1 9999999999999999999;
   KWord (SA vFK 640) 8 (add vF (V 26));
   KWord (SA vFK 648) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vFK 656) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vFK 664) 8 (add (add (V 24) (mul (-1) (V 25))) (ELit (-1)));
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 2 1048576;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CF2M : ST.tmpl := ST.TM 0xc23fc CF2M_regs CF2M_kn 46%nat (ELit 121634816) 0%nat.

(* [comment removed for export] *)
Definition CE_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); (V 30); (V 31); (V 32);
   (vSP); (vSPA); (V 33); ((V 27)); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 40); (V 41);
   (vV); (ELit 2147450880); ((V 28)); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition CE_kn : list kentry :=
  [KRange (add (V 28) (ELit 9223372036854775808)) 9223372036854775466 9223372036854776116;
   KRange (V 27) 1 9999999999999999999;
   KWord (SA vFK 640) 8 (add vF (V 26));
   KWord (SA vFK 648) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vFK 656) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vFK 664) 8 (add (add (V 24) (mul (-1) (V 25))) (ELit (-1)));
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 2 1048576;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition CE : ST.tmpl := ST.TM 0xc267c CE_regs CE_kn 47%nat (ELit 117440512) 0%nat.

(* [comment removed for export] *)
Definition JSE_regs : list expr :=
  [ELit 0; (V 30); (vSPA); (vGP); (vTP); (V 31); (V 32); (V 33);
   (vSP); (vSPA); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 42); ((V 28));
   (add vFK (ELit 32)); (ELit 2147450880); (add (V 27) (ELit (-342))); ((V 29)); (V 43); (V 44); (V 45); (V 46)].
Definition JSE_kn : list kentry :=
  [KRange (V 27) 0 668;
   KWord (SA vFK 640) 8 (add vF (V 26));
   KWord (SA vFK 648) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vFK 656) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vFK 664) 8 (add (add (V 24) (mul (-1) (V 25))) (ELit (-1)));
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 2 1048576;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition JSE : ST.tmpl := ST.TM 0xc2884 JSE_regs JSE_kn 47%nat (ELit 113246208) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xc299c); (vSPA); (vGP); (vTP); (V 30); (V 31); (V 32);
   (vSP); (vSPA); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (ELit 0xffffffff); ((V 28));
   (add vFK (ELit 32)); (ELit 2147450880); (add (V 27) (ELit (-342))); ((V 29)); (V 41); (V 42); (V 43); (V 44)].
Definition R1_kn : list kentry :=
  [KRange (V 27) 0 668;
   KZero (SA vFK 32) (ELit 504);
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KWord (SA vSPA 80) 8 (ELit 0);
   KWord (SA vFK 640) 8 (add vF (V 26));
   KWord (SA vFK 648) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vFK 656) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vFK 664) 8 (add (add (V 24) (mul (-1) (V 25))) (ELit (-1)));
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 2 1048576;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition R1 : ST.tmpl := ST.TM 0xc299c R1_regs R1_kn 45%nat (ELit 109051904) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xc29b0); (vSPA); (vGP); (vTP); (V 29); (V 30); (V 31);
   (vSP); (vSPA); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (ELit 0xffffffff); ((V 25));
   (add vFK (ELit 32)); (ELit 2147450880); (add (V 24) (ELit (-342))); ((V 26)); (V 40); (V 41); (V 42); (V 43)].
Definition R2_kn : list kentry :=
  [KRange (V 24) 0 668;
   KWord (SA vSPA 80) 8 (V 27);
   KRange (V 27) 0 770;
   KWord (SA vFK 528) 2 (V 28);
   KRange (V 28) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KZero (SA (mul 128 vF10) 2147450956) (ELit 9);
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KZero (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition R2 : ST.tmpl := ST.TM 0xc29b0 R2_regs R2_kn 44%nat (ELit 104857600) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0xc29cc); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (ELit 0xffffffff); (V 35);
   (add vFK (ELit 32)); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition R3_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition R3 : ST.tmpl := ST.TM 0xc29cc R3_regs R3_kn 42%nat (ELit 100663296) 0%nat.

(* [comment removed for export] *)
Definition R4_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (ELit 0xffffffff); (V 36);
   (add vFK (ELit 32)); (ELit 2147450880); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition R4_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 72) 8 (vFK);
   KWord (SA vSPA 48) 8 (vFK);
   KWord (SA vSPA 56) 8 (vV);
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition R4 : ST.tmpl := ST.TM 0xc29e8 R4_regs R4_kn 43%nat (ELit 96468992) 0%nat.

(* [comment removed for export] *)
Definition XSS_regs : list expr :=
  [ELit 0; (ELit 0xc2b8c); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (add (mul 128 vF10) (ELit 2147450880)); (ELit 128); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); ((V 24)); ((V 25)); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition XSS_kn : list kentry :=
  [KUnk (SA vV 0) (ELit 8);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450274) (ELit 606);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KRange vPB 0 1;
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
   KRange vTP 0x642e70 0x642e70;
   KRange vSP16 8795556151599 0x80000000000;
   KWr (SA vSP (-4848)) (ELit 4848);
   KUnk (SA vSP (-4848)) (ELit 4848);
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vF 0) vN;
   KDisj (SA vSP (-4848)) (ELit 4848) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xcca00 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KRange vV8 0xfffc0000000 0xffffffffffe;
   KRange (sub vV vSP) 8 8;
   KWr (SA vV 0) (ELit 8);
   KZero (SA vV8 2147450880) (ELit 1);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition XSS : ST.tmpl := ST.TM 0x69720 XSS_regs XSS_kn 44%nat (ELit 0) 0%nat.

Definition SLOWABCF : SP.prog := SP.PGH 24 [T0; CF2M; CE; JSE; R1; R2; R3; R4] [XSS] [(vSP, -4848, ELit 4848); (vV, 0, ELit 8); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [SX.SpHav 0xc2288 14; SX.SpHav 0xc22bc 16; SX.SpHav 0xc24a0 14; SX.SpHav 0xc24d4 15; SX.SpHav 0xc2718 14; SX.SpHav 0xc274c 14; SX.SpW 0xc29b4; SX.SpW 0xc29b8] [(AMH.MSAG 0 0xc299c); PMSA; PDSA; NDSA] (Some [(vSP, -4848, ELit 4848); (mul 2 vSP16, 2147450274, ELit 606); (vF, 0, vN); (vF8, 2147450880, vFG); (vV, 0, ELit 8); (vV8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)]) (Some (vSP)) [(vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128); (ELit 0, 0x10b978, ELit 4)] [].
