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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition SLOWABF_IT : itab := APC.mk_itab_ranges SG [(0xc0ae4, 2318%nat)].
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
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (V 33); (add (V 25) (mul (-1) (V 26))); (V 34); (V 35);
   (V 36); (V 37); (vFK); (V 38); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (add vF (V 24)); (V 39); (ELit 0xa0000002e); (V 40); (ELit 53); (add (add vF (V 25)) (ELit 1))].
Definition T0_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 1 1048576;
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
Definition T0 : ST.tmpl := ST.TMG 0xc1858 T0_regs T0_kn 41%nat (ELit 209715200) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]].

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 28); (vSPA); (vGP); (vTP); (V 29); (V 30); (ELit 9);
   (vSP); (vSPA); (add vF (V 27)); (V 31); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 32); (V 33);
   (add (add (V 25) (mul (-1) (V 24))) (ELit 1)); (add (add (V 24) (mul (-1) (V 26))) (ELit (-1))); (vFK); (add (add vF (V 25)) (ELit 1)); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (add vF (V 24)); (add vF (V 27)); (ELit 10); (ELit 0x10000000); (V 34); (ELit 0xa0000002e)].
Definition EL_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add vN (mul (-1) (V 27))) 1 1048576;
   KRange (add (V 27) (mul (-1) (V 24))) 1 1048576;
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
Definition EL : ST.tmpl := ST.TMG 0xc19f8 EL_regs EL_kn 35%nat (add (ELit 205520896) (add vN (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]].

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 33); (V 34);
   (V 35); (add (add (V 24) (mul (-1) (V 26))) (ELit (-1))); (vFK); (V 36); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (V 37); (V 38); (ELit 0xa0000002e); (V 39); (V 40); (add (add vF (V 25)) (ELit 1))].
Definition J3_kn : list kentry :=
  [KRange (V 24) 0 1048576;
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
Definition J3 : ST.tmpl := ST.TMG 0xc1ad0 J3_regs J3_kn 41%nat (ELit 201326592) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]].

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); (V 30); (ELit 46); (ELit 48);
   (vSP); (vSPA); (add vF (V 27)); (V 31); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 32); (V 33);
   (V 34); ((V 28)); (vFK); (V 35); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (V 36); (V 37); (add vF (V 27)); (V 38); (V 39); (add (add vF (V 25)) (ELit 1))].
Definition ZS_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add vN (mul (-1) (V 27))) 1 1048576;
   KRange (add (V 27) (mul (-1) (V 26))) 0 1048576;
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
Definition ZS : ST.tmpl := ST.TMG 0xc1b04 ZS_regs ZS_kn 40%nat (add (ELit 197132288) (add vN (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 4 [add vF (V 26); add (V 27) (mul (-1) (V 26)); add (add (add (V 24) (mul (-1) (V 26))) (ELit (-1))) (mul (-1) (V 28))]].

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 28); (vSPA); (vGP); (vTP); (V 29); (V 30); (V 31);
   (vSP); (vSPA); (V 32); (V 33); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 34); (V 35);
   (V 36); ((V 27)); (vFK); (V 37); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41); (V 42); (add (add vF (V 25)) (ELit 1))].
Definition J4_kn : list kentry :=
  [KRange (V 24) 0 1048576;
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
Definition J4 : ST.tmpl := ST.TMG 0xc1b3c J4_regs J4_kn 43%nat (ELit 192937984) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]].

(* [comment removed for export] *)
Definition TI_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); (V 30); (ELit 0xde0b6b3a7640000); (V 31);
   (vSP); (vSPA); (add vF (V 27)); ((V 28)); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 32); (V 33);
   (add vF (V 27)); (ELit 10); (vFK); (V 34); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (V 35); (V 36); (V 37); (V 38); (V 39); (add (add vF (V 25)) (ELit 1))].
Definition TI_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add (V 25) (mul (-1) (V 27))) 0 1048576;
   KRange (add (V 27) (mul (-1) (V 26))) 0 1048576;
   KRange (V 28) 0 999999999999999999;
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
Definition TI : ST.tmpl := ST.TMG 0xc1b60 TI_regs TI_kn 40%nat (add (ELit 188743680) (add (V 25) (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 6 [add vF (V 26); add (V 27) (mul (-1) (V 26)); (V 28)]].

(* [comment removed for export] *)
Definition TF_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); (V 30); (ELit 10); (add (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))) (add (mul (-1) (V 27)) (ELit (-1))));
   (vSP); (vSPA); (add (add (add vF (V 25)) (ELit 1)) (V 27)); ((V 28)); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 31); (V 32);
   (add (add (add vF (V 25)) (ELit 1)) (V 27)); (ELit 0xde0b6b3a763ffff); (vFK); (V 33); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (add vF (V 25)); (ELit 2147450880); (V 34); (V 35); (V 36); (V 37); (V 38); (add (add vF (V 25)) (ELit 1))].
Definition TF_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))) (mul (-1) (V 27))) 1 1048576;
   KRange (V 28) 0 999999999999999999;
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
Definition TF : ST.tmpl := ST.TMG 0xc1bc4 TF_regs TF_kn 39%nat (add (ELit 184549376) (add (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))) (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); add (add (V 24) (mul (-1) (V 25))) (ELit (-1))]; ST.GA 6 [add vF (V 26); add (V 25) (mul (-1) (V 26)); (V 28)]; ST.GA 6 [add (add vF (V 25)) (ELit 1); (V 27); (V 28)]].

(* [comment removed for export] *)
Definition J5T_regs : list expr :=
  [ELit 0; (V 28); (vSPA); (vGP); (vTP); (V 29); (V 30); (V 31);
   (vSP); (vSPA); (V 32); ((V 27)); (add (add (V 24) (mul (-1) (V 25))) (ELit (-1))); (add (V 25) (mul (-1) (V 26))); (V 33); (V 34);
   (V 35); (V 36); (vFK); (V 37); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (add vF (V 26)); (add vF vN);
   (V 38); (ELit 2147450880); (V 39); (V 40); (V 41); (V 42); (V 43); (add (add vF (V 25)) (ELit 1))].
Definition J5T_kn : list kentry :=
  [KRange (V 27) 1 9999999999999999999;
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
Definition J5T : ST.tmpl := ST.TM 0xc1c14 J5T_regs J5T_kn 44%nat (ELit 180355072) 0%nat.

(* [comment removed for export] *)
Definition E5A_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (add vFK (ELit 640)); (ELit 0); (ELit 32); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vFK); (V 33); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 34); (add vF vN);
   (V 35); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition E5A_kn : list kentry :=
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
Definition E5A : ST.tmpl := ST.TM 0xc1a84 E5A_regs E5A_kn 42%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E5B_regs : list expr :=
  [ELit 0; (ELit 793224); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (V 35); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 36); (add vF vN);
   (V 37); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition E5B_kn : list kentry :=
  [KZero (SA vFK 640) (ELit 32);
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
Definition E5B : ST.tmpl := ST.TM 0xc1a88 E5B_regs E5B_kn 44%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E5C_regs : list expr :=
  [ELit 0; (ELit 793240); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (V 35); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 36); (add vF vN);
   (V 37); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition E5C_kn : list kentry :=
  [KZero (SA vFK 640) (ELit 32);
   KZero (SA vFK 608) (ELit 27);
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
Definition E5C : ST.tmpl := ST.TM 0xc1a98 E5C_regs E5C_kn 44%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition XCLN_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (ELit 0); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 35); (V 36);
   (vV); (ELit 2147450880); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition XCLN_kn : list kentry :=
  [KWord (SA vFK 634) 1 (ELit 0);
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
Definition XCLN : ST.tmpl := ST.TM 0xc20fc XCLN_regs XCLN_kn 43%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XCF_regs : list expr :=
  [ELit 0; (V 28); (vSPA); (vGP); (vTP); (V 29); (V 30); (V 31);
   (vSP); (vSPA); (V 32); (V 33); (ELit 1); (V 34); (V 35); (V 36);
   (V 37); (V 38); (vFK); (vFK); (add (mul 128 vF10) (ELit 2147450880)); (add vFK (ELit 608)); (V 39); (V 40);
   (vV); (ELit 2147450880); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition XCF_kn : list kentry :=
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
Definition XCF : ST.tmpl := ST.TM 0xc21a4 XCF_regs XCF_kn 47%nat (ELit 0) 0%nat.

Definition SLOWABF : SP.prog := SP.PGCA 24 [T0; EL; J3; ZS; J4; TI; TF; J5T; E5A; E5B; E5C] [XCLN; XCF] [(vSP, -4848, ELit 4848); (vV, 0, ELit 8); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [] [(AMH.MSAG 0 0xc1a88); (AMH.MSAG 0 0xc1a98)] [(vSP, -4848, ELit 4848); (mul 2 vSP16, 2147450274, ELit 606); (vF, 0, vN); (vF8, 2147450880, vFG); (vV, 0, ELit 8); (vV8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)].
