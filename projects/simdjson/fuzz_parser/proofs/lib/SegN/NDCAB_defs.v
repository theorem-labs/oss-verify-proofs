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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import P5A_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition NDCAB_IT : itab := APC.mk_itab_ranges SG [(0xc5040, 607%nat); (0xc5be4, 1%nat)].
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
Definition vSPA := V 23.
Definition vX := mul 8 vX8.
Definition vF := mul 1024 vF10.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (ELit 0xc50bc); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (vF); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vS2); (vP2); (vS4); (vM); (vX); (vS7);
   (vRE); (vS9); (vS10); (ELit 2147450880); (V 35); (V 36); (V 37); (V 38)].
Definition T0_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KZero (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition T0 : ST.tmpl := ST.TM 0xc50bc T0_regs T0_kn 39%nat (add (ELit 6871947673600) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition JP_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (ELit (-1)); (V 29); (V 30); (EAluw ALU_ADD vP2 (ELit 0)); (V 31); (V 32);
   (V 33); (V 34); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vM); (vX); (V 35);
   (vRE); (V 36); (vF); (ELit 2147450880); (V 37); (V 38); (V 39); (V 40)].
Definition JP_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition JP : ST.tmpl := ST.TM 0xc5264 JP_regs JP_kn 41%nat (add (ELit 6734508720128) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition J0_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (vRE); ((V 25)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition J0_kn : list kentry :=
  [KRange (add (V 25) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition J0 : ST.tmpl := ST.TM 0xc5310 J0_regs J0_kn 42%nat (add (ELit 6528350289920) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xc5424); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); ((V 25)); (add vF (ELit 32));
   (vRE); ((V 26)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition R1_kn : list kentry :=
  [KRange (add (V 26) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KZero (SA vF 40) (ELit 496);
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition R1 : ST.tmpl := ST.TM 0xc5424 R1_regs R1_kn 42%nat (add (ELit 6184752906240) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xc5444); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (V 38); (add vF (ELit 32));
   (vRE); ((V 26)); (vF); (ELit 2147450880); (V 39); (V 40); (V 41); (V 42)].
Definition R2_kn : list kentry :=
  [KRange (add (V 26) (ELit 9223372036854775808)) 9223372036854774733 9223372036855825355;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition R2 : ST.tmpl := ST.TM 0xc5444 R2_regs R2_kn 43%nat (add (ELit 5497558138880) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SBT_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); (V 30); (V 31); (V 32);
   (vSP); (vSPA); (add (add vF (ELit 32)) (mul 8 (sub (V 25) (V 27)))); ((V 25)); ((V 28)); (sub (ELit 64) (V 28)); (add (add (mul 128 vF10) (sub (V 25) (V 27))) (ELit 2147450884)); (add (add vF (ELit 32)) (mul 8 (sub (V 25) (V 27))));
   ((V 27)); (V 33); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 34); (V 35); (V 36); (V 37)].
Definition SBT_kn : list kentry :=
  [KRange (V 27) 1 62;
   KRange (sub (V 25) (V 27)) 0 61;
   KRange (V 28) 1 63;
   KRange (V 26) 1 1049547;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 1 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition SBT : ST.tmpl := ST.TM 0xc5480 SBT_regs SBT_kn 38%nat (add (ELit 4810363371520) (V 27)) 0%nat.

(* [comment removed for export] *)
Definition J1T_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 39); (V 40); (V 41); (V 42)].
Definition J1T_kn : list kentry :=
  [KRange (V 26) 1 1049547;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition J1T : ST.tmpl := ST.TM 0xc54e8 J1T_regs J1T_kn 43%nat (add (ELit 4123168604160) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition JMT_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (add (V 26) (V 25)); (ELit 62); ((V 25)); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39)].
Definition JMT_kn : list kentry :=
  [KRange (V 26) 1 61;
   KRange (add (V 26) (V 25)) 2 62;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 1 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition JMT : ST.tmpl := ST.TM 0xc5508 JMT_regs JMT_kn 40%nat (add (ELit 3779571220480) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R3T_regs : list expr :=
  [ELit 0; (ELit 0xc5520); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (mul 8 (V 26)); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition R3T_kn : list kentry :=
  [KRange (V 26) 1 61;
   KRange (add (V 26) (V 25)) 2 62;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 1 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition R3T : ST.tmpl := ST.TM 0xc5520 R3T_regs R3T_kn 42%nat (add (ELit 3435973836800) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R4T_regs : list expr :=
  [ELit 0; (ELit 0xc5534); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition R4T_kn : list kentry :=
  [KRange (V 26) 1 61;
   KRange (add (V 26) (V 25)) 2 62;
   KZero (SA vF 32) (mul 8 (V 26));
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 1 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition R4T : ST.tmpl := ST.TM 0xc5534 R4T_regs R4T_kn 42%nat (add (ELit 3092376453120) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SBX_regs : list expr :=
  [ELit 0; (V 29); (vSPA); (vGP); (vTP); ((V 27)); (V 30); (V 31);
   (vSP); (vSPA); (add vX (mul 8 (sub (V 24) (V 27)))); ((V 26)); (add vX8 (ELit 2147450942)); ((V 24)); ((V 28)); (sub (ELit 64) (V 28));
   (add (add vX8 (sub (V 24) (V 27))) (ELit 2147450880)); (add vX (mul 8 (sub (V 24) (V 27)))); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); (V 32); (vF); (ELit 2147450880); (V 33); (V 34); (V 35); (V 36)].
Definition SBX_kn : list kentry :=
  [KRange (V 27) 1 62;
   KRange (sub (V 24) (V 27)) 0 61;
   KRange (V 28) 1 63;
   KRange (V 26) 1 1075;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
Definition SBX : ST.tmpl := ST.TM 0xc558c SBX_regs SBX_kn 37%nat (add (ELit 4810363371520) (V 27)) 0%nat.

(* [comment removed for export] *)
Definition J1X_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); ((V 26)); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (vX); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); (V 38); (vF); (ELit 2147450880); (V 39); (V 40); (V 41); (V 42)].
Definition J1X_kn : list kentry :=
  [KRange (V 26) 1 1075;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition J1X : ST.tmpl := ST.TM 0xc55fc J1X_regs J1X_kn 43%nat (add (ELit 4123168604160) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition JMX_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (add (V 26) (V 24)); (ELit 62); ((V 24)); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (add vX8 (ELit 2147450942)); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39)].
Definition JMX_kn : list kentry :=
  [KRange (V 26) 1 16;
   KRange (add (V 26) (V 24)) 2 62;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
Definition JMX : ST.tmpl := ST.TM 0xc562c JMX_regs JMX_kn 40%nat (add (ELit 3779571220480) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R3X_regs : list expr :=
  [ELit 0; (ELit 0xc5644); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (add vX8 (ELit 2147450942)); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition R3X_kn : list kentry :=
  [KRange (V 26) 1 16;
   KRange (add (V 26) (V 24)) 2 62;
   KWord (SA vSPA 16) 8 (mul 8 (V 26));
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
Definition R3X : ST.tmpl := ST.TM 0xc5644 R3X_regs R3X_kn 42%nat (add (ELit 3435973836800) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R4X_regs : list expr :=
  [ELit 0; (ELit 0xc5654); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (add vX8 (ELit 2147450942)); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); ((V 26)); (vF); (ELit 2147450880); (V 38); (V 39); (V 40); (V 41)].
Definition R4X_kn : list kentry :=
  [KRange (V 26) 1 16;
   KRange (add (V 26) (V 24)) 2 62;
   KZero (SA vX 0) (mul 8 (V 26));
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
Definition R4X : ST.tmpl := ST.TM 0xc5654 R4X_regs R4X_kn 42%nat (add (ELit 3092376453120) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (V 38); (vX); (add vF (ELit 32));
   (add vX (ELit 496)); (V 39); (vF); (ELit 2147450880); (V 40); (V 41); (V 42); (V 43)].
Definition J3_kn : list kentry :=
  [KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition J3 : ST.tmpl := ST.TM 0xc5668 J3_regs J3_kn 44%nat (add (ELit 2748779069440) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition CMP_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (add vX (add (mul 8 (V 25)) (ELit (-8)))); (add (add vF (ELit 32)) (add (mul 8 (V 25)) (ELit (-8)))); (ELit 1); (V 30); (add (V 25) (ELit 1)); (V 31);
   (V 32); (V 33); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); (V 34); (add vX (add (mul 8 (V 25)) (ELit (-8)))); (add (add vF (ELit 32)) (add (mul 8 (V 25)) (ELit (-8))));
   (add vX (ELit 496)); (V 35); (vF); (ELit 2147450880); (V 36); (V 37); (V 38); (V 39)].
Definition CMP_kn : list kentry :=
  [KRange (V 25) 0 62;
   KRange (sub (V 24) (V 25)) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KRange (V 24) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KUnk (SA vSPA 24) (ELit 8);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition CMP : ST.tmpl := ST.TM 0xc56bc CMP_regs CMP_kn 40%nat (add (ELit 1374389534720) (V 25)) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (vP2); (add (mul 128 vF10) (ELit 2147450880)); ((V 25)); (V 38); (V 39);
   (V 40); (V 41); (vF); (ELit 2147450880); (V 42); (V 43); (V 44); (V 45)].
Definition J4_kn : list kentry :=
  [KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition J4 : ST.tmpl := ST.TM 0xc57b4 J4_regs J4_kn 46%nat (add (ELit 687194767360) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition XSS_regs : list expr :=
  [ELit 0; (ELit 0xc58dc); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (add (mul 128 vF10) (ELit 2147450880)); (ELit 128); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vF); ((V 26)); (V 36); ((V 25)); (V 37); (V 38);
   (V 39); (V 40); (V 41); (ELit 2147450880); (V 42); (V 43); (V 44); (V 45)].
Definition XSS_kn : list kentry :=
  [KWord (SA vF 0) 8 (ELit 0x45e0360e);
   KWord (SA vF 1016) 8 vFLG;
   KRange vF10 0x1994 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4624)) (ELit 4624) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425168 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4432)) (ELit 4592);
   KUnk (SA vSPA (-4432)) (ELit 4592);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4432)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4432)) (ELit 4432) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
Definition XSS : ST.tmpl := ST.TM 0x69720 XSS_regs XSS_kn 46%nat (ELit 0) 0%nat.

Definition NDCAB : SP.prog := SP.PGH 24 [T0; JP; J0; R1; R2; SBT; J1T; JMT; R3T; R4T; SBX; J1X; JMX; R3X; R4X; J3; CMP; J4] [XSS] [(vSP, -4624, ELit 4624); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128); (vSPA, -4432, ELit 4592)] [] [(AMH.MSAH 0 0xc5424); P5SA; (AMH.MVAH 0xc5520); (AMH.MSAH 0 0xc5534); (AMH.MVAH 0xc5644); (AMH.MSAH 0 0xc5654)] (Some [(vSP, -4624, ELit 4624); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128); (vSPA, -4432, ELit 4592)]) (Some (vSP)) [(vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [].
