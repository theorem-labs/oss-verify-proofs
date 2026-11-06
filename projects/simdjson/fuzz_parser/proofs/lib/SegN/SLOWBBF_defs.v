(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHBS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition SLOWBBF_IT : itab := APC.mk_itab_ranges SG [(0xcba2c, 2514%nat)].
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
Definition vSPA := sub (mul 16 vSP16) (add (ELit 256) (mul 16 vPB)).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (V 27); (V 28); (ELit 53);
   (vSP); (vSPA); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 37);
   (add vF (V 25)); (add vF (V 24)); (V 38); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition T0_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (sub (V 24) (V 25)) 1 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition T0 : ST.tmpl := ST.TMG 0xcc888 T0_regs T0_kn 43%nat (ELit 209715200) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (V 24) (sub (ELit (-1)) (V 25))]].

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (add (add (V 25) (mul (-1) (V 26))) (V 24)); ((V 28)); (ELit 10);
   (vSP); (vSPA); (add vF (V 27)); (V 30); (V 31); ((V 29)); (V 32); (ELit 9);
   ((V 24)); (mul (-1) (V 24)); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (vV);
   (add vF (V 25)); (add vF (add (V 25) (add (V 24) (ELit 1)))); (add vF (V 27)); (vFK); (ELit 0xfffffff); (ELit 2); (V 33); (V 34)].
Definition EL_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add vN (mul (-1) (V 27))) 1 1048576;
   KRange (add (V 27) (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 1 1048576;
   KRange (V 28) 0 2684354559;
   KRange (V 29) 0 1;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition EL : ST.tmpl := ST.TMG 0xcca4c EL_regs EL_kn 35%nat (add (ELit 205520896) (add vN (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]].

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (add (add (V 25) (mul (-1) (V 26))) (V 24)); ((V 27)); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   ((V 24)); ((V 28)); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 36);
   (add vF (V 25)); (V 37); (vV); (vFK); (V 38); (V 39); (V 40); (V 41)].
Definition J3_kn : list kentry :=
  [KRange (add (V 27) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 28) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition J3 : ST.tmpl := ST.TMG 0xccb5c J3_regs J3_kn 42%nat (ELit 201326592) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]].

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (sub (add (add (V 25) (mul (-1) (V 26))) (V 24)) (V 28)); ((V 29)); (add vF (V 27));
   (vSP); (vSPA); (add vF (V 27)); (V 31); (V 32); (ELit 48); (V 33); (ELit (-1));
   ((V 24)); ((V 30)); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 34);
   (add vF (V 25)); (V 35); (vV); (vFK); (V 36); (V 37); (V 38); (V 39)].
Definition ZS_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add vN (mul (-1) (V 27))) 1 1048576;
   KRange (add (V 27) (mul (-1) (V 26))) 0 1048576;
   KRange (V 28) 0 1048576;
   KRange (add (V 27) (mul (-1) (add (V 26) (V 28)))) 0 1048576;
   KRange (add (add (V 25) (mul (-1) (V 26))) (V 24)) 20 2097152;
   KRange (add (V 29) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 30) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition ZS : ST.tmpl := ST.TMG 0xccb78 ZS_regs ZS_kn 40%nat (add (ELit 197132288) (add vN (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 4 [add vF (V 26); add (V 27) (mul (-1) (V 26)); (V 28)]].

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); ((V 27)); ((V 28)); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   ((V 24)); ((V 29)); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 37);
   (add vF (V 25)); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition J4_kn : list kentry :=
  [KRange (add (V 28) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 29) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition J4 : ST.tmpl := ST.TMG 0xccbd4 J4_regs J4_kn 43%nat (ELit 192937984) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]].

(* [comment removed for export] *)
Definition TI_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (add vF (V 27)); ((V 29)); (V 30);
   (vSP); (vSPA); (add vF (V 27)); (V 31); ((V 28)); (ELit 2); (V 32); (ELit 10);
   ((V 24)); (ELit 1000000000000000000); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 33);
   (add vF (V 25)); (V 34); (vV); (vFK); (V 35); (V 36); (V 37); (V 38)].
Definition TI_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add (V 25) (mul (-1) (V 27))) 0 1048576;
   KRange (add (V 27) (mul (-1) (V 26))) 0 1048576;
   KRange (V 28) 0 999999999999999999;
   KRange (add (V 29) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition TI : ST.tmpl := ST.TMG 0xccc0c TI_regs TI_kn 39%nat (add (ELit 188743680) (add (V 25) (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 6 [add vF (V 26); add (V 27) (mul (-1) (V 26)); (V 28)]].

(* [comment removed for export] *)
Definition TF_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (ELit 10); ((V 29)); (add (add (add vF (V 25)) (ELit 1)) (V 27));
   (vSP); (vSPA); (add (add (add vF (V 25)) (ELit 1)) (V 27)); (V 30); ((V 28)); (ELit 999999999999999999); (V 31); (ELit (-1));
   ((V 24)); (add ((V 24)) (add (mul (-1) (V 27)) (ELit (-1)))); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 32);
   (add vF (V 25)); (V 33); (vV); (vFK); (V 34); (V 35); (V 36); (V 37)].
Definition TF_kn : list kentry :=
  [KRange (V 27) 0 1048576;
   KRange (add ((V 24)) (mul (-1) (V 27))) 1 1048576;
   KRange (V 28) 0 999999999999999999;
   KRange (add (V 29) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition TF : ST.tmpl := ST.TMG 0xccca8 TF_regs TF_kn 38%nat (add (ELit 184549376) (add ((V 24)) (mul (-1) (V 27)))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 3 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 5 [add vF (V 26); add (V 25) (mul (-1) (V 26)); add (add vF (V 25)) (ELit 1); (V 24)]; ST.GA 6 [add vF (V 26); add (V 25) (mul (-1) (V 26)); (V 28)]; ST.GA 6 [add (add vF (V 25)) (ELit 1); (V 27); (V 28)]].

(* [comment removed for export] *)
Definition J5T_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (V 30); ((V 29)); (V 31);
   (vSP); (vSPA); ((V 28)); (V 32); ((V 27)); (V 33); (V 34); (V 35);
   ((V 24)); (V 36); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 37);
   (add vF (V 25)); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition J5T_kn : list kentry :=
  [KRange (V 27) 1 9999999999999999999;
   KRange (add (V 28) (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KRange (add (V 29) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition J5T : ST.tmpl := ST.TM 0xccd14 J5T_regs J5T_kn 43%nat (ELit 180355072) 0%nat.

(* [comment removed for export] *)
Definition E5A_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (add vSPA (ELit 104)); (ELit 0); (ELit 32); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 36); (add vF vN); (V 37);
   (V 38); (V 39); (V 40); (vFK); (V 41); (V 42); (V 43); (V 44)].
Definition E5A_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition E5A : ST.tmpl := ST.TM 0xccb04 E5A_regs E5A_kn 45%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E5B_regs : list expr :=
  [ELit 0; (ELit 838408); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 38); (add vF vN); (V 39);
   (V 40); (V 41); (V 42); (vFK); (V 43); (V 44); (V 45); (V 46)].
Definition E5B_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition E5B : ST.tmpl := ST.TM 0xccb08 E5B_regs E5B_kn 47%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E5C_regs : list expr :=
  [ELit 0; (ELit 838424); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 38); (add vF vN); (V 39);
   (V 40); (V 41); (V 42); (vFK); (V 43); (V 44); (V 45); (V 46)].
Definition E5C_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KZero (SA vSPA 72) (ELit 27);
   KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition E5C : ST.tmpl := ST.TM 0xccb18 E5C_regs E5C_kn 47%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition XCLN_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (V 29); (V 30); (ELit 0); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vV); (vFK); (V 41); (V 42); (V 43); (V 44)].
Definition XCLN_kn : list kentry :=
  [KWord (SA vSPA 96) 1 (V 24);
   KRange (V 24) 0 1;
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition XCLN : ST.tmpl := ST.TM 0xcd2b4 XCLN_regs XCLN_kn 45%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XCF_regs : list expr :=
  [ELit 0; (V 30); (vSPA); (vGP); (vTP); (V 31); (V 32); (V 33);
   (vSP); (vSPA); (V 34); (V 35); (ELit 1); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 41); (V 42); (V 43);
   (V 44); (V 45); (vV); (vFK); (V 46); (V 47); (V 48); (V 49)].
Definition XCF_kn : list kentry :=
  [KWord (SA vSPA 98) 1 (ELit 1);
   KWord (SA vSPA 80) 8 (V 27);
   KRange (V 27) 1 9999999999999999999;
   KWord (SA vSPA 72) 8 (V 28);
   KRange (add (V 28) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KWord (SA vSPA 96) 1 (V 29);
   KRange (V 29) 0 1;
   KWord (SA vSPA 104) 8 (add vF (V 26));
   KWord (SA vSPA 112) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 120) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vSPA 128) 8 ((V 24));
   KRange (V 24) 1 1048576;
   KRange (add vN (mul (-1) (add (V 25) (add (V 24) (ELit 1))))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vFK 0) (ELit 1024);
   KUnk (SA vFK 0) (ELit 1024);
   KWord (SA vFK 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vFK (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vFK 0) (ELit 1024);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vFK 0) (ELit 1024);
   KDisj (SA vFK 0) (ELit 1024) (SA vF 0) vN;
   KDisj (SA vFK 0) (ELit 1024) (SA vV 0) (ELit 8);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vF8 2147450880) vFG;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vFK 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vV8 2147450880) (ELit 1);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vFK 0) (ELit 1024) (SA vF8 2147450880) vFG;
   KWord (SA vSPA 64) 8 (vFK);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151601 0x80000000000;
   KWr (SA vSP (-4880)) (ELit 4880);
   KUnk (SA vSP (-4880)) (ELit 4880);
   KZero (SA (mul 2 vSP16) 2147450270) (ELit 610);
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vF 0) vN;
   KDisj (SA vSP (-4880)) (ELit 4880) (SA vV 0) (ELit 8);
   KRange vN 1 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
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
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450270) (ELit 610)].
Definition XCF : ST.tmpl := ST.TM 0xcd280 XCF_regs XCF_kn 50%nat (ELit 0) 0%nat.

Definition SLOWBBF : SP.prog := SP.PGCA 24 [T0; EL; J3; ZS; J4; TI; TF; J5T; E5A; E5B; E5C] [XCLN; XCF] [(vSP, -4880, ELit 4880); (vV, 0, ELit 8); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [SX.SpSlt 0xcc8a0; SX.SpCmp 0xccb44 BC_LT (EVar 6) (ELit 0); SX.SpSlt 0xccb50; SX.SpW 0xcca7c; SX.SpCmp 0xccd18 BC_LT (EVar 6) (ELit 0); SX.SpSlt 0xccd20] [(AMHBS.MSAGS 0 0xccb08); (AMHBS.MSAGS 0 0xccb18)] [(vSP, -4880, ELit 4880); (mul 2 vSP16, 2147450270, ELit 610); (vF, 0, vN); (vF8, 2147450880, vFG); (vV, 0, ELit 8); (vV8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)].
