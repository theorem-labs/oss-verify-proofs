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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWB_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition PWFB_IT : itab := APC.mk_itab_ranges SG [(0x964a0, 940%nat); (0xcde70, 1%nat)].
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
  [KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition T0 : ST.tmpl := ST.TM 0x964a0 T0_regs T0_kn 33%nat (ELit 83886080) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (ELit 2); (add vF8 (V 22)); (ELit 10);
   (vS0); (vS1); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (V 20)); (V 24);
   (ELit 2147450880); (V 25); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (ELit 9); (V 26); (V 27); (V 28)].
Definition IL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 0 1048576;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition IL : ST.tmpl := ST.TM 0x96690 IL_regs IL_kn 29%nat (add (ELit 79691776) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (V 24); (add vF8 (V 22)); (V 25);
   (vS0); (vS1); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (V 26); (V 27);
   (ELit 2147450880); (V 28); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition J1_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 0 1048576;
   KRange (V 21) 0 1;
   KRange (V 22) 0 1;
   KRange (sub (add vFO (V 21)) (mul 8 (V 22))) 0 7;
   KRange (sub (V 20) (V 21)) 0 1048576;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition J1 : ST.tmpl := ST.TM 0x966e4 J1_regs J1_kn 33%nat (ELit 75497472) 0%nat.

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (V 24); (spo (-128)); (vGP); (vTP); (sub (V 21) (V 22)); (V 25); (sub vN (V 20));
   (ELit 0x8080808080808080); (ELit 0x5f5e100); (vF); (add vF vN); (add vF (V 22)); (add vF (V 20)); (add vF (add (V 20) (ELit 7))); (V 26);
   (ELit 2147450880); (V 27); (ELit 0xff000000ff); (ELit 0xf424000000064); (ELit 0x4646464646464646); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x271000000001); (ELit 7);
   (V 28); (V 29); (V 30); (V 31); (ELit 8); (V 32); (ELit 10); (add vF8 (add (V 23) (ELit 2147450880)))].
Definition SW_kn : list kentry :=
  [KRange (V 20) 1 1048576;
   KRange (sub vN (V 20)) 8 1048576;
   KRange (sub (V 20) (V 21)) 1 1048576;
   KRange (V 23) 0 0x200000;
   KRange (sub (add vFO (V 20)) (mul 8 (V 23))) 0 7;
   KRange (sub (V 21) (V 22)) 1 1048576;
   KRange (V 21) 1 1048576;
   KRange (V 22) 0 1;
   KWord (SA vSP (-128)) 8 (add (add vF (V 21)) (ELit 1));
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition SW : ST.tmpl := ST.TM 0x967b4 SW_regs SW_kn 33%nat (add (ELit 71303168) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (sub (V 21) (V 22)); (V 24); (ELit 9);
   (V 25); (V 26); (vF); (add vF vN); (add vF (V 22)); (add vF (V 20)); (add vF (V 20)); (V 27);
   (ELit 2147450880); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (add (add vF (V 21)) (ELit 1)); (V 35); (V 36); (V 37); (ELit (-1)); (ELit 10); (V 38); (V 39)].
Definition FL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (sub (V 20) (V 21)) 1 1048576;
   KRange (sub vN (V 21)) 2 1048576;
   KRange (sub (V 21) (V 22)) 1 1048576;
   KRange (V 21) 1 1048576;
   KRange (V 22) 0 1;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition FL : ST.tmpl := ST.TM 0x969b8 FL_regs FL_kn 40%nat (add (ELit 67108864) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 24); (spo (-128)); (vGP); (vTP); ((V 22)); (mul (-1) (V 23)); (V 25);
   (V 26); (V 27); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (V 28); (V 29);
   (ELit 2147450880); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J2_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 0 1048576;
   KRange (V 21) 0 1;
   KRange (sub (V 20) (V 21)) 1 1048576;
   KRange (V 22) 1 2097152;
   KRange (V 23) 0 1048576;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition J2 : ST.tmpl := ST.TM 0x96a24 J2_regs J2_kn 45%nat (ELit 62914560) 0%nat.

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); ((V 22)); (mul (-1) (V 23)); ((V 25));
   (ELit 2); (V 27); (vF); (add vF vN); (add vF (V 21)); (add vF (V 20)); (add vF (V 20)); (V 28);
   (ELit 2147450880); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); ((V 24)); (ELit 9); (ELit 10); (ELit 0xfffffff)].
Definition EL_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (V 21) 0 1;
   KRange (sub vN (V 21)) 1 1048576;
   KRange (V 22) 1 2097152;
   KRange (V 23) 0 1048576;
   KRange (V 24) 0 2684354559;
   KRange (V 25) 0 1;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition EL : ST.tmpl := ST.TM 0x96af0 EL_regs EL_kn 40%nat (add (ELit 58720256) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); ((V 21)); ((V 22)); (V 24);
   (V 25); (V 26); (vF); (add vF vN); (add vF (V 20)); (V 27); (V 28); (V 29);
   (ELit 2147450880); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J3_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (sub vN (V 20)) 1 1048576;
   KRange (V 21) 1 2097152;
   KRange (add (V 22) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition J3 : ST.tmpl := ST.TM 0x96b68 J3_regs J3_kn 45%nat (ELit 54525952) 0%nat.

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 23); (spo (-128)); (vGP); (vTP); (add (V 21) (ELit (-1048576))); ((V 22)); (ELit (-1));
   (V 24); (V 25); (vF); (add vF vN); (add vF (V 20)); (add vF (V 20)); (ELit 46); (V 26);
   (ELit 2147450880); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (ELit 48); (V 38); (V 39); (V 40)].
Definition ZS_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (sub vN (V 20)) 1 1048576;
   KRange vN 1 1048576;
   KRange (V 21) 0 3145728;
   KRange (add (V 21) (V 20)) 1048596 4194304;
   KRange (add (V 22) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition ZS : ST.tmpl := ST.TM 0x96b84 ZS_regs ZS_kn 41%nat (add (ELit 50331648) (sub vN (V 20))) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); ((V 20)); (V 23);
   (V 24); (V 25); (vF); (add vF vN); (V 26); (V 27); (V 28); (V 29);
   (ELit 2147450880); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J4_kn : list kentry :=
  [KRange vN 1 1048576;
   KRange (add (V 20) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition J4 : ST.tmpl := ST.TM 0x96bd8 J4_regs J4_kn 45%nat (ELit 46137344) 0%nat.

(* [comment removed for export] *)
Definition CF_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (add (V 20) (ELit (-342))); (V 23);
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (ELit 2147450880); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition CF : ST.tmpl := ST.TM 0x96c18 CF_regs CF_kn 47%nat (ELit 37748736) 0%nat.

(* [comment removed for export] *)
Definition CP_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); ((V 20)); (V 23);
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (ELit 2147450880); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition CP : ST.tmpl := ST.TM 0x96db0 CP_regs CP_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition CM_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); ((V 20)); (V 23);
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (ELit 2147450880); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition CM : ST.tmpl := ST.TM 0x96f08 CM_regs CM_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition CN_regs : list expr :=
  [ELit 0; (V 21); (spo (-128)); (vGP); (vTP); (V 22); (mul (-1) (V 20)); (V 23);
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (ELit 2147450880); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition CN : ST.tmpl := ST.TM 0x96f70 CN_regs CN_kn 47%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition XS_regs : list expr :=
  [ELit 0; (V 20); (spo (-128)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vF); (add vF vN); (V 26); (V 27); (V 28); (V 29);
   (ELit 2147450880); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KZero (SA (mul 2 vSP16) 2147450254) (ELit 626);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KZero (SA vF8 2147450880) vFG;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KWr (SA (mul 2 vSP16) 2147450254) (ELit 626)].
Definition XS : ST.tmpl := ST.TM 0x96fdc XS_regs XS_kn 45%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (ELit 0x96ffc); (spo (-128)); (vGP); (vTP); (V 20); (V 21); (V 22);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151609 0x80000000000;
   KWr (SA vSP (-5008)) (ELit 5008);
   KUnk (SA vSP (-5008)) (ELit 5008);
   KDisj (SA vSP (-5008)) (ELit 5008) (SA vF 0) vN;
   KRange vN 0 1048576;
   KRange vF8 0xce200 0xfffffefffff;
   KRange vFO 0 7;
   KRange (add vF vN) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) vN;
   KUnk (SA vF 0) vN;
   KRange vFG 1 0x200000;
   KRange (sub (mul 8 vFG) (add vFO vN)) 48 55;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608)].
Definition RS : ST.tmpl := ST.TM 0x96ffc RS_regs RS_kn 47%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608)].
Definition X : ST.tmpl := ST.TM 0x96f00 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PWFB : SP.prog := SP.PGH 20 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; CF; CP; CM; CN; XS; RS] [X] [(vSP, -5008, ELit 5008)] [SX.SpHav 0x96cbc 5; SX.SpSlt 0x96a18; SX.SpCmp 0x96b54 BC_LT (EVar 28) (ELit 0); SX.SpSlt 0x96b60; SX.SpW 0x96b20; SX.SpW 0x96c28; SX.SpW 0x96d14] [SLSB] (Some [(vSP, -5008, ELit 5008); (mul 2 vSP16, 2147450254, ELit 626); (vF, 0, vN); (vF8, 2147450880, vFG); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)]) (Some (vSP)) [(vF, 0, vN); (vF8, 2147450880, vFG)] [].
