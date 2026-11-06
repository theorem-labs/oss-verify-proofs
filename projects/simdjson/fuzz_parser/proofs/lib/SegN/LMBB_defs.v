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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import LADB_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition LMBB_IT : itab := APC.mk_itab_ranges SG [(0xd0fa8, 956%nat); (0xd214c, 1%nat)].
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
  [ELit 0; (ELit 0xd1024); (vSPA); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vSP); (vSPA); (vF); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); vS2; vS3; (vX); vS5; vS6; (ELit 2147450880);
   (ELit 174592); vS9; vS10; vS11; (V 32); (V 33); (V 34); (V 35)].
Definition T0_kn : list kentry :=
  [KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KZero (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xd1024 T0_regs T0_kn 36%nat (ELit 6940667150336) 0%nat.

(* [comment removed for export] *)
Definition C1_regs : list expr :=
  [ELit 0; (V 22); (vSPA); (vGP); (vTP); (V 23); (ELit 5); (V 24);
   (vSP); (vSPA); (add vF (ELit 32)); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (vL0); (add (mul 256 vF11) (ELit 2147450880)); (vX); (add vX8 (ELit 2147450942)); (V 32); (ELit 2147450880);
   (ELit 174592); (mul 8 vL0); (ELit 174592); (V 33); (V 34); (V 35); (V 36); (V 37)].
Definition C1_kn : list kentry :=
  [KRange vL0 1 62;
   KWord (SA vF 528) 2 (ELit 0);
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition C1 : ST.tmpl := ST.TM 0xd1438 C1_regs C1_kn 38%nat (add (ELit 6803228196864) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xd1448); (vSPA); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vSP); (vSPA); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vL0); (add (mul 256 vF11) (ELit 2147450880)); (vX); (add vX8 (ELit 2147450942)); (V 33); (ELit 2147450880);
   (sub (ELit (-1)) (add vF (ELit 32))); (mul 8 vL0); (ELit 174592); (V 34); (V 35); (V 36); (V 37); (V 38)].
Definition R1_kn : list kentry :=
  [KRange vL0 1 62;
   KWord (SA vF 528) 2 (ELit 0);
   KUnk (SA vF 32) (mul 8 vL0);
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R1 : ST.tmpl := ST.TM 0xd1448 R1_regs R1_kn 39%nat (add (ELit 6734508720128) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SM1_regs : list expr :=
  [ELit 0; (V 23); (vSPA); (vGP); (vTP); (V 24); (ELit 5); (vL0);
   (vSP); (vSPA); (add vX (mul 8 (sub vL0 (V 22)))); (V 25); (V 26); (sub (EAlu ALU_SRL (mul (-1) vX) (ELit 3)) (sub vL0 (V 22))); (sub (ELit 63) (sub vL0 (V 22))); (add vX (mul 8 (sub vL0 (V 22))));
   ((V 22)); (V 27); (vL0); (add (mul 256 vF11) (ELit 2147450880)); (vX); (add vX8 (ELit 2147450942)); (V 28); (ELit 2147450880);
   (ELit 174592); (mul 8 vL0); (ELit 174592); (V 29); (V 30); (V 31); (V 32); (V 33)].
Definition SM1_kn : list kentry :=
  [KRange (add (mul 8 vL0) (mul (-8) (V 22))) 0 488;
   KRange (V 22) 1 62;
   KRange (sub vL0 (V 22)) 0 61;
   KWord (SA vF 528) 2 vL0;
   KUnk (SA vF 32) (mul 8 vL0);
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition SM1 : ST.tmpl := ST.TM 0xd14b0 SM1_regs SM1_kn 34%nat (add (ELit 6665789243392) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition OL_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (ELit 5); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (ELit 174592); (add vF (ELit 608)); ((V 22)); (V 36); (V 37); (V 38); (V 39); (V 40)].
Definition OL_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KFill (SA (mul 256 vF11) 2147450956) (ELit 63) 248;
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition OL : ST.tmpl := ST.TM 0xd1754 OL_regs OL_kn 41%nat (add (sub (ELit 4054449127424) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition C2_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (ELit 5); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 36); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 37); (V 38); (V 39); (V 40)].
Definition C2_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 24) 1 62;
   KWord (SA vF 1104) 2 (ELit 0);
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition C2 : ST.tmpl := ST.TM 0xd1898 C2_regs C2_kn 41%nat (add (sub (ELit 3985729650688) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xd18a8); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 36); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 37); (V 38); (V 39); (V 40)].
Definition R2_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 24) 1 62;
   KWord (SA vF 1104) 2 (ELit 0);
   KUnk (SA vF 608) (mul 8 (V 24));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R2 : ST.tmpl := ST.TM 0xd18a8 R2_regs R2_kn 41%nat (add (sub (ELit 3917010173952) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition SM2_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (add (add vF (ELit 608)) (mul 8 (sub (V 24) (V 25)))); ((V 24)); (V 30); ((V 24)); (mul 281474976710656 (V 24)); (sub (ELit 63) (sub (V 24) (V 25)));
   (add (add vF (ELit 608)) (mul 8 (sub (V 24) (V 25)))); ((V 25)); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 31); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 32); (V 33); (V 34); (V 35)].
Definition SM2_kn : list kentry :=
  [KRange (add (mul 8 (V 24)) (mul (-8) (V 25))) 0 488;
   KRange (V 22) 1 4;
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
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition SM2 : ST.tmpl := ST.TM 0xd18e0 SM2_regs SM2_kn 36%nat (add (sub (ELit 3848290697216) (mul 687194767360 (V 22))) (V 25)) 0%nat.

(* [comment removed for export] *)
Definition CL_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 38); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 39); (V 40); (V 41); (V 42)].
Definition CL_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 25) 0 62;
   KWord (SA vF 1104) 2 (V 25);
   KUnk (SA vF 608) (mul 8 (V 25));
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition CL : ST.tmpl := ST.TM 0xd1630 CL_regs CL_kn 43%nat (add (sub (ELit 3779571220480) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition RL_regs : list expr :=
  [ELit 0; (ELit 0xd1644); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); ((V 25)); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 36); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 37); (V 38); (V 39); (V 40)].
Definition RL_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 25) 0 1;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition RL : ST.tmpl := ST.TM 0xd1644 RL_regs RL_kn 41%nat (add (sub (ELit 3710851743744) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition NX_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (ELit 5); (V 27);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (ELit (-8)); (add (mul 256 vF11) (ELit 2147450880)); (vX); (mul 8 (V 24)); (sub (ELit (-1)) (ELit 174592)); (ELit 2147450880);
   (V 36); (add vF (ELit 608)); ((V 22)); (ELit 174592); (V 37); (V 38); (V 39); (V 40)].
Definition NX_kn : list kentry :=
  [KRange (V 22) 1 4;
   KRange (V 24) 0 62;
   KWord (SA vF 528) 2 (V 24);
   KUnk (SA vF 32) (mul 8 (V 24));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KZero (SA (mul 256 vF11) 2147450956) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 56) 8 ((V 24));
   KWord (SA vSPA 24) 8 (mul 281474976710656 (V 24));
   KWord (SA vSPA 8) 8 (sub (ELit (-1)) (add vF (ELit 32)));
   KWord (SA vSPA 16) 8 (sub (ELit (-1)) (add vF (ELit 608)));
   KWord (SA vSPA 72) 8 (mul 8 (V 24));
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition NX : ST.tmpl := ST.TM 0xd164c NX_regs NX_kn 41%nat (add (sub (ELit 3642132267008) (mul 687194767360 (V 22))) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition NM_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (V 28); ((V 22)); (sub (ELit (-1)) vX); (ELit 1); (V 29); (vF);
   (add vX (ELit 496)); (add vX8 (ELit 2147450942)); (V 30); (add (mul 256 vF11) (ELit 2147450880)); (vX); (V 31); (V 32); (ELit 2147450880);
   (ELit 1); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39)].
Definition NM_kn : list kentry :=
  [KRange (V 22) 1 62;
   KRange (V 23) 0 62;
   KWord (SA vF 528) 2 (V 23);
   KUnk (SA vF 32) (mul 8 (V 23));
   KZero (SA (mul 256 vF11) 2147450884) (ELit 63);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KWord (SA vSPA 48) 8 (vF);
   KWord (SA vSPA 64) 8 (vF);
   KWord (SA vSPA 112) 8 (vF);
   KWord (SA vSPA 80) 8 (add vF (ELit 32));
   KWord (SA vSPA 32) 8 (add vX8 (ELit 2147450942));
   KWord (SA vSPA 40) 8 (add vX (ELit 496));
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition NM : ST.tmpl := ST.TM 0xd1584 NM_regs NM_kn 40%nat (add (ELit 343597383680) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition XSF_regs : list expr :=
  [ELit 0; (ELit 0xd1dd8); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (vF); (ELit 1184); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (add (mul 256 vF11) (ELit 2147450880)); (V 34); (V 35); (V 36); (ELit 2147450880);
   ((V 23)); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition XSF_kn : list kentry :=
  [KRange (V 23) 0 1;
   KWord (SA vF 0) 8 (ELit 0x45e0360e);
   KWord (SA vF 2040) 8 vFLG;
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KUnk (SA vF 0) (ELit 2048);
   KWord (SA vF 2040) 8 vFLG;
   KWr (SA (mul 256 vF11) 2147450880) (ELit 256);
   KUnk (SA (mul 256 vF11) 2147450880) (ELit 256);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vF 0) (ELit 2048);
   KDisj (SA vF 0) (ELit 2048) (SA vX 0) (ELit 504);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 256 vF11) 2147450880) (ELit 256) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KRange vSPA 140728898424832 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 224)) 0 31;
   KWr (SA vSPA (-4096)) (ELit 4320);
   KUnk (SA vSPA (-4096)) (ELit 4320);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vF 0) (ELit 2048);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4096)) (ELit 4096) (SA vSP (-224)) (ELit 224);
   KDisj (SA vSPA 0) (ELit 120) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KDisj (SA vSPA (-4096)) (ELit 4320) (SA (mul 256 vF11) 2147450880) (ELit 256);
   KWord (SA vSPA 88) 8 (ELit 5);
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
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425088 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4352)) (ELit 4352);
   KUnk (SA vSP (-4352)) (ELit 4352);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (sub vX8 (mul 8 vXH)) 4 4;
   KRange vXH 0x19c40 0x1fffffdfffe;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KWr (SA (mul 8 vXH) 2147450880) (ELit 72);
   KUnk (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition XSF : ST.tmpl := ST.TM 0x507e4 XSF_regs XSF_kn 44%nat (ELit 0) 0%nat.

Definition LMBB : SP.prog := SP.PGCA 22 [T0; C1; R1; SM1; OL; C2; R2; SM2; CL; RL; NX; NM] [XSF] [(vSP, -4352, ELit 4352); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (vF, 0, ELit 2048); (mul 256 vF11, 2147450880, ELit 256); (vSPA, -4096, ELit 4320)] [] [(AMHB.MCAH 0xd1448); (AMHB.MCAH 0xd18a8); LADSB] [(vSP, -4352, ELit 4352); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4); (vF, 0, ELit 2048); (mul 256 vF11, 2147450880, ELit 256); (vSPA, -4096, ELit 4320)].
