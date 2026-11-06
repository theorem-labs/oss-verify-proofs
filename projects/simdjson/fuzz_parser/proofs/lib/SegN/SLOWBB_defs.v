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
Definition SLOWBB_IT : itab := APC.mk_itab_ranges SG [(0xcba2c, 2514%nat)].
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
  [ELit 0; (ELit 0xcbab4); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (vFK); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (ELit 53); (ELit 2147450880); (vS4); (vF); (add vF vN); (vS7);
   (ELit 1); (ELit 0xa0000002e); (vV); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition T0_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
   KZero (SA (mul 128 vF10) 2147450880) (ELit 128);
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
Definition T0 : ST.tmpl := ST.TM 0xcbab4 T0_regs T0_kn 38%nat (ELit 251658240) 0%nat.

(* [comment removed for export] *)
Definition JP_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (ELit 53);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (vF); (add vF vN); (vS7);
   (ELit 1); (ELit 0xa0000002e); (vV); (vFK); (V 35); (V 36); (V 37); (V 38)].
Definition JP_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
Definition JP : ST.tmpl := ST.TM 0xcbc5c JP_regs JP_kn 39%nat (ELit 247463936) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (V 27); (V 28); (ELit 53);
   (vSP); (vSPA); (add vF (V 24)); (V 29); (V 30); (ELit 2); (ELit 10); (add vF8 (V 26));
   (ELit 9); (V 31); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 25)); (add vF vN); (V 32);
   (add vF (V 24)); (V 33); (vV); (vFK); (V 34); (V 35); (V 36); (V 37)].
Definition IL_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (V 25) 0 1;
   KRange (add (V 24) (mul (-1) (V 25))) 5 1048576;
   KRange (add vN (mul (-1) (V 25))) 5 1048576;
   KRange (V 26) 0 1;
   KRange (sub (add vFO (V 25)) (mul 8 (V 26))) 0 7;
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
Definition IL : ST.tmpl := ST.TMG 0xcbe34 IL_regs IL_kn 38%nat (add (ELit 243269632) (add vN (mul (-1) (V 24)))) 0%nat [ST.GA 1 [add vF (V 25); add (V 24) (mul (-1) (V 25))]].

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (add (V 24) (mul (-1) (V 25))); (V 27); (ELit 53);
   (vSP); (vSPA); (V 28); (V 29); (V 30); (V 31); (V 32); (add vF8 (V 26));
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 25)); (add vF vN); (V 35);
   (add vF (V 24)); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition J1_kn : list kentry :=
  [KRange (V 25) 0 1;
   KRange (V 24) 1 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 1 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KRange (V 26) 0 1;
   KRange (sub (add vFO (V 25)) (mul 8 (V 26))) 0 7;
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
Definition J1 : ST.tmpl := ST.TMG 0xcc0e4 J1_regs J1_kn 41%nat (ELit 239075328) 0%nat [ST.GA 1 [add vF (V 25); add (V 24) (mul (-1) (V 25))]].

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (ELit 0x4646464646464646); (vSPA); (vGP); (vTP); (V 28); (ELit 0x8080808080808080); (ELit 0x5f5e100);
   (vSP); (vSPA); (add (sub (add vF vN) (V 24)) (ELit 7)); (ELit 0xcfcfcfcfcfcfcfd0); (V 29); (V 30); (V 31); (V 32);
   ((V 24)); (V 33); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 34);
   (add vF (V 25)); (sub (add vF vN) (V 24)); (V 35); (vFK); (add vF8 (add (V 27) (ELit 2147450880))); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff)].
Definition SW_kn : list kentry :=
  [KRange (V 24) 8 1048576;
   KRange (add vN (mul (-1) (V 24))) 2 1048576;
   KRange (add vN (add (mul (-1) (V 24)) (mul (-1) (V 25)))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 9 1048576;
   KRange (V 27) 0 0x200000;
   KRange (sub (add vFO (sub vN (V 24))) (mul 8 (V 27))) 0 7;
   KRange (V 26) 0 1;
   KRange (V 25) 1 1048576;
   KRange (add (V 25) (mul (-1) (V 26))) 1 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KWord (SA vSPA 32) 8 (vV);
   KWord (SA vSPA 40) 8 (add (V 25) (mul (-1) (V 26)));
   KWord (SA vSPA 56) 8 (add (add vF (V 25)) (ELit 1));
   KWord (SA vSPA 16) 8 (ELit 53);
   KWord (SA vSPA 24) 8 (ELit 46);
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
Definition SW : ST.tmpl := ST.TMG 0xcc3cc SW_regs SW_kn 36%nat (add (ELit 234881024) ((V 24))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (add vN (add (mul (-1) (V 24)) (mul (-1) (V 25)))) (ELit (-1))]].

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (V 27); (V 28); (ELit 53);
   (vSP); (vSPA); (add vF (V 24)); (V 29); (V 30); (ELit 9); (V 31); (ELit (-1));
   (ELit 10); (V 32); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 33);
   (add vF (V 25)); (add vF (V 24)); (V 34); (vFK); (V 35); (V 36); (V 37); (V 38)].
Definition FL_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vN (mul (-1) (V 24))) 1 1048576;
   KRange (sub (V 24) (V 25)) 1 1048576;
   KRange (sub vN (V 25)) 2 1048576;
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
Definition FL : ST.tmpl := ST.TMG 0xcc838 FL_regs FL_kn 39%nat (add (ELit 230686720) (sub vN (V 24))) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (V 24) (sub (ELit (-1)) (V 25))]].

(* [comment removed for export] *)
Definition E1A_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (add vSPA (ELit 104)); (ELit 0); (ELit 32); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 33); (add vF vN); (V 34);
   (V 35); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition E1A_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
Definition E1A : ST.tmpl := ST.TM 0xcbefc E1A_regs E1A_kn 41%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E1B_regs : list expr :=
  [ELit 0; (ELit 835328); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E1B_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
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
Definition E1B : ST.tmpl := ST.TM 0xcbf00 E1B_regs E1B_kn 43%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E1C_regs : list expr :=
  [ELit 0; (ELit 835344); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E1C_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KZero (SA vSPA 72) (ELit 27);
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
Definition E1C : ST.tmpl := ST.TM 0xcbf10 E1C_regs E1C_kn 43%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition E2A_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (add vSPA (ELit 104)); (ELit 0); (ELit 32); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 33); (add vF vN); (V 34);
   (V 35); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition E2A_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
Definition E2A : ST.tmpl := ST.TM 0xcc4ec E2A_regs E2A_kn 41%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E2B_regs : list expr :=
  [ELit 0; (ELit 836848); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E2B_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
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
Definition E2B : ST.tmpl := ST.TM 0xcc4f0 E2B_regs E2B_kn 43%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E2C_regs : list expr :=
  [ELit 0; (ELit 836864); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E2C_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KZero (SA vSPA 72) (ELit 27);
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
Definition E2C : ST.tmpl := ST.TM 0xcc500 E2C_regs E2C_kn 43%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition E3A_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (add vSPA (ELit 104)); (ELit 0); (ELit 32); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 33); (add vF vN); (V 34);
   (V 35); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition E3A_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
Definition E3A : ST.tmpl := ST.TM 0xcc114 E3A_regs E3A_kn 41%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E3B_regs : list expr :=
  [ELit 0; (ELit 835864); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E3B_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
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
Definition E3B : ST.tmpl := ST.TM 0xcc118 E3B_regs E3B_kn 43%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E3C_regs : list expr :=
  [ELit 0; (ELit 835880); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E3C_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KZero (SA vSPA 72) (ELit 27);
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
Definition E3C : ST.tmpl := ST.TM 0xcc128 E3C_regs E3C_kn 43%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition E4A_regs : list expr :=
  [ELit 0; (V 24); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (add vSPA (ELit 104)); (ELit 0); (ELit 32); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 33); (add vF vN); (V 34);
   (V 35); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition E4A_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
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
Definition E4A : ST.tmpl := ST.TM 0xccd84 E4A_regs E4A_kn 41%nat (ELit 176160768) 0%nat.

(* [comment removed for export] *)
Definition E4B_regs : list expr :=
  [ELit 0; (ELit 839048); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E4B_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
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
Definition E4B : ST.tmpl := ST.TM 0xccd88 E4B_regs E4B_kn 43%nat (ELit 171966464) 0%nat.

(* [comment removed for export] *)
Definition E4C_regs : list expr :=
  [ELit 0; (ELit 839064); (vSPA); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 35); (add vF vN); (V 36);
   (V 37); (V 38); (vV); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition E4C_kn : list kentry :=
  [KZero (SA vSPA 104) (ELit 32);
   KZero (SA vSPA 72) (ELit 27);
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
Definition E4C : ST.tmpl := ST.TM 0xccd98 E4C_regs E4C_kn 43%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition XN_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (add (V 24) (mul (-1) (V 25))); (V 26); (ELit 53);
   (vSP); (vSPA); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 25)); (add vF vN); (V 35);
   (add vF (V 24)); (V 36); (vV); (vFK); (V 37); (V 38); (V 39); (V 40)].
Definition XN_kn : list kentry :=
  [KRange (V 25) 0 1;
   KRange (V 24) 1 1048576;
   KRange (add (V 24) (mul (-1) (V 25))) 1 1048576;
   KRange (add vN (mul (-1) (V 24))) 0 1048576;
   KWord (SA vSPA 40) 8 (add (V 24) (mul (-1) (V 25)));
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
Definition XN : ST.tmpl := ST.TMG 0xcc510 XN_regs XN_kn 41%nat (ELit 0) 0%nat [ST.GA 1 [add vF (V 25); add (V 24) (mul (-1) (V 25))]].

(* [comment removed for export] *)
Definition XF_regs : list expr :=
  [ELit 0; (ELit 46); (vSPA); (vGP); (vTP); (V 27); (V 28); (ELit 53);
   (vSP); (vSPA); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (add vF (V 26)); (add vF vN); (V 37);
   (add vF (V 25)); (add vF (V 24)); (V 38); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition XF_kn : list kentry :=
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
Definition XF : ST.tmpl := ST.TMG 0xcc888 XF_regs XF_kn 43%nat (ELit 0) 0%nat [ST.GA 1 [add vF (V 26); add (V 25) (mul (-1) (V 26))]; ST.GA 2 [add vF (V 25)]; ST.GA 1 [add (add vF (V 25)) (ELit 1); add (V 24) (sub (ELit (-1)) (V 25))]].

(* [comment removed for export] *)
Definition XE_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (V 29); (V 30); (ELit 0); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vV); (vFK); (V 41); (V 42); (V 43); (V 44)].
Definition XE_kn : list kentry :=
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
Definition XE : ST.tmpl := ST.TM 0xcd2b4 XE_regs XE_kn 45%nat (ELit 0) 0%nat.

Definition SLOWBB : SP.prog := SP.PGCA 24 [T0; JP; IL; J1; SW; FL; E1A; E1B; E1C; E2A; E2B; E2C; E3A; E3B; E3C; E4A; E4B; E4C] [XN; XF; XE] [(vSP, -4880, ELit 4880); (vV, 0, ELit 8); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [] [(AMHBS.MSAGS 0 0xcbf00); (AMHBS.MSAGS 0 0xcbf10); (AMHBS.MSAGS 0 0xcc4f0); (AMHBS.MSAGS 0 0xcc500); (AMHBS.MSAGS 0 0xcc118); (AMHBS.MSAGS 0 0xcc128); (AMHBS.MSAGS 0 0xccd88); (AMHBS.MSAGS 0 0xccd98)] [(vSP, -4880, ELit 4880); (mul 2 vSP16, 2147450270, ELit 610); (vF, 0, vN); (vF8, 2147450880, vFG); (vV, 0, ELit 8); (vV8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)].
