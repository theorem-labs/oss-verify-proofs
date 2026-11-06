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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition SLOWBBE_IT : itab := APC.mk_itab_ranges SG [(0xcba2c, 2514%nat)].
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
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (V 29); (V 30); (ELit 0); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); (V 36); (V 37); (V 38);
   (V 39); (V 40); (vV); (vFK); (V 41); (V 42); (V 43); (V 44)].
Definition T0_kn : list kentry :=
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
Definition T0 : ST.tmpl := ST.TM 0xcd2b4 T0_regs T0_kn 45%nat (ELit 83886080) 0%nat.

(* [comment removed for export] *)
Definition XSS_regs : list expr :=
  [ELit 0; (ELit 0xcde24); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (add (mul 128 vF10) (ELit 2147450880)); (ELit 128); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vFK); (ELit 2147450880); (add (mul 128 vF10) (ELit 2147450880)); ((V 24)); ((V 25)); (V 35);
   (V 36); (V 37); (V 38); (vFK); (V 39); (V 40); (V 41); (V 42)].
Definition XSS_kn : list kentry :=
  [KUnk (SA vV 0) (ELit 8);
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
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608)].
Definition XSS : ST.tmpl := ST.TM 0x694c4 XSS_regs XSS_kn 43%nat (ELit 0) 0%nat.

Definition SLOWBBE : SP.prog := SP.PGCA 24 [T0] [XSS] [(vSP, -4880, ELit 4880); (vV, 0, ELit 8); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [SX.SpHav 0xcd44c 17; SX.SpHav 0xcd480 6] [] [(vSP, -4880, ELit 4880); (mul 2 vSP16, 2147450270, ELit 610); (vF, 0, vN); (vF8, 2147450880, vFG); (vV, 0, ELit 8); (vV8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4); (vFK, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)].
