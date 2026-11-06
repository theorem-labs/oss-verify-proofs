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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import P5A_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition PDCA_IT : itab := APC.mk_itab_ranges SG [(0xc4aa4, 359%nat); (0xc5be4, 1%nat)].
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
Definition vEXP := V 18.
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vX); (vEXP); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xc4aa4 T0_regs T0_kn 33%nat (ELit 102400) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xc4ae0); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (vS1); ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vEXP); (ELit 2147450880); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition R1_kn : list kentry :=
  [KRange (V 20) 0 1;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R1 : ST.tmpl := ST.TM 0xc4ae0 R1_regs R1_kn 35%nat (ELit 92160) 0%nat.

(* [comment removed for export] *)
Definition SB_regs : list expr :=
  [ELit 0; (V 22); (spo (-64)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vX); (add vX (ELit 496)); (add vX (mul 8 (sub (V 19) (V 20)))); (add vX8 (ELit 2147450942)); ((V 19)); ((V 21)); (sub (ELit 64) (V 21)); (add (add vX8 (sub (V 19) (V 20))) (ELit 2147450880));
   (add vX (mul 8 (sub (V 19) (V 20)))); ((V 20)); (vEXP); (ELit 2147450880); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition SB_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 61;
   KRange (V 21) 1 63;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition SB : ST.tmpl := ST.TM 0xc4b28 SB_regs SB_kn 30%nat (add (ELit 71680) (V 20)) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 20); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (ELit 496)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (vEXP); (ELit 2147450880); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition J1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition J1 : ST.tmpl := ST.TM 0xc4b98 J1_regs J1_kn 36%nat (ELit 61440) 0%nat.

(* [comment removed for export] *)
Definition JM_regs : list expr :=
  [ELit 0; (V 21); (spo (-64)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (add vX (ELit 496)); (add (V 20) (V 19)); (ELit 62); ((V 19)); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vEXP); (ELit 2147450880); (add vX8 (ELit 2147450942)); ((V 20)); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition JM_kn : list kentry :=
  [KRange (V 20) 1 61;
   KRange (add (V 20) (V 19)) 2 62;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition JM : ST.tmpl := ST.TM 0xc4bc8 JM_regs JM_kn 34%nat (ELit 56320) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xc4bdc); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (ELit 496)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (mul 8 (V 20)); (ELit 2147450880); (add vX8 (ELit 2147450942)); ((V 20)); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition R2_kn : list kentry :=
  [KRange (V 20) 1 61;
   KRange (add (V 20) (V 19)) 2 62;
   KUnk (SA vX 0) (ELit 498);
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R2 : ST.tmpl := ST.TM 0xc4bdc R2_regs R2_kn 36%nat (ELit 51200) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0xc4bec); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (ELit 496)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (mul 8 (V 20)); (ELit 2147450880); (add vX8 (ELit 2147450942)); ((V 20)); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition R3_kn : list kentry :=
  [KRange (V 20) 1 61;
   KRange (add (V 20) (V 19)) 2 62;
   KZero (SA vX 0) (mul 8 (V 20));
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition R3 : ST.tmpl := ST.TM 0xc4bec R3_regs R3_kn 36%nat (ELit 46080) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 20); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (ELit 496)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (ELit 2147450880); (V 33); (V 34); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition J2_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition J2 : ST.tmpl := ST.TM 0xc4c00 J2_regs J2_kn 39%nat (ELit 40960) 0%nat.

(* [comment removed for export] *)
Definition NZ_regs : list expr :=
  [ELit 0; (V 21); (spo (-64)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (add vX (ELit 496)); (add vX (mul 8 (V 20))); (V 25); ((V 19)); (V 26); (add (V 19) (ELit (-1))); (add vX (mul 8 (V 20)));
   ((V 20)); (V 27); (V 28); (ELit 2147450880); (V 29); (V 30); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition NZ_kn : list kentry :=
  [KRange (V 20) 0 59;
   KRange (sub (V 19) (V 20)) 3 62;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 3 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425232 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4496)) (ELit 4496);
   KUnk (SA vSP (-4496)) (ELit 4496);
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
   KDisj (SA vSP (-4496)) (ELit 4496) (SA vX 0) (ELit 504);
   KRange vEXP 0 2147483647;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition NZ : ST.tmpl := ST.TM 0xc4e10 NZ_regs NZ_kn 35%nat (add (ELit 10240) (V 20)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition XR_kn : list kentry :=
  [KZero (SA vX8 2147450880) (ELit 63);
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition XR : ST.tmpl := ST.TM 0xc4fb8 XR_regs XR_kn 35%nat (ELit 0) 0%nat.

Definition PDCA : SP.prog := SP.PGH 19 [T0; R1; SB; J1; JM; R2; R3; J2; NZ] [XR] [(vSP, -4496, ELit 4496); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63)] [SX.SpHav 0xc4ce8 13; SX.SpHav 0xc4de0 10; SX.SpHav 0xc4f14 10] [P5SA; (AMH.MVAH 0xc4bdc); (AMH.MSAH 0 0xc4bec)] (Some [(vSP, -4496, ELit 4496); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4)]) (Some (vSP)) [(vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72)] [].
