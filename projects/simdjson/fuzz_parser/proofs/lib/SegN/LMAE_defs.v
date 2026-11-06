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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition LMAE_IT : itab := APC.mk_itab_ranges SG [(0xc5c3c, 1065%nat)].
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
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (ELit 175424); (ELit 5); (V 22); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xc5c3c T0_regs T0_kn 31%nat (ELit 4096) 0%nat.

(* [comment removed for export] *)
Definition T1_regs : list expr :=
  [ELit 0; (V 20); (sub vSP (add (ELit 256) (V 19))); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vSP); (sub vSP (add (ELit 256) (V 19))); (vX); (ELit 175424); (ELit 5); (V 24); (V 25); (V 26);
   (V 27); (V 28); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition T1_kn : list kentry :=
  [KRange (V 19) 0 31;
   KAlign (V 19) 16;
   KWord (SA vSP (-256)) 8 (ELit 0);
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
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition T1 : ST.tmpl := ST.TM 0xc5c84 T1_regs T1_kn 33%nat (ELit 100) 0%nat.

(* [comment removed for export] *)
Definition XSM_regs : list expr :=
  [ELit 0; (ELit 0xc5cb4); (sub vSP (add (ELit 256) (V 19))); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vSP); (sub vSP (add (ELit 256) (V 19))); (ELit 1184); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vS2); (vS3); (vS4); (ELit 175424); (vS6); (vS7);
   (vS8); (ELit 5); (ELit 2147450880); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition XSM_kn : list kentry :=
  [KRange (V 19) 0 31;
   KAlign (V 19) 16;
   KWord (SA (sub vSP (add (ELit 256) (V 19))) 120) 8 vX;
   KWord (SA vSP (-256)) 8 (ELit 0);
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
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vTP 0x642e70 0x642e70;
   KRange vSP 140728898425120 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4384)) (ELit 4384);
   KUnk (SA vSP (-4384)) (ELit 4384);
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
   KDisj (SA vSP (-4384)) (ELit 4384) (SA vX 0) (ELit 504);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1)].
Definition XSM : ST.tmpl := ST.TM 0x50834 XSM_regs XSM_kn 34%nat (ELit 0) 0%nat.

Definition LMAE : SP.prog := SP.PGCA 18 [T0; T1] [XSM] [(vSP, -4384, ELit 4384); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63)] [] [] [(vSP, -4384, ELit 4384); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4)].
