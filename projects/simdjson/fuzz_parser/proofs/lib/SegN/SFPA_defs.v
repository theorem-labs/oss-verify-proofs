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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import PWFA_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition SFPA_IT : itab := APC.mk_itab_ranges SG [(0xc6ce0, 56%nat); (0x96fe4, 1%nat)].
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
Definition vRB8 := V 16.
Definition vRBO := V 17.
Definition vRL := V 18.
Definition vP := V 19.
Definition vOUT8 := V 20.
Definition vRG := V 21.
Definition vSP := mul 16 vSP16.
Definition vRB := add (mul 8 vRB8) vRBO.
Definition vOUT := mul 8 vOUT8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 22); (V 23); (V 24);
   vS0; vS1; (add vRB vP); (vOUT); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition T0_kn : list kentry :=
  [KRange vTP 0x642e70 0x642e70;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB8 0xcca00 0xfffffefffff;
   KRange vRBO 0 7;
   KRange (add vRB (add vRL (ELit 1))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vRB 0) (add vRL (ELit 1));
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vRG 1 0x200000;
   KZero (SA vRB8 2147450880) vRG;
   KRange (sub (mul 8 vRG) (add (add vRBO vRL) (ELit 57))) 0 0x1000000;
   KRange vSP16 8795556151808 0x80000000000;
   KWr (SA vSP (-8192)) (ELit 8192);
   KUnk (SA vSP (-8192)) (ELit 8192);
   KZero (SA (mul 2 vSP16) 2147449856) (ELit 1024);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vRB 0) (add vRL (ELit 1));
   KRange vOUT8 0xfffc0000000 0xffffffffffe;
   KRange (sub vOUT vSP) 0 65536;
   KWr (SA vOUT 0) (ELit 8);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vOUT 0) (ELit 8);
   KZero (SA vOUT8 2147450880) (ELit 1);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0xc6ce0 T0_regs T0_kn 35%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 23); (spo (-32)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vOUT); (ELit 2147450880); (add vRB vP); (add vRB (V 22)); (add vRB (V 22)); (ELit 10); (ELit 58); (ELit 288230376218820621);
   (V 27); (V 28); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 22) vP) 0 1048576;
   KRange (sub vRL (V 22)) 0 1048576;
   KRange (V 22) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vTP 0x642e70 0x642e70;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB8 0xcca00 0xfffffefffff;
   KRange vRBO 0 7;
   KRange (add vRB (add vRL (ELit 1))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vRB 0) (add vRL (ELit 1));
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vRG 1 0x200000;
   KZero (SA vRB8 2147450880) vRG;
   KRange (sub (mul 8 vRG) (add (add vRBO vRL) (ELit 57))) 0 0x1000000;
   KRange vSP16 8795556151808 0x80000000000;
   KWr (SA vSP (-8192)) (ELit 8192);
   KUnk (SA vSP (-8192)) (ELit 8192);
   KZero (SA (mul 2 vSP16) 2147449856) (ELit 1024);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vRB 0) (add vRL (ELit 1));
   KRange vOUT8 0xfffc0000000 0xffffffffffe;
   KRange (sub vOUT vSP) 0 65536;
   KWr (SA vOUT 0) (ELit 8);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vOUT 0) (ELit 8);
   KZero (SA vOUT8 2147450880) (ELit 1);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0xc6d30 FE_regs FE_kn 33%nat (add (sub vRL (V 22)) (ELit 2)) 1%nat.

(* [comment removed for export] *)
Definition XC_regs : list expr :=
  [ELit 0; (V 23); (spo (-32)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vOUT); (ELit 2147450880); (add vRB vP); (add vRB (V 22)); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition XC_kn : list kentry :=
  [KRange (sub (V 22) vP) 0 1048576;
   KRange (sub vRL (V 22)) 0 1048576;
   KRange (V 22) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vTP 0x642e70 0x642e70;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB8 0xcca00 0xfffffefffff;
   KRange vRBO 0 7;
   KRange (add vRB (add vRL (ELit 1))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vRB 0) (add vRL (ELit 1));
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vRG 1 0x200000;
   KZero (SA vRB8 2147450880) vRG;
   KRange (sub (mul 8 vRG) (add (add vRBO vRL) (ELit 57))) 0 0x1000000;
   KRange vSP16 8795556151808 0x80000000000;
   KWr (SA vSP (-8192)) (ELit 8192);
   KUnk (SA vSP (-8192)) (ELit 8192);
   KZero (SA (mul 2 vSP16) 2147449856) (ELit 1024);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vRB 0) (add vRL (ELit 1));
   KRange vOUT8 0xfffc0000000 0xffffffffffe;
   KRange (sub vOUT vSP) 0 65536;
   KWr (SA vOUT 0) (ELit 8);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vOUT 0) (ELit 8);
   KZero (SA vOUT8 2147450880) (ELit 1);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition XC : ST.tmpl := ST.TM 0xc6d74 XC_regs XC_kn 37%nat (ELit 1) 0%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 814456); (spo (-32)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (ELit 2147450880); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition RT_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vTP 0x642e70 0x642e70;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB8 0xcca00 0xfffffefffff;
   KRange vRBO 0 7;
   KRange (add vRB (add vRL (ELit 1))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vRB 0) (add vRL (ELit 1));
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KRange vRG 1 0x200000;
   KRange (sub (mul 8 vRG) (add (add vRBO vRL) (ELit 57))) 0 0x1000000;
   KRange vSP16 8795556151808 0x80000000000;
   KWr (SA vSP (-8192)) (ELit 8192);
   KUnk (SA vSP (-8192)) (ELit 8192);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vRB 0) (add vRL (ELit 1));
   KRange vOUT8 0xfffc0000000 0xffffffffffe;
   KRange (sub vOUT vSP) 0 65536;
   KWr (SA vOUT 0) (ELit 8);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vOUT 0) (ELit 8);
   KZero (SA vOUT8 2147450880) (ELit 1);
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0xc6d78 RT_regs RT_kn 37%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 23); (V 24); (V 25);
   vS0; vS1; ((V 22)); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 33); (V 34); (V 35); (V 36)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KZero (SA vOUT8 2147450880) (ELit 1);
   KRange (V 22) 0 63;
   KImg 0x10000 0x42c40;
   KZero (SA (ELit 0) 2147471480) (ELit 1324);
   KZero (SA (ELit 0) 2147472808) (ELit 80);
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x107358) 8 (ELit 0x10fb00);
   KWord (SA (ELit 0) 0x10fb00) 4 (ELit 1);
   KWord (SA (ELit 0) 0x10b978) 4 (ELit 8388608)].
Definition X : ST.tmpl := ST.TM 0xc6db4 X_regs X_kn 37%nat (ELit 0) 0%nat.

Definition SFPA : SP.prog := SP.PGH 22 [T0; FE; XC; RT] [X] [(vSP, -8192, ELit 8192); (vOUT, 0, ELit 8)] [SX.SpCmpV 0xc6d30 BC_EQ (EVar 22) (EVar 18)] [PWFSA] (Some [(vSP, -8192, ELit 8192); (mul 2 vSP16, 2147449856, ELit 1024); (vRB, 0, add vRL (ELit 1)); (vRB8, 2147450880, vRG); (vOUT, 0, ELit 8); (vOUT8, 2147450880, ELit 1); (ELit 0, 0x10000, ELit 0x655000); (ELit 0, 164800, ELit 10592); (ELit 0, 175424, ELit 640); (ELit 0, 2147471480, ELit 1324); (ELit 0, 2147472808, ELit 80); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x107358, ELit 8); (ELit 0, 0x10fb00, ELit 4)]) (Some (vSP)) [(vRB, 0, add vRL (ELit 1)); (vRB8, 2147450880, vRG)] [].
