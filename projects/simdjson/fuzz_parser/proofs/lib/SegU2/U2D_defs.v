(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.simdjson.fuzz_parser.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition U2D_IT : itab := APC.mk_itab_ranges SG [(0x29abc, 11772%nat)].
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
Definition vTHIS := V 16.
Definition vDOC := V 17.
Definition vBUF := V 18.
Definition vLEN := V 19.
Definition vIDX := V 20.
Definition vN := V 21.
Definition vTBASE := V 22.
Definition vCAPT := V 23.
Definition vSBASE := V 24.
Definition vCAPS := V 25.
Definition vOCB := V 26.
Definition vIAB := V 27.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition DA_regs : list expr :=
  [ELit 0; (V 29); (spo (-368)); (vGP); (vTP); (V 30); (V 31); (V 32);
   (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40);
   (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48);
   (V 49); (V 50); (V 51); (V 52); (V 53); (V 54); (V 55); (V 56)].
Definition DA_kn : list kentry :=
  [KWord (SA vSP (-304)) 8 vTHIS;
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
   KRange vN 1 1048512;
   KRange vCAPT 4 16777216;
   KRange (sub vCAPT vN) 3 16777216;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vIDX 16 0x7fffff7fffff;
   KAlign vIDX 16;
   KRange (add vIDX (add (mul 4 vN) (ELit 12))) 16 0x7fffff800000;
   KRange vTBASE 16 0x7fffff7fffff;
   KAlign vTBASE 16;
   KRange (add vTBASE (mul 8 vCAPT)) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSP (-368)) (ELit 368) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-368)) (ELit 368) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vSP (-368)) (ELit 368) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vTHIS 0) (ELit 96) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vTHIS 0) (ELit 96) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vTBASE 0) (mul 8 vCAPT);
   KRange vDOC 0x7fff00000000 0xfffffffffffffff0;
   KAlign vDOC 8;
   KDisj (SA vSP (-368)) (ELit 368) (SA vDOC 0) (ELit 16);
   KDisj (SA vDOC 0) (ELit 16) (SA vTHIS 0) (ELit 96);
   KDisj (SA vDOC 0) (ELit 16) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vDOC 0) (ELit 16) (SA vTBASE 0) (mul 8 vCAPT);
   KWr (SA vSP (-368)) (ELit 368);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTBASE 0) (mul 8 vCAPT);
   KImg 0x10000 0x2550c].
Definition DA : ST.tmpl := ST.TM 0x29f04 DA_regs DA_kn 57%nat (ELit 10) 0%nat.

(* [comment removed for export] *)
Definition DB_regs : list expr :=
  [ELit 0; (V 29); (spo (-368)); (vGP); (vTP); (V 30); (V 31); (V 32);
   ((V 28)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47);
   (V 48); (V 49); (V 50); (V 51); (V 52); (V 53); (V 54); (V 55)].
Definition DB_kn : list kentry :=
  [KRange (V 28) 0 63;
   KWord (SA vSP (-304)) 8 vTHIS;
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
   KRange vN 1 1048512;
   KRange vCAPT 4 16777216;
   KRange (sub vCAPT vN) 3 16777216;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vIDX 16 0x7fffff7fffff;
   KAlign vIDX 16;
   KRange (add vIDX (add (mul 4 vN) (ELit 12))) 16 0x7fffff800000;
   KRange vTBASE 16 0x7fffff7fffff;
   KAlign vTBASE 16;
   KRange (add vTBASE (mul 8 vCAPT)) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSP (-368)) (ELit 368) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-368)) (ELit 368) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vSP (-368)) (ELit 368) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vTHIS 0) (ELit 96) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vTHIS 0) (ELit 96) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vTBASE 0) (mul 8 vCAPT);
   KRange vDOC 0x7fff00000000 0xfffffffffffffff0;
   KAlign vDOC 8;
   KDisj (SA vSP (-368)) (ELit 368) (SA vDOC 0) (ELit 16);
   KDisj (SA vDOC 0) (ELit 16) (SA vTHIS 0) (ELit 96);
   KDisj (SA vDOC 0) (ELit 16) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vDOC 0) (ELit 16) (SA vTBASE 0) (mul 8 vCAPT);
   KWr (SA vSP (-368)) (ELit 368);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTBASE 0) (mul 8 vCAPT);
   KImg 0x10000 0x2550c].
Definition DB : ST.tmpl := ST.TM 0x2d35c DB_regs DB_kn 56%nat (ELit 10) 0%nat.

(* [comment removed for export] *)
Definition DC_regs : list expr :=
  [ELit 0; (V 30); (spo (-368)); (vGP); (vTP); (V 31); (V 32); (V 33);
   ((V 28)); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40);
   (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48);
   (V 49); (V 50); (V 51); (V 52); (V 53); (V 54); (V 55); (V 56)].
Definition DC_kn : list kentry :=
  [KRange (V 28) 0 63;
   KWord (SA vSP (-328)) 8 (add vTBASE (V 29));
   KRange (V 29) 8 24;
   KAlign (V 29) 8;
   KWord (SA vSP (-320)) 8 (add vIDX (ELit 4));
   KWord (SA vSP (-304)) 8 vTHIS;
   KWord (SA vTHIS 8) 4 vN;
   KWord (SA vTHIS 16) 8 vIDX;
   KWord (SA vTHIS 88) 8 vDOC;
   KWord (SA vDOC 0) 8 vTBASE;
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
   KRange vN 1 1048512;
   KRange vCAPT 4 16777216;
   KRange (sub vCAPT vN) 3 16777216;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vIDX 16 0x7fffff7fffff;
   KAlign vIDX 16;
   KRange (add vIDX (add (mul 4 vN) (ELit 12))) 16 0x7fffff800000;
   KRange vTBASE 16 0x7fffff7fffff;
   KAlign vTBASE 16;
   KRange (add vTBASE (mul 8 vCAPT)) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSP (-368)) (ELit 368) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-368)) (ELit 368) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vSP (-368)) (ELit 368) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vTHIS 0) (ELit 96) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vTHIS 0) (ELit 96) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vTBASE 0) (mul 8 vCAPT);
   KRange vDOC 0x7fff00000000 0xfffffffffffffff0;
   KAlign vDOC 8;
   KDisj (SA vSP (-368)) (ELit 368) (SA vDOC 0) (ELit 16);
   KDisj (SA vDOC 0) (ELit 16) (SA vTHIS 0) (ELit 96);
   KDisj (SA vDOC 0) (ELit 16) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vDOC 0) (ELit 16) (SA vTBASE 0) (mul 8 vCAPT);
   KWr (SA vSP (-368)) (ELit 368);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTBASE 0) (mul 8 vCAPT);
   KImg 0x10000 0x2550c].
Definition DC : ST.tmpl := ST.TM 0x2d588 DC_regs DC_kn 57%nat (ELit 10) 0%nat.

(* [comment removed for export] *)
Definition XRET_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 29); (V 30); (V 31);
   vS0; vS1; ((V 28)); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 39); (V 40); (V 41); (V 42)].
Definition XRET_kn : list kentry :=
  [KRange vN 1 1048512;
   KRange vCAPT 4 16777216;
   KRange (sub vCAPT vN) 3 16777216;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vIDX 16 0x7fffff7fffff;
   KAlign vIDX 16;
   KRange (add vIDX (add (mul 4 vN) (ELit 12))) 16 0x7fffff800000;
   KRange vTBASE 16 0x7fffff7fffff;
   KAlign vTBASE 16;
   KRange (add vTBASE (mul 8 vCAPT)) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSP (-368)) (ELit 368) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-368)) (ELit 368) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vSP (-368)) (ELit 368) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vTHIS 0) (ELit 96) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vTHIS 0) (ELit 96) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vTBASE 0) (mul 8 vCAPT);
   KRange vDOC 0x7fff00000000 0xfffffffffffffff0;
   KAlign vDOC 8;
   KDisj (SA vSP (-368)) (ELit 368) (SA vDOC 0) (ELit 16);
   KDisj (SA vDOC 0) (ELit 16) (SA vTHIS 0) (ELit 96);
   KDisj (SA vDOC 0) (ELit 16) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vDOC 0) (ELit 16) (SA vTBASE 0) (mul 8 vCAPT);
   KWr (SA vSP (-368)) (ELit 368);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTBASE 0) (mul 8 vCAPT);
   KImg 0x10000 0x2550c;
   KRange (V 28) 0 63].
Definition XRET : ST.tmpl := ST.TM 0x323b8 XRET_regs XRET_kn 43%nat (ELit 0) 0%nat.

Definition U2D : SP.prog := SP.PGC 28 [DA; DB; DC] [XRET] [(vSP, -368, ELit 368); (vTHIS, 24, ELit 4); (vTBASE, 0, mul 8 vCAPT)] [] [].
