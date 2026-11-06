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
Definition B2F_IT : itab := APC.mk_itab_ranges SG [(0xb13f8, 21%nat)].
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
Definition vT8 := V 16.
Definition vDOC8 := V 17.
Definition vB8 := V 18.
Definition vLEN := V 19.
Definition vI8 := V 20.
Definition vN := V 21.
Definition vTB8 := V 22.
Definition vCAPT := V 23.
Definition vSB8 := V 24.
Definition vCAPS := V 25.
Definition vOC8 := V 26.
Definition vIA8 := V 27.
Definition vF11 := V 28.
Definition vPB := V 29.
Definition vFLAG := V 30.
Definition vBO := V 31.
Definition vBG := V 32.
Definition vIG := V 33.
Definition vSG := V 34.
Definition vSP := mul 16 vSP16.
Definition vTHIS := mul 8 vT8.
Definition vDOC := mul 8 vDOC8.
Definition vBUF := add (mul 8 vB8) vBO.
Definition vIDX := mul 8 vI8.
Definition vTBASE := mul 8 vTB8.
Definition vSBASE := mul 8 vSB8.
Definition vOCB := mul 8 vOC8.
Definition vIAB := mul 8 vIA8.
Definition vF := mul 2048 vF11.
Definition vSHF := add (mul 256 vF11) (ELit 2147450880).
Definition vSPA := sub (add vSP (ELit (-416))) (mul 16 vPB).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (V 36); (vSPA); (vGP); (vTP); (V 37); (V 38); (V 39);
   (vSP); (vSPA); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45);
   (V 46); (V 47); (V 48); (V 49); (V 50); (V 51); (V 52); (V 53);
   (V 54); (V 55); (V 56); (V 57); (V 58); (V 59); (V 60); (V 61)].
Definition T0_kn : list kentry :=
  [KRange (V 35) 0 63;
   KWord (SA vSPA 272) 8 (V 35);
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
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vPB 0 1].
Definition T0 : ST.tmpl := ST.TM 0xb13f8 T0_regs T0_kn 62%nat (ELit 10) 1%nat.

(* [comment removed for export] *)
Definition XRET_regs : list expr :=
  [ELit 0; vRA; (vSP); vGP; vTP; (V 36); (V 37); (V 38);
   vS0; vS1; ((V 35)); (V 39); (V 40); (V 41); (V 42); (V 43);
   (V 44); (V 45); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 46); (V 47); (V 48); (V 49)].
Definition XRET_kn : list kentry :=
  [KRange (V 35) 0 63].
Definition XRET : ST.tmpl := ST.TM 0xb1448 XRET_regs XRET_kn 50%nat (ELit 0) 0%nat.

Definition B2F : SP.prog := SP.PGCA 35 [T0] [XRET] [] [] [] [(vSP, -104, ELit 104); (vSPA, 272, ELit 8)].
