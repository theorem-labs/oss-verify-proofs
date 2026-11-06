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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition LMBNF_IT : itab := APC.mk_itab_ranges SG [(0xd0fa8, 956%nat)].
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
Definition vL0 := V 18.
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (V 21); (V 22); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vSP); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40);
   ((V 20)); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition T0_kn : list kentry :=
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
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
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
   KDisj (SA vSP (-4352)) (ELit 4352) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange (V 20) 1 1;
   KRange (sub (add vL0 (ELit 6)) (V 19)) 0 68;
   KRange vL0 0 49].
Definition T0 : ST.tmpl := ST.TMG 0xd1dd8 T0_regs T0_kn 48%nat (ELit 1) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition XR_kn : list kentry :=
  [KZero (SA vX8 2147450880) (ELit 63);
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange (V 20) 1 1;
   KRange (sub (add vL0 (ELit 6)) (V 19)) 0 68;
   KRange vL0 0 49].
Definition XR : ST.tmpl := ST.TMG 0xd1e28 XR_regs XR_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 19)]].

Definition LMBNF : SP.prog := SP.PGCA 19 [T0] [XR] [(vSP, -4352, ELit 4352); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63)] [] [] [(vSP, -4352, ELit 4352); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)].
