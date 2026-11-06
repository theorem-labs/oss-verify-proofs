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
Definition HI64B_IT : itab := APC.mk_itab_ranges SG [(0xd097c, 224%nat)].
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
Definition vX8 := V 16.
Definition vSP := mul 16 vSP16.
Definition vX := mul 8 vX8.
Definition vTR := add (mul 16 vSP16) (ELit 15).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (vX); (vTR); (V 21); (V 22); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62;
   KRange vSP16 8795556151297 0x80000000000;
   KWr (SA vSP (-16)) (ELit 16);
   KWr (SA vSP 15) (ELit 1);
   KZero (SA (mul 2 vSP16) 2147450881) (ELit 1);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KDisj (SA vSP (-16)) (ELit 64) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TMG 0xd097c T0_regs T0_kn 31%nat (ELit 4096) 0%nat [ST.GA 7 [vX; (V 17)]].

(* [comment removed for export] *)
Definition G1_regs : list expr :=
  [ELit 0; (vRA); (spo (-16)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (vS0); (vS1); ((V 17)); (vTR); (V 21); (sub (ELit (-1)) vX); (ELit 2147450880); (V 22);
   (ELit 1); (V 23); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 24); (V 25); (V 26); (V 27)].
Definition G1_kn : list kentry :=
  [KRange (V 17) 1 18446744073709551615;
   KWord (SA vX 496) 2 (ELit 1);
   KWord (SA vSP 15) 1 (ELit 0);
   KWord (SA vSP (-8)) 8 vRA;
   KRange vSP16 8795556151297 0x80000000000;
   KWr (SA vSP (-16)) (ELit 16);
   KWr (SA vSP 15) (ELit 1);
   KZero (SA (mul 2 vSP16) 2147450881) (ELit 1);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KDisj (SA vSP (-16)) (ELit 64) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition G1 : ST.tmpl := ST.TMG 0xd0a14 G1_regs G1_kn 28%nat (ELit 3072) 0%nat [ST.GA 7 [vX; (ELit 1)]].

(* [comment removed for export] *)
Definition G2_regs : list expr :=
  [ELit 0; (vRA); (spo (-16)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vS0); (vS1); (vX); (vTR); ((V 18)); (add vX (mul 8 (add (V 17) (ELit (-2))))); (ELit 2147450880); (sub (ELit (-1)) vX);
   ((V 17)); (V 22); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 23); (V 24); (V 25); (V 26)].
Definition G2_kn : list kentry :=
  [KRange (V 18) 1 18446744073709551615;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 2 62;
   KWord (SA vSP (-8)) 8 vRA;
   KRange vSP16 8795556151297 0x80000000000;
   KWr (SA vSP (-16)) (ELit 16);
   KWr (SA vSP 15) (ELit 1);
   KZero (SA (mul 2 vSP16) 2147450881) (ELit 1);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KDisj (SA vSP (-16)) (ELit 64) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition G2 : ST.tmpl := ST.TMG 0xd0b1c G2_regs G2_kn 27%nat (ELit 3072) 0%nat [ST.GA 7 [vX; (V 17)]].

(* [comment removed for export] *)
Definition NZ_regs : list expr :=
  [ELit 0; (vRA); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); (vX); (vTR); (V 23); ((V 18)); (ELit 2147450880); (sub (ELit (-1)) vX);
   (V 24); (add (mul 2 vSP16) (ELit 2147450881)); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 25); (V 26); (V 27); (V 28)].
Definition NZ_kn : list kentry :=
  [KAlign (V 18) 8;
   KRange (V 18) 0 472;
   KWord (SA vSP 15) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 3 62;
   KWord (SA vSP (-8)) 8 vRA;
   KRange vSP16 8795556151297 0x80000000000;
   KWr (SA vSP (-16)) (ELit 16);
   KWr (SA vSP 15) (ELit 1);
   KZero (SA (mul 2 vSP16) 2147450881) (ELit 1);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KDisj (SA vSP (-16)) (ELit 64) (SA vX 0) (ELit 504);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition NZ : ST.tmpl := ST.TMG 0xd0c10 NZ_regs NZ_kn 29%nat ((V 18)) 0%nat [ST.GA 7 [vX; (V 17)]].

(* [comment removed for export] *)
Definition X0_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition X0_kn : list kentry :=
  [KWord (SA vSP 15) 1 (V 18);
   KRange (V 18) 0 1;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62].
Definition X0 : ST.tmpl := ST.TMG 0xd09d4 X0_regs X0_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 17)]].

(* [comment removed for export] *)
Definition X1_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition X1_kn : list kentry :=
  [KWord (SA vSP 15) 1 (V 18);
   KRange (V 18) 0 1;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62].
Definition X1 : ST.tmpl := ST.TMG 0xd0ac8 X1_regs X1_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 17)]].

(* [comment removed for export] *)
Definition X2_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition X2_kn : list kentry :=
  [KWord (SA vSP 15) 1 (V 18);
   KRange (V 18) 0 1;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62].
Definition X2 : ST.tmpl := ST.TMG 0xd0c74 X2_regs X2_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 17)]].

Definition HI64B : SP.prog := SP.PGCA 17 [T0; G1; G2; NZ] [X0; X1; X2] [(vSP, -16, ELit 16); (vSP, 15, ELit 1)] [SX.SpCmpV 0xd097c BC_LTU (EVar 17) (ELit 2); SX.SpHav 0xd0a7c 11; SX.SpHav 0xd0b84 17; SX.SpAl 0xd0c0c] [] [(vSP, -16, ELit 16); (vSP, 15, ELit 1); (mul 2 vSP16, 2147450881, ELit 1); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)].
