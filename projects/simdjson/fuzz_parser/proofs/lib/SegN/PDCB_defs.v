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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRCB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import P5BN_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SHLBN_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import HI64B_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition PDCB_IT : itab := APC.mk_itab_ranges SG [(0xcffb8, 139%nat); (0xd0f4c, 1%nat); (0xd23b4, 1%nat); (0xd09d4, 1%nat); (0xd0ac8, 1%nat); (0xd0c74, 1%nat)].
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
Definition vXH := V 17.
Definition vE := V 18.
Definition vSP := mul 16 vSP16.
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vX); (vE); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KRange (V 19) 0 40;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151574 0x80000000000;
   KWr (SA vSP (-4448)) (ELit 4448);
   KUnk (SA vSP (-4448)) (ELit 4448);
   KZero (SA (mul 2 vSP16) 2147450874) (ELit 6);
   KRange (sub (mul 2 vSP16) (EAlu ALU_SRL (add (mul 16 vSP16) (ELit (-48))) (ELit 3))) 6 6;
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX 0) (ELit 504);
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
   KDisj (SA vSP (-4448)) (ELit 4448) (SA vX (-8)) (ELit 512);
   KRange vE 0 327;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TMG 0xcffb8 T0_regs T0_kn 33%nat (ELit 5000) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xcffe8); (spo (-48)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (vE); (ELit 1); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (ELit 2147450880); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition R1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KRange (V 19) 0 56;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151574 0x80000000000;
   KWr (SA vSP (-4448)) (ELit 4448);
   KUnk (SA vSP (-4448)) (ELit 4448);
   KZero (SA (mul 2 vSP16) 2147450874) (ELit 6);
   KRange (sub (mul 2 vSP16) (EAlu ALU_SRL (add (mul 16 vSP16) (ELit (-48))) (ELit 3))) 6 6;
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX 0) (ELit 504);
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
   KDisj (SA vSP (-4448)) (ELit 4448) (SA vX (-8)) (ELit 512);
   KRange vE 0 327;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R1 : ST.tmpl := ST.TMG 0xcffe8 R1_regs R1_kn 34%nat (ELit 4000) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (vE); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 2147450880); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition R2_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151574 0x80000000000;
   KWr (SA vSP (-4448)) (ELit 4448);
   KUnk (SA vSP (-4448)) (ELit 4448);
   KZero (SA (mul 2 vSP16) 2147450874) (ELit 6);
   KRange (sub (mul 2 vSP16) (EAlu ALU_SRL (add (mul 16 vSP16) (ELit (-48))) (ELit 3))) 6 6;
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX 0) (ELit 504);
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
   KDisj (SA vSP (-4448)) (ELit 4448) (SA vX (-8)) (ELit 512);
   KRange vE 0 327;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R2 : ST.tmpl := ST.TMG 0xcfffc R2_regs R2_kn 36%nat (ELit 3000) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0xd0008); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (vE); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 2147450880); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition R3_kn : list kentry :=
  [KWord (SA vSP (-33)) 1 (V 20);
   KRange (V 20) 0 1;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151574 0x80000000000;
   KWr (SA vSP (-4448)) (ELit 4448);
   KUnk (SA vSP (-4448)) (ELit 4448);
   KZero (SA (mul 2 vSP16) 2147450874) (ELit 6);
   KRange (sub (mul 2 vSP16) (EAlu ALU_SRL (add (mul 16 vSP16) (ELit (-48))) (ELit 3))) 6 6;
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX 0) (ELit 504);
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
   KDisj (SA vSP (-4448)) (ELit 4448) (SA vX (-8)) (ELit 512);
   KRange vE 0 327;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R3 : ST.tmpl := ST.TMG 0xd0008 R3_regs R3_kn 36%nat (ELit 2000) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition G_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (add vX (mul 8 (add (V 19) (ELit (-1))))); (vE); (V 26); ((V 19)); ((V 21)); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 2147450880); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition G_kn : list kentry :=
  [KRange (V 21) 1 18446744073709551615;
   KWord (SA vSP (-33)) 1 (V 20);
   KRange (V 20) 0 1;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP16 8795556151574 0x80000000000;
   KWr (SA vSP (-4448)) (ELit 4448);
   KUnk (SA vSP (-4448)) (ELit 4448);
   KZero (SA (mul 2 vSP16) 2147450874) (ELit 6);
   KRange (sub (mul 2 vSP16) (EAlu ALU_SRL (add (mul 16 vSP16) (ELit (-48))) (ELit 3))) 6 6;
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 2 vSP16) 2147450874) (ELit 6) (SA vX 0) (ELit 504);
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
   KDisj (SA vSP (-4448)) (ELit 4448) (SA vX (-8)) (ELit 512);
   KRange vE 0 327;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition G : ST.tmpl := ST.TMG 0xd0054 G_regs G_kn 36%nat (ELit 1000) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; (mul 16 vSP16); vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
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
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition XR : ST.tmpl := ST.TM 0xd01c4 XR_regs XR_kn 35%nat (ELit 0) 0%nat.

Definition PDCB : SP.prog := SP.PGH 19 [T0; R1; R2; R3; G] [XR] [(vSP, -4448, ELit 4448); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63)] [SX.SpHav 0xd00bc 12] [P5SBN; SHLSBN; HI64SB] (Some [(vSP, -4448, ELit 4448); (mul 2 vSP16, 2147450874, ELit 6); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)]) (Some (vSP)) [(vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72)] [].
