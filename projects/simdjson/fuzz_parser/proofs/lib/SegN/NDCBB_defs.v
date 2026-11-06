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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHB.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import P5B_sum.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SHLB_sum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition NDCBB_IT : itab := APC.mk_itab_ranges SG [(0xd01e4, 486%nat); (0xd0f4c, 1%nat); (0xd23b4, 1%nat)].
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
Definition vM := V 18.
Definition vP2 := V 19.
Definition vRE := V 20.
Definition vF10 := V 21.
Definition vFLG := V 22.
Definition vSPA := V 23.
Definition vX := mul 8 vX8.
Definition vF := mul 1024 vF10.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; (ELit 0xd0260); (vSPA); (vGP); (vTP); (V 25); (V 26); (V 27);
   (vSP); (vSPA); (vF); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vM); vS3; (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); vS5; (vX); (vRE);
   vS8; vS9; (ELit 2147450880); vS11; (V 35); (V 36); (V 37); (V 38)].
Definition T0_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KZero (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TM 0xd0260 T0_regs T0_kn 39%nat (add (ELit 6871947673600) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition JP_regs : list expr :=
  [ELit 0; (V 25); (vSPA); (vGP); (vTP); (V 26); (V 27); (V 28);
   (vSP); (vSPA); (vF); (V 29); (EAluw ALU_ADD (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)) (ELit 0)); (V 30); (V 31); (V 32);
   (V 33); (V 34); (vM); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 35); (vX); (vRE);
   (V 36); (vF); (ELit 2147450880); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition JP_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition JP : ST.tmpl := ST.TM 0xd0400 JP_regs JP_kn 42%nat (add (ELit 6734508720128) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition J0_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vM); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); ((V 25)); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 38); (V 39); (V 40); (V 41)].
Definition J0_kn : list kentry :=
  [KRange (add (V 25) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition J0 : ST.tmpl := ST.TM 0xd04c0 J0_regs J0_kn 42%nat (add (ELit 6528350289920) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0xd05dc); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); ((V 25)); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); ((V 26)); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 38); (V 39); (V 40); (V 41)].
Definition R1_kn : list kentry :=
  [KRange (add (V 26) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KZero (SA vF 40) (ELit 496);
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R1 : ST.tmpl := ST.TM 0xd05dc R1_regs R1_kn 42%nat (add (ELit 6184752906240) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0xd060c); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); ((V 26)); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 38); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 39); (V 40); (V 41); (V 42)].
Definition R2_kn : list kentry :=
  [KRange (add (V 26) (ELit 9223372036854775808)) 9223372036854774733 9223372036855825355;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition R2 : ST.tmpl := ST.TM 0xd060c R2_regs R2_kn 43%nat (add (ELit 5497558138880) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition CST_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); ((V 26)); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 39); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 40); (V 41); (V 42); (V 43)].
Definition CST_kn : list kentry :=
  [KRange (V 26) 1 1049547;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition CST : ST.tmpl := ST.TM 0xd0610 CST_regs CST_kn 44%nat (add (ELit 4810363371520) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition CSX_regs : list expr :=
  [ELit 0; (V 27); (vSPA); (vGP); (vTP); (V 28); (V 29); (V 30);
   (vSP); (vSPA); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); ((V 26)); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 39); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 40); (V 41); (V 42); (V 43)].
Definition CSX_kn : list kentry :=
  [KRange (V 26) 1 1075;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition CSX : ST.tmpl := ST.TM 0xd0954 CSX_regs CSX_kn 44%nat (add (ELit 4810363371520) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (ELit 0xd0620); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); ((V 26)); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 38); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 39); (V 40); (V 41); (V 42)].
Definition RS_kn : list kentry :=
  [KRange (V 26) 0 1;
   KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition RS : ST.tmpl := ST.TM 0xd0620 RS_regs RS_kn 43%nat (add (ELit 4123168604160) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 39); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 40); (V 41); (V 42); (V 43)].
Definition J3_kn : list kentry :=
  [KWord (SA vF 528) 2 (V 25);
   KRange (V 25) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition J3 : ST.tmpl := ST.TM 0xd0628 J3_regs J3_kn 44%nat (add (ELit 2748779069440) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition CMP_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (add (V 25) (ELit (-8))); (sub (ELit (-1)) vX); (ELit 1); (V 31); (sub (ELit (-1)) (add vF (ELit 32)));
   (ELit (-16)); (V 32); (V 33); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (V 34); (vX); (vRE);
   (add vF (ELit 32)); (vF); (ELit 2147450880); (mul (-1) vP2); (V 35); (V 36); (V 37); (V 38)].
Definition CMP_kn : list kentry :=
  [KRange (sub (mul 8 (V 24)) (V 25)) 0 496;
   KRange (V 25) 0 496;
   KAlign (V 25) 8;
   KWord (SA vF 528) 2 (V 24);
   KRange (V 24) 0 62;
   KZero (SA (mul 128 vF10) 2147450884) (ELit 63);
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KWord (SA vSPA 48) 8 vF;
   KWord (SA vSPA 24) 8 vF;
   KWord (SA vSPA 16) 8 vM;
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition CMP : ST.tmpl := ST.TM 0xd0688 CMP_regs CMP_kn 39%nat (add (ELit 1374389534720) (V 25)) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 26); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (vF); (add (mul 128 vF10) (ELit 2147450880)); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); ((V 25)); (vX); (vRE);
   (V 38); (vF); (ELit 2147450880); (mul (-1) vP2); (V 39); (V 40); (V 41); (V 42)].
Definition J4_kn : list kentry :=
  [KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition J4 : ST.tmpl := ST.TM 0xd0794 J4_regs J4_kn 43%nat (add (ELit 687194767360) (ELit 0)) 0%nat.

(* [comment removed for export] *)
Definition XSS_regs : list expr :=
  [ELit 0; (ELit 0xd08c4); (vSPA); (vGP); (vTP); (V 27); (V 28); (V 29);
   (vSP); (vSPA); (add (mul 128 vF10) (ELit 2147450880)); (ELit 128); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (vF); (V 36); ((V 26)); ((V 25)); (V 37); (V 38);
   (V 39); (V 40); (ELit 2147450880); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition XSS_kn : list kentry :=
  [KWord (SA vF 0) 8 (ELit 0x45e0360e);
   KWord (SA vF 1016) 8 vFLG;
   KRange vF10 0x19c4 0x1ffffffdfff;
   KWr (SA vF 0) (ELit 1024);
   KUnk (SA vF 0) (ELit 1024);
   KWord (SA vF 1016) 8 vFLG;
   KWr (SA (mul 128 vF10) 2147450880) (ELit 128);
   KUnk (SA (mul 128 vF10) 2147450880) (ELit 128);
   KRange (add vF (ELit 1024)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 1024);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vF 0) (ELit 1024);
   KDisj (SA vF 0) (ELit 1024) (SA vX 0) (ELit 504);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX8 2147450880) (ELit 63);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA (mul 8 vXH) 2147450880) (ELit 72);
   KDisj (SA vSP (-4592)) (ELit 4592) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vF 0) (ELit 1024) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA (mul 128 vF10) 2147450880) (ELit 128) (SA vX 0) (ELit 504);
   KRange vSPA 140728898425136 0x800000000000;
   KAlign vSPA 16;
   KRange (sub (sub vSP vSPA) (ELit 160)) 0 31;
   KWr (SA vSPA (-4400)) (ELit 4560);
   KUnk (SA vSPA (-4400)) (ELit 4560);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vF 0) (ELit 1024);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA vX 0) (ELit 504);
   KDisj (SA vSPA (-4400)) (ELit 4560) (SA (mul 128 vF10) 2147450880) (ELit 128);
   KDisj (SA vSPA (-4400)) (ELit 4400) (SA vSP (-104)) (ELit 104);
   KDisj (SA vSPA 0) (ELit 56) (SA vSP (-104)) (ELit 104);
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
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vSP 140728898425328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4592)) (ELit 4592);
   KUnk (SA vSP (-4592)) (ELit 4592);
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
   KDisj (SA vSP (-4592)) (ELit 4592) (SA vX 0) (ELit 504);
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition XSS : ST.tmpl := ST.TM 0x694c4 XSS_regs XSS_kn 46%nat (ELit 0) 0%nat.

Definition NDCBB : SP.prog := SP.PGH 24 [T0; JP; J0; R1; R2; CST; CSX; RS; J3; CMP; J4] [XSS] [(vSP, -4592, ELit 4592); (vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128); (vSPA, -4400, ELit 4560)] [SX.SpW 0xd0400; SX.SpW 0xd040c; SX.SpW 0xd0424; SX.SpW 0xd0458; SX.SpW 0xd0478; SX.SpW 0xd05f0; SX.SpW 0xd05fc; SX.SpW 0xd06f4; SX.SpW 0xd0928; SX.SpW 0xd0744; SX.SpW 0xd0764; SX.SpW 0xd094c; SX.SpAl 0xd0698] [(AMHB.MSAH 0 0xd05dc); P5SB; SHLSB] (Some [(vSP, -4592, ELit 4592); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128); (vSPA, -4400, ELit 4560)]) (Some (vSP)) [(vX, 0, ELit 498); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (vF, 0, ELit 1024); (mul 128 vF10, 2147450880, ELit 128)] [].
