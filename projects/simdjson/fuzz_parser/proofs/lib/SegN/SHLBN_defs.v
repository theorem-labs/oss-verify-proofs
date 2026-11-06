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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import AMEMHBN.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRCB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := AsanUbsan.M.loaded_segments.
Definition SHLBN_IT : itab := APC.mk_itab_ranges SG [(0xd21cc, 147%nat)].
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
Definition vN0 := V 18.
Definition vX := mul 8 vX8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vX); (vN0); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange (V 19) 0 56;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition T0 : ST.tmpl := ST.TMG 0xd21cc T0_regs T0_kn 33%nat (ELit 4096) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition SB_regs : list expr :=
  [ELit 0; (vRA); (spo (-64)); (vGP); (vTP); ((V 20)); (V 22); (V 23);
   (add vX (ELit 496)); (vX); (add vX (mul 8 (sub (V 19) (V 20)))); (vN0); (add vX8 (ELit 2147450942)); ((V 19)); ((V 21)); (sub (ELit 64) (V 21));
   (add (sub (ELit 63) (V 19)) (V 20)); (add vX (mul 8 (sub (V 19) (V 20)))); (vS2); (ELit 2147450880); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 24); (V 25); (V 26); (V 27)].
Definition SB_kn : list kentry :=
  [KRange (V 19) 1 56;
   KRange vN0 0 327;
   KRange (V 20) 1 62;
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
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition SB : ST.tmpl := ST.TMG 0xd2240 SB_regs SB_kn 28%nat (add (ELit 3072) (V 20)) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (vRA); (spo (-64)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (add vX (ELit 496)); (vX); (V 23); (vN0); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vS2); (ELit 2147450880); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition J1_kn : list kentry :=
  [KRange (V 19) 0 57;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1)].
Definition J1 : ST.tmpl := ST.TMG 0xd22c4 J1_regs J1_kn 34%nat (ELit 2048) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition JM_regs : list expr :=
  [ELit 0; (vRA); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (add vX (ELit 496)); (vX); (ELit 62); (vN0); ((V 19)); (V 24); (V 25); (V 26);
   (V 27); (V 28); (vS2); (ELit 2147450880); (add (V 20) (V 19)); (add vX8 (ELit 2147450942)); ((V 20)); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
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
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vN0 0 327].
Definition JM : ST.tmpl := ST.TMG 0xd22f4 JM_regs JM_kn 33%nat (ELit 1800) 0%nat [ST.GA 10 [add vX (mul 8 (V 19))]].

(* [comment removed for export] *)
Definition RM_regs : list expr :=
  [ELit 0; (ELit 0xd2328); (spo (-64)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (add vX (ELit 496)); (vX); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (add vX (mul 8 (V 20))); (ELit 2147450880); (add (V 20) (V 19)); (add vX8 (ELit 2147450942)); ((V 20)); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition RM_kn : list kentry :=
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
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vN0 0 327].
Definition RM : ST.tmpl := ST.TMG 0xd2328 RM_regs RM_kn 36%nat (ELit 1500) 0%nat [ST.GA 10 [add vX (mul 8 (add (V 20) (V 19)))]].

(* [comment removed for export] *)
Definition ZF_regs : list expr :=
  [ELit 0; (ELit 0xd2328); (spo (-64)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (add vX (ELit 496)); (add vX (mul 8 (V 21))); (add vX (mul 8 (V 21))); (add (sub (V 20) (V 21)) (ELit 1)); (ELit (-8)); (ELit 1); (V 25); (V 26);
   (V 27); (V 28); (add vX (mul 8 (V 20))); (add (add vX8 (ELit 2147450880)) (V 21)); (add (V 20) (V 19)); (add vX8 (ELit 2147450942)); ((V 20)); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition ZF_kn : list kentry :=
  [KRange (V 21) 0 60;
   KRange (sub (V 20) (V 21)) 1 61;
   KRange (V 20) 1 61;
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
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898424896 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-4160)) (ELit 4160);
   KUnk (SA vSP (-4160)) (ELit 4160);
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
   KDisj (SA vSP (-4160)) (ELit 4160) (SA vX (-8)) (ELit 512);
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vN0 0 327].
Definition ZF : ST.tmpl := ST.TMG 0xd2344 ZF_regs ZF_kn 33%nat (sub (V 20) (V 21)) 0%nat [ST.GA 10 [add vX (mul 8 (add (V 20) (V 19)))]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition XR_kn : list kentry :=
  [KRange (V 20) 1 1;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62].
Definition XR : ST.tmpl := ST.TMG 0xd23b4 XR_regs XR_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 19)]].

Definition SHLBN : SP.prog := SP.PGCA 19 [T0; SB; J1; JM; RM; ZF] [XR] [(vSP, -4160, ELit 4160); (vX, 0, ELit 498)] [] [(AMHBN.MVAHN 0xd2328)] [(vSP, -4160, ELit 4160); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (mul 8 vXH, 2147450880, ELit 72); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)].
