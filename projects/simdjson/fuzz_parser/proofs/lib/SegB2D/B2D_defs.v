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
Definition B2D_IT : itab := APC.mk_itab_ranges SG [(0x9abb0, 24157%nat)].
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
Definition DA_regs : list expr :=
  [ELit 0; (V 35); (vSPA); (vGP); (vTP); (V 36); (V 37); (V 38);
   (vSP); (vSPA); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44);
   (V 45); (V 46); (V 47); (vSHF); (V 48); (V 49); (V 50); (V 51);
   (V 52); (V 53); (vF); (V 54); (V 55); (V 56); (V 57); (V 58)].
Definition DA_kn : list kentry :=
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
   KWord (SA vSPA 264) 8 vF;
   KWord (SA vSPA 280) 8 (ELit 2147450880);
   KWord (SA vSPA 296) 8 vF;
   KWord (SA vF 2040) 8 vFLAG;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vF 0) (ELit 2048);
   KWr (SA vSP (-8640)) (ELit 8640);
   KUnk (SA vSP (-8640)) (ELit 8224);
   KZero (SA (mul 2 vSP16) (2147449800)) (sub (ELit 1066) (mul 2 vPB));
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450866)) (ELit 1);
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450867)) (add (ELit 13) (mul 2 vPB));
   KWr (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KDisj (SA vSHF 0) (ELit 256) (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KWr (SA vSHF 0) (ELit 256);
   KRange vPB 0 1;
   KAlign vSPA 32].
Definition DA : ST.tmpl := ST.TM 0x9b684 DA_regs DA_kn 59%nat (ELit 10) 0%nat.

(* [comment removed for export] *)
Definition DB_regs : list expr :=
  [ELit 0; (V 36); (vSPA); (vGP); (vTP); (V 37); (V 38); (V 39);
   (vSP); (vSPA); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45);
   (V 46); (V 47); (V 48); (vSHF); (V 49); (V 50); (V 51); (V 52);
   (V 53); (V 54); (vF); (V 55); (V 56); (V 57); (V 58); (V 59)].
Definition DB_kn : list kentry :=
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
   KWord (SA vSPA 264) 8 vF;
   KWord (SA vSPA 280) 8 (ELit 2147450880);
   KWord (SA vSPA 296) 8 vF;
   KWord (SA vF 2040) 8 vFLAG;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vF 0) (ELit 2048);
   KWr (SA vSP (-8640)) (ELit 8640);
   KUnk (SA vSP (-8640)) (ELit 8224);
   KZero (SA (mul 2 vSP16) (2147449800)) (sub (ELit 1066) (mul 2 vPB));
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450866)) (ELit 1);
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450867)) (add (ELit 13) (mul 2 vPB));
   KWr (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KDisj (SA vSHF 0) (ELit 256) (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KWr (SA vSHF 0) (ELit 256);
   KRange vPB 0 1;
   KAlign vSPA 32].
Definition DB : ST.tmpl := ST.TM 0xa0f08 DB_regs DB_kn 60%nat (ELit 10) 0%nat.

(* [comment removed for export] *)
Definition DC_regs : list expr :=
  [ELit 0; (V 37); (vSPA); (vGP); (vTP); (V 38); (V 39); (V 40);
   (vSP); (vSPA); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46);
   (V 47); (V 48); ((V 35)); (vSHF); (V 49); (V 50); (V 51); (V 52);
   (V 53); (V 54); (vF); (V 55); (V 56); (V 57); (V 58); (V 59)].
Definition DC_kn : list kentry :=
  [KRange (V 35) 0 63;
   KRange (V 36) 8 24;
   KAlign (V 36) 8;
   KWord (SA vSPA 184) 8 (add vTBASE (V 36));
   KWord (SA vSPA 192) 8 (add vIDX (ELit 4));
   KWord (SA vSPA 208) 8 (add vTHIS (ELit 16));
   KWord (SA vSPA 216) 8 (add vTHIS (ELit 8));
   KWord (SA vSPA 224) 8 (add (add vT8 (ELit 2147450880)) (ELit 2));
   KWord (SA vSPA 232) 8 (add (add vT8 (ELit 2147450880)) (ELit 1));
   KWord (SA vSPA 240) 8 (add (add vT8 (ELit 2147450880)) (ELit 11));
   KWord (SA vSPA 248) 8 (add vTHIS (ELit 88));
   KWord (SA vSPA 256) 8 vTHIS;
   KWord (SA vTHIS 8) 4 vN;
   KWord (SA vTHIS 16) 8 vIDX;
   KWord (SA vTHIS 49) 1 (ELit 0);
   KWord (SA vDOC 0) 8 vTBASE;
   KWord (SA vTHIS 48) 1 (ELit 0);
   KWord (SA vTHIS 88) 8 vDOC;
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
   KWord (SA vSPA 264) 8 vF;
   KWord (SA vSPA 280) 8 (ELit 2147450880);
   KWord (SA vSPA 296) 8 vF;
   KWord (SA vF 2040) 8 vFLAG;
   KRange vTP 0x64e9f0 0x64e9f0;
   KRange vLEN 1 1048512;
   KRange vN 1 1048512;
   KRange (sub vLEN vN) 0 1048512;
   KRange vCAPT 4 16777216;
   KRange (sub vCAPT vN) 3 16777216;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xce200 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vDOC8 0xce200 0xfffffefffff;
   KRange (add vDOC (ELit 16)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vDOC 0) (ELit 16);
   KRange vI8 0xce200 0xfffffefffff;
   KRange (add vIDX (add (mul 4 vN) (ELit 12))) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KRange vTB8 0xce200 0xfffffefffff;
   KRange (add vTBASE (mul 8 vCAPT)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTBASE 0) (mul 8 vCAPT);
   KRange (add vF (ELit 2048)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vF 0) (ELit 2048);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vDOC 0) (ELit 16);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSP (-8640)) (ELit 8640) (SA vF 0) (ELit 2048);
   KDisj (SA vTHIS 0) (ELit 96) (SA vDOC 0) (ELit 16);
   KDisj (SA vTHIS 0) (ELit 96) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vTHIS 0) (ELit 96) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vTHIS 0) (ELit 96) (SA vF 0) (ELit 2048);
   KDisj (SA vDOC 0) (ELit 16) (SA vIDX 0) (add (mul 4 vN) (ELit 12));
   KDisj (SA vDOC 0) (ELit 16) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vDOC 0) (ELit 16) (SA vF 0) (ELit 2048);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vIDX 0) (add (mul 4 vN) (ELit 12)) (SA vF 0) (ELit 2048);
   KDisj (SA vTBASE 0) (mul 8 vCAPT) (SA vF 0) (ELit 2048);
   KZero (SA vT8 2147450880) (ELit 12);
   KZero (SA vDOC8 2147450880) (ELit 2);
   KRange vBO 0 7;
   KZero (SA vTB8 2147450880) vCAPT;
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KWord (SA (ELit 0) 0x113720) 8 (ELit 182384);
   KImg 0x10000 0x429e4;
   KWord (SA (ELit 0) 0x1174c0) 4 (ELit 8388608);
   KZero (SA (ELit 0) 2147468976) (ELit 32);
   KZero (SA (ELit 0) 2147469016) (ELit 443);
   KZero (SA (ELit 0) 2147469568) (ELit 23);
   KZero (SA (ELit 0) 2147469596) (ELit 1302);
   KZero (SA (ELit 0) 2147471336) (ELit 32);
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWr (SA vSP (-8640)) (ELit 8640);
   KUnk (SA vSP (-8640)) (ELit 8224);
   KZero (SA (mul 2 vSP16) (2147449800)) (sub (ELit 1066) (mul 2 vPB));
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450866)) (ELit 1);
   KZero (SA (sub (mul 2 vSP16) (mul 2 vPB)) (2147450867)) (add (ELit 13) (mul 2 vPB));
   KWr (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 88) (ELit 8);
   KWr (SA vTBASE 0) (mul 8 vCAPT);
   KDisj (SA vSHF 0) (ELit 256) (SA vT8 2147450880) (ELit 12);
   KDisj (SA vSHF 0) (ELit 256) (SA vDOC8 2147450880) (ELit 2);
   KDisj (SA vSHF 0) (ELit 256) (SA vTB8 2147450880) vCAPT;
   KDisj (SA vSHF 0) (ELit 256) (SA (mul 2 vSP16) (2147449800)) (ELit 1080);
   KRange vF11 0xce2 0xfffffefff;
   KWr (SA vF 0) (ELit 2048);
   KWr (SA vSHF 0) (ELit 256);
   KRange vPB 0 1;
   KAlign vSPA 32].
Definition DC : ST.tmpl := ST.TM 0xa0f28 DC_regs DC_kn 60%nat (ELit 20) 0%nat.

(* [comment removed for export] *)
Definition XSF_regs : list expr :=
  [ELit 0; (ELit 0xb13f8); (vSPA); (vGP); (vTP); (V 36); (V 37); (V 38);
   (vSP); (vSPA); (vF); (ELit 1312); (V 39); (V 40); (V 41); (V 42);
   (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49); (V 50);
   (V 51); (V 52); (vF); (V 53); (V 54); (V 55); (V 56); (V 57)].
Definition XSF_kn : list kentry :=
  [KRange (V 35) 0 63;
   KWord (SA vSPA 272) 8 (V 35);
   KWord (SA vF 2040) 8 vFLAG;
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
   KWord (SA vSP (-104)) 8 vS11].
Definition XSF : ST.tmpl := ST.TM 0x507e4 XSF_regs XSF_kn 58%nat (ELit 0) 0%nat.

Definition B2D : SP.prog := SP.PGCA 35 [DA; DB; DC] [XSF] [(vSP, -8640, ELit 8640); (vTHIS, 24, ELit 4); (vTHIS, 88, ELit 8); (vTBASE, 0, mul 8 vCAPT); (vSBASE, 0, vCAPS); (vOCB, 0, ELit 8192); (vIAB, 0, ELit 1024); (vF, 0, ELit 2048); (vSHF, 0, ELit 256); (vSPA, -8192, ELit 8192)] [] [] [(vSP, -8640, ELit 8640); (ELit 0, 0x10000, ELit 0x661000); (mul 2 vSP16, 2147449800, ELit 1080); (ELit 0, 2147468976, ELit 32); (ELit 0, 2147469016, ELit 443); (ELit 0, 2147469568, ELit 23); (ELit 0, 2147469596, ELit 1302); (ELit 0, 2147471336, ELit 32); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (vTHIS, 0, ELit 96); (vDOC, 0, ELit 16); (vBUF, 0, add vLEN (ELit 64)); (vIDX, 0, add (mul 4 vN) (ELit 12)); (vTBASE, 0, mul 8 vCAPT); (vSBASE, 0, vCAPS); (vOCB, 0, ELit 8192); (vIAB, 0, ELit 1024); (vT8, 2147450880, ELit 12); (vDOC8, 2147450880, ELit 2); (vB8, 2147450880, vBG); (vI8, 2147450880, vIG); (vTB8, 2147450880, vCAPT); (vSB8, 2147450880, vSG); (vOC8, 2147450880, ELit 1024); (vIA8, 2147450880, ELit 128); (vF, 0, ELit 2048); (vSHF, 0, ELit 256)].
