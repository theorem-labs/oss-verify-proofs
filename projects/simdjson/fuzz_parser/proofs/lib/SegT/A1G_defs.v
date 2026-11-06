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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegT Require Import A1G_mc.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Asan.M.loaded_segments.
Definition A1G_IT : itab := APC.mk_itab_ranges SG [(0x97628, 2277%nat)].
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
Definition vB8 := V 17.
Definition vLEN := V 18.
Definition vI8 := V 19.
Definition vG := V 20.
Definition vIG := V 21.
Definition vBO := V 22.
Definition vSP := mul 16 vSP16.
Definition vTHIS := mul 8 vT8.
Definition vBUF := add (mul 8 vB8) vBO.
Definition vA1 := mul 8 vI8.
Definition idxlen := add (mul 4 vLEN) (ELit 36).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; (vSP); vGP; vTP; (V 23); (V 24); (V 25);
   vS0; vS1; (vTHIS); (vBUF); (vLEN); (ELit 0); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition T0_kn : list kentry :=
  [KWord (SA vTHIS 16) 8 vA1;
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition T0 : ST.tmpl := ST.TMG 0x97628 T0_regs T0_kn 34%nat (ELit 2097152) 100%nat [ST.GA 1 [vBUF; vLEN]].

(* [comment removed for export] *)
Definition T1_regs : list expr :=
  [ELit 0; (ELit 0x976c8); (spo (-432)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vS0); (ELit 0); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vTHIS); (vLEN); (ELit 0x7fff8000); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vBUF); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition T1_kn : list kentry :=
  [KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition T1 : ST.tmpl := ST.TMG 0x976c8 T1_regs T1_kn 38%nat (ELit 2097152) 99%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]].

(* [comment removed for export] *)
Definition H_regs : list expr :=
  [ELit 0; ((V 25)); (spo (-432)); (vGP); (vTP); (ELit 32); (V 26); (V 27);
   (vA1); (ELit 0); (V 28); (V 29); (add vA1 (V 24)); (ELit 0); (vLEN); (spo (-400));
   (ELit 34); (ELit 92); (vTHIS); (vLEN); (ELit 0x7fff8000); (ELit 18446744073709551552); (ELit 244); (ELit 240);
   (ELit 30); ((V 23)); (vBUF); (V 30); (V 31); (V 32); (ELit 224); (ELit 160)].
Definition H_kn : list kentry :=
  [KRange (V 23) 0 1048512;
   KRange (sub vLEN (V 23)) 1 1048512;
   KRange (V 24) 0 4194048;
   KRange (sub (mul 4 (V 23)) (V 24)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 24)) 4 4194048;
   KAlign (V 24) 4;
   KRange (V 25) 0 14;
   KRange (sub (mul 8 vG) (add (V 23) vBO)) 58 2097152;
   KRange (sub (mul 8 vIG) (V 24)) 36 0x800000;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-108)) 4 (ELit 0);
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition H : ST.tmpl := ST.TMG 0x97734 H_regs H_kn 33%nat (sub vLEN (V 23)) 2%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 3 [vA1; (V 23); (V 24); (V 25)]].

(* [comment removed for export] *)
Definition W_regs : list expr :=
  [ELit 0; ((V 25)); (spo (-432)); (vGP); (vTP); (ELit 32); (add (V 23) (ELit 2)); (vLEN);
   (vA1); (ELit 0); (V 26); (V 27); (add vA1 (V 24)); (ELit 0); (vLEN); (spo (-400));
   (ELit 34); (ELit 92); (vTHIS); (vLEN); (ELit 0x7fff8000); (ELit 18446744073709551552); (ELit 244); (ELit 240);
   (ELit 30); ((V 23)); (vBUF); (V 28); (V 29); (V 30); (ELit 224); (ELit 160)].
Definition W_kn : list kentry :=
  [KRange (V 23) 0 1048512;
   KRange (sub vLEN (V 23)) 1 1048512;
   KRange (V 24) 0 4194048;
   KRange (sub (mul 4 (V 23)) (V 24)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 24)) 4 4194048;
   KAlign (V 24) 4;
   KRange (V 25) 0 14;
   KRange (sub (mul 8 vG) (add (V 23) vBO)) 58 2097152;
   KRange (sub (mul 8 vIG) (V 24)) 36 0x800000;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-108)) 4 (ELit 0);
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition W : ST.tmpl := ST.TMG 0x97748 W_regs W_kn 31%nat (sub vLEN (V 23)) 1%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 3 [vA1; (V 23); (V 24); (V 25)]].

(* [comment removed for export] *)
Definition S_regs : list expr :=
  [ELit 0; ((V 25)); (spo (-432)); (vGP); (vTP); (ELit 32); (V 27); (vLEN);
   (vA1); (ELit 0); (V 28); (V 29); (add vA1 (V 24)); (ELit 0); (vLEN); (spo (-400));
   (ELit 34); (ELit 92); (vTHIS); (vLEN); (ELit 0x7fff8000); (ELit 18446744073709551552); (ELit 244); (ELit 240);
   (ELit 30); (V 30); (ELit 1); ((V 23)); (V 31); (vBUF); (ELit 224); (ELit 160)].
Definition S_kn : list kentry :=
  [KWord (SA (add vA1 (V 24)) 0) 4 (V 26);
   KRange (V 23) 0 1048512;
   KRange (sub vLEN (V 23)) 1 1048512;
   KRange (V 24) 0 4194048;
   KRange (sub (mul 4 (V 23)) (V 24)) 4 4194048;
   KRange (sub (mul 4 vLEN) (V 24)) 4 4194048;
   KAlign (V 24) 4;
   KRange (V 25) 0 14;
   KRange (sub (mul 8 vG) (add (V 23) vBO)) 58 2097152;
   KRange (sub (mul 8 vIG) (V 24)) 36 0x800000;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-108)) 4 (ELit 0);
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition S : ST.tmpl := ST.TMG 0x977d8 S_regs S_kn 32%nat (sub vLEN (V 23)) 1%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 4 [vA1; (V 26); (V 23); (V 24); (V 25)]].

(* [comment removed for export] *)
Definition SI_regs : list expr :=
  [ELit 0; (vLEN); (spo (-432)); (vGP); (vTP); (ELit 32); ((V 25)); (vLEN);
   (vA1); (ELit 0); (V 27); (V 28); (add vA1 (V 24)); (ELit 0); (vLEN); (spo (-400));
   (ELit 34); (ELit 92); (vTHIS); (vLEN); (ELit 0x7fff8000); (ELit 18446744073709551552); (ELit 244); (ELit 240);
   (ELit 30); ((V 23)); (ELit 1); (V 29); (V 30); (vBUF); (ELit 224); (ELit 160)].
Definition SI_kn : list kentry :=
  [KWord (SA (add vA1 (V 24)) 0) 4 (V 26);
   KRange (V 23) 0 1048512;
   KRange (sub vLEN (V 23)) 1 1048512;
   KRange (V 24) 0 4194048;
   KRange (sub (mul 4 (V 23)) (V 24)) 4 4194048;
   KRange (sub (mul 4 vLEN) (V 24)) 4 4194048;
   KAlign (V 24) 4;
   KRange (V 25) 0 14;
   KRange (sub (mul 8 vG) (add (V 23) vBO)) 58 2097152;
   KRange (sub (mul 8 vIG) (V 24)) 36 0x800000;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-108)) 4 (ELit 0);
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition SI : ST.tmpl := ST.TMG 0x977f0 SI_regs SI_kn 31%nat (sub vLEN (V 23)) 0%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 4 [vA1; (V 26); (V 23); (V 24); (V 25)]].

(* [comment removed for export] *)
Definition P_regs : list expr :=
  [ELit 0; ((V 25)); (spo (-432)); (vGP); (vTP); (ELit 32); (add vBUF (add (V 23) (ELit 2))); (add vLEN (ELit (-1)));
   (vA1); (ELit 0); (V 27); (add vBUF (add (V 23) (ELit 2))); (add vA1 (V 24)); (ELit 0); (vLEN); (spo (-400));
   (ELit 34); (ELit 92); (vTHIS); (vLEN); (ELit 0x7fff8000); (ELit 18446744073709551552); (ELit 244); (ELit 240);
   (ELit 30); ((V 23)); (add vLEN (ELit (-2))); (V 28); (V 29); (vBUF); (ELit 224); (ELit 160)].
Definition P_kn : list kentry :=
  [KWord (SA (add vA1 (V 24)) 0) 4 (V 26);
   KRange (add vLEN (ELit (-2))) 0 1048510;
   KRange (sub (add vLEN (ELit (-2))) (V 23)) 0 1048510;
   KRange (V 23) 0 1048512;
   KRange (sub vLEN (V 23)) 2 1048512;
   KRange (V 24) 0 4194048;
   KRange (sub (mul 4 (V 23)) (V 24)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 24)) 4 4194048;
   KAlign (V 24) 4;
   KRange (V 25) 0 14;
   KRange (sub (mul 8 vG) (add (V 23) vBO)) 58 2097152;
   KRange (sub (mul 8 vIG) (V 24)) 36 0x800000;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA (mul 8 vT8) 72) 8 vBUF;
   KWord (SA (mul 8 vT8) 80) 8 vLEN;
   KWord (SA vTHIS 16) 8 vA1;
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-108)) 4 (ELit 0);
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
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024)].
Definition P : ST.tmpl := ST.TMG 0x97b48 P_regs P_kn 30%nat (sub vLEN (V 23)) 0%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 5 [vA1; (V 26); (V 23); (V 24); (V 25)]].

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; (vSP); vGP; vTP; (V 25); (V 26); (V 27);
   vS0; vS1; ((V 23)); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 35); (V 36); (V 37); (V 38)].
Definition X_kn : list kentry :=
  [KWord (SA vTHIS 8) 4 (V 24);
   KRange vLEN 0 1048512;
   KRange vSP16 0x7fff0000000 0x80000000000;
   KRange vT8 0xcca00 0xfffffefffff;
   KRange (add vTHIS (ELit 96)) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vTHIS 0) (ELit 96);
   KRange vB8 0xcca00 0xfffffefffff;
   KRange (add vBUF (add vLEN (ELit 64))) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vBUF 0) (add vLEN (ELit 64));
   KRange vI8 0xcca00 0xfffffefffff;
   KRange (add vA1 idxlen) 0x665000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-8192)) (ELit 8192) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KRange vBO 0 7;
   KRange (sub (mul 8 vG) (add vLEN vBO)) 57 64;
   KRange vG 8 131080;
   KRange (sub (mul 8 vIG) (mul 4 vLEN)) 32 0x800000;
   KRange vIG 5 0x100000;
   KZero (SA vT8 0x7fff8000) (ELit 12);
   KZero (SA vB8 0x7fff8000) vG;
   KZero (SA vI8 0x7fff8000) vIG;
   KWord (SA (ELit 0) 0x107300) 8 (ELit 0x10faf8);
   KWord (SA (ELit 0) 0x10faf8) 8 (ELit 0x7fff8000);
   KWr (SA vSP (-2656)) (ELit 2656);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x42c40;
   KUnk (SA vSP (-2656)) (ELit 2656);
   KZero (SA (ELit 0) 0x7fffd028) (ELit 32);
   KWr (SA (ELit 0) 0x7fffd028) (ELit 32);
   KZero (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWr (SA (mul 2 vSP16) (0x7fff8000 - 1024)) (ELit 1024);
   KWord (SA vTHIS 72) 8 vBUF;
   KWord (SA vTHIS 80) 8 vLEN].
Definition X : ST.tmpl := ST.TMG 0x9938c X_regs X_kn 39%nat (ELit 0) 0%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 6 [vA1; (V 23); (V 24); vTHIS]].

Definition A1G : SP.prog := SP.PGCA 23 [T0; T1; H; W; S; SI; P] [X] [(vSP, -2656, ELit 2656); (vTHIS, 8, ELit 4); (vTHIS, 24, ELit 4); (vTHIS, 72, ELit 16); (vA1, 0, idxlen)] [] [MCG] [(vSP, -2656, ELit 2656); (vTHIS, 0, ELit 96); (vT8, 0x7fff8000, ELit 12); (vBUF, 0, add vLEN (ELit 64)); (vB8, 0x7fff8000, vG); (vA1, 0, idxlen); (vI8, 0x7fff8000, vIG); (ELit 0, 0x107300, ELit 8); (ELit 0, 0x10faf8, ELit 8); (ELit 0, 0x28140, ELit 256); (ELit 0, 0x7fffd028, ELit 32); (mul 2 vSP16, 0x7fff8000 - 1024, ELit 1024); (ELit 0, 0x10000, ELit 0x655000)].
