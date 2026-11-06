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
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS1Ghost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition U1G_IT : itab := APC.mk_itab_ranges SG [(0x27ddc, 1621%nat); (0x79f84, 257%nat)].
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
Definition vBUF := V 17.
Definition vLEN := V 18.
Definition vA1 := V 19.
Definition idxlen := add (mul 4 vLEN) (ELit 36).
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (vTHIS); (vBUF); (vLEN); (ELit 0); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KWord (SA vTHIS 16) 8 vA1;
   KRange vLEN 0 1048512;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vBUF 16 0x7fffff7fffff;
   KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vA1 16 0x7fffff7fffff;
   KAlign vA1 16;
   KRange (add vA1 idxlen) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-432)) (ELit 432) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-432)) (ELit 432) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-432)) (ELit 432) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KWr (SA vSP (-432)) (ELit 432);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x2550c].
Definition T0 : ST.tmpl := ST.TMG 0x27ddc T0_regs T0_kn 31%nat (ELit 2097152) 100%nat [ST.GA 1 [vBUF; vLEN]].

(* [comment removed for export] *)
Definition H_regs : list expr :=
  [ELit 0; (V 23); (spo (-432)); (vGP); (vTP); (ELit 92); (ELit 31); (ELit 14);
   (vTHIS); (vBUF); (add vA1 (V 21)); (vA1); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vSP) (ELit (399))); (V 24); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vBUF) (ELit (-1))); (V 25);
   (ELit 34); (ELit 18446744073709551612); (ELit 0); ((V 20)); (vLEN); (spo (-400)); (ELit 240); (ELit 144);
   (ELit 244); (ELit 143); (ELit 245); (ELit 30); (ELit 0); (ELit 18446744073709551551); (V 26); (V 27)].
Definition H_kn : list kentry :=
  [KRange (V 20) 0 1048512;
   KRange (sub vLEN (V 20)) 1 1048512;
   KRange (V 21) 0 4194048;
   KRange (sub (mul 4 (V 20)) (V 21)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 21)) 4 4194048;
   KAlign (V 21) 4;
   KRange (V 22) 0 14;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-136)) 8 (add vA1 (V 21));
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-116)) 4 (V 20);
   KWord (SA vSP (-112)) 4 (V 22);
   KWord (SA vSP (-108)) 4 (ELit 0);
   KWord (SA vTHIS 72) 8 vBUF;
   KWord (SA vTHIS 80) 8 vLEN;
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
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vBUF 16 0x7fffff7fffff;
   KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vA1 16 0x7fffff7fffff;
   KAlign vA1 16;
   KRange (add vA1 idxlen) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-432)) (ELit 432) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-432)) (ELit 432) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-432)) (ELit 432) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KWr (SA vSP (-432)) (ELit 432);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x2550c].
Definition H : ST.tmpl := ST.TMG 0x27ed4 H_regs H_kn 28%nat (sub vLEN (V 20)) 0%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 3 [vA1; (V 20); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition S_regs : list expr :=
  [ELit 0; ((V 20)); (spo (-432)); (vGP); (vTP); (ELit 92); (ELit 31); (ELit 14);
   (vTHIS); (vBUF); (add vA1 (V 21)); (vA1); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vSP) (ELit (399))); (ELit 1); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vBUF) (ELit (-1))); (V 24);
   (ELit 34); (ELit 18446744073709551612); (ELit 0); (V 25); (vLEN); (spo (-400)); (ELit 240); (ELit 144);
   (ELit 244); (ELit 143); (ELit 245); (ELit 30); (ELit 0); (ELit 18446744073709551551); (V 26); (V 27)].
Definition S_kn : list kentry :=
  [KWord (SA (add vA1 (V 21)) (-4)) 4 (V 23);
   KRange (V 20) 0 1048512;
   KRange (sub vLEN (V 20)) 1 1048512;
   KRange (V 21) 0 4194048;
   KRange (sub (mul 4 (V 20)) (V 21)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 21)) 4 4194048;
   KAlign (V 21) 4;
   KRange (V 22) 0 14;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-136)) 8 (add vA1 (V 21));
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-116)) 4 (V 20);
   KWord (SA vSP (-112)) 4 (V 22);
   KWord (SA vSP (-108)) 4 (ELit 0);
   KWord (SA vTHIS 72) 8 vBUF;
   KWord (SA vTHIS 80) 8 vLEN;
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
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vBUF 16 0x7fffff7fffff;
   KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vA1 16 0x7fffff7fffff;
   KAlign vA1 16;
   KRange (add vA1 idxlen) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-432)) (ELit 432) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-432)) (ELit 432) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-432)) (ELit 432) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KWr (SA vSP (-432)) (ELit 432);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x2550c].
Definition S : ST.tmpl := ST.TMG 0x27f8c S_regs S_kn 28%nat (sub vLEN (V 20)) 1%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 4 [vA1; (V 23); (V 20); add (V 21) (ELit (-4)); (V 22)]].

(* [comment removed for export] *)
Definition P_regs : list expr :=
  [ELit 0; (add vBUF (V 20)); (spo (-432)); (vGP); (vTP); (ELit 92); (ELit 31); (ELit 14);
   (vTHIS); (vBUF); (add vA1 (V 21)); (vA1); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vSP) (ELit (399))); ((V 20)); (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) vBUF) (ELit (-1))); (V 24);
   (ELit 34); (ELit 18446744073709551612); (ELit 0); (add (V 20) (ELit (-1))); (vLEN); (spo (-400)); (ELit 240); (ELit 144);
   (ELit 244); (ELit 143); (ELit 245); (ELit 30); (ELit 0); (ELit 18446744073709551551); (V 25); (add vBUF (V 20))].
Definition P_kn : list kentry :=
  [KWord (SA (add vA1 (V 21)) (-4)) 4 (V 23);
   KRange (V 20) 0 1048512;
   KRange (sub vLEN (V 20)) 1 1048512;
   KRange (V 21) 0 4194048;
   KRange (sub (mul 4 (V 20)) (V 21)) 0 4194048;
   KRange (sub (mul 4 vLEN) (V 21)) 4 4194048;
   KAlign (V 21) 4;
   KRange (V 22) 0 14;
   KUnk (SA vSP (-400)) (ELit 256);
   KWord (SA vSP (-144)) 8 vBUF;
   KWord (SA vSP (-136)) 8 (add vA1 (V 21));
   KWord (SA vSP (-128)) 8 vTHIS;
   KWord (SA vSP (-120)) 4 vLEN;
   KWord (SA vSP (-116)) 4 (add (V 20) (ELit (-1)));
   KWord (SA vSP (-112)) 4 (V 22);
   KWord (SA vSP (-108)) 4 (ELit 0);
   KWord (SA vTHIS 72) 8 vBUF;
   KWord (SA vTHIS 80) 8 vLEN;
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
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vBUF 16 0x7fffff7fffff;
   KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vA1 16 0x7fffff7fffff;
   KAlign vA1 16;
   KRange (add vA1 idxlen) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-432)) (ELit 432) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-432)) (ELit 432) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-432)) (ELit 432) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KWr (SA vSP (-432)) (ELit 432);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x2550c].
Definition P : ST.tmpl := ST.TMG 0x28220 P_regs P_kn 26%nat (sub vLEN (V 20)) 1%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 2 [vSP]; ST.GA 7 [vA1; (V 23); add (V 20) (ELit (-1)); add (V 21) (ELit (-4)); (V 22)]].

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 22); (V 23); (V 24);
   vS0; vS1; ((V 20)); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 32); (V 33); (V 34); (V 35)].
Definition X_kn : list kentry :=
  [KWord (SA vTHIS 8) 4 (V 21);
   KRange vLEN 0 1048512;
   KRange vSP 0x7fff00000000 0x800000000000;
   KAlign vSP 16;
   KRange vBUF 16 0x7fffff7fffff;
   KRange (add vBUF (add vLEN (ELit 64))) 16 0x7fffff800000;
   KRange vTHIS 16 0x7fffff7fffff;
   KAlign vTHIS 16;
   KRange (add vTHIS (ELit 96)) 16 0x7fffff800000;
   KRange vA1 16 0x7fffff7fffff;
   KAlign vA1 16;
   KRange (add vA1 idxlen) 16 0x7fffff800000;
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vTHIS 0) (ELit 96);
   KDisj (SA (ELit 0) 0x10000) (ELit 0xa3000) (SA vA1 0) idxlen;
   KDisj (SA vSP (-432)) (ELit 432) (SA vBUF 0) (add vLEN (ELit 64));
   KDisj (SA vSP (-432)) (ELit 432) (SA vTHIS 0) (ELit 96);
   KDisj (SA vSP (-432)) (ELit 432) (SA vA1 0) idxlen;
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vTHIS 0) (ELit 96);
   KDisj (SA vBUF 0) (add vLEN (ELit 64)) (SA vA1 0) idxlen;
   KDisj (SA vTHIS 0) (ELit 96) (SA vA1 0) idxlen;
   KWr (SA vSP (-432)) (ELit 432);
   KWr (SA vTHIS 8) (ELit 4);
   KWr (SA vTHIS 24) (ELit 4);
   KWr (SA vTHIS 72) (ELit 16);
   KWr (SA vA1 0) idxlen;
   KUnk (SA vBUF 0) (add vLEN (ELit 64));
   KImg 0x10000 0x2550c;
   KRange (V 20) 0 63;
   KWord (SA vTHIS 72) 8 vBUF;
   KWord (SA vTHIS 80) 8 vLEN].
Definition X : ST.tmpl := ST.TMG 0x29660 X_regs X_kn 36%nat (ELit 0) 0%nat [ST.GA 1 [vBUF; vLEN]; ST.GA 6 [vA1; (V 20); (V 21); vTHIS]].

Definition U1G : SP.prog := SP.PGC 20 [T0; H; S; P] [X] [(vSP, -432, ELit 432); (vTHIS, 8, ELit 4); (vTHIS, 24, ELit 4); (vTHIS, 72, ELit 16); (vA1, 0, idxlen)] [] [].
