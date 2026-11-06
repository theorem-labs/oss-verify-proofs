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
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemU.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module MMVU_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition MMVU_IT : itab := APC.mk_itab_ranges SG [(0x7a388, 95%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition vDO := V 17.
Definition vN := V 18.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; ((add vX vDO)); (vX); (vN); (V 22); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition T0 : ST.tmpl := ST.TM 0x7a388 T0_regs T0_kn 31%nat (ELit 1000) 9%nat.

(* [comment removed for export] *)
Definition MC_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (sub (add vX (vN)) (V 19)); ((V 19)); (sub (add (add vX vDO) (vN)) (V 19)); (ELit 15); (V 23);
   (V 24); (V 25); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition MC_kn : list kentry :=
  [KRange (V 19) 16 488;
   KAlign (V 19) 8;
   KRange (sub (vN) (V 19)) 0 2000;
   KRange (sub vDO vN) 0 480;
   KDisj (SA vX 0) vN (SA (add vX vDO) 0) vN;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition MC : ST.tmpl := ST.TM 0x7a0b0 MC_regs MC_kn 30%nat ((V 19)) 1%nat.

(* [comment removed for export] *)
Definition TJ_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (sub (add vX (vN)) (V 19)); ((V 19)); (sub (add (add vX vDO) (vN)) (V 19)); (V 23); (V 24);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition TJ_kn : list kentry :=
  [KRange (V 19) 0 15;
   KRange (sub (vN) (V 19)) 0 2000;
   KRange (sub vDO vN) 0 480;
   KDisj (SA vX 0) vN (SA (add vX vDO) 0) vN;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition TJ : ST.tmpl := ST.TM 0x7a0e0 TJ_regs TJ_kn 31%nat ((V 19)) 0%nat.

(* [comment removed for export] *)
Definition BW_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (vX); ((V 19)); (V 23); (add vX (ELit (-8))); (add (add vX vDO) (ELit (-8)));
   (ELit 7); (V 24); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 25); (V 26); (V 27); (V 28)].
Definition BW_kn : list kentry :=
  [KRange (V 19) 8 488;
   KAlign (V 19) 8;
   KRange (sub (vN) (V 19)) 0 480;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition BW : ST.tmpl := ST.TM 0x7a4b4 BW_regs BW_kn 29%nat ((V 19)) 0%nat.

(* [comment removed for export] *)
Definition BB_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (add vX (V 19)); (sub (ELit (-1)) (V 19)); (add (add vX vDO) (V 19)); (V 23); (V 24);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition BB_kn : list kentry :=
  [KRange (V 19) 0 487;
   KRange (sub (vN) (V 19)) 1 488;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition BB : ST.tmpl := ST.TM 0x7a3fc BB_regs BB_kn 31%nat ((V 19)) 0%nat.

(* [comment removed for export] *)
Definition XM_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XM_kn : list kentry :=
  [].
Definition XM : ST.tmpl := ST.TM 0x7a414 XM_regs XM_kn 34%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XC1_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC1_kn : list kentry :=
  [].
Definition XC1 : ST.tmpl := ST.TM 0x7a354 XC1_regs XC1_kn 34%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XC2_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC2_kn : list kentry :=
  [].
Definition XC2 : ST.tmpl := ST.TM 0x7a384 XC2_regs XC2_kn 34%nat (ELit 0) 0%nat.

Definition MMVU : SP.prog := SP.PGC 19 [T0; MC; TJ; BW; BB] [XM; XC1; XC2] [((add vX vDO), 0, vN)] [SX.SpEnum 0x7a0e0 (EVar 12) 0 15] [].
End MMVU_defs.

Module MMVU_sum.
(* [comment removed for export] *)
Definition MMVSU : SP.summ := SP.SUM 19 MMVU_defs.T0 [MMVU_defs.XM; MMVU_defs.XC1; MMVU_defs.XC2]
  [(MMVU_defs.add MMVU_defs.vX MMVU_defs.vDO, 0, MMVU_defs.vN)].
End MMVU_sum.

Module LADU_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition LADU_IT : itab := APC.mk_itab_ranges SG [(0x44e58, 121%nat)].
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
Definition vX := V 16.
Definition vY := V 17.
Definition vZL := V 18.
Definition vI := V 19.
Definition vLX := V 20.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; (vX); (vY); (vZL); (vI); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62].
Definition T0 : ST.tmpl := ST.TM 0x44e58 T0_regs T0_kn 32%nat (ELit 4096) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vX); (vY); (vZL); (vI); ((add vZL vI)); (V 26);
   (vLX); (V 27); (V 28); (V 29); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition RS_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) vLX))) 8 496;
   KRange (add vZL (add vI (mul (-1) vLX))) 1 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62].
Definition RS : ST.tmpl := ST.TM 0x44e98 RS_regs RS_kn 34%nat (ELit 3500) 0%nat.

(* [comment removed for export] *)
Definition RZ_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (ELit 1); (V 22); (V 23);
   (V 24); (V 25); (vX); (vY); (vZL); (vI); ((add vZL vI)); (add vX (mul 8 (sub (add vZL vI) (V 21))));
   (add (V 21) (ELit 1)); (ELit (-8)); (V 26); (V 27); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition RZ_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 21)))) 0 488;
   KRange (V 21) 1 62;
   KRange (sub (add vZL vI) (V 21)) 0 61;
   KRange (add vZL vI) 1 62;
   KRange (sub (sub (add vZL vI) (V 21)) vLX) 0 61;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62].
Definition RZ : ST.tmpl := ST.TM 0x44ec4 RZ_regs RZ_kn 32%nat (add (ELit 3072) (V 21)) 0%nat.

(* [comment removed for export] *)
Definition ML_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (ELit 0); (sub (ELit (-1)) vY); (add (sub (add vZL vI) (V 22)) (ELit (-63)));
   (V 24); (V 25); (vX); (vY); (vZL); (vI); (ELit 1); (sub (ELit (-1)) vX);
   (mul 8 (sub vZL (V 22))); ((V 23)); (V 26); (V 27); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (mul 8 (sub (add vZL vI) (V 22))); ((V 22)); (V 28); (V 29)].
Definition ML_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 22)))) 8 488;
   KRange (V 22) 1 62;
   KRange (sub vZL (V 22)) 0 61;
   KRange (sub (add vZL vI) (V 22)) 1 61;
   KRange (V 23) 0 1;
   KRange (sub (V 21) (add vZL vI)) 0 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 1 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62].
Definition ML : ST.tmpl := ST.TM 0x44f40 ML_regs ML_kn 30%nat (add (ELit 2048) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition CL_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vX); ((V 21)); (add (sub (V 21) (V 22)) (ELit (-64))); (mul 8 (sub (V 21) (V 22))); (ELit 1); (sub (ELit (-1)) vX);
   ((V 22)); (V 28); (V 29); (V 30); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition CL_kn : list kentry :=
  [KRange (add (mul 8 (V 21)) (mul (-8) (V 22))) 8 496;
   KRange (V 22) 0 61;
   KRange (sub (V 21) (V 22)) 1 62;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 1 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62].
Definition CL : ST.tmpl := ST.TM 0x44fb4 CL_regs CL_kn 35%nat ((V 22)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 23); (V 24); (V 25);
   vS0; vS1; ((V 22)); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 33); (V 34); (V 35); (V 36)].
Definition XR_kn : list kentry :=
  [KRange (V 22) 0 1;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 0 62].
Definition XR : ST.tmpl := ST.TM 0x45028 XR_regs XR_kn 37%nat (ELit 0) 0%nat.

Definition LADU : SP.prog := SP.PGC 21 [T0; RS; RZ; ML; CL] [XR] [(vSP, -32, ELit 32); (vX, 0, ELit 498)] [] [].
End LADU_defs.

Module LADU_sum.
(* [comment removed for export] *)
Definition LADSU : SP.summ := SP.SUM 21 LADU_defs.T0 [LADU_defs.XR] [(LADU_defs.vSP, -32, ELit 32); (LADU_defs.vX, 0, ELit 498)].
End LADU_sum.

Module LMU_defs.
Import LADU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition LMU_IT : itab := APC.mk_itab_ranges SG [(0x44b18, 208%nat); (0x44e58, 121%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (vX); (ELit 105168); (ELit 5); (V 21); (V 22); (V 23);
   (V 24); (V 25); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 26); (V 27); (V 28); (V 29)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62;
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition T0 : ST.tmpl := ST.TM 0x44b18 T0_regs T0_kn 30%nat (ELit 32768) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x44b94); (spo (-1120)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (vX); (ELit 5); (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); (ELit 105168); (mul 8 (V 17)); ((V 17)); (sub (ELit (-1)) (spo (-608))); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition R1_kn : list kentry :=
  [KWord (SA vSP (-112)) 2 (ELit 0);
   KUnk (SA vSP (-608)) (mul 8 (V 17));
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition R1 : ST.tmpl := ST.TM 0x44b94 R1_regs R1_kn 33%nat (ELit 28672) 0%nat.

(* [comment removed for export] *)
Definition SM1_regs : list expr :=
  [ELit 0; (V 20); (spo (-1120)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 5); ((V 19)); (sub (ELit 63) (V 18)); (sub (EAlu ALU_SRL (mul (-1) vX) (ELit 3)) (V 18)); (ELit 1414648277510068013); (sub (EAlu ALU_SRL (mul (-1) vX) (ELit 3)) (V 17)); (add vX (mul 8 (V 18)));
   (V 24); (V 25); (ELit 105168); (mul 8 (V 17)); ((V 17)); ((V 17)); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition SM1_kn : list kentry :=
  [KRange (add (mul 8 (V 17)) (mul (-8) (V 18))) 8 496;
   KRange (V 18) 0 61;
   KRange (sub (V 17) (V 18)) 1 62;
   KWord (SA vSP (-112)) 2 (V 17);
   KRange (V 17) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 17));
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition SM1 : ST.tmpl := ST.TM 0x44bec SM1_regs SM1_kn 30%nat (add (ELit 24576) (sub (V 17) (V 18))) 0%nat.

(* [comment removed for export] *)
Definition OL_regs : list expr :=
  [ELit 0; (V 20); (spo (-1120)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 5); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105168); ((V 17)); (mul 8 (V 19)); ((V 19)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 19));
   (V 32); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 33); (V 34); (V 35); (V 36)].
Definition OL_kn : list kentry :=
  [KRange (V 17) 1 4;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-112)) 2 (V 19);
   KRange (V 19) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 19));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition OL : ST.tmpl := ST.TM 0x44cfc OL_regs OL_kn 37%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 4000))) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x44d34); (spo (-1120)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (ELit 5); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 105168); ((V 17)); (mul 8 (V 19)); ((V 19)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 19));
   (V 31); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 32); (V 33); (V 34); (V 35)].
Definition R2_kn : list kentry :=
  [KRange (V 19) 1 62;
   KWord (SA vSP (-616)) 2 (ELit 0);
   KUnk (SA vSP (-1112)) (mul 8 (V 19));
   KRange (V 17) 1 4;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-112)) 2 (V 19);
   KRange (V 19) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 19));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition R2 : ST.tmpl := ST.TM 0x44d34 R2_regs R2_kn 36%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 3600))) 0%nat.

(* [comment removed for export] *)
Definition SMZ_regs : list expr :=
  [ELit 0; (V 22); (spo (-1120)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vX); (ELit 5); ((V 19)); ((V 19)); ((V 21)); (add (sub (ELit 63) (V 19)) (V 20)); (add (spo (-1112)) (mul 8 (V 19))); (add (spo (-1112)) (mul 8 (sub (V 19) (V 20))));
   (V 26); (V 27); (ELit 105168); ((V 17)); (mul 8 (V 19)); ((V 19)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 19));
   (V 28); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 29); (V 30); (V 31); (V 32)].
Definition SMZ_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 62;
   KRange (V 19) 1 62;
   KWord (SA vSP (-616)) 2 (V 19);
   KUnk (SA vSP (-1112)) (mul 8 (V 19));
   KRange (V 17) 1 4;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-112)) 2 (V 19);
   KRange (V 19) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 19));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition SMZ : ST.tmpl := ST.TM 0x44d88 SMZ_regs SMZ_kn 33%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (add (ELit 3000) (V 20)))) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x44cf0); (spo (-1120)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 5); ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 105168); ((V 17)); (mul 8 (V 19)); ((V 19)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 19));
   (V 31); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 32); (V 33); (V 34); (V 35)].
Definition R3_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (V 17) 1 4;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-112)) 2 (V 19);
   KRange (V 19) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 19));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition R3 : ST.tmpl := ST.TM 0x44cf0 R3_regs R3_kn 36%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 2000))) 0%nat.

(* [comment removed for export] *)
Definition NM_regs : list expr :=
  [ELit 0; (V 18); (spo (-1120)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (V 22); (ELit 1); ((V 17)); (sub (ELit (-1)) vX); (V 23); (V 24); (V 25);
   (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition NM_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition NM : ST.tmpl := ST.TM 0x44c68 NM_regs NM_kn 42%nat ((V 17)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; ((V 18)); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition XR_kn : list kentry :=
  [KRange (V 18) 0 1;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62].
Definition XR : ST.tmpl := ST.TM 0x44e50 XR_regs XR_kn 33%nat (ELit 0) 0%nat.

Definition LMU : SP.prog := SP.PGC 17 [T0; R1; SM1; OL; R2; SMZ; R3; NM] [XR] [(vSP, -1152, ELit 1152); (vX, 0, ELit 498)] [] [MMU.MCPU 0x44b94; MMU.MCPU 0x44d34; LADSU].
End LMU_defs.

Module LMU_sum.
(* [comment removed for export] *)
Definition LMSU : SP.summ := SP.SUM 17 LMU_defs.T0 [LMU_defs.XR] [(LMU_defs.vSP, -1152, ELit 1152); (LMU_defs.vX, 0, ELit 498)].
End LMU_sum.

Module P5U_defs.
Import LMU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition P5U_IT : itab := APC.mk_itab_ranges SG [(0x44920, 126%nat); (0x44b18, 208%nat)].
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
Definition vX := V 16.
Definition vE0 := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vE0); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KRange vE0 0 2147483647;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition T0 : ST.tmpl := ST.TM 0x44920 T0_regs T0_kn 32%nat (ELit 8589934592) 0%nat.

(* [comment removed for export] *)
Definition PA_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105168); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition PA_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition PA : ST.tmpl := ST.TM 0x44954 PA_regs PA_kn 36%nat (add (ELit 4294967296) (V 18)) 1%nat.

(* [comment removed for export] *)
Definition PR_regs : list expr :=
  [ELit 0; (ELit 0x44964); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 105168); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition PR_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KRange (V 20) 0 1;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition PR : ST.tmpl := ST.TM 0x44964 PR_regs PR_kn 35%nat (add (ELit 4294967296) (V 18)) 0%nat.

(* [comment removed for export] *)
Definition PB_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (sub (ELit (-1)) vX); (V 24); (ELit 7450580596923828125); (add vX (ELit 8)); (ELit 26); (ELit 61);
   (V 25); (V 26); (V 27); (V 28); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition PB_kn : list kentry :=
  [KRange (V 18) 27 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition PB : ST.tmpl := ST.TM 0x449a0 PB_regs PB_kn 33%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (ELit 1000))) 0%nat.

(* [comment removed for export] *)
Definition PC_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (add vX (mul 8 (V 19))); (add vX (mul 8 (sub (V 19) (V 20)))); (V 23);
   (vX); ((V 18)); (sub (ELit (-1)) vX); ((V 19)); (ELit 7450580596923828125); (add vX (ELit 8)); (ELit 26); (ELit 61);
   ((V 21)); (add (sub (ELit 63) (V 19)) (V 20)); (V 24); (V 25); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition PC_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 62;
   KRange (V 18) 27 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition PC : ST.tmpl := ST.TM 0x449c8 PC_regs PC_kn 30%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (V 20))) 0%nat.

(* [comment removed for export] *)
Definition PD_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vX); (add (ELit 105208) (V 18)); (ELit 1); ((V 19)); ((V 21)); (add (sub (ELit 63) (V 19)) (V 20)); (V 26); (add vX (mul 8 (V 19)));
   (add vX (mul 8 (sub (V 19) (V 20)))); (V 27); (V 28); (V 29); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition PD_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 62;
   KRange (V 18) 8 208;
   KAlign (V 18) 8;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c].
Definition PD : ST.tmpl := ST.TM 0x44a6c PD_regs PD_kn 34%nat ((V 20)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; ((V 19)); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TM 0x44b10 XR_regs XR_kn 34%nat (ELit 0) 0%nat.

Definition P5U : SP.prog := SP.PGC 18 [T0; PA; PR; PB; PC; PD] [XR] [(vSP, -1200, ELit 1200); (vX, 0, ELit 498)] [] [LMSU].
End P5U_defs.

Module P5U_sum.
(* [comment removed for export] *)
Definition P5SU : SP.summ := SP.SUM 18 P5U_defs.T0 [P5U_defs.XR] [(P5U_defs.vSP, -1200, ELit 1200); (P5U_defs.vX, 0, ELit 498)].
End P5U_sum.

Module SHLU_defs.
Import MMVU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition SHLU_IT : itab := APC.mk_itab_ranges SG [(0x4503c, 90%nat); (0x7a388, 95%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition vN0 := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vN0); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX 0) (ELit 498)].
Definition T0 : ST.tmpl := ST.TM 0x4503c T0_regs T0_kn 32%nat (ELit 4096) 0%nat.

(* [comment removed for export] *)
Definition SB_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (V 25); ((V 18)); (vN0); ((V 20)); (add (sub (ELit 63) (V 18)) (V 19)); (sub (ELit 64) (V 20)); (add vX (mul 8 (V 18)));
   (V 26); (add vX (mul 8 (sub (V 18) (V 19)))); (V 27); (V 28); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition SB_kn : list kentry :=
  [KRange (V 19) 1 62;
   KRange (sub (V 18) (V 19)) 0 62;
   KRange (V 20) 1 63;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX 0) (ELit 498)].
Definition SB : ST.tmpl := ST.TM 0x45094 SB_regs SB_kn 33%nat (add (ELit 3072) (V 19)) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 19); (spo (-48)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (V 24); (vN0); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (V 32); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition J1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX 0) (ELit 498)].
Definition J1 : ST.tmpl := ST.TM 0x450e8 J1_regs J1_kn 37%nat (ELit 2048) 0%nat.

(* [comment removed for export] *)
Definition RM_regs : list expr :=
  [ELit 0; (ELit 0x4513c); (spo (-48)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (add vX (mul 8 (EAlu ALU_SRL vN0 (ELit 6)))); (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)); ((EAlu ALU_SRL vN0 (ELit 6))); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition RM_kn : list kentry :=
  [KRange (EAlu ALU_SRL vN0 (ELit 6)) 1 61;
   KRange (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)) 2 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX 0) (ELit 498)].
Definition RM : ST.tmpl := ST.TM 0x4513c RM_regs RM_kn 34%nat (ELit 1500) 0%nat.

(* [comment removed for export] *)
Definition ZF_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (mul 8 (EAlu ALU_SRL vN0 (ELit 6)))); (add (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) (ELit 1)); (ELit (-8)); (ELit 1); (add vX (mul 8 (V 19))); (V 24); (V 25);
   (V 26); (V 27); (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)); ((EAlu ALU_SRL vN0 (ELit 6))); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition ZF_kn : list kentry :=
  [KRange (add (mul 8 (EAlu ALU_SRL vN0 (ELit 6))) (mul (-8) (V 19))) 8 488;
   KRange (V 19) 0 60;
   KRange (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) 1 61;
   KRange (EAlu ALU_SRL vN0 (ELit 6)) 1 61;
   KRange (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)) 2 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX 0) (ELit 498)].
Definition ZF : ST.tmpl := ST.TM 0x45150 ZF_regs ZF_kn 32%nat (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; ((V 19)); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TM 0x4519c XR_regs XR_kn 34%nat (ELit 0) 0%nat.

Definition SHLU : SP.prog := SP.PGC 18 [T0; SB; J1; RM; ZF] [XR] [(vSP, -48, ELit 48); (vX, 0, ELit 498)] [] [MMVSU].
End SHLU_defs.

Module SHLU_sum.
(* [comment removed for export] *)
Definition SHLSU : SP.summ := SP.SUM 18 SHLU_defs.T0 [SHLU_defs.XR] [(SHLU_defs.vSP, -48, ELit 48); (SHLU_defs.vX, 0, ELit 498)].
End SHLU_sum.

Module NDCU_defs.
Import P5U_sum.
Import SHLU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition NDCU_IT : itab := APC.mk_itab_ranges SG [(0x443d0, 193%nat); (0x44920, 126%nat); (0x4503c, 90%nat); (0x7a504, 100%nat)].
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
Definition vX := V 16.
Definition vM := V 17.
Definition vP2 := V 18.
Definition vRE := V 19.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; (vX); (vM); (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (vRE); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KRange vSP 140728898422512 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1776)) (ELit 1776);
   KUnk (SA vSP (-1776)) (ELit 1776);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1776)) (ELit 1776) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c;
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960].
Definition T0 : ST.tmpl := ST.TM 0x443d0 T0_regs T0_kn 32%nat (ELit 102400) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x444e4); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (vRE); (vP2); (mul (-1) vP2); ((V 21)); ((V 22));
   (vS8); (vS9); (vS10); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition R1_kn : list kentry :=
  [KRange (add (V 22) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898422512 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1776)) (ELit 1776);
   KUnk (SA vSP (-1776)) (ELit 1776);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1776)) (ELit 1776) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c;
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960].
Definition R1 : ST.tmpl := ST.TM 0x444e4 R1_regs R1_kn 38%nat (ELit 92160) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x44514); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (vRE); (vP2); (mul (-1) vP2); (sub (V 22) vRE); ((V 22));
   (vS8); (vS9); (vS10); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition R2_kn : list kentry :=
  [KRange (add (V 22) (ELit 9223372036854775808)) 9223372036854774732 9223372036854776779;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-80)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898422512 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1776)) (ELit 1776);
   KUnk (SA vSP (-1776)) (ELit 1776);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1776)) (ELit 1776) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c;
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960].
Definition R2 : ST.tmpl := ST.TM 0x44514 R2_regs R2_kn 38%nat (ELit 81920) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x44528); (spo (-576)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (vM); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (vX); (vRE); (vP2); (mul (-1) vP2); (V 33); (V 34);
   (vS8); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition R3_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-80)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898422512 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1776)) (ELit 1776);
   KUnk (SA vSP (-1776)) (ELit 1776);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1776)) (ELit 1776) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c;
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960].
Definition R3 : ST.tmpl := ST.TM 0x44528 R3_regs R3_kn 39%nat (ELit 71680) 0%nat.

(* [comment removed for export] *)
Definition CMP_regs : list expr :=
  [ELit 0; (V 22); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (EAlu ALU_SRL (mul 4294967296 vP2) (ELit 32)); (vM); (ELit 1); (V 26); (sub (ELit (-1)) vX); ((spo (-576))); (sub (ELit (-1)) (spo (-576))); (ELit (-16));
   (add (V 21) (ELit (-8))); (V 27); (vX); (vRE); (vP2); (mul (-1) vP2); (V 28); (V 29);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition CMP_kn : list kentry :=
  [KRange (sub (mul 8 (V 20)) (V 21)) 0 496;
   KRange (V 21) 0 496;
   KAlign (V 21) 8;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-80)) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898422512 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1776)) (ELit 1776);
   KUnk (SA vSP (-1776)) (ELit 1776);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1776)) (ELit 1776) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2550c;
   KRange (mul (-1) vRE) 1 1048576;
   KRange (add vRE (ELit 9223372036854775808)) 9223372036853727232 9223372036854775807;
   KRange (add vP2 (ELit 9223372036854775808)) 9223372036852678656 9223372036856872960].
Definition CMP : ST.tmpl := ST.TM 0x44580 CMP_regs CMP_kn 34%nat (add (ELit 20480) (V 21)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 32); (V 33); (V 34); (V 35)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62].
Definition XR : ST.tmpl := ST.TM 0x44694 XR_regs XR_kn 36%nat (ELit 0) 0%nat.

Definition NDCU : SP.prog := SP.PGC 20 [T0; R1; R2; R3; CMP] [XR] [(vSP, -1776, ELit 1776); (vX, 0, ELit 498)] [SX.SpW 0x44408; SX.SpW 0x44424; SX.SpW 0x44474; SX.SpW 0x44490; SX.SpW 0x444f8; SX.SpW 0x44504; SX.SpW 0x445c4; SX.SpW 0x44610; SX.SpW 0x4462c; SX.SpW 0x4469c; SX.SpW 0x446c0; SX.SpAl 0x44590] [MMU.MSP 0 0x444e4; P5SU; SHLSU].
End NDCU_defs.

Module NDCU_sum.
(* [comment removed for export] *)
Definition NDCSU : SP.summ := SP.SUM 20 NDCU_defs.T0 [NDCU_defs.XR] [(NDCU_defs.vSP, -1776, ELit 1776); (NDCU_defs.vX, 0, ELit 498)].
End NDCU_sum.

Module MMVUN_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition MMVUN_IT : itab := APC.mk_itab_ranges SG [(0x7a388, 95%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition vDO := V 17.
Definition vN := V 18.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; ((add vX vDO)); (vX); (vN); (V 22); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition T0 : ST.tmpl := ST.TMG 0x7a388 T0_regs T0_kn 31%nat (ELit 1000) 9%nat [ST.GA 10 [add vX vN]].

(* [comment removed for export] *)
Definition MC_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (sub (add vX (vN)) (V 19)); ((V 19)); (sub (add (add vX vDO) (vN)) (V 19)); (ELit 15); (V 23);
   (V 24); (V 25); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition MC_kn : list kentry :=
  [KRange (V 19) 16 488;
   KAlign (V 19) 8;
   KRange (sub (vN) (V 19)) 0 2000;
   KRange (sub vDO vN) 0 480;
   KDisj (SA vX 0) vN (SA (add vX vDO) 0) vN;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition MC : ST.tmpl := ST.TMG 0x7a0b0 MC_regs MC_kn 30%nat ((V 19)) 1%nat [ST.GA 10 [add vX vN]].

(* [comment removed for export] *)
Definition TJ8_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (sub (add vX (vN)) (V 19)); ((V 19)); (sub (add (add vX vDO) (vN)) (V 19)); (V 23); (V 24);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition TJ8_kn : list kentry :=
  [KRange (V 19) 8 15;
   KAlign (V 19) 8;
   KRange (sub (vN) (V 19)) 0 2000;
   KRange (sub vDO vN) 0 480;
   KDisj (SA vX 0) vN (SA (add vX vDO) 0) vN;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition TJ8 : ST.tmpl := ST.TMG 0x7a0e8 TJ8_regs TJ8_kn 31%nat ((V 19)) 0%nat [ST.GA 10 [add vX vN]].

(* [comment removed for export] *)
Definition TJ0_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vS0); (vS1); ((add vX vDO)); (sub (add vX (vN)) (V 20)); ((V 19)); (sub (add (add vX vDO) (vN)) (V 20)); (V 24); (V 25);
   (V 26); (V 27); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition TJ0_kn : list kentry :=
  [KRange (V 19) 0 15;
   KAlign (V 19) 8;
   KRange (V 20) 0 7;
   KAlign (V 20) 8;
   KRange (sub (vN) (V 20)) 0 2000;
   KRange (sub vDO vN) 0 480;
   KDisj (SA vX 0) vN (SA (add vX vDO) 0) vN;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition TJ0 : ST.tmpl := ST.TMG 0x7a100 TJ0_regs TJ0_kn 32%nat (ELit 0) 0%nat [ST.GA 10 [add (add vX vDO) vN]].

(* [comment removed for export] *)
Definition BWS_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); ((add vX vDO)); (vX); (add (add vX vDO) (V 19)); ((V 19)); (add vX (ELit (-8))); (add (add vX vDO) (ELit (-8)));
   (ELit 7); (V 23); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 24); (V 25); (V 26); (V 27)].
Definition BWS_kn : list kentry :=
  [KRange (V 19) 0 480;
   KAlign (V 19) 8;
   KRange (sub (vN) (V 19)) 8 488;
   KAlign vX 8;
   KRange vX 0x10000 0x800000000000;
   KAlign vDO 8;
   KAlign vN 8;
   KRange vDO 8 488;
   KRange vN 8 488;
   KRange (add vDO vN) 16 496;
   KUnk (SA vX 0) vN;
   KWr (SA (add vX vDO) 0) vN].
Definition BWS : ST.tmpl := ST.TMG 0x7a4c8 BWS_regs BWS_kn 28%nat ((V 19)) 0%nat [ST.GA 10 [add (add vX vDO) vN]].

(* [comment removed for export] *)
Definition XM_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XM_kn : list kentry :=
  [].
Definition XM : ST.tmpl := ST.TMG 0x7a414 XM_regs XM_kn 34%nat (ELit 0) 0%nat [ST.GA 10 [add (add vX vDO) vN]].

(* [comment removed for export] *)
Definition XC1_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC1_kn : list kentry :=
  [].
Definition XC1 : ST.tmpl := ST.TMG 0x7a354 XC1_regs XC1_kn 34%nat (ELit 0) 0%nat [ST.GA 10 [add (add vX vDO) vN]].

(* [comment removed for export] *)
Definition XC2_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC2_kn : list kentry :=
  [].
Definition XC2 : ST.tmpl := ST.TMG 0x7a384 XC2_regs XC2_kn 34%nat (ELit 0) 0%nat [ST.GA 10 [add (add vX vDO) vN]].

Definition MMVUN : SP.prog := SP.PGC 19 [T0; MC; TJ8; TJ0; BWS] [XM; XC1; XC2] [((add vX vDO), 0, vN)] [SX.SpW 0x7a104; SX.SpW 0x7a348; SX.SpW 0x7a350; SX.SpW 0x7a3e0] [].
End MMVUN_defs.

Module MMVUN_sum.
(* [comment removed for export] *)
Definition MMVSUN : SP.summ := SP.SUM 19 MMVUN_defs.T0 [MMVUN_defs.XM; MMVUN_defs.XC1; MMVUN_defs.XC2] [(MMVUN_defs.add MMVUN_defs.vX MMVUN_defs.vDO, 0, MMVUN_defs.vN)].
End MMVUN_sum.

Module LADUN_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition LADUN_IT : itab := APC.mk_itab_ranges SG [(0x44e58, 121%nat)].
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
Definition vX := V 16.
Definition vY := V 17.
Definition vZL := V 18.
Definition vI := V 19.
Definition vLX := V 20.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; (vX); (vY); (vZL); (vI); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62;
   KRange vS5 0 55;
   KRange (sub (add vS5 (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vS5 (add vI (ELit 1))) vLX) 0 66].
Definition T0 : ST.tmpl := ST.TM 0x44e58 T0_regs T0_kn 32%nat (ELit 4096) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vX); (vY); (vZL); (vI); ((add vZL vI)); (V 26);
   (vLX); (V 27); (V 28); (V 29); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition RS_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) vLX))) 8 496;
   KRange (add vZL (add vI (mul (-1) vLX))) 1 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62;
   KRange vS5 0 55;
   KRange (sub (add vS5 (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vS5 (add vI (ELit 1))) vLX) 0 66].
Definition RS : ST.tmpl := ST.TM 0x44e98 RS_regs RS_kn 34%nat (ELit 3500) 0%nat.

(* [comment removed for export] *)
Definition RZ_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (ELit 1); (V 22); (V 23);
   (V 24); (V 25); (vX); (vY); (vZL); (vI); ((add vZL vI)); (add vX (mul 8 (sub (add vZL vI) (V 21))));
   (add (V 21) (ELit 1)); (ELit (-8)); (V 26); (V 27); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition RZ_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 21)))) 0 488;
   KRange (V 21) 1 62;
   KRange (sub (add vZL vI) (V 21)) 0 61;
   KRange (add vZL vI) 1 62;
   KRange (sub (sub (add vZL vI) (V 21)) vLX) 0 61;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62;
   KRange vS5 0 55;
   KRange (sub (add vS5 (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vS5 (add vI (ELit 1))) vLX) 0 66].
Definition RZ : ST.tmpl := ST.TM 0x44ec4 RZ_regs RZ_kn 32%nat (add (ELit 3072) (V 21)) 0%nat.

(* [comment removed for export] *)
Definition ML_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (ELit 0); (sub (ELit (-1)) vY); (add (sub (add vZL vI) (V 22)) (ELit (-63)));
   (V 24); (V 25); (vX); (vY); (vZL); (vI); (ELit 1); (sub (ELit (-1)) vX);
   (mul 8 (sub vZL (V 22))); ((V 23)); (V 26); (V 27); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (mul 8 (sub (add vZL vI) (V 22))); ((V 22)); (V 28); (V 29)].
Definition ML_kn : list kentry :=
  [KRange (V 21) 1 61;
   KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 22)))) 8 488;
   KRange (V 22) 1 62;
   KRange (sub vZL (V 22)) 0 61;
   KRange (sub (add vZL vI) (V 22)) 1 61;
   KRange (V 23) 0 1;
   KRange (sub (V 21) (add vZL vI)) 0 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 1 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62;
   KRange vS5 0 55;
   KRange (sub (add vS5 (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vS5 (add vI (ELit 1))) vLX) 0 66;
   KRange (sub (add vS5 (add vI (ELit 1))) (V 21)) 0 66].
Definition ML : ST.tmpl := ST.TM 0x44f40 ML_regs ML_kn 30%nat (add (ELit 2048) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition CL_regs : list expr :=
  [ELit 0; (vRA); (spo (-32)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vX); ((V 21)); (add (sub (V 21) (V 22)) (ELit (-64))); (mul 8 (sub (V 21) (V 22))); (ELit 1); (sub (ELit (-1)) vX);
   ((V 22)); (V 28); (V 29); (V 30); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition CL_kn : list kentry :=
  [KRange (V 21) 1 61;
   KRange (add (mul 8 (V 21)) (mul (-8) (V 22))) 8 496;
   KRange (V 22) 0 61;
   KRange (sub (V 21) (V 22)) 1 62;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 1 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KRange vSP 140728898420768 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-32)) (ELit 32);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vX 0) (ELit 498);
   KRange vY 0x7ffe00000000 0x800000000000;
   KAlign vY 8;
   KRange vZL 0 62;
   KRange vI 1 4;
   KUnk (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-32)) (ELit 32) (SA vY 0) (mul 8 vZL);
   KRange vLX 0 62;
   KRange vS5 0 55;
   KRange (sub (add vS5 (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vS5 (add vI (ELit 1))) vLX) 0 66;
   KRange (sub (add vS5 (add vI (ELit 1))) (V 21)) 0 66].
Definition CL : ST.tmpl := ST.TM 0x44fb4 CL_regs CL_kn 35%nat ((V 22)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 23); (V 24); (V 25);
   vS0; vS1; ((V 22)); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 33); (V 34); (V 35); (V 36)].
Definition XR_kn : list kentry :=
  [KRange (V 22) 1 1;
   KRange (sub (add vS5 (add vI (ELit 2))) (V 21)) 0 67;
   KWord (SA vX 496) 2 (V 21);
   KRange (V 21) 0 62].
Definition XR : ST.tmpl := ST.TM 0x45028 XR_regs XR_kn 37%nat (ELit 0) 0%nat.

Definition LADUN : SP.prog := SP.PGC 21 [T0; RS; RZ; ML; CL] [XR] [(vSP, -32, ELit 32); (vX, 0, ELit 498)] [] [].
End LADUN_defs.

Module LADUN_sum.
(* [comment removed for export] *)
Definition LADSUN : SP.summ := SP.SUM 21 LADUN_defs.T0 [LADUN_defs.XR] [(LADUN_defs.vSP, -32, ELit 32); (LADUN_defs.vX, 0, ELit 498)].
End LADUN_sum.

Module LMUN_defs.
Import LADUN_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition LMUN_IT : itab := APC.mk_itab_ranges SG [(0x44b18, 208%nat); (0x44e58, 121%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition vL0 := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (vX); (ELit 105168); (ELit 5); (V 21); (V 22); (V 23);
   (V 24); (V 25); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 26); (V 27); (V 28); (V 29)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 vL0;
   KRange vL0 0 62;
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vL0 0 49].
Definition T0 : ST.tmpl := ST.TM 0x44b18 T0_regs T0_kn 30%nat (ELit 32768) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x44b94); (spo (-1120)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (vX); (ELit 5); (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); (ELit 105168); (mul 8 vL0); (vL0); (sub (ELit (-1)) (spo (-608))); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition R1_kn : list kentry :=
  [KWord (SA vSP (-112)) 2 (ELit 0);
   KUnk (SA vSP (-608)) (mul 8 vL0);
   KWord (SA vX 496) 2 vL0;
   KRange vL0 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vL0 1 49].
Definition R1 : ST.tmpl := ST.TM 0x44b94 R1_regs R1_kn 33%nat (ELit 28672) 0%nat.

(* [comment removed for export] *)
Definition SM1_regs : list expr :=
  [ELit 0; (V 20); (spo (-1120)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 5); ((V 19)); (sub (ELit 63) (V 18)); (sub (EAlu ALU_SRL (mul (-1) vX) (ELit 3)) (V 18)); (ELit 1414648277510068013); (sub (EAlu ALU_SRL (mul (-1) vX) (ELit 3)) vL0); (add vX (mul 8 (V 18)));
   (V 24); (V 25); (ELit 105168); (mul 8 vL0); (vL0); (vL0); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition SM1_kn : list kentry :=
  [KRange (add (mul 8 vL0) (mul (-8) (V 18))) 8 496;
   KRange (V 18) 0 61;
   KRange (sub vL0 (V 18)) 1 62;
   KWord (SA vSP (-112)) 2 vL0;
   KRange vL0 0 62;
   KUnk (SA vSP (-608)) (mul 8 vL0);
   KWord (SA vX 496) 2 vL0;
   KRange vL0 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vL0 1 49].
Definition SM1 : ST.tmpl := ST.TM 0x44bec SM1_regs SM1_kn 30%nat (add (ELit 24576) (sub vL0 (V 18))) 0%nat.

(* [comment removed for export] *)
Definition OL_regs : list expr :=
  [ELit 0; (V 21); (spo (-1120)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (ELit 5); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (ELit 105168); ((V 18)); (mul 8 (V 20)); ((V 20)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 20));
   (V 33); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 34); (V 35); (V 36); (V 37)].
Definition OL_kn : list kentry :=
  [KRange (V 18) 1 4;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-112)) 2 (V 20);
   KRange (V 20) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 20));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange (sub (V 20) vL0) 0 0;
   KRange vL0 0 49;
   KRange (sub (add vL0 (add (V 18) (ELit 1))) (V 19)) 0 66].
Definition OL : ST.tmpl := ST.TM 0x44cfc OL_regs OL_kn 38%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 18))) (ELit 4000))) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x44d34); (spo (-1120)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 5); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105168); ((V 18)); (mul 8 (V 20)); ((V 20)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 20));
   (V 32); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 33); (V 34); (V 35); (V 36)].
Definition R2_kn : list kentry :=
  [KRange (V 20) 1 62;
   KWord (SA vSP (-616)) 2 (ELit 0);
   KUnk (SA vSP (-1112)) (mul 8 (V 20));
   KRange (V 18) 1 4;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-112)) 2 (V 20);
   KRange (V 20) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 20));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange (sub (V 20) vL0) 0 0;
   KRange vL0 0 49;
   KRange (sub (add vL0 (add (V 18) (ELit 1))) (V 19)) 0 66].
Definition R2 : ST.tmpl := ST.TM 0x44d34 R2_regs R2_kn 37%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 18))) (ELit 3600))) 0%nat.

(* [comment removed for export] *)
Definition SMZ_regs : list expr :=
  [ELit 0; (V 23); (spo (-1120)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vX); (ELit 5); ((V 20)); ((V 20)); ((V 22)); (add (sub (ELit 63) (V 20)) (V 21)); (add (spo (-1112)) (mul 8 (V 20))); (add (spo (-1112)) (mul 8 (sub (V 20) (V 21))));
   (V 27); (V 28); (ELit 105168); ((V 18)); (mul 8 (V 20)); ((V 20)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 20));
   (V 29); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 30); (V 31); (V 32); (V 33)].
Definition SMZ_kn : list kentry :=
  [KRange (V 21) 1 62;
   KRange (sub (V 20) (V 21)) 0 62;
   KRange (V 20) 1 62;
   KWord (SA vSP (-616)) 2 (V 20);
   KUnk (SA vSP (-1112)) (mul 8 (V 20));
   KRange (V 18) 1 4;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-112)) 2 (V 20);
   KRange (V 20) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 20));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange (sub (V 20) vL0) 0 0;
   KRange vL0 0 49;
   KRange (sub (add vL0 (add (V 18) (ELit 1))) (V 19)) 0 66].
Definition SMZ : ST.tmpl := ST.TM 0x44d88 SMZ_regs SMZ_kn 34%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 18))) (add (ELit 3000) (V 21)))) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x44cf0); (spo (-1120)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (ELit 5); ((V 21)); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105168); ((V 18)); (mul 8 (V 20)); ((V 20)); (sub (ELit (-1)) (ELit 105168)); (mul 281474976710656 (V 20));
   (V 32); (spo (-1104)); (sub (ELit (-1)) (spo (-1112))); (sub (ELit (-1)) (spo (-608))); (V 33); (V 34); (V 35); (V 36)].
Definition R3_kn : list kentry :=
  [KRange (V 18) 1 4;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-112)) 2 (V 20);
   KRange (V 20) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 20));
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange (V 21) 1 1;
   KRange (sub (V 20) vL0) 0 0;
   KRange vL0 0 49;
   KRange (sub (add vL0 (add (V 18) (ELit 2))) (V 19)) 0 67].
Definition R3 : ST.tmpl := ST.TM 0x44cf0 R3_regs R3_kn 37%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 18))) (ELit 2000))) 0%nat.

(* [comment removed for export] *)
Definition NM_regs : list expr :=
  [ELit 0; (V 19); (spo (-1120)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (ELit 1); ((V 18)); (sub (ELit (-1)) vX); (V 24); (V 25); (V 26);
   (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition NM_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
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
   KRange vSP 140728898421888 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1152)) (ELit 1152);
   KUnk (SA vSP (-1152)) (ELit 1152);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1152)) (ELit 1152) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vL0 0 49;
   KRange (sub (add vL0 (ELit 6)) (V 18)) 0 68].
Definition NM : ST.tmpl := ST.TM 0x44c68 NM_regs NM_kn 43%nat ((V 18)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; ((V 19)); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KRange (V 19) 1 1;
   KRange (sub (add vL0 (ELit 6)) (V 18)) 0 68;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TMG 0x44e50 XR_regs XR_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

Definition LMUN : SP.prog := SP.PGC 18 [T0; R1; SM1; OL; R2; SMZ; R3; NM] [XR] [(vSP, -1152, ELit 1152); (vX, 0, ELit 498)] [] [MMU.MCPU 0x44b94; MMU.MCPU 0x44d34; LADSUN].
End LMUN_defs.

Module LMUN_sum.
(* [comment removed for export] *)
Definition LMSUN : SP.summ := SP.SUM 18 LMUN_defs.T0 [LMUN_defs.XR] [(LMUN_defs.vSP, -1152, ELit 1152); (LMUN_defs.vX, 0, ELit 498)].
End LMUN_sum.

Module P5UN_defs.
Import LMUN_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition P5UN_IT : itab := APC.mk_itab_ranges SG [(0x44920, 126%nat); (0x44b18, 208%nat)].
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
Definition vX := V 16.
Definition vE0 := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vE0); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KRange vE0 0 327;
   KRange (V 18) 0 40;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition T0 : ST.tmpl := ST.TMG 0x44920 T0_regs T0_kn 32%nat (ELit 8589934592) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition PA_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105168); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition PA_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KRange (add (mul 22 (V 19)) (V 18)) 0 1207;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition PA : ST.tmpl := ST.TMG 0x44954 PA_regs PA_kn 36%nat (add (ELit 4294967296) (V 18)) 1%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition PR_regs : list expr :=
  [ELit 0; (ELit 0x44964); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 105168); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition PR_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KRange (V 20) 1 1;
   KRange (add (mul 22 (V 19)) (V 18)) 0 1339;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition PR : ST.tmpl := ST.TMG 0x44964 PR_regs PR_kn 35%nat (add (ELit 4294967296) (V 18)) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition PB_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (sub (ELit (-1)) vX); (V 24); (ELit 7450580596923828125); (add vX (ELit 8)); (ELit 26); (ELit 61);
   (V 25); (V 26); (V 27); (V 28); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition PB_kn : list kentry :=
  [KRange (V 18) 27 2147483647;
   KRange (add (mul 22 (V 19)) (V 18)) 0 1207;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition PB : ST.tmpl := ST.TMG 0x449a0 PB_regs PB_kn 33%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (ELit 1000))) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition PC_regs : list expr :=
  [ELit 0; (V 22); (spo (-48)); (vGP); (vTP); (add vX (mul 8 (V 19))); (add vX (mul 8 (sub (V 19) (V 20)))); (V 23);
   (vX); ((V 18)); (sub (ELit (-1)) vX); ((V 19)); (ELit 7450580596923828125); (add vX (ELit 8)); (ELit 26); (ELit 61);
   ((V 21)); (add (sub (ELit 63) (V 19)) (V 20)); (V 24); (V 25); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 26); (V 27); (V 28); (V 29)].
Definition PC_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 62;
   KRange (V 18) 27 2147483647;
   KRange (add (mul 22 (V 19)) (V 18)) 0 1207;
   KRange (V 19) 1 54;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition PC : ST.tmpl := ST.TMG 0x449c8 PC_regs PC_kn 30%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (V 20))) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition PD_regs : list expr :=
  [ELit 0; (V 23); (spo (-48)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vX); (add (ELit 105208) (V 18)); (ELit 1); ((V 19)); ((V 21)); (add (sub (ELit 63) (V 19)) (V 20)); ((V 22)); (add vX (mul 8 (V 19)));
   (add vX (mul 8 (sub (V 19) (V 20)))); (V 27); (V 28); (V 29); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition PD_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 19) (V 20)) 0 62;
   KRange (V 18) 8 208;
   KAlign (V 18) 8;
   KRange (V 19) 1 55;
   KRange (V 22) 1 18446744073709551615;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421936 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1200)) (ELit 1200);
   KUnk (SA vSP (-1200)) (ELit 1200);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1200)) (ELit 1200) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c].
Definition PD : ST.tmpl := ST.TMG 0x44a6c PD_regs PD_kn 34%nat ((V 20)) 0%nat [ST.GA 7 [vX; (V 19)]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; ((V 19)); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KRange (V 19) 1 1;
   KRange (V 18) 0 56;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TMG 0x44b10 XR_regs XR_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

Definition P5UN : SP.prog := SP.PGC 18 [T0; PA; PR; PB; PC; PD] [XR] [(vSP, -1200, ELit 1200); (vX, 0, ELit 498)] [SX.SpEnum 0x44a40 (EVar 9) 8 208] [LMSUN].
End P5UN_defs.

Module P5UN_sum.
(* [comment removed for export] *)
Definition P5SUN : SP.summ := SP.SUM 18 P5UN_defs.T0 [P5UN_defs.XR] [(P5UN_defs.vSP, -1200, ELit 1200); (P5UN_defs.vX, 0, ELit 498)].
End P5UN_sum.

Module SHLUN_defs.
Import MMVUN_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition SHLUN_IT : itab := APC.mk_itab_ranges SG [(0x4503c, 90%nat); (0x7a388, 95%nat); (0x79f84, 257%nat)].
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
Definition vX := V 16.
Definition vN0 := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vN0); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KRange (V 18) 0 56;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition T0 : ST.tmpl := ST.TMG 0x4503c T0_regs T0_kn 32%nat (ELit 4096) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition SB_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (V 25); ((V 18)); (vN0); ((V 20)); (add (sub (ELit 63) (V 18)) (V 19)); (sub (ELit 64) (V 20)); (add vX (mul 8 (V 18)));
   (V 26); (add vX (mul 8 (sub (V 18) (V 19)))); (V 27); (V 28); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition SB_kn : list kentry :=
  [KRange (V 18) 1 56;
   KRange vN0 0 327;
   KRange (V 19) 1 62;
   KRange (sub (V 18) (V 19)) 0 62;
   KRange (V 20) 1 63;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition SB : ST.tmpl := ST.TMG 0x45094 SB_regs SB_kn 33%nat (add (ELit 3072) (V 19)) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 19); (spo (-48)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (V 24); (vN0); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (V 32); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition J1_kn : list kentry :=
  [KRange (V 18) 0 57;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition J1 : ST.tmpl := ST.TMG 0x450e8 J1_regs J1_kn 37%nat (ELit 2048) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition JM_regs : list expr :=
  [ELit 0; (V 19); (spo (-48)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (ELit 62); (vN0); ((V 18)); (V 24); (V 25); (V 26);
   (V 27); (V 28); (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)); ((EAlu ALU_SRL vN0 (ELit 6))); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition JM_kn : list kentry :=
  [KRange (EAlu ALU_SRL vN0 (ELit 6)) 1 61;
   KRange (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)) 2 62;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition JM : ST.tmpl := ST.TMG 0x45108 JM_regs JM_kn 33%nat (ELit 1800) 0%nat [ST.GA 10 [add vX (mul 8 (V 18))]].

(* [comment removed for export] *)
Definition RM_regs : list expr :=
  [ELit 0; (ELit 0x4513c); (spo (-48)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (add vX (mul 8 (EAlu ALU_SRL vN0 (ELit 6)))); (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)); ((EAlu ALU_SRL vN0 (ELit 6))); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition RM_kn : list kentry :=
  [KRange (EAlu ALU_SRL vN0 (ELit 6)) 1 61;
   KRange (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)) 2 62;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition RM : ST.tmpl := ST.TMG 0x4513c RM_regs RM_kn 34%nat (ELit 1500) 0%nat [ST.GA 10 [add vX (add (mul 8 (EAlu ALU_SRL vN0 (ELit 6))) (mul 8 (V 18)))]].

(* [comment removed for export] *)
Definition ZF_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (add vX (mul 8 (EAlu ALU_SRL vN0 (ELit 6)))); (add (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) (ELit 1)); (ELit (-8)); (ELit 1); (add vX (mul 8 (V 19))); (V 24); (V 25);
   (V 26); (V 27); (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)); ((EAlu ALU_SRL vN0 (ELit 6))); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition ZF_kn : list kentry :=
  [KRange (add (mul 8 (EAlu ALU_SRL vN0 (ELit 6))) (mul (-8) (V 19))) 8 488;
   KRange (V 19) 0 60;
   KRange (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) 1 61;
   KRange (EAlu ALU_SRL vN0 (ELit 6)) 1 61;
   KRange (add (EAlu ALU_SRL vN0 (ELit 6)) (V 18)) 2 62;
   KRange vN0 0 327;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898420784 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-48)) (ELit 48);
   KUnk (SA vSP (-48)) (ELit 48);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-48)) (ELit 48) (SA vX (-8)) (ELit 506)].
Definition ZF : ST.tmpl := ST.TMG 0x45150 ZF_regs ZF_kn 32%nat (sub (EAlu ALU_SRL vN0 (ELit 6)) (V 19)) 0%nat [ST.GA 10 [add vX (add (mul 8 (EAlu ALU_SRL vN0 (ELit 6))) (mul 8 (V 18)))]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; ((V 19)); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KRange (V 19) 1 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TMG 0x4519c XR_regs XR_kn 34%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

Definition SHLUN : SP.prog := SP.PGC 18 [T0; SB; J1; JM; RM; ZF] [XR] [(vSP, -48, ELit 48); (vX, 0, ELit 498)] [] [MMVSUN].
End SHLUN_defs.

Module SHLUN_sum.
(* [comment removed for export] *)
Definition SHLSUN : SP.summ := SP.SUM 18 SHLUN_defs.T0 [SHLUN_defs.XR] [(SHLUN_defs.vSP, -48, ELit 48); (SHLUN_defs.vX, 0, ELit 498)].
End SHLUN_sum.

Module HI64U_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition HI64U_IT : itab := APC.mk_itab_ranges SG [(0x446d4, 147%nat)].
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
Definition vX := V 16.
Definition vTR := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vTR); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898420736 0x800000000000;
   KAlign vSP 16;
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KUnk (SA vX 0) (ELit 498);
   KRange vTR 0x7ffe00000000 0x800000000000;
   KWr (SA vTR 0) (ELit 1);
   KDisj (SA vTR 0) (ELit 1) (SA vX (-8)) (ELit 506)].
Definition T0 : ST.tmpl := ST.TMG 0x446d4 T0_regs T0_kn 32%nat (ELit 4096) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition G1_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vS0); (vS1); ((V 18)); (vTR); (V 22); (sub (ELit (-1)) vX); (V 23); (V 24);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition G1_kn : list kentry :=
  [KRange (V 18) 1 18446744073709551615;
   KWord (SA vX 496) 2 (ELit 1);
   KWord (SA vTR 0) 1 (ELit 0);
   KRange vSP 140728898420736 0x800000000000;
   KAlign vSP 16;
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KUnk (SA vX 0) (ELit 498);
   KRange vTR 0x7ffe00000000 0x800000000000;
   KWr (SA vTR 0) (ELit 1);
   KDisj (SA vTR 0) (ELit 1) (SA vX (-8)) (ELit 506)].
Definition G1 : ST.tmpl := ST.TMG 0x4470c G1_regs G1_kn 31%nat (ELit 3072) 0%nat [ST.GA 7 [vX; (ELit 1)]].

(* [comment removed for export] *)
Definition G2_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vS0); (vS1); (vX); (vTR); ((V 19)); (sub (ELit (-1)) vX); (mul 8 (add (V 18) (ELit (-2)))); (add vX (mul 8 (add (V 18) (ELit (-1)))));
   (V 23); (V 24); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 25); (V 26); (V 27); (V 28)].
Definition G2_kn : list kentry :=
  [KRange (V 19) 1 18446744073709551615;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 2 62;
   KRange vSP 140728898420736 0x800000000000;
   KAlign vSP 16;
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KUnk (SA vX 0) (ELit 498);
   KRange vTR 0x7ffe00000000 0x800000000000;
   KWr (SA vTR 0) (ELit 1);
   KDisj (SA vTR 0) (ELit 1) (SA vX (-8)) (ELit 506)].
Definition G2 : ST.tmpl := ST.TMG 0x447e8 G2_regs G2_kn 29%nat (ELit 3072) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition NZ_regs : list expr :=
  [ELit 0; (vRA); (vSP); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vS0); (vS1); (vX); (vTR); (V 24); (sub (ELit (-1)) vX); ((V 20)); (V 25);
   (V 26); ((V 19)); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition NZ_kn : list kentry :=
  [KAlign (V 19) 8;
   KRange (V 19) 0 472;
   KRange (V 20) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 3 62;
   KRange vSP 140728898420736 0x800000000000;
   KAlign vSP 16;
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KUnk (SA vX 0) (ELit 498);
   KRange vTR 0x7ffe00000000 0x800000000000;
   KWr (SA vTR 0) (ELit 1);
   KDisj (SA vTR 0) (ELit 1) (SA vX (-8)) (ELit 506)].
Definition NZ : ST.tmpl := ST.TMG 0x448e0 NZ_regs NZ_kn 31%nat ((V 19)) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition X0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X0_kn : list kentry :=
  [KWord (SA vTR 0) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition X0 : ST.tmpl := ST.TMG 0x446ec X0_regs X0_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition X1_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X1_kn : list kentry :=
  [KWord (SA vTR 0) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition X1 : ST.tmpl := ST.TMG 0x447b8 X1_regs X1_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition X2_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X2_kn : list kentry :=
  [KWord (SA vTR 0) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition X2 : ST.tmpl := ST.TMG 0x44908 X2_regs X2_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition X3_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X3_kn : list kentry :=
  [KWord (SA vTR 0) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition X3 : ST.tmpl := ST.TMG 0x44918 X3_regs X3_kn 35%nat (ELit 0) 0%nat [ST.GA 7 [vX; (V 18)]].

Definition HI64U : SP.prog := SP.PGC 18 [T0; G1; G2; NZ] [X0; X1; X2; X3] [(vTR, 0, ELit 1)] [SX.SpCmpV 0x446d4 BC_LTU (EVar 18) (ELit 2); SX.SpHav 0x44774 11; SX.SpHav 0x44850 15; SX.SpAl 0x448dc] [].
End HI64U_defs.

Module HI64U_sum.
(* [comment removed for export] *)
Definition HI64SU : SP.summ := SP.SUM 18 HI64U_defs.T0 [HI64U_defs.X0; HI64U_defs.X1; HI64U_defs.X2; HI64U_defs.X3] [(HI64U_defs.vTR, 0, ELit 1)].
End HI64U_sum.

Module PDCU_defs.
Import P5UN_sum.
Import SHLUN_sum.
Import HI64U_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition PDCU_IT : itab := APC.mk_itab_ranges SG [(0x441fc, 117%nat); (0x44920, 126%nat); (0x4503c, 90%nat); (0x446d4, 147%nat)].
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
Definition vX := V 16.
Definition vE := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vE); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange (V 18) 0 40;
   KRange vSP 140728898421968 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1232)) (ELit 1232);
   KUnk (SA vSP (-1232)) (ELit 1232);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1232)) (ELit 1232) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vE 0 327].
Definition T0 : ST.tmpl := ST.TMG 0x441fc T0_regs T0_kn 32%nat (ELit 5000) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x44218); (spo (-32)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (vE); (ELit 1); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition R1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange (V 18) 0 56;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vSP 140728898421968 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1232)) (ELit 1232);
   KUnk (SA vSP (-1232)) (ELit 1232);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1232)) (ELit 1232) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vE 0 327].
Definition R1 : ST.tmpl := ST.TMG 0x44218 R1_regs R1_kn 33%nat (ELit 4000) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (V 19); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (vE); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition R2_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vSP 140728898421968 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1232)) (ELit 1232);
   KUnk (SA vSP (-1232)) (ELit 1232);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1232)) (ELit 1232) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vE 0 327].
Definition R2 : ST.tmpl := ST.TMG 0x4422c R2_regs R2_kn 35%nat (ELit 3000) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x44238); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (vE); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition R3_kn : list kentry :=
  [KWord (SA vSP (-25)) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vSP 140728898421968 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1232)) (ELit 1232);
   KUnk (SA vSP (-1232)) (ELit 1232);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1232)) (ELit 1232) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vE 0 327].
Definition R3 : ST.tmpl := ST.TMG 0x44238 R3_regs R3_kn 35%nat (ELit 2000) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition G_regs : list expr :=
  [ELit 0; (V 21); (spo (-32)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (vE); (V 25); ((V 18)); ((V 20)); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition G_kn : list kentry :=
  [KRange (V 20) 1 18446744073709551615;
   KWord (SA vSP (-25)) 1 (V 19);
   KRange (V 19) 0 1;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KRange vSP 140728898421968 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1232)) (ELit 1232);
   KUnk (SA vSP (-1232)) (ELit 1232);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1232)) (ELit 1232) (SA vX (-8)) (ELit 506);
   KImg 0x10000 0x2550c;
   KRange vE 0 327].
Definition G : ST.tmpl := ST.TMG 0x44260 G_regs G_kn 35%nat (ELit 1000) 0%nat [ST.GA 7 [vX; (V 18)]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TM 0x443cc XR_regs XR_kn 34%nat (ELit 0) 0%nat.

Definition PDCU : SP.prog := SP.PGC 18 [T0; R1; R2; R3; G] [XR] [(vSP, -1232, ELit 1232); (vX, 0, ELit 498)] [SX.SpHav 0x442c8 12] [P5SUN; SHLSUN; HI64SU].
End PDCU_defs.

Module PDCU_sum.
(* [comment removed for export] *)
Definition PDCSU : SP.summ := SP.SUM 18 PDCU_defs.T0 [PDCU_defs.XR] [(PDCU_defs.vSP, -1232, ELit 1232); (PDCU_defs.vX, 0, ELit 498)].
End PDCU_sum.

Module PMUN_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition PMUN_IT : itab := APC.mk_itab_ranges SG [(0x43260, 999%nat)].
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
Definition vX := V 16.
Definition vNUM := V 17.
Definition vDG := V 18.
Definition vIP := V 19.
Definition vIL := V 20.
Definition vFP := V 21.
Definition vFL := V 22.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 23); (V 24); (V 25);
   vS0; vS1; (vX); (vNUM); (ELit 769); (vDG); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (ELit 0);
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition T0 : ST.tmpl := ST.TM 0x43260 T0_regs T0_kn 34%nat (ELit 17179869184) 0%nat.

(* [comment removed for export] *)
Definition ZS8_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (ELit 8); (ELit 3472328296227680304); (ELit 7);
   (V 26); (V 27); (V 28); (vNUM); (ELit 769); (vDG); ((V 23)); (sub (add vIP vIL) (V 23));
   ((add vIP vIL)); (sub (add vIP vIL) (V 23)); (vX); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition ZS8_kn : list kentry :=
  [KRange (V 24) 0 0;
   KRange (V 23) 8 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition ZS8 : ST.tmpl := ST.TMG 0x432e0 ZS8_regs ZS8_kn 42%nat (add (ELit 12884901888) (V 23)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition ZS1_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (ELit (-1)); (V 26); (V 27);
   (V 28); (V 29); ((add vIP vIL)); (vNUM); (ELit 769); (vDG); (ELit 105008); (ELit 48);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition ZS1_kn : list kentry :=
  [KRange (V 24) 0 0;
   KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition ZS1 : ST.tmpl := ST.TMG 0x43374 ZS1_regs ZS1_kn 43%nat (add (ELit 10737418240) (sub vIL (V 23))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition CH_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (V 29); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30);
   (V 31); (sub (ELit 769) (V 25)); (V 32); (V 33); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition CH_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (ELit 1538) (mul 2 (V 25))) (mul 19 (V 24))) 0 2000].
Definition CH : ST.tmpl := ST.TMG 0x43408 CH_regs CH_kn 34%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 23))) (ELit 1000))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition DL_regs : list expr :=
  [ELit 0; (add vIP (V 23)); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (V 29); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30);
   (V 31); (sub (ELit 769) (V 25)); ((V 26)); (V 32); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition DL_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KRange (V 26) 0 18;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (sub (ELit 1538) (mul 2 (V 25))) (mul 2 (V 26))) (mul 19 (V 24))) 0 2000].
Definition DL : ST.tmpl := ST.TMG 0x4358c DL_regs DL_kn 33%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 23))) (ELit 999))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition JC_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (V 28); (V 29); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (V 30); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 31);
   (V 32); (sub (ELit 769) (V 25)); (V 33); ((V 26)); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition JC_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 19;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (sub (ELit 1538) (mul 2 (V 25))) (mul 2 (V 26))) (mul 19 (V 24))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (add (V 26) (ELit 13)) (ELit 5))) (sub (V 23) vIL)) 0 2097152].
Definition JC : ST.tmpl := ST.TMG 0x435f0 JC_regs JC_kn 34%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 23))) (ELit 2000))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SMI_regs : list expr :=
  [ELit 0; ((V 23)); (spo (-128)); (vGP); (vTP); (V 28); (add vX (mul 8 (V 25))); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (add vX (mul 8 (sub (V 25) (V 27)))); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 29);
   (V 30); ((V 25)); (V 31); (add (sub (ELit 63) (V 25)) (V 27)); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition SMI_kn : list kentry :=
  [KRange (V 27) 1 62;
   KRange (sub (V 25) (V 27)) 0 62;
   KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (-2))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vIL)) 0 2097152].
Definition SMI : ST.tmpl := ST.TMG 0x43630 SMI_regs SMI_kn 32%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 24))) (add (ELit 1500) (V 27)))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SMIX_regs : list expr :=
  [ELit 0; ((V 23)); (spo (-128)); (vGP); (vTP); ((V 27)); (V 28); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (V 29); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30);
   (V 31); ((V 25)); (V 32); (V 33); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition SMIX_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (-2))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vIL)) 0 2097152].
Definition SMIX : ST.tmpl := ST.TMG 0x4365c SMIX_regs SMIX_kn 34%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 24))) (ELit 1400))) 0%nat [ST.GA 9 [vX; (V 25); (V 27)]].

(* [comment removed for export] *)
Definition SA0_regs : list expr :=
  [ELit 0; ((V 23)); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (V 29); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30);
   (V 31); ((V 25)); (V 32); (V 33); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition SA0_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (17))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vIL)) 0 2097152].
Definition SA0 : ST.tmpl := ST.TMG 0x4368c SA0_regs SA0_kn 34%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 24))) (ELit 1200))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SAI_regs : list expr :=
  [ELit 0; ((V 23)); (spo (-128)); (vGP); (vTP); (V 28); ((V 27)); (ELit 8);
   (ELit 19); (add vX (ELit 8)); (add vX (add (mul 8 (V 25)) (mul (-8) (V 27)))); (vNUM); (ELit 769); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (ELit 0xf424000000064); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 29);
   (add (add (mul 8 (V 25)) (mul (-8) (V 27))) (ELit (-512))); ((V 25)); (V 30); (V 31); (ELit 9); (ELit 10); (ELit (-1)); (ELit 17)].
Definition SAI_kn : list kentry :=
  [KRange (add (mul 8 (V 25)) (mul (-8) (V 27))) 8 496;
   KRange (V 27) 1 61;
   KRange (sub (V 25) (V 27)) 1 62;
   KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 761);
   KWord (SA vSP (-120)) 8 (ELit 100000000);
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (17))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vIL)) 0 2097152].
Definition SAI : ST.tmpl := ST.TMG 0x436ac SAI_regs SAI_kn 32%nat (add (ELit 8589934592) (add (mul 1024 (sub vIL (V 24))) (add (ELit 1100) (V 27)))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition JF_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vNUM); (ELit 769); (vDG); (ELit 105008); (V 32);
   (V 33); (V 34); (vX); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition JF_kn : list kentry :=
  [KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 768;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (add (mul 2 (V 24)) (ELit (36))) (mul 19 (V 23))) 0 2000].
Definition JF : ST.tmpl := ST.TMG 0x436f8 JF_regs JF_kn 48%nat (ELit 7516192768) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition ZF8_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (ELit 8); (ELit 3472328296227680304); (ELit 7);
   (V 26); (V 27); (V 28); ((V 23)); (ELit 769); (vDG); (ELit 105008); (sub (add vFP vFL) (V 23));
   ((add vFP vFL)); (sub (add vFP vFL) (V 23)); (vX); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41)].
Definition ZF8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (ELit 36) (mul 19 (V 24))) 0 36].
Definition ZF8 : ST.tmpl := ST.TMG 0x43b80 ZF8_regs ZF8_kn 42%nat (add (ELit 6442450944) (V 23)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition ZF1_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); ((add vFP vFL)); (ELit 48); (ELit 769); (vDG); (ELit 105008); (add vFP (V 23));
   ((add vFP vFL)); (ELit (-1)); (vX); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition ZF1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (ELit 36) (mul 19 (V 24))) 0 36].
Definition ZF1 : ST.tmpl := ST.TMG 0x43cf8 ZF1_regs ZF1_kn 44%nat (add (ELit 4294967296) (sub vFL (V 23))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition CHF_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (V 27); (V 28); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 23));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 29); (V 30);
   (sub (ELit 769) (V 25)); (V 31); (V 32); (V 33); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition CHF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (ELit 1574) (mul 2 (V 25))) (mul 19 (V 24))) 0 2000].
Definition CHF : ST.tmpl := ST.TMG 0x437a4 CHF_regs CHF_kn 34%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 23))) (ELit 1000))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition DLF_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (V 28); (V 29); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 23));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30); (V 31);
   (sub (ELit 769) (V 25)); ((V 26)); (V 32); (add vFP (V 23)); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition DLF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KRange (V 26) 0 18;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (sub (ELit 1574) (mul 2 (V 25))) (mul 2 (V 26))) (mul 19 (V 24))) 0 2000].
Definition DLF : ST.tmpl := ST.TMG 0x43924 DLF_regs DLF_kn 33%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 23))) (ELit 999))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition JCF_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (V 28); (V 29); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 23));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30); (V 31);
   (sub (ELit 769) (V 25)); (V 32); ((V 26)); (V 33); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition JCF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 19;
   KWord (SA vDG 0) 8 (sub (ELit 769) (V 25));
   KRange (V 25) 1 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (sub (sub (sub (ELit 1574) (mul 2 (V 25))) (mul 2 (V 26))) (mul 19 (V 24))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (add (V 26) (ELit 13)) (ELit 5))) (sub (V 23) vFL)) 0 2097152].
Definition JCF : ST.tmpl := ST.TMG 0x43988 JCF_regs JCF_kn 34%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 23))) (ELit 2000))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SMF_regs : list expr :=
  [ELit 0; (add vX (mul 8 (V 25))); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (add vX (mul 8 (sub (V 25) (V 27)))); (V 28); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 24));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 29); (V 30);
   ((V 25)); (V 31); (add (sub (ELit 63) (V 25)) (V 27)); ((V 23)); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition SMF_kn : list kentry :=
  [KRange (V 27) 1 62;
   KRange (sub (V 25) (V 27)) 0 62;
   KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (34))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vFL)) 0 2097152].
Definition SMF : ST.tmpl := ST.TMG 0x439c8 SMF_regs SMF_kn 32%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 24))) (add (ELit 1500) (V 27)))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SMFX_regs : list expr :=
  [ELit 0; (V 28); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (V 29); (V 30); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 24));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); ((V 27)); (V 31);
   ((V 25)); (V 32); (V 33); ((V 23)); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition SMFX_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (34))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vFL)) 0 2097152].
Definition SMFX : ST.tmpl := ST.TMG 0x439f4 SMFX_regs SMFX_kn 34%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 24))) (ELit 1400))) 0%nat [ST.GA 9 [vX; (V 25); (V 27)]].

(* [comment removed for export] *)
Definition SAF0_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (V 28); (V 29); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 24));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30); (V 31);
   ((V 25)); (V 32); (V 33); ((V 23)); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition SAF0_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (53))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vFL)) 0 2097152].
Definition SAF0 : ST.tmpl := ST.TMG 0x43a24 SAF0_regs SAF0_kn 34%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 24))) (ELit 1200))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SAF2_regs : list expr :=
  [ELit 0; (V 28); (spo (-128)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 9);
   (ELit 0xf424000000064); (add vX (add (mul 8 (V 25)) (mul (-8) (V 27)))); (V 29); (sub (ELit (-1)) vX); (ELit 769); (vDG); (ELit 105008); (add vFP (V 24));
   ((add vFP vFL)); (ELit 761); (vX); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (V 30); ((V 27));
   ((V 25)); (add (add (mul 8 (V 25)) (mul (-8) (V 27))) (ELit (-512))); (V 31); ((V 23)); (ELit 10); (ELit (-1)); (ELit 17); (ELit 19)].
Definition SAF2_kn : list kentry :=
  [KRange (add (mul 8 (V 25)) (mul (-8) (V 27))) 8 496;
   KRange (V 27) 1 61;
   KRange (sub (V 25) (V 27)) 1 62;
   KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (V 26);
   KRange (V 26) 0 768;
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KWord (SA vSP (-112)) 8 (ELit 100000000);
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000;
   KRange (sub (sub (add (mul 2 (V 26)) (ELit (53))) (mul 36 (EAlu ALU_SRL (V 23) (ELit 63)))) (mul 19 (V 25))) 0 2000;
   KRange (add (mul 1048576 (EAlu ALU_SRL (V 23) (ELit 63))) (sub (V 24) vFL)) 0 2097152].
Definition SAF2 : ST.tmpl := ST.TMG 0x43a44 SAF2_regs SAF2_kn 32%nat (add (ELit 2147483648) (add (mul 1024 (sub vFL (V 24))) (add (ELit 1100) (V 27)))) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition TE_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (vNUM); (V 33); (vDG); (ELit 105008); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); ((V 25)); (V 42); (V 43); (V 44); (V 45)].
Definition TE_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 25) 1 19;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TE : ST.tmpl := ST.TMG 0x43a78 TE_regs TE_kn 46%nat (add (ELit 20971520) (ELit 0)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SMM_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (add (sub (ELit 63) (V 25)) (V 26)); ((V 23)); (add vX (mul 8 (V 25)));
   (V 28); (V 29); (V 30); (vNUM); ((V 25)); (vDG); (V 31); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (add vX (mul 8 (sub (V 25) (V 26)))); (V 41); (V 42); (V 43)].
Definition SMM_kn : list kentry :=
  [KRange (V 26) 1 62;
   KRange (sub (V 25) (V 26)) 0 62;
   KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000].
Definition SMM : ST.tmpl := ST.TMG 0x43ac0 SMM_regs SMM_kn 44%nat (add (ELit 18874368) (V 26)) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SMMX_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); (V 28); ((V 23)); (V 29);
   (V 30); (V 31); (V 32); (vNUM); ((V 25)); (vDG); ((V 26)); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 24)); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition SMMX_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vIL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000].
Definition SMMX : ST.tmpl := ST.TMG 0x43aec SMMX_regs SMMX_kn 46%nat (add (ELit 16777216) (ELit 100)) 0%nat [ST.GA 9 [vX; (V 25); (V 26)]].

(* [comment removed for export] *)
Definition SAM0_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vNUM); ((V 24)); (vDG); (V 32); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition SAM0_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition SAM0 : ST.tmpl := ST.TMG 0x43b1c SAM0_regs SAM0_kn 46%nat (add (ELit 14680064) (ELit 100)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SAM_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (add (add (mul 8 (V 24)) (mul (-8) (V 25))) (ELit (-512))); (add vX (add (mul 8 (V 24)) (mul (-8) (V 25)))); (V 27);
   (V 28); (V 29); (V 30); (vNUM); ((V 24)); (vDG); ((V 25)); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition SAM_kn : list kentry :=
  [KRange (add (mul 8 (V 24)) (mul (-8) (V 25))) 8 496;
   KRange (V 25) 1 61;
   KRange (sub (V 24) (V 25)) 1 62;
   KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition SAM : ST.tmpl := ST.TMG 0x43b3c SAM_regs SAM_kn 44%nat (add (ELit 14680064) (V 25)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TZ_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vNUM); (V 32); (vDG); (V 33); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition TZ_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TZ : ST.tmpl := ST.TMG 0x43d38 TZ_regs TZ_kn 47%nat (add (ELit 12582912) (ELit 2097151)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TI8_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (ELit 3472328296227680304); (ELit 7); (V 26);
   (V 27); (V 28); (V 29); (vNUM); (add vIL (mul (-1) (V 23))); (vDG); (ELit (-8)); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition TI8_kn : list kentry :=
  [KRange (add vIL (mul (-1) (V 23))) 8 1048576;
   KRange (V 23) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TI8 : ST.tmpl := ST.TMG 0x43d5c TI8_regs TI8_kn 43%nat (add (ELit 12582912) (add vIL (mul (-1) (V 23)))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TI1_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 48); (vNUM); (V 31); (vDG); (ELit (-1)); (sub (ELit (-1)) vX);
   ((add vIP vIL)); (add vIP (V 23)); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition TI1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TI1 : ST.tmpl := ST.TMG 0x43dd4 TI1_regs TI1_kn 45%nat (add (ELit 10485760) (sub vIL (V 23))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TF8_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (ELit 3472328296227680304); (ELit 7); (add vFL (mul (-1) (V 23)));
   (V 27); (V 28); (V 29); (add vFP (V 23)); ((V 25)); (vDG); (vFP); (sub (ELit (-1)) vX);
   (vFL); (ELit (-8)); (vX); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition TF8_kn : list kentry :=
  [KRange (add vFL (mul (-1) (V 23))) 8 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 25) 0 1;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TF8 : ST.tmpl := ST.TMG 0x43e54 TF8_regs TF8_kn 43%nat (add (ELit 8388608) (add vFL (mul (-1) (V 23)))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TF1_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 48); (add vFP (V 23)); ((V 25)); (vDG); ((add vFP vFL)); (sub (ELit (-1)) vX);
   (ELit (-1)); (V 32); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition TF1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KRange (V 25) 0 1;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TF1 : ST.tmpl := ST.TMG 0x43ed0 TF1_regs TF1_kn 46%nat (add (ELit 6291456) (sub vFL (V 23))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition RM10_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (add vX (mul 8 (sub (V 23) (V 24)))); (V 26); (V 27);
   (V 28); (V 29); (V 30); ((V 23)); (V 31); (vDG); (add (sub (ELit 63) (V 23)) (V 24)); (sub (ELit (-1)) vX);
   (add vX (mul 8 (V 23))); (ELit 10); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition RM10_kn : list kentry :=
  [KRange (V 24) 1 62;
   KRange (sub (V 23) (V 24)) 0 62;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RM10 : ST.tmpl := ST.TMG 0x43f18 RM10_regs RM10_kn 45%nat (add (ELit 4194304) (add (ELit 200) (V 24))) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition RM10X_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); ((V 23)); ((V 24)); (vDG); (V 32); (sub (ELit (-1)) vX);
   (V 33); (V 34); (vX); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition RM10X_kn : list kentry :=
  [KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RM10X : ST.tmpl := ST.TMG 0x43f44 RM10X_regs RM10X_kn 48%nat (add (ELit 4194304) (ELit 100)) 0%nat [ST.GA 9 [vX; (V 23); (V 24)]].

(* [comment removed for export] *)
Definition RA1_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); ((V 23)); ((V 24)); (vDG); (add (add (mul 8 (V 23)) (mul (-8) (V 24))) (ELit (-512))); (sub (ELit (-1)) vX);
   (add vX (add (mul 8 (V 23)) (mul (-8) (V 24)))); (V 32); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition RA1_kn : list kentry :=
  [KRange (add (mul 8 (V 23)) (mul (-8) (V 24))) 8 496;
   KRange (V 24) 1 61;
   KRange (sub (V 23) (V 24)) 1 62;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RA1 : ST.tmpl := ST.TMG 0x43f94 RA1_regs RA1_kn 46%nat (add (ELit 2097152) (V 24)) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition TEF_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (sub (ELit (-1)) vX); (V 33); (vDG); (ELit 105008); (add vFP (V 23));
   ((add vFP vFL)); (V 34); (vX); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); ((V 25)); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition TEF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 25) 1 19;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TEF : ST.tmpl := ST.TMG 0x43bf8 TEF_regs TEF_kn 47%nat (add (ELit 20971520) (ELit 0)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SMMF_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); ((V 23)); (add vX (mul 8 (V 25))); (V 28);
   (V 29); (V 30); (add vX (mul 8 (sub (V 25) (V 26)))); (sub (ELit (-1)) vX); ((V 25)); (vDG); (V 31); (add vFP (V 24));
   ((add vFP vFL)); (add (sub (ELit 63) (V 25)) (V 26)); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition SMMF_kn : list kentry :=
  [KRange (V 26) 1 62;
   KRange (sub (V 25) (V 26)) 0 62;
   KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000].
Definition SMMF : ST.tmpl := ST.TMG 0x43c40 SMMF_regs SMMF_kn 45%nat (add (ELit 18874368) (V 26)) 0%nat [ST.GA 8 [vX; (V 25)]].

(* [comment removed for export] *)
Definition SMMFX_regs : list expr :=
  [ELit 0; (V 27); (spo (-128)); (vGP); (vTP); ((V 23)); (V 28); (V 29);
   (V 30); (V 31); (V 32); (sub (ELit (-1)) vX); ((V 25)); (vDG); ((V 26)); (add vFP (V 24));
   ((add vFP vFL)); (V 33); (vX); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition SMMFX_kn : list kentry :=
  [KRange (V 24) 0 1048576;
   KRange (add vFL (mul (-1) (V 24))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 25);
   KRange (V 25) 1 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506);
   KRange (V 23) 1 10000000000000000000].
Definition SMMFX : ST.tmpl := ST.TMG 0x43c6c SMMFX_regs SMMFX_kn 47%nat (add (ELit 16777216) (ELit 100)) 0%nat [ST.GA 9 [vX; (V 25); (V 26)]].

(* [comment removed for export] *)
Definition SAMF0_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (sub (ELit (-1)) vX); ((V 24)); (vDG); (V 32); (add vFP (V 23));
   ((add vFP vFL)); (V 33); (vX); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition SAMF0_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition SAMF0 : ST.tmpl := ST.TMG 0x43c9c SAMF0_regs SAMF0_kn 47%nat (add (ELit 14680064) (ELit 100)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition SAMF_regs : list expr :=
  [ELit 0; (V 26); (spo (-128)); (vGP); (vTP); (add vX (add (mul 8 (V 24)) (mul (-8) (V 25)))); (V 27); (V 28);
   (V 29); (V 30); (V 31); (sub (ELit (-1)) vX); ((V 24)); (vDG); ((V 25)); (add vFP (V 23));
   ((add vFP vFL)); (add (add (mul 8 (V 24)) (mul (-8) (V 25))) (ELit (-512))); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition SAMF_kn : list kentry :=
  [KRange (add (mul 8 (V 24)) (mul (-8) (V 25))) 8 496;
   KRange (V 25) 1 61;
   KRange (sub (V 24) (V 25)) 1 62;
   KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 1 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition SAMF : ST.tmpl := ST.TMG 0x43cbc SAMF_regs SAMF_kn 45%nat (add (ELit 14680064) (V 25)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TZF_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (sub (ELit (-1)) vX); (V 32); (vDG); (V 33); (add vFP (V 23));
   ((add vFP vFL)); (V 34); (vX); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition TZF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TZF : ST.tmpl := ST.TMG 0x44004 TZF_regs TZF_kn 48%nat (add (ELit 8388608) (ELit 2097151)) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TG8_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (ELit 7); (V 26); (V 27);
   (V 28); (V 29); (V 30); (sub (ELit (-1)) vX); (add vFL (mul (-1) (V 23))); (vDG); (ELit (-8)); (add vFP (V 23));
   ((add vFP vFL)); (ELit 3472328296227680304); (vX); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition TG8_kn : list kentry :=
  [KRange (add vFL (mul (-1) (V 23))) 8 1048576;
   KRange (V 23) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TG8 : ST.tmpl := ST.TMG 0x44028 TG8_regs TG8_kn 44%nat (add (ELit 8388608) (add vFL (mul (-1) (V 23)))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition TG1_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 48); (sub (ELit (-1)) vX); (ELit (-1)); (vDG); (V 31); (add vFP (V 23));
   ((add vFP vFL)); (V 32); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition TG1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KRange vFP 1 0x7fffff7fffff;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition TG1 : ST.tmpl := ST.TMG 0x440a0 TG1_regs TG1_kn 46%nat (add (ELit 6291456) (sub vFL (V 23))) 0%nat [ST.GA 8 [vX; (V 24)]].

(* [comment removed for export] *)
Definition RM10F_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (add vX (mul 8 (sub (V 23) (V 24)))); (sub (ELit (-1)) vX); ((V 23)); (vDG); (V 31); (add (sub (ELit 63) (V 23)) (V 24));
   (add vX (mul 8 (V 23))); (ELit 10); (vX); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition RM10F_kn : list kentry :=
  [KRange (V 24) 1 62;
   KRange (sub (V 23) (V 24)) 0 62;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RM10F : ST.tmpl := ST.TMG 0x440ec RM10F_regs RM10F_kn 45%nat (add (ELit 4194304) (add (ELit 200) (V 24))) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition RM10FX_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (sub (ELit (-1)) vX); ((V 23)); (vDG); ((V 24)); (V 32);
   (V 33); (V 34); (vX); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition RM10FX_kn : list kentry :=
  [KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RM10FX : ST.tmpl := ST.TMG 0x44118 RM10FX_regs RM10FX_kn 48%nat (add (ELit 4194304) (ELit 100)) 0%nat [ST.GA 9 [vX; (V 23); (V 24)]].

(* [comment removed for export] *)
Definition RA1F_regs : list expr :=
  [ELit 0; (V 25); (spo (-128)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (sub (ELit (-1)) vX); ((V 23)); (vDG); ((V 24)); (add (add (mul 8 (V 23)) (mul (-8) (V 24))) (ELit (-512)));
   (add vX (add (mul 8 (V 23)) (mul (-8) (V 24)))); (V 32); (vX); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition RA1F_kn : list kentry :=
  [KRange (add (mul 8 (V 23)) (mul (-8) (V 24))) 8 496;
   KRange (V 24) 1 61;
   KRange (sub (V 23) (V 24)) 1 62;
   KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RA1F : ST.tmpl := ST.TMG 0x44168 RA1F_regs RA1F_kn 46%nat (add (ELit 2097152) (V 24)) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition RZ_regs : list expr :=
  [ELit 0; (V 24); (spo (-128)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (V 29); (V 30); (V 31); (V 32); (vDG); (V 33); (V 34);
   (V 35); (V 36); (vX); (V 37); (V 38); (V 39); (V 40); (V 41);
   (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49)].
Definition RZ_kn : list kentry :=
  [KWord (SA vDG 0) 8 (ELit 769);
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 1 62;
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
   KRange vSP 140728898420864 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-128)) (ELit 128);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-128)) (ELit 128) (SA vDG 0) (ELit 8);
   KRange vIL 0 1048576;
   KRange vIP 16 0x7fffff7fffff;
   KRange (add vIP vIL) 16 0x7fffff800000;
   KUnk (SA vIP 0) vIL;
   KRange vFL 0 1048576;
   KRange vFP 0 0x7fffff7fffff;
   KRange (add vFP vFL) 0 0x7fffff800000;
   KUnk (SA vFP 0) vFL;
   KWord (SA vNUM 32) 8 vIP;
   KWord (SA vNUM 40) 8 vIL;
   KWord (SA vNUM 48) 8 vFP;
   KWord (SA vNUM 56) 8 vFL;
   KRange vNUM 0x7ffe00000000 0x800000000000;
   KDisj (SA vNUM 0) (ELit 64) (SA vX 0) (ELit 498);
   KDisj (SA vNUM 0) (ELit 64) (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-128)) (ELit 128) (SA vIP 0) vIL;
   KDisj (SA vSP (-128)) (ELit 128) (SA vFP 0) vFL;
   KImg 0x10000 0x2550c;
   KDisj (SA vDG 0) (ELit 8) (SA vX (-8)) (ELit 506);
   KDisj (SA vSP (-128)) (ELit 128) (SA vX (-8)) (ELit 506)].
Definition RZ : ST.tmpl := ST.TMG 0x441b0 RZ_regs RZ_kn 50%nat (add (ELit 0) (ELit 0)) 0%nat [ST.GA 8 [vX; (V 23)]].

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 25); (V 26); (V 27);
   vS0; vS1; (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 36); (V 37); (V 38); (V 39)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 770;
   KRange (sub (add (mul 2 (V 24)) (ELit 91)) (mul 19 (V 23))) 0 2000].
Definition XR : ST.tmpl := ST.TMG 0x441f4 XR_regs XR_kn 40%nat (ELit 0) 0%nat [ST.GA 8 [vX; (V 23)]].

Definition PMUN : SP.prog := SP.PGC 23 [T0; ZS8; ZS1; CH; DL; JC; SMI; SMIX; SA0; SAI; JF; ZF8; ZF1; CHF; DLF; JCF; SMF; SMFX; SAF0; SAF2; TE; SMM; SMMX; SAM0; SAM; TZ; TI8; TI1; TF8; TF1; RM10; RM10X; RA1; TEF; SMMF; SMMFX; SAMF0; SAMF; TZF; TG8; TG1; RM10F; RM10FX; RA1F; RZ] [XR] [(vSP, -128, ELit 128); (vX, 0, ELit 498); (vDG, 0, ELit 8)] [SX.SpHav 0x434b4 24; SX.SpHav 0x43570 24; SX.SpHav 0x43850 23; SX.SpHav 0x43908 23; SX.SpEnumV 0x43620 (EVar 26) 1 19; SX.SpEnumV 0x439b8 (EVar 26) 1 19; SX.SpEnumV 0x43aac (EVar 25) 1 19; SX.SpEnumV 0x43c2c (EVar 25) 1 19; SX.SpCmp 0x436dc BC_LTU (EVar 27) (ELit 19); SX.SpCmp 0x43400 BC_LTU (EAlu ALU_SRL (EVar 1) (ELit 63)) (ELit 1); SX.SpCmp 0x4379c BC_LTU (EAlu ALU_SRL (EVar 27) (ELit 63)) (ELit 1)] [].
End PMUN_defs.

Module PMUN_sum.
(* [comment removed for export] *)
Definition PMSUN : SP.summ := SP.SUM 23 PMUN_defs.T0 [PMUN_defs.XR] [(PMUN_defs.vSP, -128, ELit 128); (PMUN_defs.vX, 0, ELit 498); (PMUN_defs.vDG, 0, ELit 8)].
End PMUN_sum.

Module SLOWU_defs.
Import PMUN_sum.
Import PDCU_sum.
Import NDCU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition SLOWU_IT : itab := APC.mk_itab_ranges SG [(0x41908, 1622%nat); (0x7a504, 100%nat); (0x43260, 999%nat); (0x441fc, 117%nat); (0x443d0, 193%nat)].
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
Definition vF := V 16.
Definition vN := V 17.
Definition vV := V 18.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vF); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (ELit 1);
   (V 22); (V 23); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 24); (V 25); (V 26); (V 27)].
Definition T0_kn : list kentry :=
  [KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x41908 T0_regs T0_kn 28%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (vRA); (spo (-704)); (vGP); (vTP); (add vF (V 19)); (ELit 10); (V 21);
   (vS0); (vS1); (ELit 2); ((add vF vN)); (vV); (ELit 53); (V 22); (V 23);
   (add vF (V 20)); (ELit 46); (vS2); (vS3); (vS4); (vS5); (vS6); (vV);
   (vS8); (vS9); (vS10); (vS11); (add vF (V 19)); (ELit 9); (V 24); (V 25)].
Definition IL_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 20) 0 1;
   KRange (add (V 19) (mul (-1) (V 20))) 5 1048576;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition IL : ST.tmpl := ST.TMG 0x41b60 IL_regs IL_kn 26%nat (add (ELit 163577856) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]].

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (vRA); (spo (-704)); (vGP); (vTP); (add vF (V 19)); (add (V 19) (mul (-1) (V 20))); (V 21);
   (vS0); (vS1); (V 22); ((add vF vN)); (vV); (ELit 53); (V 23); (V 24);
   (add vF (V 20)); (ELit 46); (vS2); (vS3); (vS4); (vS5); (vS6); (vV);
   (vS8); (vS9); (vS10); (vS11); (V 25); (V 26); (V 27); (V 28)].
Definition J1_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J1 : ST.tmpl := ST.TMG 0x41d3c J1_regs J1_kn 29%nat (ELit 159383552) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]].

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (V 22); (spo (-704)); (vGP); (vTP); (add vF (V 20)); (add (V 20) (mul (-1) (V 21))); (V 23);
   (ELit 0x5f5e100); (ELit 0xf424000000064); (sub (add vF vN) (V 19)); ((add vF vN)); (add (add vF (V 20)) (ELit 1)); (ELit 53); (V 24); (V 25);
   (add vF (V 21)); (ELit 46); (ELit 0x271000000001); (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x4646464646464646); (ELit 10); (ELit 7);
   (V 26); (V 27); (V 28); (V 29); (sub (add vF vN) (V 19)); ((V 19)); (ELit 8); (ELit 0x8080808080808080)].
Definition SW_kn : list kentry :=
  [KRange (V 19) 8 1048576;
   KRange (add vN (mul (-1) (V 19))) 2 1048576;
   KRange (add vN (add (mul (-1) (V 19)) (mul (-1) (V 20)))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 9 1048576;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KWord (SA vSP (-696)) 8 vV;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition SW : ST.tmpl := ST.TMG 0x41e28 SW_regs SW_kn 30%nat (add (ELit 155189248) ((V 19))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 2 [add vF (V 20)]; ST.GA 1 [add (add vF (V 20)) (ELit 1); add (add vN (add (mul (-1) (V 19)) (mul (-1) (V 20)))) (ELit (-1))]].

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (V 22); (spo (-704)); (vGP); (vTP); (add vF (V 20)); (add (V 20) (mul (-1) (V 21))); (V 23);
   (V 24); (V 25); (add vF (V 19)); ((add vF vN)); (add (add vF (V 20)) (ELit 1)); (ELit 53); (V 26); (V 27);
   (add vF (V 21)); (ELit 46); (V 28); (V 29); (V 30); (V 31); (V 32); (vV);
   (V 33); (V 34); (V 35); (V 36); (ELit 9); (ELit (-1)); (ELit 10); (V 37)].
Definition FL_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 2 1048576;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FL : ST.tmpl := ST.TMG 0x42260 FL_regs FL_kn 38%nat (add (ELit 150994944) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 2 [add vF (V 20)]; ST.GA 1 [add (add vF (V 20)) (ELit 1); add (add (V 19) (mul (-1) (V 20))) (ELit (-1))]].

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 24); (spo (-704)); (vGP); (vTP); (add vF (V 20)); (add (V 20) (mul (-1) (V 21))); (ELit 1);
   (V 25); (mul (-1) (V 23)); (add vF (V 19)); ((add vF vN)); ((V 22)); (ELit 53); (V 26); (V 27);
   (add vF (V 21)); (ELit 46); (V 28); (V 29); (V 30); (V 31); (V 32); (vV);
   (V 33); (V 34); (V 35); (V 36); ((V 23)); (add (add (V 20) (mul (-1) (V 21))) (V 23)); (V 37); (V 38)].
Definition J2_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 0 1048576;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 22) 0) (V 23);
   KRange (sub (add vF vN) (add (V 22) (V 23))) 0 0x7fffff800000;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J2 : ST.tmpl := ST.TMG 0x422ac J2_regs J2_kn 39%nat (ELit 146800640) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]].

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (add vF (V 20)); (add (V 20) (mul (-1) (V 21))); (V 27);
   (ELit 9); (mul (-1) (V 23)); (ELit 10); ((add vF vN)); ((V 22)); ((V 24)); (V 28); (V 29);
   (add vF (V 21)); (ELit 46); (ELit 0xfffffff); (ELit 2); (add vF (V 19)); (V 30); (V 31); (vV);
   (V 32); (V 33); (V 34); (V 35); ((V 23)); (add (add (V 20) (mul (-1) (V 21))) (V 23)); (add vF (V 19)); ((V 25))].
Definition EL_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (V 24) 0 2684354559;
   KRange (V 25) 0 1;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 22) 0) (V 23);
   KRange (sub (add vF vN) (add (V 22) (V 23))) 0 0x7fffff800000;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition EL : ST.tmpl := ST.TMG 0x423d0 EL_regs EL_kn 36%nat (add (ELit 142606336) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]].

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (add vF (V 19)); (add (V 19) (mul (-1) (V 20))); (ELit 20);
   (V 27); ((V 24)); (add vF (V 25)); ((add vF vN)); ((V 21)); ((V 23)); (V 28); (V 29);
   (add vF (V 20)); (ELit 46); (V 30); (V 31); (V 32); (V 33); (V 34); (vV);
   (V 35); (V 36); (V 37); (V 38); ((V 22)); (add (add (V 19) (mul (-1) (V 20))) (V 22)); (V 39); (V 40)].
Definition J3_kn : list kentry :=
  [KRange (add (V 23) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 24) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 25) 0 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (add (add (V 19) (mul (-1) (V 20))) (V 22)) 20 2097152;
   KRange (V 20) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KRange (sub (add vF vN) (add (V 21) (V 22))) 0 0x7fffff800000;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J3 : ST.tmpl := ST.TMG 0x42450 J3_regs J3_kn 41%nat (ELit 138412032) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]; ST.GA 1 [(V 21); (V 22)]; ST.GA 3 [add vF (V 20); add (V 19) (mul (-1) (V 20)); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 28); (spo (-704)); (vGP); (vTP); (add vF (V 20)); (add (V 20) (mul (-1) (V 21))); (ELit 20);
   (add vF (V 19)); ((V 26)); (add vF (V 27)); ((add vF vN)); ((V 22)); ((V 25)); (V 29); (V 30);
   (add vF (V 21)); (ELit 46); (V 31); (V 32); (V 33); (V 34); (V 35); (vV);
   (V 36); (V 37); (V 38); (V 39); ((V 23)); (sub (add (add (V 20) (mul (-1) (V 21))) (V 23)) (V 24)); (ELit 48); (ELit (-1))].
Definition ZS_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 21))) 0 1048576;
   KRange (V 24) 0 1048576;
   KRange (add (V 19) (mul (-1) (add (V 21) (V 24)))) 0 1048576;
   KRange (add (V 25) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 26) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 27) 0 1048576;
   KRange (add vN (mul (-1) (V 27))) 0 1048576;
   KRange (add (add (V 20) (mul (-1) (V 21))) (V 23)) 20 2097152;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 22) 0) (V 23);
   KRange (sub (add vF vN) (add (V 22) (V 23))) 0 0x7fffff800000;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition ZS : ST.tmpl := ST.TMG 0x42460 ZS_regs ZS_kn 40%nat (add (ELit 134217728) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]; ST.GA 4 [add vF (V 21); add (V 19) (mul (-1) (V 21)); (V 24)]].

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 27); (spo (-704)); (vGP); (vTP); (add vF (V 19)); (add (V 19) (mul (-1) (V 20))); (V 28);
   (V 29); ((V 25)); (add vF (V 26)); (V 30); ((V 21)); ((V 24)); (V 31); (V 32);
   (add vF (V 20)); (ELit 46); (V 33); (V 34); (V 35); (V 36); (V 37); (vV);
   (V 38); (V 39); (V 40); (V 41); ((V 22)); ((V 23)); (V 42); (V 43)].
Definition J4_kn : list kentry :=
  [KRange (add (V 24) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (add (V 25) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 26) 0 1048576;
   KRange (add vN (mul (-1) (V 26))) 0 1048576;
   KRange (V 20) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J4 : ST.tmpl := ST.TMG 0x42490 J4_regs J4_kn 44%nat (ELit 130023424) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]; ST.GA 1 [(V 21); (V 22)]; ST.GA 5 [add vF (V 20); add (V 19) (mul (-1) (V 20)); (V 21); (V 22)]; ST.GA 3 [add vF (V 20); add (V 19) (mul (-1) (V 20)); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition TI_regs : list expr :=
  [ELit 0; (V 27); (spo (-704)); (vGP); (vTP); (add vF (V 19)); (add (V 19) (mul (-1) (V 21))); (V 28);
   (V 29); (V 30); (add vF (V 26)); (ELit 0xde0b6b3a763ffff); ((V 22)); ((V 25)); ((V 24)); (V 31);
   (add vF (V 21)); (add vF (V 20)); (V 32); (V 33); (V 34); (V 35); (V 36); (vV);
   (V 37); (V 38); (V 39); (V 40); ((V 23)); (ELit 2); (ELit 10); (add (add vF (V 20)) (ELit 1))].
Definition TI_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 0 1048576;
   KRange (add (V 25) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 26) 0 1048576;
   KRange (add vN (mul (-1) (V 26))) 0 1048576;
   KRange (V 24) 0 999999999999999999;
   KRange (V 21) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 22) 0) (V 23);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition TI : ST.tmpl := ST.TMG 0x424b4 TI_regs TI_kn 41%nat (add (ELit 125829120) (add (V 19) (mul (-1) (V 20)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 19) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 5 [add vF (V 21); add (V 19) (mul (-1) (V 21)); (V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 19) (mul (-1) (V 21)); (V 22); (V 23)]; ST.GA 6 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 24)]].

(* [comment removed for export] *)
Definition TG_regs : list expr :=
  [ELit 0; (V 27); (spo (-704)); (vGP); (vTP); (V 28); ((V 20)); (V 29);
   (V 30); (V 31); (add vF (V 25)); (ELit 0xde0b6b3a763ffff); ((V 21)); ((V 24)); ((V 23)); (V 32);
   ((V 19)); ((V 26)); (V 33); (V 34); (V 35); (V 36); (V 37); (vV);
   (V 38); (V 39); (V 40); (V 41); ((V 22)); (V 42); (V 43); (V 44)].
Definition TG_kn : list kentry :=
  [KRange (V 26) 1 1;
   KRange (add (V 24) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 25) 0 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 23) 0 999999999999999999;
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition TG : ST.tmpl := ST.TMG 0x42518 TG_regs TG_kn 45%nat (add (ELit 121634816) (ELit 2097152)) 0%nat [ST.GA 1 [(V 19); (V 20)]; ST.GA 1 [(V 21); (V 22)]; ST.GA 5 [(V 19); (V 20); (V 21); (V 22)]; ST.GA 6 [(V 19); (V 20); (V 23)]; ST.GA 3 [(V 19); (V 20); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition TF_regs : list expr :=
  [ELit 0; (V 27); (spo (-704)); (vGP); (vTP); (ELit (-1)); ((V 20)); (V 28);
   (V 29); (V 30); (add vF (V 26)); (ELit 0xde0b6b3a763ffff); ((V 21)); ((V 25)); ((V 24)); (V 31);
   ((V 19)); (add (V 21) (V 23)); (V 32); (V 33); (V 34); (V 35); (V 36); (vV);
   (V 37); (V 38); (V 39); (V 40); ((V 22)); (ELit 10); (add (V 22) (add (mul (-1) (V 23)) (ELit (-1)))); (add (V 21) (V 23))].
Definition TF_kn : list kentry :=
  [KRange (V 21) 16 0x7fffff7fffff;
   KRange (V 23) 0 1048576;
   KRange (add (V 22) (mul (-1) (V 23))) 1 1048576;
   KRange (add (V 25) (ELit 9223372036854775808)) 9223372034170421249 9223372039539130367;
   KRange (V 26) 0 1048576;
   KRange (add vN (mul (-1) (V 26))) 0 1048576;
   KRange (V 24) 0 999999999999999999;
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition TF : ST.tmpl := ST.TMG 0x42534 TF_regs TF_kn 41%nat (add (ELit 121634816) (add (V 22) (mul (-1) (V 23)))) 0%nat [ST.GA 1 [(V 19); (V 20)]; ST.GA 1 [(V 21); (V 22)]; ST.GA 5 [(V 19); (V 20); (V 21); (V 22)]; ST.GA 6 [(V 19); (V 20); (V 24)]; ST.GA 6 [(V 21); (V 23); (V 24)]].

(* [comment removed for export] *)
Definition J5T_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (V 27); ((V 20)); (V 28);
   (V 29); ((V 24)); (add vF (V 25)); (V 30); ((V 21)); (V 31); ((V 23)); (V 32);
   ((V 19)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (vV);
   (V 39); (V 40); (V 41); (V 42); ((V 22)); (V 43); (V 44); (V 45)].
Definition J5T_kn : list kentry :=
  [KRange (V 23) 1 9999999999999999999;
   KRange (add (V 24) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
   KRange (V 25) 0 1048576;
   KRange (add vN (mul (-1) (V 25))) 0 1048576;
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J5T : ST.tmpl := ST.TM 0x42580 J5T_regs J5T_kn 46%nat (ELit 117440512) 1%nat.

(* [comment removed for export] *)
Definition J5N_regs : list expr :=
  [ELit 0; (V 20); (spo (-704)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); ((V 19)); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (vV);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition J5N_kn : list kentry :=
  [KRange (add (V 19) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J5N : ST.tmpl := ST.TM 0x424fc J5N_regs J5N_kn 46%nat (ELit 117440512) 1%nat.

(* [comment removed for export] *)
Definition JC_regs : list expr :=
  [ELit 0; (V 20); (spo (-704)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); ((V 19)); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (ELit 0); (V 32); (V 33); (V 34); (V 35); (V 36); (vV);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition JC_kn : list kentry :=
  [KRange (add (V 19) (ELit 9223372036854775808)) 9223372034168324097 9223372039541227519;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition JC : ST.tmpl := ST.TM 0x4298c JC_regs JC_kn 45%nat (ELit 117440512) 0%nat.

(* [comment removed for export] *)
Definition CF2M_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); ((V 24)); (V 31); (add (V 23) (ELit 1)); (V 32); (V 33); ((V 23)); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (vV);
   (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49)].
Definition CF2M_kn : list kentry :=
  [KRange (add (V 24) (ELit 9223372036854775808)) 9223372036854775466 9223372036854776116;
   KRange (V 23) 1 9999999999999999999;
   KWord (SA vSP (-664)) 1 (V 25);
   KRange (V 25) 0 1;
   KWord (SA vSP (-656)) 8 (V 19);
   KWord (SA vSP (-648)) 8 (V 20);
   KWord (SA vSP (-640)) 8 (V 21);
   KWord (SA vSP (-632)) 8 (V 22);
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition CF2M : ST.tmpl := ST.TM 0x42c80 CF2M_regs CF2M_kn 50%nat (ELit 113246208) 0%nat.

(* [comment removed for export] *)
Definition CE_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); ((V 24)); (V 31); (V 32); (V 33); (V 34); ((V 23)); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (vV);
   (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49); (V 50)].
Definition CE_kn : list kentry :=
  [KRange (add (V 24) (ELit 9223372036854775808)) 9223372036854775466 9223372036854776116;
   KRange (V 23) 1 9999999999999999999;
   KWord (SA vSP (-664)) 1 (V 25);
   KRange (V 25) 0 1;
   KWord (SA vSP (-656)) 8 (V 19);
   KWord (SA vSP (-648)) 8 (V 20);
   KWord (SA vSP (-640)) 8 (V 21);
   KWord (SA vSP (-632)) 8 (V 22);
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition CE : ST.tmpl := ST.TM 0x42ec4 CE_regs CE_kn 51%nat (ELit 109051904) 0%nat.

(* [comment removed for export] *)
Definition JSE_regs : list expr :=
  [ELit 0; (V 26); (spo (-704)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (add (V 23) (ELit (-342))); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); ((V 24)); (V 39); (V 40); (V 41); (V 42); (vV);
   (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49); (V 50)].
Definition JSE_kn : list kentry :=
  [KRange (V 23) 0 668;
   KRange (add (V 24) (ELit 9223372036854775808)) 9223372036853727232 9223372036855824384;
   KWord (SA vSP (-664)) 1 (V 25);
   KRange (V 25) 0 1;
   KWord (SA vSP (-656)) 8 (V 19);
   KWord (SA vSP (-648)) 8 (V 20);
   KWord (SA vSP (-640)) 8 (V 21);
   KWord (SA vSP (-632)) 8 (V 22);
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition JSE : ST.tmpl := ST.TM 0x430e0 JSE_regs JSE_kn 51%nat (ELit 100663296) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x430f8); (spo (-704)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (add (V 23) (ELit (-342))); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); ((V 24)); (V 38); (V 39); (V 40); (V 41); (vV);
   (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48); (V 49)].
Definition R1_kn : list kentry :=
  [KRange (V 23) 0 668;
   KRange (add (V 24) (ELit 9223372036854775808)) 9223372036853727232 9223372036855824384;
   KWord (SA vSP (-120)) 2 (ELit 0);
   KWord (SA vSP (-112)) 8 (ELit 0);
   KWord (SA vSP (-664)) 1 (V 25);
   KRange (V 25) 0 1;
   KWord (SA vSP (-656)) 8 (V 19);
   KWord (SA vSP (-648)) 8 (V 20);
   KWord (SA vSP (-640)) 8 (V 21);
   KWord (SA vSP (-632)) 8 (V 22);
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA (V 19) 0) (V 20);
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition R1 : ST.tmpl := ST.TM 0x430f8 R1_regs R1_kn 50%nat (ELit 96468992) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x4310c); (spo (-704)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (V 27); (add (V 19) (ELit (-342))); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); ((V 20)); (V 36); (V 37); (V 38); (V 39); (vV);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition R2_kn : list kentry :=
  [KRange (V 19) 0 668;
   KRange (add (V 20) (ELit 9223372036854775808)) 9223372036853727232 9223372036855824384;
   KWord (SA vSP (-120)) 2 (V 22);
   KRange (V 22) 0 62;
   KWord (SA vSP (-112)) 8 (V 23);
   KRange (V 23) 0 770;
   KRange (sub (add (mul 2 (V 23)) (ELit 91)) (mul 19 (V 22))) 0 2000;
   KWord (SA vSP (-664)) 1 (V 21);
   KRange (V 21) 0 1;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition R2 : ST.tmpl := ST.TMG 0x4310c R2_regs R2_kn 48%nat (ELit 92274688) 1%nat [ST.GA 8 [spo (-616); (V 22)]].

(* [comment removed for export] *)
Definition RP_regs : list expr :=
  [ELit 0; (V 22); (spo (-704)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); ((V 19)); (V 27); (V 28); (V 29); ((V 19)); (V 30); (V 31);
   (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (vV);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition RP_kn : list kentry :=
  [KRange (V 19) 0 327;
   KRange (V 20) 0 40;
   KWord (SA vSP (-120)) 2 (V 20);
   KWord (SA vSP (-664)) 1 (V 21);
   KRange (V 21) 0 1;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RP : ST.tmpl := ST.TMG 0x4312c RP_regs RP_kn 47%nat (ELit 92274688) 0%nat [ST.GA 7 [spo (-616); (V 20)]].

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x43138); (spo (-704)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (vV);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition R3_kn : list kentry :=
  [KWord (SA vSP (-664)) 1 (V 19);
   KRange (V 19) 0 1;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition R3 : ST.tmpl := ST.TM 0x43138 R3_regs R3_kn 46%nat (ELit 88080384) 0%nat.

(* [comment removed for export] *)
Definition R4_regs : list expr :=
  [ELit 0; (V 20); (spo (-704)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (vV);
   (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46)].
Definition R4_kn : list kentry :=
  [KWord (SA vSP (-664)) 1 (V 19);
   KRange (V 19) 0 1;
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423216 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2480)) (ELit 2480);
   KUnk (SA vSP (-2480)) (ELit 2480);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2480)) (ELit 2480) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition R4 : ST.tmpl := ST.TM 0x43188 R4_regs R4_kn 47%nat (ELit 83886080) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition X_kn : list kentry :=
  [KUnk (SA vV 0) (ELit 8)].
Definition X : ST.tmpl := ST.TM 0x43218 X_regs X_kn 34%nat (ELit 0) 0%nat.

Definition SLOWU : SP.prog := SP.PGC 19 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; TI; TG; TF; J5T; J5N; JC; CF2M; CE; JSE; R1; R2; RP; R3; R4] [X] [(vSP, -2480, ELit 2480); (vV, 0, ELit 8)] [SX.SpSlt 0x42298; SX.SpSlt 0x42440; SX.SpSlt 0x4257c; SX.SpCmp 0x42434 BC_LT (EVar 13) (ELit 0); SX.SpCmp 0x42570 BC_LT (EVar 13) (ELit 0); SX.SpHav 0x42af4 12; SX.SpHav 0x42d10 12; SX.SpHav 0x42f70 12; SX.SpW 0x42b48; SX.SpW 0x42b58; SX.SpW 0x42d64; SX.SpW 0x42d74; SX.SpW 0x42fc0; SX.SpW 0x42fd0; SX.SpW 0x423f0; SX.SpW 0x42ed8; SX.SpW 0x42ffc; SX.SpW 0x4304c; SX.SpW 0x4307c; SX.SpW 0x430cc; SX.SpW 0x43114; SX.SpW 0x43124] [MMU.MSP 0 0x430f8; PMSUN; PDCSU; NDCSU].
End SLOWU_defs.

Module SLOWU_sum.
(* [comment removed for export] *)
Definition SLOWSU : SP.summ := SP.SUM 19 SLOWU_defs.T0 [SLOWU_defs.X] [(SLOWU_defs.vSP, -2480, ELit 2480); (SLOWU_defs.vV, 0, ELit 8)].
End SLOWU_sum.

Module PWFU_defs.
Import SLOWU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition PWFU_IT : itab := APC.mk_itab_ranges SG [(0x27150, 598%nat); (0x41908, 1622%nat)].
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
Definition vF := V 16.
Definition vN := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (vF); ((add vF vN)); (V 21); (V 22); (V 23); (V 24);
   (V 25); (V 26); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 27); (V 28); (V 29); (V 30)].
Definition T0_kn : list kentry :=
  [KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x27150 T0_regs T0_kn 31%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (V 20); (spo (-112)); (vGP); (vTP); (ELit 10); (add vF (V 18)); (ELit 9);
   (vS0); (vS1); (vF); ((add vF vN)); (V 21); (V 22); (add vF (V 19)); (ELit 2);
   (add vF (V 18)); (V 23); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 24); (V 25); (V 26); (V 27)].
Definition IL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (add vN (mul (-1) (V 18))) 0 1048576;
   KRange (V 19) 0 1;
   KRange vN 1 1048576;
   KRange (add (V 18) (mul (-1) (V 19))) 5 1048576;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition IL : ST.tmpl := ST.TM 0x272c8 IL_regs IL_kn 28%nat (add (ELit 37748736) (add vN (mul (-1) (V 18)))) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 20); (spo (-112)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vS0); (vS1); (vF); ((add vF vN)); (V 24); (V 25); (add vF (V 19)); (add (V 18) (mul (-1) (V 19)));
   (add vF (V 18)); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition J1_kn : list kentry :=
  [KRange (V 18) 1 1048576;
   KRange (add vN (mul (-1) (V 18))) 0 1048576;
   KRange (add (V 18) (mul (-1) (V 19))) 1 1048576;
   KRange (V 19) 0 1;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J1 : ST.tmpl := ST.TM 0x27328 J1_regs J1_kn 31%nat (ELit 33554432) 0%nat.

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (V 21); (spo (-112)); (vGP); (vTP); (V 22); (sub (add vF vN) (V 18)); ((V 18));
   (ELit 0xff000000ff); (ELit 0xf424000000064); (vF); ((add vF vN)); (V 23); (V 24); (add vF (V 20)); (add (V 19) (mul (-1) (V 20)));
   (sub (add vF vN) (V 18)); (add (add vF (V 19)) (ELit 1)); (ELit 0x4646464646464646); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x271000000001); (ELit 7); (V 25); (V 26);
   (V 27); (V 28); (V 29); (V 30); (ELit 8); (ELit 10); (ELit 0x8080808080808080); (ELit 0x5f5e100)].
Definition SW_kn : list kentry :=
  [KRange (V 18) 8 1048576;
   KRange (add vN (mul (-1) (V 18))) 2 1048576;
   KRange (add vN (add (mul (-1) (V 18)) (mul (-1) (V 19)))) 1 1048576;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (V 20) 0 1;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition SW : ST.tmpl := ST.TM 0x273b4 SW_regs SW_kn 31%nat (add (ELit 29360128) ((V 18))) 0%nat.

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (V 21); (spo (-112)); (vGP); (vTP); (V 22); (ELit 9); (ELit 0xffffffffffffffff);
   (V 23); (V 24); (vF); ((add vF vN)); (V 25); (V 26); (add vF (V 20)); (add (V 19) (mul (-1) (V 20)));
   (add vF (V 18)); (add (add vF (V 19)) (ELit 1)); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (V 35); (V 36); (ELit 10); (V 37); (V 38); (V 39)].
Definition FL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (add vN (mul (-1) (V 18))) 1 1048576;
   KRange (add (V 18) (mul (-1) (V 19))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 2 1048576;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (V 20) 0 1;
   KRange vN 1 1048576;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FL : ST.tmpl := ST.TM 0x27530 FL_regs FL_kn 40%nat (add (ELit 25165824) (add vN (mul (-1) (V 18)))) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 22); (spo (-112)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (V 26); (V 27); (vF); ((add vF vN)); (V 28); (V 29); (add vF (V 19)); ((V 20));
   (add vF (V 18)); (mul (-1) (V 21)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition J2_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (add vN (mul (-1) (V 18))) 0 1048576;
   KRange (V 19) 0 1;
   KRange vN 1 1048576;
   KRange (add (V 18) (mul (-1) (V 19))) 1 1048576;
   KRange (V 20) 1 2097152;
   KRange (V 21) 0 1048576;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J2 : ST.tmpl := ST.TM 0x27574 J2_regs J2_kn 44%nat (ELit 20971520) 0%nat.

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 24); (spo (-112)); (vGP); (vTP); (add vF (V 18)); ((V 23)); (ELit 9);
   (V 25); (V 26); (vF); ((add vF vN)); (V 27); (V 28); (add vF (V 19)); ((V 20));
   ((V 22)); (mul (-1) (V 21)); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (ELit 10); (ELit 0xfffffff); (ELit 2); (add vF (V 18))].
Definition EL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (add vN (mul (-1) (V 18))) 1 1048576;
   KRange (V 19) 0 1;
   KRange vN 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (V 20) 1 2097152;
   KRange (V 21) 0 1048576;
   KRange (V 22) 0 2684354559;
   KRange (V 23) 0 1;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition EL : ST.tmpl := ST.TM 0x2760c EL_regs EL_kn 39%nat (add (ELit 16777216) (add vN (mul (-1) (V 18)))) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 21); (spo (-112)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (V 26); (vF); ((add vF vN)); (V 27); (V 28); (add vF (V 18)); ((V 19));
   (V 29); ((V 20)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition J3_kn : list kentry :=
  [KRange (V 18) 0 1;
   KRange vN 1 1048576;
   KRange (add vN (mul (-1) (V 18))) 1 1048576;
   KRange (V 19) 1 2097152;
   KRange (add (V 20) (ELit 9223372036854775808)) 9223372034169372673 9223372039539130367;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J3 : ST.tmpl := ST.TM 0x27660 J3_regs J3_kn 44%nat (ELit 12582912) 0%nat.

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 21); (spo (-112)); (vGP); (vTP); (ELit 0xffffffffffffffff); (ELit 48); (V 22);
   (V 23); (V 24); (vF); ((add vF vN)); (V 25); (V 26); (add vF (V 18)); (add (V 19) (ELit (-1048576)));
   (ELit 46); ((V 20)); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40)].
Definition ZS_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (add vN (mul (-1) (V 18))) 1 1048576;
   KRange vN 1 1048576;
   KRange (V 19) 0 3145728;
   KRange (add (V 19) (V 18)) 1048596 4194304;
   KRange (add (V 20) (ELit 9223372036854775808)) 9223372034169372673 9223372039539130367;
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition ZS : ST.tmpl := ST.TM 0x27678 ZS_regs ZS_kn 41%nat (add (ELit 8388608) (add vN (mul (-1) (V 18)))) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 18); (spo (-112)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (V 22); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition J4_kn : list kentry :=
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
   KWord (SA vSP (-112)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition J4 : ST.tmpl := ST.TM 0x276a4 J4_regs J4_kn 46%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (ELit 0x27a94); (spo (-112)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (V 21); (V 22); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition RS_kn : list kentry :=
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
   KUnk (SA vSP (-112)) (ELit 8);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423328 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2592)) (ELit 2592);
   KUnk (SA vSP (-2592)) (ELit 2592);
   KDisj (SA vSP (-2592)) (ELit 2592) (SA vF 0) vN;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RS : ST.tmpl := ST.TM 0x27a94 RS_regs RS_kn 45%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition X_kn : list kentry :=
  [].
Definition X : ST.tmpl := ST.TM 0x279a8 X_regs X_kn 33%nat (ELit 0) 0%nat.

Definition PWFU : SP.prog := SP.PGC 18 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; RS] [X] [(vSP, -2592, ELit 2592)] [SX.SpHav 0x27774 16; SX.SpHav 0x277ac 5; SX.SpSlt 0x27568; SX.SpCmp 0x2764c BC_LT (EVar 16) (ELit 0); SX.SpSlt 0x27658; SX.SpW 0x277c8; SX.SpW 0x277d8; SX.SpW 0x2762c] [SLOWSU].
End PWFU_defs.

Module PWFU_sum.
(* [comment removed for export] *)
Definition PWFSU : SP.summ := SP.SUM 18 PWFU_defs.T0 [PWFU_defs.X] [(PWFU_defs.vSP, -2592, ELit 2592)].
End PWFU_sum.

Module SFPU_defs.
Import PWFU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition SFPU_IT : itab := APC.mk_itab_ranges SG [(0x451a4, 44%nat); (0x27150, 695%nat)].
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
Definition vRB := V 16.
Definition vRL := V 17.
Definition vP := V 18.
Definition vOUT := V 19.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (add vRB vP); (vOUT); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x451a4 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit (-1)); (ELit 58); (ELit 288230376218820621);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 1 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 1 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x45204 FE_regs FE_kn 31%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 283160); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vOUT); (vS1); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition RT_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x45218 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KRange (V 20) 0 63].
Definition X : ST.tmpl := ST.TM 0x4524c X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition SFPU : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2608, ELit 2608); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x451dc BC_EQ (EVar 18) (EVar 17); SX.SpCmpV 0x45204 BC_EQ (EVar 20) (EVar 17)] [PWFSU].
End SFPU_defs.

Module SFPCU_defs.
Import PWFU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition SFPCU_IT : itab := APC.mk_itab_ranges SG [(0x451a4, 44%nat); (0x27150, 695%nat)].
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
Definition vRB := V 16.
Definition vRL := V 17.
Definition vP := V 18.
Definition vOUT := V 19.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (add vRB vP); (vOUT); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x451a4 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit (-1)); (ELit 58); (ELit 288230376218820621);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 1 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 1 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x45204 FE_regs FE_kn 31%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 283160); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vOUT); (vS1); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition RT_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x45218 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KRange (V 20) 0 63].
Definition X : ST.tmpl := ST.TM 0x4524c X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition SFPCU : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2608, ELit 2608); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x451dc BC_EQ (EVar 18) (EVar 17); SX.SpCmpV 0x45204 BC_EQ (EVar 20) (EVar 17)] [PWFSU].
End SFPCU_defs.

Module PFFU_defs.
Import PWFU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition PFFU_IT : itab := APC.mk_itab_ranges SG [(0x45254, 43%nat); (0x27150, 695%nat)].
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
Definition vRB := V 16.
Definition vRL := V 17.
Definition vP := V 18.
Definition vOUT := V 19.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (add vRB vP); (vOUT); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x45254 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit (-1)); (ELit 58); (ELit 288230376218820621);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 1 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 1 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x452b4 FE_regs FE_kn 31%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 283336); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vOUT); (vS1); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition RT_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x452c8 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KRange (V 20) 0 63].
Definition X : ST.tmpl := ST.TM 0x452f8 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PFFU : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2608, ELit 2608); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x4528c BC_EQ (EVar 18) (EVar 17); SX.SpCmpV 0x452b4 BC_EQ (EVar 20) (EVar 17)] [PWFSU].
End PFFU_defs.

Module PFFCU_defs.
Import PWFU_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Ubsan.M.loaded_segments.
Definition PFFCU_IT : itab := APC.mk_itab_ranges SG [(0x45254, 43%nat); (0x27150, 695%nat)].
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
Definition vRB := V 16.
Definition vRL := V 17.
Definition vP := V 18.
Definition vOUT := V 19.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (add vRB vP); (vOUT); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x45254 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit (-1)); (ELit 58); (ELit 288230376218820621);
   (V 25); (V 26); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 27); (V 28); (V 29); (V 30)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 1 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 1 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x452b4 FE_regs FE_kn 31%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 283336); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vOUT); (vS1); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition RT_kn : list kentry :=
  [KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423344 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2608)) (ELit 2608);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2608)) (ELit 2608) (SA vOUT 0) (ELit 8);
   KAlign vOUT 8;
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2550c;
   KWord (SA (ELit 0) 0x80f30) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x452c8 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; ((V 20)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2608)) (ELit 2608);
   KRange (V 20) 0 63].
Definition X : ST.tmpl := ST.TM 0x452f8 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PFFCU : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2608, ELit 2608); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x4528c BC_EQ (EVar 18) (EVar 17); SX.SpCmpV 0x452b4 BC_EQ (EVar 20) (EVar 17)] [PWFSU].
End PFFCU_defs.
