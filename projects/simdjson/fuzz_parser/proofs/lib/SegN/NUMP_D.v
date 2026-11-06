(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.simdjson.fuzz_parser.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA Require Import MuslMemP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import SLOWG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Module MMV_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition MMV_IT : itab := APC.mk_itab_ranges SG [(0x70628, 95%nat); (0x70224, 257%nat)].
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
Definition T0 : ST.tmpl := ST.TM 0x70628 T0_regs T0_kn 31%nat (ELit 1000) 9%nat.

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
Definition MC : ST.tmpl := ST.TM 0x70350 MC_regs MC_kn 30%nat ((V 19)) 1%nat.

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
Definition TJ : ST.tmpl := ST.TM 0x70380 TJ_regs TJ_kn 31%nat ((V 19)) 0%nat.

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
Definition BW : ST.tmpl := ST.TM 0x70754 BW_regs BW_kn 29%nat ((V 19)) 0%nat.

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
Definition BB : ST.tmpl := ST.TM 0x7069c BB_regs BB_kn 31%nat ((V 19)) 0%nat.

(* [comment removed for export] *)
Definition XM_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XM_kn : list kentry :=
  [].
Definition XM : ST.tmpl := ST.TM 0x706b4 XM_regs XM_kn 34%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XC1_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC1_kn : list kentry :=
  [].
Definition XC1 : ST.tmpl := ST.TM 0x705f4 XC1_regs XC1_kn 34%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition XC2_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XC2_kn : list kentry :=
  [].
Definition XC2 : ST.tmpl := ST.TM 0x70624 XC2_regs XC2_kn 34%nat (ELit 0) 0%nat.

Definition MMV : SP.prog := SP.PGC 19 [T0; MC; TJ; BW; BB] [XM; XC1; XC2] [((add vX vDO), 0, vN)] [SX.SpEnum 0x70380 (EVar 12) 0 15] [].
End MMV_defs.

Module MMV_sum.
(* [comment removed for export] *)
Definition MMVS : SP.summ := SP.SUM 19 MMV_defs.T0 [MMV_defs.XM; MMV_defs.XC1; MMV_defs.XC2]
  [(MMV_defs.add MMV_defs.vX MMV_defs.vDO, 0, MMV_defs.vN)].
End MMV_sum.

Module LM_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition LM_IT : itab := APC.mk_itab_ranges SG [(0x3b10c, 226%nat); (0x70224, 257%nat); (0x707a4, 100%nat)].
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
   vS0; vS1; (vX); (ELit 105936); (ELit 5); (V 21); (V 22); (V 23);
   (V 24); (V 25); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 26); (V 27); (V 28); (V 29)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62;
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition T0 : ST.tmpl := ST.TM 0x3b10c T0_regs T0_kn 30%nat (ELit 32768) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x3b178); (spo (-1136)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (vX); (ELit 105936); (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); (ELit 5); ((V 17)); (ELit 0); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition R1_kn : list kentry :=
  [KWord (SA vSP (-112)) 2 (ELit 0);
   KUnk (SA vSP (-608)) (mul 8 (V 17));
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62;
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition R1 : ST.tmpl := ST.TM 0x3b178 R1_regs R1_kn 33%nat (ELit 28672) 0%nat.

(* [comment removed for export] *)
Definition SM1_regs : list expr :=
  [ELit 0; (V 19); (spo (-1136)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (ELit 105936); (add vX (mul 8 (V 17))); (V 23); (V 24); (add vX (V 18)); (V 25); (V 26);
   (V 27); (V 28); (ELit 5); ((V 17)); ((V 17)); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition SM1_kn : list kentry :=
  [KRange (V 17) 1 62;
   KAlign (V 18) 8;
   KRange (V 18) 0 488;
   KRange (sub (mul 8 (V 17)) (V 18)) 8 496;
   KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62;
   KWord (SA vSP (-112)) 2 (V 17);
   KRange (V 17) 0 62;
   KUnk (SA vSP (-608)) (mul 8 (V 17));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition SM1 : ST.tmpl := ST.TM 0x3b1a8 SM1_regs SM1_kn 33%nat (add (ELit 24576) (sub (mul 8 (V 17)) (V 18))) 0%nat.

(* [comment removed for export] *)
Definition OL_regs : list expr :=
  [ELit 0; (V 20); (spo (-1136)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (ELit 105936); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38)].
Definition OL_kn : list kentry :=
  [KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition OL : ST.tmpl := ST.TM 0x3b26c OL_regs OL_kn 39%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 4000))) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x3b294); (spo (-1136)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (ELit 105936); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37)].
Definition R2_kn : list kentry :=
  [KWord (SA vSP (-616)) 2 (ELit 0);
   KUnk (SA vSP (-1112)) (mul 8 (V 19));
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition R2 : ST.tmpl := ST.TM 0x3b294 R2_regs R2_kn 38%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 3600))) 0%nat.

(* [comment removed for export] *)
Definition SMZ_regs : list expr :=
  [ELit 0; (V 21); (spo (-1136)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (ELit 105936); ((V 19)); ((V 19)); (mul 8 (V 19)); (V 25); (add (spo (-1112)) (V 20)); (add (spo (-1112)) (mul 8 (V 19)));
   (V 26); (V 27); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34)].
Definition SMZ_kn : list kentry :=
  [KRange (V 19) 1 62;
   KAlign (V 20) 8;
   KRange (V 20) 0 488;
   KRange (sub (mul 8 (V 19)) (V 20)) 8 496;
   KUnk (SA vSP (-1112)) (mul 8 (V 19));
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition SMZ : ST.tmpl := ST.TM 0x3b2b8 SMZ_regs SMZ_kn 35%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (add (ELit 3000) (sub (mul 8 (V 19)) (V 20))))) 0%nat.

(* [comment removed for export] *)
Definition PMS_regs : list expr :=
  [ELit 0; (V 22); (spo (-1136)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vX); (ELit 105936); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); ((V 20)); (mul 281474976710656 (V 20)); ((V 21)); (V 34); (V 35); (V 36); (V 37)].
Definition PMS_kn : list kentry :=
  [KRange (V 21) 1 62;
   KRange (sub (V 21) (V 18)) 1 62;
   KRange (V 20) 0 62;
   KRange (add (mul (-1) (V 17)) (add (mul (-1) (V 20)) (V 21))) 0 0;
   KUnk (SA vSP (-1112)) (mul 8 (V 20));
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition PMS : ST.tmpl := ST.TM 0x3b33c PMS_regs PMS_kn 38%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 2800))) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (V 21); (spo (-1136)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (ELit 105936); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); ((V 20)); (mul 281474976710656 (V 20)); (add (V 17) (V 20)); (V 33); (V 34); (V 35); (V 36)].
Definition R3_kn : list kentry :=
  [KRange (V 20) 0 62;
   KRange (add (V 17) (V 20)) 1 62;
   KRange (sub (add (V 17) (V 20)) (V 18)) 1 62;
   KUnk (SA vSP (-1112)) (mul 8 (V 20));
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition R3 : ST.tmpl := ST.TM 0x3b354 R3_regs R3_kn 37%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (ELit 2600))) 0%nat.

(* [comment removed for export] *)
Definition LA_regs : list expr :=
  [ELit 0; (V 22); (spo (-1136)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vX); (ELit 105936); (V 26); (add (spo (-1112)) (V 21)); (add (spo (-1112)) (mul 8 (V 20))); (add (add vX (mul 8 (V 17))) (V 21)); (V 27); (V 28);
   (V 29); (V 30); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); ((V 20)); (mul 281474976710656 (V 20)); (V 31); (V 32); (V 33); (V 34); (V 35)].
Definition LA_kn : list kentry :=
  [KRange (V 20) 1 62;
   KAlign (V 21) 8;
   KRange (V 21) 0 488;
   KRange (add (mul 8 (V 17)) (V 21)) 0 488;
   KRange (sub (mul 8 (V 20)) (V 21)) 8 496;
   KRange (sub (mul 8 (V 18)) (add (mul 8 (V 17)) (V 21))) 8 496;
   KRange (sub (V 18) (add (V 17) (V 20))) 0 62;
   KUnk (SA vSP (-1112)) (mul 8 (V 20));
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition LA : ST.tmpl := ST.TM 0x3b398 LA_regs LA_kn 36%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (add (ELit 2000) (sub (mul 8 (V 20)) (V 21))))) 0%nat.

(* [comment removed for export] *)
Definition SAF_regs : list expr :=
  [ELit 0; (V 21); (spo (-1136)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); (ELit 105936); ((V 20)); (sub (add vX (mul 8 (V 18))) (mul 8 (add (V 20) (ELit (-1))))); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 5); ((V 18)); ((V 19)); (mul 281474976710656 (V 19)); (add (mul (-1) (V 17)) (ELit 1)); (add vX (mul 8 (V 17)));
   ((V 17)); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37)].
Definition SAF_kn : list kentry :=
  [KRange (V 20) 1 62;
   KRange (sub (V 18) (add (V 20) (ELit (-1)))) 0 62;
   KRange (V 17) 1 4;
   KWord (SA vSP (-1120)) 8 (mul 8 (V 19));
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition SAF : ST.tmpl := ST.TM 0x3b3e0 SAF_regs SAF_kn 38%nat (add (ELit 0) (add (mul 4096 (sub (ELit 5) (V 17))) (add (ELit 1000) (V 20)))) 0%nat.

(* [comment removed for export] *)
Definition NM_regs : list expr :=
  [ELit 0; (V 18); (spo (-1136)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (V 22); (ELit 1); ((V 17)); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42)].
Definition NM_kn : list kentry :=
  [KRange (V 17) 1 62;
   KWord (SA vX 496) 2 (V 17);
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
   KRange vSP 140728898421872 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1136)) (ELit 1136);
   KUnk (SA vSP (-1136)) (ELit 1136);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1136)) (ELit 1136) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition NM : ST.tmpl := ST.TM 0x3b1f8 NM_regs NM_kn 43%nat ((V 17)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 17);
   KRange (V 17) 0 62].
Definition XR : ST.tmpl := ST.TM 0x3b490 XR_regs XR_kn 33%nat (ELit 0) 0%nat.

Definition LM : SP.prog := SP.PGC 17 [T0; R1; SM1; OL; R2; SMZ; PMS; R3; LA; SAF; NM] [XR] [(vSP, -1136, ELit 1136); (vX, 0, ELit 498)] [] [MMP.MCPU 0x3b178; MMP.MCPU 0x3b294; MMP.MSP 0 0x3b354].
End LM_defs.

Module LM_sum.
(* [comment removed for export] *)
Definition LMS : SP.summ := SP.SUM 17 LM_defs.T0 [LM_defs.XR] [(LM_defs.vSP, -1136, ELit 1136); (LM_defs.vX, 0, ELit 498)].
End LM_sum.

Module P5_defs.
Import LM_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition P5_IT : itab := APC.mk_itab_ranges SG [(0x3afb0, 87%nat); (0x3b10c, 226%nat)].
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
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition T0 : ST.tmpl := ST.TM 0x3afb0 T0_regs T0_kn 32%nat (ELit 8589934592) 0%nat.

(* [comment removed for export] *)
Definition P5A_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (ELit 105936); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition P5A_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition P5A : ST.tmpl := ST.TM 0x3afe4 P5A_regs P5A_kn 36%nat (add (ELit 4294967296) (V 18)) 1%nat.

(* [comment removed for export] *)
Definition PR_regs : list expr :=
  [ELit 0; (ELit 0x3aff4); (spo (-48)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); ((V 18)); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (ELit 105936); (ELit 134); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition PR_kn : list kentry :=
  [KRange (V 18) 135 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition PR : ST.tmpl := ST.TM 0x3aff4 PR_regs PR_kn 35%nat (add (ELit 4294967296) (V 18)) 0%nat.

(* [comment removed for export] *)
Definition P5B_regs : list expr :=
  [ELit 0; (V 20); (spo (-48)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); ((V 18)); (ELit 0x6765c793fa10079d); ((V 19)); (ELit 26); (ELit 61); (V 24); (V 25);
   (V 26); (V 27); (V 28); (V 29); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition P5B_kn : list kentry :=
  [KRange (V 18) 27 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition P5B : ST.tmpl := ST.TM 0x3b028 P5B_regs P5B_kn 34%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (ELit 1000))) 0%nat.

(* [comment removed for export] *)
Definition P5C_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); ((V 18)); (ELit 0x6765c793fa10079d); ((V 19)); (ELit 26); (ELit 61); (add vX (mul 8 (V 19))); (V 25);
   (add vX (V 20)); (V 26); (V 27); (V 28); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 29); (V 30); (V 31); (V 32)].
Definition P5C_kn : list kentry :=
  [KRange (V 19) 1 62;
   KAlign (V 20) 8;
   KRange (V 20) 0 488;
   KRange (sub (mul 8 (V 19)) (V 20)) 8 496;
   KRange (V 18) 27 2147483647;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition P5C : ST.tmpl := ST.TM 0x3b03c P5C_regs P5C_kn 33%nat (add (ELit 2147483648) (add (mul 1024 (V 18)) (sub (mul 8 (V 19)) (V 20)))) 0%nat.

(* [comment removed for export] *)
Definition P5D_regs : list expr :=
  [ELit 0; (V 21); (spo (-48)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vX); ((V 18)); (V 25); ((V 19)); (V 26); (add vX (mul 8 (V 19))); (V 27); (add vX (V 20));
   (V 28); (V 29); (V 30); (V 31); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition P5D_kn : list kentry :=
  [KRange (V 19) 1 62;
   KAlign (V 20) 8;
   KRange (V 20) 0 488;
   KRange (sub (mul 8 (V 19)) (V 20)) 8 496;
   KRange (V 18) 8 208;
   KWord (SA vX 496) 2 (V 19);
   KRange (V 19) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KRange vSP 140728898421920 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1184)) (ELit 1184);
   KUnk (SA vSP (-1184)) (ELit 1184);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1184)) (ELit 1184) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c].
Definition P5D : ST.tmpl := ST.TM 0x3b0ac P5D_regs P5D_kn 36%nat (sub (mul 8 (V 19)) (V 20)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TM 0x3b108 XR_regs XR_kn 34%nat (ELit 0) 0%nat.

Definition P5 : SP.prog := SP.PGC 18 [T0; P5A; PR; P5B; P5C; P5D] [XR] [(vSP, -1184, ELit 1184); (vX, 0, ELit 498)] [] [LMS].
End P5_defs.

Module P5_sum.
(* [comment removed for export] *)
Definition P5S : SP.summ := SP.SUM 18 P5_defs.T0 [P5_defs.XR] [(P5_defs.vSP, -1184, ELit 1184); (P5_defs.vX, 0, ELit 498)].
End P5_sum.

Module NDC_defs.
Import P5_sum.
Import MMV_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition NDC_IT : itab := APC.mk_itab_ranges SG [(0x3abe4, 243%nat); (0x3afb0, 87%nat); (0x70628, 95%nat); (0x70224, 257%nat); (0x707a4, 100%nat)].
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
   vS0; vS1; (vX); (vM); (vP2); (vRE); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition T0 : ST.tmpl := ST.TM 0x3abe4 T0_regs T0_kn 32%nat (ELit 102400) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x3acd0); (spo (-576)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vP2); (vM); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (vX); (vRE); (V 32); (V 33); (V 34); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition R1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R1 : ST.tmpl := ST.TM 0x3acd0 R1_regs R1_kn 39%nat (ELit 92160) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (V 22); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (vRE); (V 34); (V 35); (V 36); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 37); (V 38); (V 39); (V 40)].
Definition R2_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R2 : ST.tmpl := ST.TM 0x3acf0 R2_regs R2_kn 41%nat (ELit 81920) 0%nat.

(* [comment removed for export] *)
Definition SB1_regs : list expr :=
  [ELit 0; (V 23); (spo (-576)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vP2); (vM); ((V 21)); (mul 8 (V 21)); (V 27); (V 28); (V 29); (add (spo (-568)) (V 22));
   (add (spo (-568)) (mul 8 (V 21))); (V 30); (vX); (vRE); (V 31); (V 32); (V 33); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition SB1_kn : list kentry :=
  [KRange (V 21) 1 62;
   KAlign (V 22) 8;
   KRange (V 22) 0 488;
   KRange (sub (mul 8 (V 21)) (V 22)) 8 496;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition SB1 : ST.tmpl := ST.TM 0x3ad1c SB1_regs SB1_kn 38%nat (add (ELit 71680) (sub (mul 8 (V 21)) (V 22))) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x3ad98); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (mul 8 (V 22)); (V 34); ((V 22)); (V 35); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 36); (V 37); (V 38); (V 39)].
Definition R3_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (add (V 22) (V 21)) 2 62;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R3 : ST.tmpl := ST.TM 0x3ad98 R3_regs R3_kn 40%nat (ELit 61440) 0%nat.

(* [comment removed for export] *)
Definition R4_regs : list expr :=
  [ELit 0; (ELit 0x3ada8); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (mul 8 (V 22)); (V 34); ((V 22)); (V 35); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 36); (V 37); (V 38); (V 39)].
Definition R4_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (add (V 22) (V 21)) 2 62;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R4 : ST.tmpl := ST.TM 0x3ada8 R4_regs R4_kn 40%nat (ELit 56320) 0%nat.

(* [comment removed for export] *)
Definition SB2_regs : list expr :=
  [ELit 0; (V 23); (spo (-576)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (vP2); (vM); (V 27); ((V 20)); (V 28); (add vX (mul 8 (V 20))); (V 29); (V 30);
   (add vX (V 22)); (V 31); (vX); (vRE); (V 32); (V 33); (V 34); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition SB2_kn : list kentry :=
  [KRange (V 20) 1 62;
   KAlign (V 22) 8;
   KRange (V 22) 0 488;
   KRange (sub (mul 8 (V 20)) (V 22)) 8 496;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition SB2 : ST.tmpl := ST.TM 0x3ade8 SB2_regs SB2_kn 39%nat (add (ELit 51200) (sub (mul 8 (V 20)) (V 22))) 0%nat.

(* [comment removed for export] *)
Definition R5_regs : list expr :=
  [ELit 0; (ELit 0x3ae58); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (mul 8 (V 22)); (V 34); ((V 22)); (V 35); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 36); (V 37); (V 38); (V 39)].
Definition R5_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (add (V 22) (V 20)) 2 62;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R5 : ST.tmpl := ST.TM 0x3ae58 R5_regs R5_kn 40%nat (ELit 40960) 0%nat.

(* [comment removed for export] *)
Definition R6_regs : list expr :=
  [ELit 0; (ELit 0x3ae68); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (vX); (mul 8 (V 22)); (V 34); ((V 22)); (V 35); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 36); (V 37); (V 38); (V 39)].
Definition R6_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (add (V 22) (V 20)) 2 62;
   KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-72)) 2 (V 21);
   KRange (V 21) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition R6 : ST.tmpl := ST.TM 0x3ae68 R6_regs R6_kn 40%nat (ELit 35840) 0%nat.

(* [comment removed for export] *)
Definition CMP_regs : list expr :=
  [ELit 0; (V 22); (spo (-576)); (vGP); (vTP); (V 23); (V 24); (V 25);
   (vP2); (vM); (V 26); (V 27); (add (spo (-568)) (add (mul 8 (V 21)) (ELit (-16)))); ((V 21)); (V 28); (V 29);
   (V 30); (V 31); (add vX (add (mul 8 (V 21)) (ELit (-16)))); (V 32); (V 33); (V 34); (V 35); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 36); (V 37); (V 38); (V 39)].
Definition CMP_kn : list kentry :=
  [KRange (V 21) 1 63;
   KRange (add (V 20) (ELit 1)) 1 63;
   KRange (sub (add (V 20) (ELit 1)) (V 21)) 0 62;
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
   KRange vSP 140728898422496 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1760)) (ELit 1760);
   KUnk (SA vSP (-1760)) (ELit 1760);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1760)) (ELit 1760) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange (mul (-1) vRE) 1 1073741824].
Definition CMP : ST.tmpl := ST.TM 0x3aeb4 CMP_regs CMP_kn 40%nat (add (ELit 20480) (V 21)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 21); (V 22); (V 23);
   vS0; vS1; (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 32); (V 33); (V 34); (V 35)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 20);
   KRange (V 20) 0 62].
Definition XR : ST.tmpl := ST.TM 0x3afac XR_regs XR_kn 36%nat (ELit 0) 0%nat.

Definition NDC : SP.prog := SP.PGC 20 [T0; R1; R2; SB1; R3; R4; SB2; R5; R6; CMP] [XR] [(vSP, -1760, ELit 1760); (vX, 0, ELit 498)] [] [MMP.MSP 0 0x3acd0; P5S; MMVS; MMP.MSP 0 0x3ada8; MMP.MSP 0 0x3ae68].
End NDC_defs.

Module NDC_sum.
(* [comment removed for export] *)
Definition NDCS : SP.summ := SP.SUM 20 NDC_defs.T0 [NDC_defs.XR] [(NDC_defs.vSP, -1760, ELit 1760); (NDC_defs.vX, 0, ELit 498)].
End NDC_sum.

Module PDC_defs.
Import P5_sum.
Import MMV_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition PDC_IT : itab := APC.mk_itab_ranges SG [(0x3a880, 217%nat); (0x3afb0, 87%nat); (0x70628, 95%nat); (0x70224, 257%nat); (0x707a4, 100%nat)].
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
Definition vEXP := V 17.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (vX); (vEXP); (V 22); (V 23); (V 24); (V 25);
   (V 26); (V 27); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 28); (V 29); (V 30); (V 31)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition T0 : ST.tmpl := ST.TM 0x3a880 T0_regs T0_kn 32%nat (ELit 102400) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x3a8a0); (spo (-32)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (vX); (vEXP); (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); (V 30); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition R1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition R1 : ST.tmpl := ST.TM 0x3a8a0 R1_regs R1_kn 35%nat (ELit 92160) 0%nat.

(* [comment removed for export] *)
Definition SB_regs : list expr :=
  [ELit 0; (V 20); (spo (-32)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (vX); (vEXP); ((V 18)); (V 24); (add vX (mul 8 (V 18))); (V 25); (V 26); (add vX (V 19));
   (V 27); (V 28); (V 29); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 30); (V 31); (V 32); (V 33)].
Definition SB_kn : list kentry :=
  [KRange (V 18) 1 62;
   KAlign (V 19) 8;
   KRange (V 19) 0 488;
   KRange (sub (mul 8 (V 18)) (V 19)) 8 496;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition SB : ST.tmpl := ST.TM 0x3a8cc SB_regs SB_kn 34%nat (add (ELit 71680) (sub (mul 8 (V 18)) (V 19))) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x3a93c); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (mul 8 (V 19)); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); ((V 19)); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 31); (V 32); (V 33); (V 34)].
Definition R2_kn : list kentry :=
  [KRange (V 19) 1 61;
   KRange (add (V 19) (V 18)) 2 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition R2 : ST.tmpl := ST.TM 0x3a93c R2_regs R2_kn 35%nat (ELit 61440) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x3a94c); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); ((V 19)); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition R3_kn : list kentry :=
  [KRange (V 19) 1 61;
   KRange (add (V 19) (V 18)) 2 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition R3 : ST.tmpl := ST.TM 0x3a94c R3_regs R3_kn 36%nat (ELit 56320) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 19); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (vX); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition J1_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition J1 : ST.tmpl := ST.TM 0x3a958 J1_regs J1_kn 37%nat (ELit 51200) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 19); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (add vX (mul 8 (V 18))); (V 23); ((V 18)); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 32); (V 33); (V 34); (V 35)].
Definition J2_kn : list kentry :=
  [KRange (V 18) 2 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition J2 : ST.tmpl := ST.TM 0x3ab10 J2_regs J2_kn 36%nat (ELit 40960) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 19); (spo (-32)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 34); (V 35); (V 36); (V 37)].
Definition J3_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition J3 : ST.tmpl := ST.TM 0x3ab40 J3_regs J3_kn 38%nat (ELit 5120) 0%nat.

(* [comment removed for export] *)
Definition NZ_regs : list expr :=
  [ELit 0; (V 20); (spo (-32)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (add vX (mul 8 (V 19))); (V 24); (V 25); (V 26); (V 27); (V 28); ((V 19)); (V 29);
   (V 30); (V 31); (V 32); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition NZ_kn : list kentry :=
  [KRange (V 19) 0 59;
   KRange (sub (V 18) (V 19)) 3 62;
   KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KRange vSP 140728898421952 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-1216)) (ELit 1216);
   KUnk (SA vSP (-1216)) (ELit 1216);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-1216)) (ELit 1216) (SA vX 0) (ELit 498);
   KImg 0x10000 0x2572c;
   KRange vEXP 0 2147483647].
Definition NZ : ST.tmpl := ST.TM 0x3ab20 NZ_regs NZ_kn 37%nat (add (ELit 10240) (V 19)) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition XR_kn : list kentry :=
  [KWord (SA vX 496) 2 (V 18);
   KRange (V 18) 0 62].
Definition XR : ST.tmpl := ST.TM 0x3abe0 XR_regs XR_kn 34%nat (ELit 0) 0%nat.

Definition PDC : SP.prog := SP.PGC 18 [T0; R1; SB; R2; R3; J1; J2; J3; NZ] [XR] [(vSP, -1216, ELit 1216); (vX, 0, ELit 498)] [] [P5S; MMVS; MMP.MSP 0 0x3a94c].
End PDC_defs.

Module PDC_sum.
(* [comment removed for export] *)
Definition PDCS : SP.summ := SP.SUM 18 PDC_defs.T0 [PDC_defs.XR] [(PDC_defs.vSP, -1216, ELit 1216); (PDC_defs.vX, 0, ELit 498)].
End PDC_sum.

Module PM_defs.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition PM_IT : itab := APC.mk_itab_ranges SG [(0x39b8c, 829%nat)].
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
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition T0 : ST.tmpl := ST.TM 0x39b8c T0_regs T0_kn 34%nat (ELit 17179869184) 0%nat.

(* [comment removed for export] *)
Definition ZS8_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 0x3030303030303030); (ELit 7); (V 26);
   (V 27); (V 28); (vX); (vNUM); (ELit 769); (vDG); ((V 23)); ((add vIP vIL));
   (sub (add vIP vIL) (V 23)); (sub (add vIP vIL) (V 23)); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (vS11); (V 38); (V 39); (V 40); (V 41)].
Definition ZS8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition ZS8 : ST.tmpl := ST.TM 0x39bec ZS8_regs ZS8_kn 42%nat (add (ELit 12884901888) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition ZS1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 48); (V 26); (V 27);
   (V 28); (V 29); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); ((add vIP vIL)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (vS11); (V 39); (V 40); (V 41); (V 42)].
Definition ZS1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition ZS1 : ST.tmpl := ST.TM 0x39c78 ZS1_regs ZS1_kn 43%nat (add (ELit 10737418240) (sub vIL (V 23))) 0%nat.

(* [comment removed for export] *)
Definition CH_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); (V 26); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition CH_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition CH : ST.tmpl := ST.TM 0x39d08 CH_regs CH_kn 34%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (ELit 1000)) 0%nat.

(* [comment removed for export] *)
Definition DL_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); (V 27); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); (V 28); ((V 25)); ((V 26)); (V 29);
   (V 30); (V 31); (V 32); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition DL_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 1 1048576;
   KRange (V 26) 0 18;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition DL : ST.tmpl := ST.TM 0x39e88 DL_regs DL_kn 33%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (ELit 999)) 0%nat.

(* [comment removed for export] *)
Definition JC_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); (V 27); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); (V 28); ((V 25)); ((V 26)); (V 29);
   (V 30); (V 31); (V 32); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition JC_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 0 19;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition JC : ST.tmpl := ST.TM 0x39eb8 JC_regs JC_kn 33%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (ELit 2000)) 0%nat.

(* [comment removed for export] *)
Definition SMI_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); (V 27); (add vX (mul 8 (V 24))); (V 28); (V 29);
   (add vX (V 26)); (V 30); (V 31); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition SMI_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KAlign (V 26) 8;
   KRange (V 26) 0 488;
   KRange (add (mul 8 (V 24)) (mul (-1) (V 26))) 8 496;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMI : ST.tmpl := ST.TM 0x39ee0 SMI_regs SMI_kn 32%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (add (ELit 1500) (sub (mul 8 (V 24)) (V 26)))) 0%nat.

(* [comment removed for export] *)
Definition SAI_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); ((V 26)); (sub (add vX (mul 8 (V 24))) (mul 8 (add (V 26) (ELit (-1))))); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition SAI_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 62;
   KRange (sub (V 24) (add (V 26) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SAI : ST.tmpl := ST.TM 0x39f34 SAI_regs SAI_kn 32%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (add (ELit 1100) (V 26))) 0%nat.

(* [comment removed for export] *)
Definition SMIX_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 761); (add vX (ELit 8)); (ELit 8);
   (ELit 0x271000000001); (ELit 0xff000000ff); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 61); (V 26); (add vX (mul 8 (V 24))); (V 27); (V 28);
   (V 29); (V 30); (V 31); (vS11); (ELit 10); (ELit 17); (ELit 100000000); (ELit 0xf424000000064)].
Definition SMIX_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMIX : ST.tmpl := ST.TM 0x39f04 SMIX_regs SMIX_kn 32%nat (add (add (ELit 8589934592) (mul 1024 (sub vIL (V 23)))) (ELit 1400)) 0%nat.

(* [comment removed for export] *)
Definition JF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vX); (vNUM); (ELit 769); (vDG); (ELit 0x19d30); (V 30);
   (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition JF_kn : list kentry :=
  [KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 768;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition JF : ST.tmpl := ST.TM 0x39f64 JF_regs JF_kn 46%nat (ELit 7516192768) 0%nat.

(* [comment removed for export] *)
Definition ZF8_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 0x3030303030303030); (ELit 7); (V 26);
   (V 27); (V 28); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (sub (add vFP vFL) (V 23));
   ((V 23)); (sub (add vFP vFL) (V 23)); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (vS11); (V 38); (V 39); (V 40); (V 41)].
Definition ZF8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition ZF8 : ST.tmpl := ST.TM 0x3a314 ZF8_regs ZF8_kn 42%nat (add (ELit 6442450944) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition ZF1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   ((add vFP vFL)); (ELit 48); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (vS11); (V 40); (V 41); (V 42); (V 43)].
Definition ZF1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (ELit 0);
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition ZF1 : ST.tmpl := ST.TM 0x3a434 ZF1_regs ZF1_kn 44%nat (add (ELit 4294967296) (sub vFL (V 23))) 0%nat.

(* [comment removed for export] *)
Definition CHF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   (V 26); (ELit 761); (ELit 61); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (V 34); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition CHF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition CHF : ST.tmpl := ST.TM 0x39ff0 CHF_regs CHF_kn 35%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (ELit 1000)) 0%nat.

(* [comment removed for export] *)
Definition DLF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   (V 27); (ELit 761); (ELit 61); (V 28); ((V 25)); ((V 26)); (V 29); (V 30);
   (V 31); (V 32); (V 33); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition DLF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KRange (V 26) 0 18;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition DLF : ST.tmpl := ST.TM 0x3a170 DLF_regs DLF_kn 34%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (ELit 999)) 0%nat.

(* [comment removed for export] *)
Definition JCF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   (V 27); (ELit 761); (ELit 61); (V 28); ((V 25)); ((V 26)); (V 29); (V 30);
   (V 31); (V 32); (V 33); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition JCF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 0 19;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition JCF : ST.tmpl := ST.TM 0x3a1a0 JCF_regs JCF_kn 34%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (ELit 2000)) 0%nat.

(* [comment removed for export] *)
Definition SMF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   ((V 24)); (ELit 761); (ELit 61); (V 27); (add vX (mul 8 (V 24))); (V 28); (V 29); (add vX (V 26));
   (V 30); (V 31); (V 32); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition SMF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KAlign (V 26) 8;
   KRange (V 26) 0 488;
   KRange (add (mul 8 (V 24)) (mul (-1) (V 26))) 8 496;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMF : ST.tmpl := ST.TM 0x3a1c8 SMF_regs SMF_kn 33%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (add (ELit 1500) (sub (mul 8 (V 24)) (V 26)))) 0%nat.

(* [comment removed for export] *)
Definition SAF2_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   ((V 24)); (ELit 761); (ELit 61); ((V 26)); (sub (add vX (mul 8 (V 24))) (mul 8 (add (V 26) (ELit (-1))))); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition SAF2_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 62;
   KRange (sub (V 24) (add (V 26) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SAF2 : ST.tmpl := ST.TM 0x3a21c SAF2_regs SAF2_kn 33%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (add (ELit 1100) (V 26))) 0%nat.

(* [comment removed for export] *)
Definition SMFX_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (ELit 8)); (ELit 8); (ELit 10);
   (ELit 0xff000000ff); (ELit 0xcfcfcfcfcfcfcfd0); (vX); ((add vFP vFL)); (ELit 769); (vDG); (ELit 0x19d30); (add vFP (V 23));
   ((V 24)); (ELit 761); (ELit 61); (V 26); (add vX (mul 8 (V 24))); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (vS11); (ELit 17); (ELit 100000000); (ELit 0xf424000000064); (ELit 0x271000000001)].
Definition SMFX_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 768;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMFX : ST.tmpl := ST.TM 0x3a1ec SMFX_regs SMFX_kn 33%nat (add (add (ELit 2147483648) (mul 1024 (sub vFL (V 23)))) (ELit 1400)) 0%nat.

(* [comment removed for export] *)
Definition SMM_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 27); (add vX (V 26)); (V 28);
   (V 29); (V 30); (vX); (vNUM); (add vX (mul 8 (V 24))); (vDG); (V 31); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (vS11); (V 41); (V 42); (V 43); (V 44)].
Definition SMM_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KAlign (V 26) 8;
   KRange (V 26) 0 488;
   KRange (add (mul 8 (V 24)) (mul (-1) (V 26))) 8 496;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMM : ST.tmpl := ST.TM 0x3a278 SMM_regs SMM_kn 45%nat (add (ELit 18874368) (sub (mul 8 (V 24)) (V 26))) 0%nat.

(* [comment removed for export] *)
Definition SMMX_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); (vNUM); (add vX (mul 8 (V 24))); (vDG); (V 31); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (vS11); (V 41); (V 42); (V 43); (V 44)].
Definition SMMX_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMMX : ST.tmpl := ST.TM 0x3a29c SMMX_regs SMMX_kn 45%nat (add (ELit 16777216) (ELit 100)) 0%nat.

(* [comment removed for export] *)
Definition SAM_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (V 31); (vX); (vNUM); ((V 26)); (vDG); (sub (add vX (mul 8 (V 24))) (mul 8 (add (V 26) (ELit (-1))))); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (vS11); (V 41); (V 42); (V 43); (V 44)].
Definition SAM_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 62;
   KRange (sub (V 24) (add (V 26) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SAM : ST.tmpl := ST.TM 0x3a2d0 SAM_regs SAM_kn 45%nat (add (ELit 14680064) (V 26)) 0%nat.

(* [comment removed for export] *)
Definition TI8_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 7); (V 26); (V 27);
   (V 28); (V 29); (vX); (vNUM); ((V 23)); (vDG); (ELit 0x3030303030303030); ((add vIP vIL));
   (sub (add vIP vIL) (V 23)); ((V 24)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (vS11); (V 39); (V 40); (V 41); (V 42)].
Definition TI8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TI8 : ST.tmpl := ST.TM 0x3a484 TI8_regs TI8_kn 43%nat (add (ELit 12582912) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition TI1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); (vNUM); (V 31); (vDG); (ELit 48); ((add vIP vIL));
   (add vIP (V 23)); ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (vS11); (V 41); (V 42); (V 43); (V 44)].
Definition TI1_kn : list kentry :=
  [KRange (V 23) 1 1048576;
   KRange (add vIL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TI1 : ST.tmpl := ST.TM 0x3a4f8 TI1_regs TI1_kn 45%nat (add (ELit 10485760) (sub vIL (V 23))) 0%nat.

(* [comment removed for export] *)
Definition TF8_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (ELit 7); ((V 23)); (V 26);
   (V 27); (V 28); (vX); (sub (add vFP vFL) (V 23)); (V 29); (vDG); (vFP); (vFL);
   (ELit 0x3030303030303030); ((V 24)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (vS11); (V 39); (V 40); (V 41); (V 42)].
Definition TF8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TF8 : ST.tmpl := ST.TM 0x3a6c4 TF8_regs TF8_kn 43%nat (add (ELit 8388608) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition TF1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); (add vFP (V 23)); (V 31); (vDG); ((add vFP vFL)); (ELit 48);
   (V 32); ((V 24)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition TF1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TF1 : ST.tmpl := ST.TM 0x3a738 TF1_regs TF1_kn 46%nat (add (ELit 6291456) (sub vFL (V 23))) 0%nat.

(* [comment removed for export] *)
Definition RM10_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); (add vX (mul 8 (V 23))); (V 31); (vDG); (ELit 10); (add vX (V 25));
   (V 32); ((V 23)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition RM10_kn : list kentry :=
  [KRange (V 23) 1 62;
   KAlign (V 25) 8;
   KRange (V 25) 0 488;
   KRange (add (mul 8 (V 23)) (mul (-1) (V 25))) 8 496;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RM10 : ST.tmpl := ST.TM 0x3a764 RM10_regs RM10_kn 46%nat (add (ELit 4194304) (add (ELit 200) (sub (mul 8 (V 23)) (V 25)))) 0%nat.

(* [comment removed for export] *)
Definition RM10X_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vX); (add vX (mul 8 (V 23))); (V 30); (vDG); (V 31); (V 32);
   (V 33); ((V 23)); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (vS11); (V 43); (V 44); (V 45); (V 46)].
Definition RM10X_kn : list kentry :=
  [KRange (V 23) 1 62;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RM10X : ST.tmpl := ST.TM 0x3a788 RM10X_regs RM10X_kn 47%nat (add (ELit 4194304) (ELit 100)) 0%nat.

(* [comment removed for export] *)
Definition RA1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((V 25)); (sub (add vX (mul 8 (V 23))) (mul 8 (add (V 25) (ELit (-1))))); (vDG); (V 31); (V 32);
   (V 33); ((V 23)); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (vS11); (V 43); (V 44); (V 45); (V 46)].
Definition RA1_kn : list kentry :=
  [KRange (V 25) 1 62;
   KRange (sub (V 23) (add (V 25) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RA1 : ST.tmpl := ST.TM 0x3a7b8 RA1_regs RA1_kn 47%nat (add (ELit 2097152) (V 25)) 0%nat.

(* [comment removed for export] *)
Definition SMMF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (add vX (V 26)); (V 27); (V 28);
   (V 29); (V 30); (vX); ((add vFP vFL)); (add vX (mul 8 (V 24))); (vDG); (V 31); (add vFP (V 23));
   ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition SMMF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KAlign (V 26) 8;
   KRange (V 26) 0 488;
   KRange (add (mul 8 (V 24)) (mul (-1) (V 26))) 8 496;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMMF : ST.tmpl := ST.TM 0x3a3a4 SMMF_regs SMMF_kn 46%nat (add (ELit 18874368) (sub (mul 8 (V 24)) (V 26))) 0%nat.

(* [comment removed for export] *)
Definition SMMFX_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((add vFP vFL)); (add vX (mul 8 (V 24))); (vDG); (V 31); (add vFP (V 23));
   ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition SMMFX_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 24) 1 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SMMFX : ST.tmpl := ST.TM 0x3a3c8 SMMFX_regs SMMFX_kn 46%nat (add (ELit 16777216) (ELit 100)) 0%nat.

(* [comment removed for export] *)
Definition SAMF_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 27); (V 28); (V 29);
   (V 30); (V 31); (vX); ((add vFP vFL)); ((V 26)); (vDG); (sub (add vX (mul 8 (V 24))) (mul 8 (add (V 26) (ELit (-1))))); (add vFP (V 23));
   ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition SAMF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KRange (V 26) 1 62;
   KRange (sub (V 24) (add (V 26) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition SAMF : ST.tmpl := ST.TM 0x3a3fc SAMF_regs SAMF_kn 46%nat (add (ELit 14680064) (V 26)) 0%nat.

(* [comment removed for export] *)
Definition TG8_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((add vFP vFL)); ((V 23)); (vDG); (ELit 0x3030303030303030); (sub (add vFP vFL) (V 23));
   ((V 24)); (ELit 7); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (vS11); (V 40); (V 41); (V 42); (V 43)].
Definition TG8_kn : list kentry :=
  [KRange (V 23) 8 1048576;
   KRange (add vFL (mul (-1) (V 23))) 0 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TG8 : ST.tmpl := ST.TM 0x3a578 TG8_regs TG8_kn 44%nat (add (ELit 8388608) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition TG1_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((add vFP vFL)); (ELit 48); (vDG); (V 31); (add vFP (V 23));
   ((V 24)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition TG1_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add vFL (mul (-1) (V 23))) 1 1048576;
   KWord (SA vDG 0) 8 (V 25);
   KRange (V 25) 0 769;
   KWord (SA vX 496) 2 (V 24);
   KRange (V 24) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition TG1 : ST.tmpl := ST.TM 0x3a5e8 TG1_regs TG1_kn 46%nat (add (ELit 6291456) (sub vFL (V 23))) 0%nat.

(* [comment removed for export] *)
Definition RM10F_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); (add vX (mul 8 (V 23))); (V 31); (vDG); (ELit 10); (add vX (V 25));
   ((V 23)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38);
   (V 39); (V 40); (V 41); (vS11); (V 42); (V 43); (V 44); (V 45)].
Definition RM10F_kn : list kentry :=
  [KRange (V 23) 1 62;
   KAlign (V 25) 8;
   KRange (V 25) 0 488;
   KRange (add (mul 8 (V 23)) (mul (-1) (V 25))) 8 496;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RM10F : ST.tmpl := ST.TM 0x3a614 RM10F_regs RM10F_kn 46%nat (add (ELit 4194304) (add (ELit 200) (sub (mul 8 (V 23)) (V 25)))) 0%nat.

(* [comment removed for export] *)
Definition RM10FX_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (V 29); (vX); (add vX (mul 8 (V 23))); (V 30); (vDG); (V 31); (V 32);
   ((V 23)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (vS11); (V 43); (V 44); (V 45); (V 46)].
Definition RM10FX_kn : list kentry :=
  [KRange (V 23) 1 62;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RM10FX : ST.tmpl := ST.TM 0x3a638 RM10FX_regs RM10FX_kn 47%nat (add (ELit 4194304) (ELit 100)) 0%nat.

(* [comment removed for export] *)
Definition RA1F_regs : list expr :=
  [ELit 0; (vRA); (spo (-96)); (vGP); (vTP); (V 26); (V 27); (V 28);
   (V 29); (V 30); (vX); ((V 25)); (sub (add vX (mul 8 (V 23))) (mul 8 (add (V 25) (ELit (-1))))); (vDG); (V 31); (V 32);
   ((V 23)); (V 33); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (vS11); (V 43); (V 44); (V 45); (V 46)].
Definition RA1F_kn : list kentry :=
  [KRange (V 25) 1 62;
   KRange (sub (V 23) (add (V 25) (ELit (-1)))) 0 62;
   KWord (SA vDG 0) 8 (V 24);
   KRange (V 24) 0 769;
   KWord (SA vX 496) 2 (V 23);
   KRange (V 23) 0 62;
   KWord (SA vSP (-8)) 8 vS0;
   KWord (SA vSP (-16)) 8 vS1;
   KWord (SA vSP (-24)) 8 vS2;
   KWord (SA vSP (-32)) 8 vS3;
   KWord (SA vSP (-40)) 8 vS4;
   KWord (SA vSP (-48)) 8 vS5;
   KWord (SA vSP (-56)) 8 vS6;
   KWord (SA vSP (-64)) 8 vS7;
   KWord (SA vSP (-72)) 8 vS8;
   KWord (SA vSP (-80)) 8 vS9;
   KWord (SA vSP (-88)) 8 vS10;
   KRange vSP 140728898420832 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-96)) (ELit 96);
   KRange vX 0x7ffe00000000 0x800000000000;
   KAlign vX 8;
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vX 0) (ELit 498);
   KRange vDG 0x7ffe00000000 0x800000000000;
   KWr (SA vDG 0) (ELit 8);
   KDisj (SA vDG 0) (ELit 8) (SA vX 0) (ELit 498);
   KDisj (SA vSP (-96)) (ELit 96) (SA vDG 0) (ELit 8);
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
   KDisj (SA vSP (-96)) (ELit 96) (SA vNUM 0) (ELit 64);
   KDisj (SA vIP 0) vIL (SA vX 0) (ELit 498);
   KDisj (SA vFP 0) vFL (SA vX 0) (ELit 498);
   KDisj (SA vIP 0) vIL (SA vDG 0) (ELit 8);
   KDisj (SA vFP 0) vFL (SA vDG 0) (ELit 8);
   KDisj (SA vSP (-96)) (ELit 96) (SA vIP 0) vIL;
   KDisj (SA vSP (-96)) (ELit 96) (SA vFP 0) vFL;
   KImg 0x10000 0x2572c].
Definition RA1F : ST.tmpl := ST.TM 0x3a668 RA1F_regs RA1F_kn 47%nat (add (ELit 2097152) (V 25)) 0%nat.

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
   KRange (V 24) 0 770].
Definition XR : ST.tmpl := ST.TM 0x3a87c XR_regs XR_kn 40%nat (ELit 0) 0%nat.

Definition PM : SP.prog := SP.PGC 23 [T0; ZS8; ZS1; CH; DL; JC; SMI; SAI; SMIX; JF; ZF8; ZF1; CHF; DLF; JCF; SMF; SAF2; SMFX; SMM; SMMX; SAM; TI8; TI1; TF8; TF1; RM10; RM10X; RA1; SMMF; SMMFX; SAMF; TG8; TG1; RM10F; RM10FX; RA1F] [XR] [(vSP, -96, ELit 96); (vX, 0, ELit 498); (vDG, 0, ELit 8)] [] [].
End PM_defs.

Module PM_sum.
(* [comment removed for export] *)
Definition PMS : SP.summ := SP.SUM 23 PM_defs.T0 [PM_defs.XR] [(PM_defs.vSP, -96, ELit 96); (PM_defs.vX, 0, ELit 498); (PM_defs.vDG, 0, ELit 8)].
End PM_sum.

Module SLOW_defs.
Import PM_sum.
Import PDC_sum.
Import NDC_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition SLOW_IT : itab := APC.mk_itab_ranges SG [(0x3872c, 1304%nat); (0x707a4, 100%nat); (0x39b8c, 829%nat); (0x3a880, 217%nat); (0x3abe4, 243%nat)].
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x3872c T0_regs T0_kn 28%nat (ELit 167772160) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 19)); (V 21); (ELit 9);
   (vS0); (vS1); (add vF (V 20)); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (ELit 10);
   (V 22); (V 23); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 24); (V 25); (V 26); (V 27)].
Definition IL_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition IL : ST.tmpl := ST.TMG 0x3885c IL_regs IL_kn 28%nat (add (ELit 163577856) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]].

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 19)); (V 21); (V 22);
   (vS0); (vS1); (add vF (V 20)); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (add (V 19) (mul (-1) (V 20)));
   (V 23); (V 24); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J1 : ST.tmpl := ST.TMG 0x38a44 J1_regs J1_kn 29%nat (ELit 159383552) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]].

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 20)); (add vF (V 21)); (add (add vF (V 20)) (ELit 1));
   (ELit 0x271000000001); (ELit 0xff000000ff); (sub (add vF vN) (V 19)); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (add (V 20) (mul (-1) (V 21)));
   (V 22); (V 23); (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x4646464646464646); (ELit 10); (ELit 7); (V 24); (V 25);
   (V 26); (V 27); (V 28); (V 29); ((V 19)); (ELit 0x8080808080808080); (ELit 0x5f5e100); (ELit 0xf424000000064)].
Definition SW_kn : list kentry :=
  [KRange (V 19) 8 1048576;
   KRange (add vN (mul (-1) (V 19))) 2 1048576;
   KRange (add vN (add (mul (-1) (V 19)) (mul (-1) (V 20)))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 9 1048576;
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition SW : ST.tmpl := ST.TMG 0x38ac8 SW_regs SW_kn 30%nat (add (ELit 155189248) ((V 19))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 2 [add vF (V 20)]; ST.GA 1 [add (add vF (V 20)) (ELit 1); add (add vN (add (mul (-1) (V 19)) (mul (-1) (V 20)))) (ELit (-1))]].

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 20)); (add vF (V 21)); (add (add vF (V 20)) (ELit 1));
   (V 22); (V 23); (add vF (V 19)); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (add (V 20) (mul (-1) (V 21)));
   (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (V 34); (V 35); (ELit 9); (ELit 10); (V 36); (V 37)].
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FL : ST.tmpl := ST.TMG 0x38fdc FL_regs FL_kn 38%nat (add (ELit 150994944) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 2 [add vF (V 20)]; ST.GA 1 [add (add vF (V 20)) (ELit 1); add (add (V 19) (mul (-1) (V 20))) (ELit (-1))]].

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 20)); (add vF (V 21)); ((V 22));
   (V 24); (V 25); (add vF (V 19)); ((add vF vN)); (vV); (ELit 53); (ELit 0xa0000002e); (add (V 20) (mul (-1) (V 21)));
   (V 26); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); ((V 23)); (add (add (V 20) (mul (-1) (V 21))) (V 23)); (V 38); (V 39)].
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 22) 0) (V 23);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J2 : ST.tmpl := ST.TMG 0x39018 J2_regs J2_kn 40%nat (ELit 146800640) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]].

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 20)); (add vF (V 21)); ((V 22));
   (ELit 9); (V 24); (ELit 10); ((add vF vN)); (vV); (V 25); (ELit 0xa0000002e); (add (V 20) (mul (-1) (V 21)));
   (V 26); (V 27); (ELit 0x10000000); (V 28); (V 29); (V 30); (V 31); (V 32);
   (V 33); (V 34); (V 35); (V 36); ((V 23)); (add (add (V 20) (mul (-1) (V 21))) (V 23)); (add vF (V 19)); (V 37)].
Definition EL_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 22) 0) (V 23);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition EL : ST.tmpl := ST.TMG 0x39230 EL_regs EL_kn 38%nat (add (ELit 142606336) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]].

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 19)); (add vF (V 20)); ((V 21));
   (V 23); (V 24); (V 25); ((add vF vN)); (vV); (V 26); (ELit 0xa0000002e); (add (V 19) (mul (-1) (V 20)));
   (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (V 36); (V 37); (V 38); ((V 22)); (add (add (V 19) (mul (-1) (V 20))) (V 22)); (V 39); (V 40)].
Definition J3_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J3 : ST.tmpl := ST.TMG 0x39374 J3_regs J3_kn 41%nat (ELit 138412032) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]; ST.GA 1 [(V 21); (V 22)]; ST.GA 3 [add vF (V 20); add (V 19) (mul (-1) (V 20)); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 20)); (add vF (V 21)); ((V 22));
   (V 25); (V 26); (V 27); ((add vF vN)); (vV); (V 28); (ELit 46); (add (V 20) (mul (-1) (V 21)));
   (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); ((V 23)); ((V 24)); (ELit 48); (add vF (V 19))].
Definition ZS_kn : list kentry :=
  [KRange (V 19) 0 1048576;
   KRange (add vN (mul (-1) (V 19))) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 21))) 0 1048576;
   KRange (V 21) 0 1;
   KRange (V 20) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 22) 0) (V 23);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition ZS : ST.tmpl := ST.TMG 0x3939c ZS_regs ZS_kn 41%nat (add (ELit 134217728) (add vN (mul (-1) (V 19)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 20) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 3 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 22); (V 23)]; ST.GA 4 [add vF (V 21); add (V 19) (mul (-1) (V 21)); add (add (add (V 20) (mul (-1) (V 21))) (V 23)) (mul (-1) (V 24))]].

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 19)); (add vF (V 20)); ((V 21));
   (V 24); (V 25); (V 26); (V 27); (vV); (V 28); (V 29); (add (V 19) (mul (-1) (V 20)));
   (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); ((V 22)); ((V 23)); (V 42); (V 43)].
Definition J4_kn : list kentry :=
  [KRange (V 20) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J4 : ST.tmpl := ST.TMG 0x393b0 J4_regs J4_kn 44%nat (ELit 130023424) 0%nat [ST.GA 1 [add vF (V 20); add (V 19) (mul (-1) (V 20))]; ST.GA 1 [(V 21); (V 22)]; ST.GA 5 [add vF (V 20); add (V 19) (mul (-1) (V 20)); (V 21); (V 22)]].

(* [comment removed for export] *)
Definition TI_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (add vF (V 19)); (add vF (V 21)); ((V 22));
   (V 25); (V 26); (V 27); (add vF (V 20)); (vV); (V 28); (ELit 0xde0b6b3a763ffff); (add (V 19) (mul (-1) (V 21)));
   (V 29); ((V 24)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); ((V 23)); (ELit 10); (V 40); (V 41)].
Definition TI_kn : list kentry :=
  [KRange (V 20) 0 1048576;
   KRange (add (V 19) (mul (-1) (V 20))) 1 1048576;
   KRange (add vN (mul (-1) (V 20))) 1 1048576;
   KRange (add (V 20) (mul (-1) (V 21))) 0 1048576;
   KRange (V 24) 0 999999999999999999;
   KRange (V 21) 0 1;
   KRange (V 19) 1 1048576;
   KRange (add (V 19) (mul (-1) (V 21))) 1 1048576;
   KRange (add vN (mul (-1) (V 19))) 0 1048576;
   KRange (V 23) 0 1048576;
   KRange (V 22) 0 0x7fffff7fffff;
   KRange (add (V 22) (V 23)) 0 0x7fffff800000;
   KUnk (SA (V 22) 0) (V 23);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 22) 0) (V 23);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition TI : ST.tmpl := ST.TMG 0x393c8 TI_regs TI_kn 42%nat (add (ELit 125829120) (add (V 19) (mul (-1) (V 20)))) 0%nat [ST.GA 1 [add vF (V 21); add (V 19) (mul (-1) (V 21))]; ST.GA 1 [(V 22); (V 23)]; ST.GA 5 [add vF (V 21); add (V 19) (mul (-1) (V 21)); (V 22); (V 23)]; ST.GA 6 [add vF (V 21); add (V 20) (mul (-1) (V 21)); (V 24)]].

(* [comment removed for export] *)
Definition TF_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (ELit 10); ((V 19)); ((V 21));
   (V 25); (V 26); (V 27); (sub (sub (add (V 21) (V 22)) (V 23)) (ELit 1)); (vV); (V 28); (ELit 0xde0b6b3a763ffff); ((V 20));
   (V 29); ((V 24)); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); ((V 22)); ((V 23)); (V 40); (V 41)].
Definition TF_kn : list kentry :=
  [KRange (V 23) 0 1048576;
   KRange (add (V 22) (mul (-1) (V 23))) 1 1048576;
   KRange (V 24) 0 999999999999999999;
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition TF : ST.tmpl := ST.TMG 0x39400 TF_regs TF_kn 42%nat (add (ELit 121634816) ((V 23))) 0%nat [ST.GA 1 [(V 19); (V 20)]; ST.GA 1 [(V 21); (V 22)]; ST.GA 5 [(V 19); (V 20); (V 21); (V 22)]; ST.GA 6 [(V 19); (V 20); (V 24)]; ST.GA 6 [(V 21); add (add (V 22) (mul (-1) (V 23))) (ELit (-1)); (V 24)]].

(* [comment removed for export] *)
Definition J5T_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 24); ((V 19)); ((V 21));
   (V 25); (V 26); (V 27); (V 28); (vV); (V 29); (V 30); ((V 20));
   (V 31); ((V 23)); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); ((V 22)); (V 42); (V 43); (V 44)].
Definition J5T_kn : list kentry :=
  [KRange (V 23) 1 9999999999999999999;
   KRange (V 20) 0 1048576;
   KRange (V 19) 16 0x7fffff7fffff;
   KRange (add (V 19) (V 20)) 16 0x7fffff800000;
   KUnk (SA (V 19) 0) (V 20);
   KRange (V 22) 0 1048576;
   KRange (V 21) 0 0x7fffff7fffff;
   KRange (add (V 21) (V 22)) 0 0x7fffff800000;
   KUnk (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J5T : ST.tmpl := ST.TM 0x39488 J5T_regs J5T_kn 45%nat (ELit 117440512) 0%nat.

(* [comment removed for export] *)
Definition J5N_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (V 22); (V 23); (V 24); (V 25); (vV); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition J5N_kn : list kentry :=
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J5N : ST.tmpl := ST.TM 0x3942c J5N_regs J5N_kn 45%nat (ELit 117440512) 0%nat.

(* [comment removed for export] *)
Definition CF2M_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (add (ELit (-342)) (V 24)); (V 29); (add (V 23) (ELit 1)); (vV); (V 30); (V 31); (V 32);
   (V 33); ((V 23)); (V 34); (V 35); (V 36); (V 37); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition CF2M_kn : list kentry :=
  [KRange (V 24) 0 650;
   KRange (V 23) 1 9999999999999999999;
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition CF2M : ST.tmpl := ST.TM 0x396fc CF2M_regs CF2M_kn 48%nat (ELit 113246208) 0%nat.

(* [comment removed for export] *)
Definition CE_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (add (ELit (-342)) (V 24)); (V 29); (V 30); (vV); (V 31); (V 32); (V 33);
   (V 34); ((V 23)); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40);
   (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48)].
Definition CE_kn : list kentry :=
  [KRange (V 24) 0 650;
   KRange (V 23) 1 9999999999999999999;
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition CE : ST.tmpl := ST.TM 0x398c4 CE_regs CE_kn 49%nat (ELit 109051904) 0%nat.

(* [comment removed for export] *)
Definition JDC_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 25); (V 26); (V 27);
   (V 28); (add (ELit (-342)) (V 24)); (V 29); (V 30); (vV); (V 31); (V 32); (V 33);
   (V 34); ((V 23)); (V 35); (V 36); (V 37); (V 38); (V 39); (V 40);
   (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48)].
Definition JDC_kn : list kentry :=
  [KRange (V 24) 0 650;
   KRange (V 23) 1 9999999999999999999;
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition JDC : ST.tmpl := ST.TM 0x399f8 JDC_regs JDC_kn 49%nat (ELit 104857600) 0%nat.

(* [comment removed for export] *)
Definition JSE_regs : list expr :=
  [ELit 0; (vRA); (spo (-688)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (V 27); (add (ELit (-342)) (V 23)); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (vV); (V 38); (V 39); (V 40);
   (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47); (V 48)].
Definition JSE_kn : list kentry :=
  [KRange (V 23) 0 669;
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition JSE : ST.tmpl := ST.TM 0x39a98 JSE_regs JSE_kn 49%nat (ELit 100663296) 0%nat.

(* [comment removed for export] *)
Definition R1_regs : list expr :=
  [ELit 0; (ELit 0x39ab4); (spo (-688)); (vGP); (vTP); (V 24); (V 25); (V 26);
   (V 27); (add (ELit (-342)) (V 23)); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (V 35); (V 36); (V 37); (vV); (ELit 0xffffffff); (V 38); (V 39);
   (V 40); (V 41); (V 42); (V 43); (V 44); (V 45); (V 46); (V 47)].
Definition R1_kn : list kentry :=
  [KRange (V 23) 0 669;
   KWord (SA vSP (-120)) 2 (ELit 0);
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
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 21) 0) (V 22);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA (V 19) 0) (V 20);
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition R1 : ST.tmpl := ST.TM 0x39ab4 R1_regs R1_kn 48%nat (ELit 96468992) 0%nat.

(* [comment removed for export] *)
Definition R2_regs : list expr :=
  [ELit 0; (ELit 0x39ac8); (spo (-688)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (V 25); (add (ELit (-342)) (V 19)); (V 26); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); (V 34); (V 35); (vV); (ELit 0xffffffff); (V 36); (V 37);
   (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44); (V 45)].
Definition R2_kn : list kentry :=
  [KRange (V 19) 0 669;
   KWord (SA vSP (-120)) 2 (V 20);
   KRange (V 20) 0 62;
   KWord (SA vSP (-112)) 8 (V 21);
   KRange (V 21) 0 770;
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
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition R2 : ST.tmpl := ST.TM 0x39ac8 R2_regs R2_kn 46%nat (ELit 92274688) 0%nat.

(* [comment removed for export] *)
Definition R3_regs : list expr :=
  [ELit 0; (ELit 0x39ae4); (spo (-688)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (V 22); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (V 33); (vV); (ELit 0xffffffff); (V 34); (V 35);
   (V 36); (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43)].
Definition R3_kn : list kentry :=
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition R3 : ST.tmpl := ST.TM 0x39ae4 R3_regs R3_kn 44%nat (ELit 88080384) 0%nat.

(* [comment removed for export] *)
Definition R4_regs : list expr :=
  [ELit 0; (V 19); (spo (-688)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29); (V 30);
   (V 31); (V 32); (V 33); (V 34); (vV); (ELit 0xffffffff); (V 35); (V 36);
   (V 37); (V 38); (V 39); (V 40); (V 41); (V 42); (V 43); (V 44)].
Definition R4_kn : list kentry :=
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
   KRange vN 1 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423184 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2448)) (ELit 2448);
   KUnk (SA vSP (-2448)) (ELit 2448);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vF 0) vN;
   KRange vV 0x7ffe00000000 0x800000000000;
   KWr (SA vV 0) (ELit 8);
   KUnk (SA vV 0) (ELit 8);
   KDisj (SA vSP (-2448)) (ELit 2448) (SA vV 0) (ELit 8);
   KDisj (SA vV 0) (ELit 8) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition R4 : ST.tmpl := ST.TM 0x39b00 R4_regs R4_kn 45%nat (ELit 83886080) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 19); (V 20); (V 21);
   vS0; vS1; (V 22); (V 23); (V 24); (V 25); (V 26); (V 27);
   (V 28); (V 29); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 30); (V 31); (V 32); (V 33)].
Definition X_kn : list kentry :=
  [KUnk (SA vV 0) (ELit 8)].
Definition X : ST.tmpl := ST.TM 0x39b88 X_regs X_kn 34%nat (ELit 0) 0%nat.

Definition SLOW : SP.prog := SP.PGC 19 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; TI; TF; J5T; J5N; CF2M; CE; JDC; JSE; R1; R2; R3; R4] [X] [(vSP, -2448, ELit 2448); (vV, 0, ELit 8)] [SX.SpHav 0x3958c 13; SX.SpHav 0x395c0 15; SX.SpHav 0x39784 7; SX.SpHav 0x397b8 14; SX.SpHav 0x39940 13; SX.SpHav 0x39984 13] [MMP.MSP 0 0x39ab4; PMS; PDCS; NDCS].
End SLOW_defs.

Module SLOW_sum.
(* [comment removed for export] *)
Definition SLOWS : SP.summ := SP.SUM 19 SLOW_defs.T0 [SLOW_defs.X] [(SLOW_defs.vSP, -2448, ELit 2448); (SLOW_defs.vV, 0, ELit 8)].
End SLOW_sum.

Module PWF_defs.
Import SLOW_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition PWF_IT : itab := APC.mk_itab_ranges SG [(0x272a8, 505%nat); (0x3872c, 1304%nat)].
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
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x272a8 T0_regs T0_kn 31%nat (ELit 41943040) 0%nat.

(* [comment removed for export] *)
Definition IL_regs : list expr :=
  [ELit 0; (V 20); (spo (-96)); (vGP); (vTP); ((add vF vN)); (ELit 9); (V 21);
   (vS0); (vS1); (vF); ((add vF vN)); (V 22); (V 23); (add vF (V 19)); (ELit 10);
   (add vF (V 18)); (V 24); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 25); (V 26); (V 27); (V 28)].
Definition IL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 1 1048576;
   KRange (V 19) 0 1;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition IL : ST.tmpl := ST.TM 0x273e0 IL_regs IL_kn 29%nat (add (ELit 37748736) (sub vN (V 18))) 0%nat.

(* [comment removed for export] *)
Definition J1_regs : list expr :=
  [ELit 0; (V 20); (spo (-96)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vF); ((add vF vN)); (V 26); (V 27); (add vF (V 19)); (V 28);
   (add vF (V 18)); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (vS9); (vS10); (vS11); (V 37); (V 38); (V 39); (V 40)].
Definition J1_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 0 1048576;
   KRange (V 19) 0 1;
   KRange (add (V 18) (mul (-1) (V 19))) 0 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J1 : ST.tmpl := ST.TM 0x27418 J1_regs J1_kn 41%nat (ELit 33554432) 0%nat.

(* [comment removed for export] *)
Definition SW_regs : list expr :=
  [ELit 0; (V 21); (spo (-96)); (vGP); (vTP); ((V 18)); (ELit 10); (ELit 0x8080808080808080);
   (ELit 0xcfcfcfcfcfcfcfd0); (ELit 0x271000000001); (vF); ((add vF vN)); (V 22); (V 23); (add vF (V 19)); (V 24);
   (sub (add vF vN) (V 18)); (add vF (V 20)); (ELit 7); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (vS9); (vS10); (vS11); (ELit 0x5f5e100); (ELit 0xff000000ff); (ELit 0xf424000000064); (ELit 0x4646464646464646)].
Definition SW_kn : list kentry :=
  [KRange (V 18) 8 1048576;
   KRange (sub vN (V 18)) 0 1048576;
   KRange (V 20) 0 1048576;
   KRange (V 19) 0 1;
   KRange (sub vN (V 19)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition SW : ST.tmpl := ST.TM 0x274b0 SW_regs SW_kn 31%nat (add (ELit 29360128) (V 18)) 0%nat.

(* [comment removed for export] *)
Definition FL_regs : list expr :=
  [ELit 0; (V 21); (spo (-96)); (vGP); (vTP); (ELit 9); (ELit 10); (V 22);
   (V 23); (V 24); (vF); ((add vF vN)); (V 25); (V 26); (add vF (V 19)); (V 27);
   (add vF (V 18)); (add vF (V 20)); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition FL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 1 1048576;
   KRange (V 20) 0 1048576;
   KRange (V 19) 0 1;
   KRange (sub vN (V 19)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FL : ST.tmpl := ST.TM 0x27614 FL_regs FL_kn 39%nat (add (ELit 25165824) (sub vN (V 18))) 0%nat.

(* [comment removed for export] *)
Definition J2_regs : list expr :=
  [ELit 0; (V 20); (spo (-96)); (vGP); (vTP); (V 21); (V 22); (V 23);
   (V 24); (V 25); (vF); ((add vF vN)); (V 26); (V 27); (add vF (V 19)); (V 28);
   (add vF (V 18)); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (vS9); (vS10); (vS11); (V 37); (V 38); (V 39); (V 40)].
Definition J2_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 1 1048576;
   KRange (V 19) 0 1;
   KRange (sub vN (V 19)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J2 : ST.tmpl := ST.TM 0x27648 J2_regs J2_kn 41%nat (ELit 20971520) 0%nat.

(* [comment removed for export] *)
Definition EL_regs : list expr :=
  [ELit 0; (V 20); (spo (-96)); (vGP); (vTP); (add vF (V 18)); (V 21); (ELit 9);
   (V 22); (V 23); (vF); ((add vF vN)); (V 24); (V 25); (add vF (V 19)); (V 26);
   (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34);
   (V 35); (vS9); (vS10); (vS11); (ELit 10); (ELit 0x10000000); (V 36); (V 37)].
Definition EL_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 1 1048576;
   KRange (V 19) 0 1;
   KRange (sub vN (V 19)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition EL : ST.tmpl := ST.TM 0x276b4 EL_regs EL_kn 38%nat (add (ELit 16777216) (sub vN (V 18))) 0%nat.

(* [comment removed for export] *)
Definition J3_regs : list expr :=
  [ELit 0; (V 19); (spo (-96)); (vGP); (vTP); (V 20); (V 21); (V 22);
   (V 23); (V 24); (vF); ((add vF vN)); (V 25); (V 26); (add vF (V 18)); (V 27);
   (V 28); (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35);
   (V 36); (vS9); (vS10); (vS11); (V 37); (V 38); (V 39); (V 40)].
Definition J3_kn : list kentry :=
  [KRange (V 18) 0 1;
   KRange (sub vN (V 18)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J3 : ST.tmpl := ST.TM 0x276e0 J3_regs J3_kn 41%nat (ELit 12582912) 0%nat.

(* [comment removed for export] *)
Definition ZS_regs : list expr :=
  [ELit 0; (V 19); (spo (-96)); (vGP); (vTP); (ELit 46); (V 20); (V 21);
   (V 22); (V 23); (vF); ((add vF vN)); (V 24); (V 25); (add vF (V 18)); (V 26);
   (ELit 48); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32); (V 33);
   (V 34); (vS9); (vS10); (vS11); (V 35); (V 36); (V 37); (V 38)].
Definition ZS_kn : list kentry :=
  [KRange (V 18) 0 1048576;
   KRange (sub vN (V 18)) 1 1048576;
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition ZS : ST.tmpl := ST.TM 0x27708 ZS_regs ZS_kn 39%nat (add (ELit 8388608) (sub vN (V 18))) 0%nat.

(* [comment removed for export] *)
Definition J4_regs : list expr :=
  [ELit 0; (V 18); (spo (-96)); (vGP); (vTP); (V 19); (V 20); (V 21);
   (V 22); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28); (V 29);
   (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36); (V 37);
   (V 38); (vS9); (vS10); (vS11); (V 39); (V 40); (V 41); (V 42)].
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
   KWord (SA vSP (-88)) 8 (ELit 0);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition J4 : ST.tmpl := ST.TM 0x2771c J4_regs J4_kn 43%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (ELit 0x27a50); (spo (-96)); (vGP); (vTP); (V 18); (V 19); (V 20);
   (V 21); (V 22); (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); (V 31); (V 32); (V 33); (V 34); (V 35); (V 36);
   (V 37); (vS9); (vS10); (vS11); (V 38); (V 39); (V 40); (V 41)].
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
   KUnk (SA vSP (-88)) (ELit 8);
   KRange vN 0 1048576;
   KRange vF 16 0x7fffff7fffff;
   KRange (add vF vN) 16 0x7fffff800000;
   KUnk (SA vF 0) vN;
   KRange vSP 140728898423280 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2544)) (ELit 2544);
   KUnk (SA vSP (-2544)) (ELit 2544);
   KDisj (SA vSP (-2544)) (ELit 2544) (SA vF 0) vN;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition RS : ST.tmpl := ST.TM 0x27a50 RS_regs RS_kn 42%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 18); (V 19); (V 20);
   vS0; vS1; (V 21); (V 22); (V 23); (V 24); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition X_kn : list kentry :=
  [].
Definition X : ST.tmpl := ST.TM 0x279f8 X_regs X_kn 33%nat (ELit 0) 0%nat.

Definition PWF : SP.prog := SP.PGC 18 [T0; IL; J1; SW; FL; J2; EL; J3; ZS; J4; RS] [X] [(vSP, -2544, ELit 2544)] [SX.SpHav 0x277e4 5; SX.SpHav 0x27818 11] [SLOWS].
End PWF_defs.

Module PWF_sum.
(* [comment removed for export] *)
Definition PWFS : SP.summ := SP.SUM 18 PWF_defs.T0 [PWF_defs.X] [(PWF_defs.vSP, -2544, ELit 2544)].
End PWF_sum.

Module SFP_defs.
Import PWF_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition SFP_IT : itab := APC.mk_itab_ranges SG [(0x3b494, 34%nat); (0x272a8, 505%nat)].
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x3b494 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit 58); (ELit 288230376218820621); (V 25);
   (V 26); (V 27); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 0 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x3b4cc FE_regs FE_kn 32%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 0x3b4f0); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x3b4f0 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2560)) (ELit 2560)].
Definition X : ST.tmpl := ST.TM 0x3b518 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition SFP : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2560, ELit 2560); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x3b4cc BC_EQ (EVar 20) (EVar 17)] [PWFS].
End SFP_defs.

Module SFPC_defs.
Import PWF_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition SFPC_IT : itab := APC.mk_itab_ranges SG [(0x3b494, 34%nat); (0x272a8, 505%nat)].
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x3b494 T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit 58); (ELit 288230376218820621); (V 25);
   (V 26); (V 27); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 0 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x3b4cc FE_regs FE_kn 32%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 0x3b4f0); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x3b4f0 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2560)) (ELit 2560)].
Definition X : ST.tmpl := ST.TM 0x3b518 X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition SFPC : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2560, ELit 2560); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x3b4cc BC_EQ (EVar 20) (EVar 17)] [PWFS].
End SFPC_defs.

Module PFF_defs.
Import PWF_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition PFF_IT : itab := APC.mk_itab_ranges SG [(0x3b51c, 33%nat); (0x272a8, 505%nat)].
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x3b51c T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit 58); (ELit 288230376218820621); (V 25);
   (V 26); (V 27); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 0 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KZero (SA (add vRB vRL) 0) (ELit 1);
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x3b554 FE_regs FE_kn 32%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 0x3b578); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x3b578 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2560)) (ELit 2560)].
Definition X : ST.tmpl := ST.TM 0x3b59c X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PFF : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2560, ELit 2560); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x3b554 BC_EQ (EVar 20) (EVar 17)] [PWFS].
End PFF_defs.

Module PFFC_defs.
Import PWF_sum.
(* [comment removed for export] *)

Definition SG : list Segment := Plain.M.loaded_segments.
Definition PFFC_IT : itab := APC.mk_itab_ranges SG [(0x3b51c, 33%nat); (0x272a8, 505%nat)].
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition T0 : ST.tmpl := ST.TM 0x3b51c T0_regs T0_kn 33%nat (ELit 4194304) 0%nat.

(* [comment removed for export] *)
Definition FE_regs : list expr :=
  [ELit 0; (V 21); (spo (-16)); (vGP); (vTP); (V 22); (V 23); (V 24);
   (vOUT); (vS1); (add vRB vP); (add vRB (V 20)); (ELit 10); (ELit 58); (ELit 288230376218820621); (V 25);
   (V 26); (V 27); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 28); (V 29); (V 30); (V 31)].
Definition FE_kn : list kentry :=
  [KRange (sub (V 20) vP) 0 1048576;
   KRange (sub vRL (V 20)) 0 1048576;
   KRange (V 20) 0 1048576;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KRange vRL 0 1048576;
   KRange vP 0 1048576;
   KRange (sub vRL vP) 0 1048576;
   KRange vRB 16 0x7fffff7fffff;
   KRange (add vRB (add vRL (ELit 1))) 16 0x7fffff800000;
   KUnk (SA vRB 0) (add vRL (ELit 1));
   KFill (SA (add vRB vRL) 0) (ELit 1) 32;
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition FE : ST.tmpl := ST.TM 0x3b554 FE_regs FE_kn 32%nat (sub vRL (V 20)) 1%nat.

(* [comment removed for export] *)
Definition RT_regs : list expr :=
  [ELit 0; (ELit 0x3b578); (spo (-16)); (vGP); (vTP); (V 20); (V 21); (V 22);
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
   KRange vSP 140728898423296 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-2560)) (ELit 2560);
   KUnk (SA vSP (-2560)) (ELit 2560);
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vRB 0) (add vRL (ELit 1));
   KWr (SA vOUT 0) (ELit 8);
   KRange (sub vOUT vSP) 0 65536;
   KDisj (SA vSP (-2560)) (ELit 2560) (SA vOUT 0) (ELit 8);
   KRange vOUT 0x7ffe00000000 0x7ffffffffff0;
   KImg 0x10000 0x2572c;
   KWord (SA (ELit 0) 0x76ed0) 4 (ELit 8388608)].
Definition RT : ST.tmpl := ST.TM 0x3b578 RT_regs RT_kn 35%nat (ELit 0) 0%nat.

(* [comment removed for export] *)
Definition X_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 20); (V 21); (V 22);
   vS0; vS1; (V 23); (V 24); (V 25); (V 26); (V 27); (V 28);
   (V 29); (V 30); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 31); (V 32); (V 33); (V 34)].
Definition X_kn : list kentry :=
  [KUnk (SA vOUT 0) (ELit 8);
   KUnk (SA vSP (-2560)) (ELit 2560)].
Definition X : ST.tmpl := ST.TM 0x3b59c X_regs X_kn 35%nat (ELit 0) 0%nat.

Definition PFFC : SP.prog := SP.PGC 20 [T0; FE; RT] [X] [(vSP, -2560, ELit 2560); (vOUT, 0, ELit 8)] [SX.SpCmpV 0x3b554 BC_EQ (EVar 20) (EVar 17)] [PWFS].
End PFFC_defs.
