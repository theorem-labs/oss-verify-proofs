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
Definition LADBN_IT : itab := APC.mk_itab_ranges SG [(0xd1e98, 205%nat)].
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
Definition vY8 := V 17.
Definition vZL := V 18.
Definition vI := V 19.
Definition vLX := V 20.
Definition vZ := V 21.
Definition vX := mul 8 vX8.
Definition vY := mul 8 vY8.
Definition spo (k : Z) : expr := add vSP (ELit k).

(* [comment removed for export] *)
Definition T0_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 22); (V 23); (V 24);
   vS0; vS1; (vX); (vY); (vZL); (vI); (V 25); (V 26);
   (V 27); (V 28); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 29); (V 30); (V 31); (V 32)].
Definition T0_kn : list kentry :=
  [KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KRange vSP 140728898420816 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-80)) (ELit 80);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KRange vY8 0xce200 0xfffffefffff;
   KRange (add vY (mul 8 vZL)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vY 0) (mul 8 vZL);
   KUnk (SA vY 0) (mul 8 vZL);
   KZero (SA vY8 2147450880) vZL;
   KDisj (SA vSP (-80)) (ELit 80) (SA vX 0) (ELit 504);
   KDisj (SA vSP (-80)) (ELit 80) (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 504);
   KRange vZL 0 62;
   KRange vI 1 4;
   KRange vLX 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vZ 0 55;
   KRange (sub (add vZ (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vZ (add vI (ELit 1))) vLX) 0 66].
Definition T0 : ST.tmpl := ST.TM 0xd1e98 T0_regs T0_kn 33%nat (ELit 4096) 0%nat.

(* [comment removed for export] *)
Definition RS_regs : list expr :=
  [ELit 0; (vRA); (spo (-80)); (vGP); (vTP); (add vX8 (ELit 2147450942)); (ELit 2147450880); (V 22);
   (vS0); (vS1); (add vX (ELit 496)); (vY); (vZL); (vI); (vX); (vLX);
   ((add vZL vI)); (ELit 62); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (V 23); (V 24); (V 25); (V 26)].
Definition RS_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) vLX))) 8 496;
   KRange (add vZL (add vI (mul (-1) vLX))) 1 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898420816 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-80)) (ELit 80);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KRange vY8 0xce200 0xfffffefffff;
   KRange (add vY (mul 8 vZL)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vY 0) (mul 8 vZL);
   KUnk (SA vY 0) (mul 8 vZL);
   KZero (SA vY8 2147450880) vZL;
   KDisj (SA vSP (-80)) (ELit 80) (SA vX 0) (ELit 504);
   KDisj (SA vSP (-80)) (ELit 80) (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 504);
   KRange vZL 0 62;
   KRange vI 1 4;
   KRange vLX 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vZ 0 55;
   KRange (sub (add vZ (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vZ (add vI (ELit 1))) vLX) 0 66].
Definition RS : ST.tmpl := ST.TM 0xd1f10 RS_regs RS_kn 27%nat (ELit 3500) 0%nat.

(* [comment removed for export] *)
Definition RZ_regs : list expr :=
  [ELit 0; (vRA); (spo (-80)); (vGP); (vTP); (add vX8 (ELit 2147450942)); (ELit 2147450880); (add (V 22) (ELit 1));
   (vS0); (vS1); (add vX (ELit 496)); (vY); (vZL); (vI); (vX); (add vX (mul 8 (sub (add vZL vI) (V 22))));
   ((add vZL vI)); (add vX (mul 8 (sub (add vZL vI) (V 22)))); (vS2); (vS3); (vS4); (vS5); (vS6); (vS7);
   (vS8); (vS9); (vS10); (vS11); (ELit (-8)); (add (add vX8 (ELit 2147450880)) (sub (add vZL vI) (V 22))); (ELit 1); (V 23)].
Definition RZ_kn : list kentry :=
  [KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 22)))) 0 488;
   KRange (V 22) 1 62;
   KRange (sub (add vZL vI) (V 22)) 0 61;
   KRange (add vZL vI) 1 62;
   KRange (sub (sub (add vZL vI) (V 22)) vLX) 0 61;
   KWord (SA vX 496) 2 vLX;
   KRange vLX 0 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898420816 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-80)) (ELit 80);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KRange vY8 0xce200 0xfffffefffff;
   KRange (add vY (mul 8 vZL)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vY 0) (mul 8 vZL);
   KUnk (SA vY 0) (mul 8 vZL);
   KZero (SA vY8 2147450880) vZL;
   KDisj (SA vSP (-80)) (ELit 80) (SA vX 0) (ELit 504);
   KDisj (SA vSP (-80)) (ELit 80) (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 504);
   KRange vZL 0 62;
   KRange vI 1 4;
   KRange vLX 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vZ 0 55;
   KRange (sub (add vZ (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vZ (add vI (ELit 1))) vLX) 0 66].
Definition RZ : ST.tmpl := ST.TM 0xd1f48 RZ_regs RZ_kn 24%nat (add (ELit 3072) (V 22)) 0%nat.

(* [comment removed for export] *)
Definition ML_regs : list expr :=
  [ELit 0; (vRA); (spo (-80)); (vGP); (vTP); (add vX8 (ELit 2147450942)); (ELit 2147450880); (sub (ELit (-1)) vX);
   (add vX (mul 8 vI)); (ELit 1); (add vX (ELit 496)); (vY); (vZL); (vI); (vX); (ELit 1);
   (V 25); (V 26); ((V 23)); (V 27); (V 28); (V 29); (V 30); (V 31);
   (vS8); (vS9); (vS10); (vS11); (mul 8 (sub vZL (V 23))); ((V 24)); (mul 8 vI); (add (mul 8 vI) (ELit (-504)))].
Definition ML_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (add (mul 8 vZL) (add (mul 8 vI) (mul (-8) (V 23)))) 8 488;
   KRange (V 23) 1 62;
   KRange (sub vZL (V 23)) 0 61;
   KRange (sub (add vZL vI) (V 23)) 1 61;
   KRange (V 24) 0 1;
   KRange (sub (V 22) (add vZL vI)) 0 62;
   KRange (add vZL vI) 1 62;
   KWord (SA vX 496) 2 (V 22);
   KRange (V 22) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898420816 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-80)) (ELit 80);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KRange vY8 0xce200 0xfffffefffff;
   KRange (add vY (mul 8 vZL)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vY 0) (mul 8 vZL);
   KUnk (SA vY 0) (mul 8 vZL);
   KZero (SA vY8 2147450880) vZL;
   KDisj (SA vSP (-80)) (ELit 80) (SA vX 0) (ELit 504);
   KDisj (SA vSP (-80)) (ELit 80) (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 504);
   KRange vZL 0 62;
   KRange vI 1 4;
   KRange vLX 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vZ 0 55;
   KRange (sub (add vZ (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vZ (add vI (ELit 1))) vLX) 0 66;
   KRange (sub (add vZ (add vI (ELit 1))) (V 22)) 0 66].
Definition ML : ST.tmpl := ST.TM 0xd1fb4 ML_regs ML_kn 32%nat (add (ELit 2048) (V 23)) 0%nat.

(* [comment removed for export] *)
Definition CL_regs : list expr :=
  [ELit 0; (vRA); (spo (-80)); (vGP); (vTP); (add vX8 (ELit 2147450942)); (ELit 2147450880); (sub (ELit (-1)) vX);
   (V 24); (V 25); (add vX (ELit 496)); (V 26); (mul 8 (V 23)); (add (V 23) (ELit (-64))); (vX); (ELit 1);
   ((V 22)); (sub (V 22) (V 23)); (V 27); (V 28); (V 29); (V 30); (V 31); (V 32);
   (vS8); (vS9); (vS10); (vS11); (V 33); (V 34); (V 35); (V 36)].
Definition CL_kn : list kentry :=
  [KRange (V 22) 1 61;
   KRange (mul 8 (V 23)) 8 488;
   KRange (V 23) 1 61;
   KRange (sub (V 22) (V 23)) 1 61;
   KWord (SA vX 496) 2 (V 22);
   KRange (V 22) 1 62;
   KWord (SA vSP (-8)) 8 vRA;
   KWord (SA vSP (-16)) 8 vS0;
   KWord (SA vSP (-24)) 8 vS1;
   KWord (SA vSP (-32)) 8 vS2;
   KWord (SA vSP (-40)) 8 vS3;
   KWord (SA vSP (-48)) 8 vS4;
   KWord (SA vSP (-56)) 8 vS5;
   KWord (SA vSP (-64)) 8 vS6;
   KWord (SA vSP (-72)) 8 vS7;
   KRange vSP 140728898420816 0x800000000000;
   KAlign vSP 16;
   KWr (SA vSP (-80)) (ELit 80);
   KRange vX8 0xce204 0xfffffeffff7;
   KRange (add vX (ELit 504)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vX 0) (ELit 504);
   KWr (SA vX 0) (ELit 498);
   KUnk (SA vX 0) (ELit 498);
   KZero (SA vX8 2147450880) (ELit 63);
   KRange vY8 0xce200 0xfffffefffff;
   KRange (add vY (mul 8 vZL)) 0x671000 0x7fffff800000;
   KDisj (SA (ELit 0) 0x7fff7000) (ELit 0x100000001000) (SA vY 0) (mul 8 vZL);
   KUnk (SA vY 0) (mul 8 vZL);
   KZero (SA vY8 2147450880) vZL;
   KDisj (SA vSP (-80)) (ELit 80) (SA vX 0) (ELit 504);
   KDisj (SA vSP (-80)) (ELit 80) (SA vY 0) (mul 8 vZL);
   KDisj (SA vY 0) (mul 8 vZL) (SA vX 0) (ELit 504);
   KRange vZL 0 62;
   KRange vI 1 4;
   KRange vLX 0 62;
   KImg 0x10000 0x429e4;
   KZero (SA (ELit 0) 2147471376) (ELit 1324);
   KZero (SA (ELit 0) 2147472704) (ELit 80);
   KWord (SA (ELit 0) 0x112a80) 8 (ELit 0x11b678);
   KWord (SA (ELit 0) 0x11b678) 8 (ELit 2147450880);
   KWord (SA (ELit 0) 0x112ad8) 8 (ELit 0x11b680);
   KWord (SA (ELit 0) 0x11b680) 4 (ELit 1);
   KRange vZ 0 55;
   KRange (sub (add vZ (ELit 1)) vZL) 0 62;
   KRange (add vZL vI) 1 61;
   KRange vLX 0 61;
   KRange (sub (add vZ (add vI (ELit 1))) vLX) 0 66;
   KRange (sub (add vZ (add vI (ELit 1))) (V 22)) 0 66].
Definition CL : ST.tmpl := ST.TM 0xd2094 CL_regs CL_kn 37%nat (add (ELit 1024) (sub (V 22) (V 23))) 0%nat.

(* [comment removed for export] *)
Definition XR_regs : list expr :=
  [ELit 0; vRA; vSP; vGP; vTP; (V 24); (V 25); (V 26);
   vS0; vS1; ((V 23)); (V 27); (V 28); (V 29); (V 30); (V 31);
   (V 32); (V 33); vS2; vS3; vS4; vS5; vS6; vS7;
   vS8; vS9; vS10; vS11; (V 34); (V 35); (V 36); (V 37)].
Definition XR_kn : list kentry :=
  [KRange (V 23) 1 1;
   KRange (sub (add vZ (add vI (ELit 2))) (V 22)) 0 67;
   KWord (SA vX 496) 2 (V 22);
   KRange (V 22) 0 62].
Definition XR : ST.tmpl := ST.TM 0xd214c XR_regs XR_kn 38%nat (ELit 0) 0%nat.

Definition LADBN : SP.prog := SP.PGCA 22 [T0; RS; RZ; ML; CL] [XR] [(vSP, -80, ELit 80); (vX, 0, ELit 498)] [] [] [(vSP, -80, ELit 80); (vX, 0, ELit 504); (vX8, 2147450880, ELit 63); (vY, 0, mul 8 vZL); (vY8, 2147450880, vZL); (ELit 0, 0x10000, ELit 0x661000); (ELit 0, 163968, ELit 10592); (ELit 0, 174592, ELit 640); (ELit 0, 2147471376, ELit 1324); (ELit 0, 2147472704, ELit 80); (ELit 0, 0x112a80, ELit 8); (ELit 0, 0x11b678, ELit 8); (ELit 0, 0x112ad8, ELit 8); (ELit 0, 0x11b680, ELit 4)].
