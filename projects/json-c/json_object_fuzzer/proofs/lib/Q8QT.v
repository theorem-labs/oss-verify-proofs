(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl QQLG Q91D QZAa Lib.CodeAt Lib.StepGen Lib.StepGenSF Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.
Import QQLG.Mq0.
Import Q91D.Mq0.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.

Import QZAa.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSF OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base addtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1996.

Hypothesis fe_getround_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_getround_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).
Hypothesis fe_raise_inexact_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq0.fe_raise_inexact_spec segs (base + 1996)%Z 0%Z 0%Z) 3%nat in let T := gw_fold_pcs T base (1996)%Z [0; 48]%Z in exact T).

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

Definition addtf3_post := Eval cbv beta delta [Q91D.Mq0.addtf3_post] in (Q91D.Mq0.addtf3_post segs).
Definition add_Lsub := Q91D.Mq0.add_Lsub segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Definition add_Ladd := Q91D.Mq0.add_Ladd segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Section Proofs.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
Hypothesis FRM : frm0 fc.
Hypothesis MI : mem_inv segs m1.
Hypothesis FR : rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Hypothesis STK : stk segs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
Hypothesis WM : wmono segs m m1.
Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
(MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (Z_to_bv 64 pc) fcx None m1 (seg_rom segs)).

Lemma add_L5a4 : forall x1 x8 x9 x18 x19 x20 x30 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 align d2 mask2 sticky newLo r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= bSigHi3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d2 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
(if 9223372036854775808 <=? d2 then 18446744073709551615 else 0)%Z = mask2 ->
r = align_4 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 align mask2 sticky newLo ->
evt segs (POST r) (ST (base + 0x58c) fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 sticky) x8 x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
x18 x19 x20 (Z_to_bv 64 newLo) (Z_to_bv 64 d2) x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 Hm HR. subst r. unfold align_4.
assert (Rm : (0 <= mask2 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
zstep. name_as_by srH (Z.shiftr bSigHi3 (Z.land align 63))
(change (inr64 (Z.shiftr bSigHi3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. rewrite (srai63_word d2), Hm by lia.
zstep. name_reg 16%Z newHi.
zstep. name_reg 7%Z BLo.
zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64).
zstep. name_reg 10%Z AHi.
unfold add_M6, addsub_mirror. unfold_sfw.
zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
-  eapply add_Lsub; finL.
- eapply add_Ladd; finL.
Qed.

Lemma add_L564 : forall x1 x8 x9 x18 x19 x20 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 bSigLo3 align d1 mask1 negal outHi r : Z),
(0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
(0 <= bSigHi3 < 2^64)%Z -> (0 <= bSigLo3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d1 < 2^64)%Z -> (0 <= negal < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
(if 9223372036854775808 <=? d1 then 18446744073709551615 else 0)%Z = mask1 ->
r = align_3 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 bSigLo3 align mask1 negal outHi ->
evt segs (POST r) (ST (base + 0x54c) fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 d1) x8 x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
x18 x19 x20 (Z_to_bv 64 bSigLo3) (Z_to_bv 64 negal) (Z_to_bv 64 outHi) x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold align_3. unfold_sfw. rewrite ?b2z_Zb2z.
assert (Rm : (0 <= mask1 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
zstep. model_reg 29%Z outLoRaw (Z.land (Z.shiftl bSigLo3 (Z.land negal 63)) W64).
zstep. rewrite (srai63_word d1), Hm by lia.
zstep. name_reg 7%Z outLo.
zstep. zstep. name_reg 31%Z n2.
zstep. name_reg 7%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
zstep. model_reg 29%Z d2 (Z.land (n2 - 64) W64).
zstep. name_reg 7%Z sticky.
zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
-
zstep. name_as_by srL (Z.shiftr bSigLo3 (Z.land align 63))
(change (inr64 (Z.shiftr bSigLo3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
do 4 zstep. name_reg 28%Z newLo.
eapply add_L5a4 with (mask2 := 18446744073709551615%Z); finL.
- zstep. name_as_by newLo (Z.shiftr bSigHi3 (Z.land n2 63))
(change (inr64 (Z.shiftr bSigHi3 (Z.land n2 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. eapply add_L5a4 with (mask2 := 0%Z); finL.
Qed.

Lemma add_LM4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp r : Z),
(0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
(0 <= aExp < 2^64)%Z -> (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
r = add_M4 aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp ->
evt segs (POST r) (ST (base + 0x3a8) fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
(Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M4. unfold align_mirror. unfold_sfw.
zstep. name_reg 11%Z sw.
do 6 zstep. name_reg 17%Z aSigHi3.
zstep. zstep. model_reg 28%Z bSigLo3 (Z.land (Z.shiftl bSigLo 3) W64).
zstep. zstep. name_reg 16%Z bSigHi3.
zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
-
zstep. model_reg 5%Z align (Z.land (aExp - bExp) W64).
zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
+
zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
unfold add_M6, addsub_mirror. unfold_sfw.
zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
* eapply add_Ladd; finL.
* eapply add_Lsub; finL.
+
do 4 zstep. rewrite (landM32_swrap_land64 (128 - align)). name_reg 30%Z n1.
zstep. model_reg 7%Z d1 (Z.land (n1 - 64) W64).
zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - align)).
name_as_by negal (sext32 (0 - align)) (apply sext32_range).
zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
*
zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))
(change (inr64 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
zstep. name_reg 30%Z outHi.
eapply add_L564 with (mask1 := 18446744073709551615%Z); finL.
* zstep. model_reg 30%Z outHi (Z.land (Z.shiftl bSigLo3 (Z.land n1 63)) W64). zstep.
eapply add_L564 with (mask1 := 0%Z); finL.
-
zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
unfold add_M6, addsub_mirror. unfold_sfw.
zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
+ eapply add_Ladd; finL.
+ zstep. eapply add_Lsub; finL.
Qed.
End Proofs.

End G.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.SepCache QWxq_c1 QJjn QgoP Lib.StepGenX Lib.StepGenX2 Lib.GwApply Lib.GwFold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0.

Import QJjn.
Import QgoP.
Import Q91D.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition strtolblk_code (w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 : Z) : list Z :=
[0xee010113; 0x10113c23; 0x10813823; 0x10913423; 0x11213023; 0x0f313c23; 0x00060913; 0x00058413; 0x00050493; w_9; w_10; 0x0009b503; 0x0ea13823; 0xfff00513; 0x06913023; 0x00913823; 0x00a13c23; 0x00810513; 0x00000593; w_19; 0x00810513; 0x00100613; 0xfff00693; 0x00090593; w_24; 0x02040063; 0x01013583; 0x06013603; 0x0d013683; 0x40c585b3; 0x00d486b3; 0x00b685b3; 0x00b43023; 0x0009b583; 0x0f013603; 0x02c59063; 0x11813083; 0x11013403; 0x10813483; 0x10013903; 0x0f813983; 0x12010113; 0x00008067; w_43; 0xee010113; 0x10113c23; 0x10813823; 0x10913423; 0x11213023; 0x0f313c23; 0x0f413823; 0x00060913; 0x00058413; 0x00050493; w_54; w_55; 0x0009b503; 0x0ea13423; 0xfff00a13; 0x04913c23; 0x00913423; 0x01413823; 0x00010513; 0x00000593; w_64; 0x03fa1693; 0x00010513; 0x00100613; 0x00090593; w_69; 0x02040063; 0x00813583; 0x05813603; 0x0c813683; 0x40c585b3; 0x00d486b3; 0x00b685b3; 0x00b43023; 0x0009b583; 0x0e813603; 0x02c59263; 0x11813083; 0x11013403; 0x10813483; 0x10013903; 0x0f813983; 0x0f013a03; 0x12010113; 0x00008067; w_89]%Z.

Definition shlim_code : list Z :=
[0x00853683; 0x01053603; 0x05853703; 0x00b037b3; 0x40d60833; 0x0105a833; 0x0107f7b3; 0x40d70733; 0x0cb53023; 0x0ce53423; 0x00078463; 0x00b68633; 0x0ac53c23; 0x00008067]%Z.

Fixpoint ex_cells (sizes : list nat) (k : list cell -> Prop) : Prop :=
match sizes with
| [] => k []
| s :: r => exists q : list byte, ex_cells r (fun cs => k (CB s q :: cs))
end.

Lemma ex_cells_mono : forall sizes (k k' : list cell -> Prop),
(forall cs, k cs -> k' cs) -> ex_cells sizes k -> ex_cells sizes k'.
Proof.
induction sizes as [|s r IH]; intros k k' Hk H; cbn in *.
- apply Hk. exact H.
- destruct H as [q H]. exists q. eapply IH; [|exact H]. intros cs Hcs. apply Hk. exact Hcs.
Qed.

Lemma rw_cells_CB_sizes : forall segs_ m sizes A n junk,
rw_cells segs_ m A [CB n junk] -> sum_nat sizes = n ->
ex_cells sizes (fun cs => rw_cells segs_ m A cs).
Proof.
intros segs_ m sizes. induction sizes as [|s r IH]; intros A n junk H Hs; cbn in Hs.
- cbn. subst n. exact (proj1 (proj1 (rw_cells_app segs_ m A [] [CB 0%nat junk]) H)).
- cbn. destruct (rw_cells_CB_cut segs_ m A n junk s H ltac:(lia)) as [H1 H2].
exists (firstn s junk).
eapply ex_cells_mono; [| eapply (IH _ _ _ H2); lia].
intros cs Hcs. cbn beta in Hcs.
change (CB s (firstn s junk) :: cs) with ([CB s (firstn s junk)] ++ cs).
apply (proj2 (rw_cells_app segs_ m A _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact Hcs.
Qed.

Lemma le8_read : forall segs_ m a v, bytes_at segs_ m a (le8 v) -> ov_read_bytes segs_ m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
intros segs_ m a v H.
pose proof (bytes_at_read segs_ m a (le8 v) 0 8 H ltac:(lia) ltac:(pose proof (length_le8 v); cbn; lia)) as R.
cbv beta iota delta [Z.to_nat skipn] in R.
replace (firstn 8 (le8 v)) with (le8 v) in R. 2:{ symmetry. apply firstn_all2. rewrite length_le8. lia. }
unfold wa in R. rewrite Z.add_0_r in R. exact R.
Qed.

Ltac show_goal := match goal with |- evt _ _ ?ms => idtac "STATE" ms | |- ?g => idtac "GOAL" g end.
Ltac show_fr := match goal with H : rw_cells _ _ (bv_unsigned ?sp + -288)%Z ?c |- _ => idtac "FR" c end.
Ltac lit_store_fix :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)) end;
mem_after_store.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 : Z).
Variables (hi_9 hi_54 : bv 20).
Variables (lo_10 lo_55 : bv 12).
Variables (joff_19 joff_24 joff_64 joff_69 : bv 21).
Variables (GOT_GUARD GUARD ISTAB RATP RGLOBALS_TOP : Z).
Variables (e_errno_loc e_shlim e_intscan : Z).
Hypothesis CODE : code_at segs base (strtolblk_code w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 360.
Hypothesis D_9 : decode_any (Z_to_bv 32 w_9) = Some (Auipc 10 hi_9, 4%Z).
Hypothesis E_9 : is_ecall (Z_to_bv 32 w_9) = false.
Hypothesis D_10 : decode_any (Z_to_bv 32 w_10) = Some (Load SZ8 true 19 10 lo_10, 4%Z).
Hypothesis E_10 : is_ecall (Z_to_bv 32 w_10) = false.
Hypothesis D_19 : decode_any (Z_to_bv 32 w_19) = Some (Jal 1 joff_19, 4%Z).
Hypothesis E_19 : is_ecall (Z_to_bv 32 w_19) = false.
Hypothesis D_24 : decode_any (Z_to_bv 32 w_24) = Some (Jal 1 joff_24, 4%Z).
Hypothesis E_24 : is_ecall (Z_to_bv 32 w_24) = false.
Hypothesis D_54 : decode_any (Z_to_bv 32 w_54) = Some (Auipc 10 hi_54, 4%Z).
Hypothesis E_54 : is_ecall (Z_to_bv 32 w_54) = false.
Hypothesis D_55 : decode_any (Z_to_bv 32 w_55) = Some (Load SZ8 true 19 10 lo_55, 4%Z).
Hypothesis E_55 : is_ecall (Z_to_bv 32 w_55) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Jal 1 joff_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis D_69 : decode_any (Z_to_bv 32 w_69) = Some (Jal 1 joff_69, 4%Z).
Hypothesis E_69 : is_ecall (Z_to_bv 32 w_69) = false.
Hypothesis ANCH_10 : gw_anch (Z.shiftl (bv_signed hi_9) 12 + (base + 36) + bv_signed lo_10)%Z GOT_GUARD.
Hypothesis ANCH_55 : gw_anch (Z.shiftl (bv_signed hi_54) 12 + (base + 216) + bv_signed lo_55)%Z GOT_GUARD.
Hypothesis LINK_19 : gw_anch (base + 76 + bv_signed joff_19)%Z (e_shlim + 0)%Z.
Hypothesis LINK_24 : gw_anch (base + 96 + bv_signed joff_24)%Z (e_intscan + 0)%Z.
Hypothesis LINK_64 : gw_anch (base + 256 + bv_signed joff_64)%Z (e_shlim + 0)%Z.
Hypothesis LINK_69 : gw_anch (base + 276 + bv_signed joff_69)%Z (e_intscan + 0)%Z.
Hypothesis CODE_e_shlim : code_at segs e_shlim shlim_code.
Hypothesis AL_e_shlim_b4 : gw_b4 e_shlim.
Hypothesis RNG_e_shlim_code : gw_br e_shlim 56.
Hypothesis RNG_ISTAB : gw_br ISTAB 8.
Hypothesis LAY_lo_ISTAB : gw_le 65536 ISTAB.
Hypothesis RNG_GOT_GUARD : gw_br GOT_GUARD 8.
Hypothesis RNG_RATP : gw_br RATP 8.
Hypothesis LAY_lo_RATP : gw_le 65536 RATP.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_GUARD : gw_br GUARD 8.
Hypothesis LAY_lo_GUARD : gw_le 65536 GUARD.
Hypothesis RNG_RGLOBALS_TOP : gw_br RGLOBALS_TOP 8.
Hypothesis LAY_lo_RGLOBALS_TOP : gw_le 65536 RGLOBALS_TOP.
Hypothesis AL_RGLOBALS_TOP : gw_al RGLOBALS_TOP 8.
Hypothesis LAY_GOT_GUARD_RATP : gw_le (GOT_GUARD + 8) RATP.
Hypothesis LAY_RATP_GUARD : gw_le (RATP + 8) GUARD.
Hypothesis LAY_GUARD_RGLOBALS_TOP : gw_le (GUARD + 8) RGLOBALS_TOP.

Local Definition gw_tbl_0 := tt.

Definition intscan_W : ltac:(gw_rebind_ty (@Q91D.Mq1.intscan_W RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q91D.Mq1.intscan_W RATP) constr:(gw_tbl_0)).
Local Definition gw_tbl_1 := (gw_ent (@Q91D.Mq1.intscan_W RATP) intscan_W gw_tbl_0).
Definition intscan_post : ltac:(gw_rebind_ty (@Q91D.Mq1.intscan_post segs RATP) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q91D.Mq1.intscan_post segs RATP) constr:(gw_tbl_1)).
Local Definition gw_tbl_2 := (gw_ent (@Q91D.Mq1.intscan_post segs RATP) intscan_post gw_tbl_1).
Definition intscan_stmt : ltac:(gw_rebind_ty (@Q91D.Mq1.intscan_stmt segs e_intscan RATP RGLOBALS_TOP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q91D.Mq1.intscan_stmt segs e_intscan RATP RGLOBALS_TOP) constr:(gw_tbl_2)).
Local Definition gw_tbl_3 := (gw_ent (@Q91D.Mq1.intscan_stmt segs e_intscan RATP RGLOBALS_TOP) intscan_stmt gw_tbl_2).

Hypothesis intscan_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq1.gw_all) (@Q91D.Mq1.intscan_spec) e_intscan)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_3))) in exact T).
#[using="GOT_GUARD GUARD ISTAB RATP RGLOBALS_TOP e_errno_loc e_shlim e_intscan CODE BASE4 BASER D_9 E_9 D_10 E_10 D_19 E_19 D_24 E_24 D_54 E_54 D_55 E_55 D_64 E_64 D_69 E_69 ANCH_10 ANCH_55 LINK_19 LINK_24 LINK_64 LINK_69 CODE_e_shlim AL_e_shlim_b4 RNG_e_shlim_code RNG_ISTAB LAY_lo_ISTAB RNG_GOT_GUARD RNG_RATP LAY_lo_RATP AL_RATP RNG_GUARD LAY_lo_GUARD RNG_RGLOBALS_TOP LAY_lo_RGLOBALS_TOP AL_RGLOBALS_TOP LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := clear - hs segs base w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_9 hi_54 lo_10 lo_55 joff_19 joff_24 joff_64 joff_69 GOT_GUARD GUARD ISTAB RATP RGLOBALS_TOP e_errno_loc e_shlim e_intscan CODE BASE4 BASER D_9 E_9 D_10 E_10 D_19 E_19 D_24 E_24 D_54 E_54 D_55 E_55 D_64 E_64 D_69 E_69 ANCH_10 ANCH_55 LINK_19 LINK_24 LINK_64 LINK_69 CODE_e_shlim AL_e_shlim_b4 RNG_e_shlim_code RNG_ISTAB LAY_lo_ISTAB RNG_GOT_GUARD RNG_RATP LAY_lo_RATP AL_RATP RNG_GUARD LAY_lo_GUARD RNG_RGLOBALS_TOP LAY_lo_RGLOBALS_TOP AL_RGLOBALS_TOP LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec.

Definition strtoull_entry := (base + 0x0)%Z.
Definition strtoll_entry := (base + 0xb0)%Z.

Definition strtox_W (SP E : Z) : list ivl :=
[(SP - 368, SP); (E, E + 8); (RATP - 164, RATP - 160)]%Z.

Definition strtox_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(SP A E lo : Z) (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x5 x6 x7 a0' a1' a2' a3' a4' a5' a6' a7' x28 x29 x30 x31 m' (j : Z) (e' : word),
ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch (strtox_W SP E) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' E [C8 (Z_to_bv 64 (A + j))] /\ (0 <= j <= Z.of_nat (length str))%Z
/\ bytes_at segs m' A (str ++ [b0])
/\ rw_cells segs m' (RATP - 164) [C4 e']
/\ stk segs m' lo SP.

Definition strtox_stmt (entry : Z) : Prop :=
forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (str : list byte) (SP A E lo : Z) (e g ej : word),
bv_unsigned sp = SP -> bv_unsigned a0 = A -> bv_unsigned a1 = E -> a2 = Z_to_bv 64 10 ->
bytes_at segs m A (str ++ [b0]) -> ~ In b0 str -> (A + Z.of_nat (length str) + 2 <= 2^64)%Z ->
rw_cells segs m E [C8 ej] ->
rw_cells segs m (RATP - 164) [C4 e] -> tp = Z_to_bv 64 RATP ->
bytes_at segs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at segs m GUARD (le8 g) ->
stk segs m lo SP -> (RGLOBALS_TOP <= lo)%Z -> (lo <= SP - 368)%Z ->
(RGLOBALS_TOP <= E)%Z ->
(E + 8 <= SP - 368 \/ SP <= E)%Z ->
(A + Z.of_nat (length str) + 1 <= SP - 368 \/ SP <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= E \/ E + 8 <= A)%Z ->
(A + Z.of_nat (length str) + 1 <= RATP - 164 \/ RATP - 160 <= A)%Z ->
mem_inv segs m ->
evt segs (strtox_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SP A E lo str m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)).

#[using="w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_9 lo_10 joff_19 joff_24 e_shlim e_intscan CODE BASE4 BASER D_9 E_9 D_10 E_10 D_19 E_19 D_24 E_24 ANCH_10 LINK_19 LINK_24 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec"] Lemma strtoull_spec : strtox_stmt strtoull_entry.
Proof. clear - w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_9 lo_10 joff_19 joff_24 e_shlim e_intscan CODE BASE4 BASER D_9 E_9 D_10 E_10 D_19 E_19 D_24 E_24 ANCH_10 LINK_19 LINK_24 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec.
unfold strtox_stmt, strtoull_entry. intros until ej. intros HSP HA HE Ha2 STR NONUL AB EP ERR TP GOTF GF ST LO LOS ELO SEP1 SEP2 SEP3 SEP4 MI.
subst SP a2.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
pose proof (rw_cells_bound _ _ _ _ EP) as EB. cbn [cells_size csize Nat.add] in EB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (munch_refl (strtox_W (bv_unsigned sp) E) m) as MU. pose proof (wmono_refl segs m) as WM.
unfold strtox_W in MU. gw_expose GOT_GUARD; gw_expose GUARD.

replace a0 with (Z_to_bv 64 A) by (rewrite <- HA; apply Z_to_bv_bv_unsigned).
replace a1 with (Z_to_bv 64 E) by (rewrite <- HE; apply Z_to_bv_bv_unsigned).
clear HA HE.
carve_frame 288%nat ST.
destruct (rw_cells_CB_sizes segs m [8;8;8;8;64;8;88;8;8;8;24;8;8;8;8;8;8]%nat _ _ _ FR eq_refl)
as (q0 & j0 & q1 & q2 & j1 & q3 & j2 & q4 & q5 & q6 & j3 & q7 & q8 & q9 & q10 & q11 & q12 & FR'). clear FR. rename FR' into FR.

do 9 zstep.

zstep. pose proof (le8_read segs _ _ _ GOTF) as RD1. zstep. clear RD1.
pose proof (le8_read segs _ _ _ GF) as RD2. zstep. clear RD2.
zstep.

zstep. zstep. zstep. zstep. lit_store_fix.
zstep. zstep. zstep.

do 8 zstep. zstep. lit_store_fix. zstep. zstep. if_true. zstep. lit_store_fix. zstep.
zstep. zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

replace (A - A)%Z with 0%Z in FR by lia.
apply (proj1 (rw_cells_app segs _ _ [CB 8 q0] _)) in FR. destruct FR as [FR0 FR]. cbn [cells_size csize Nat.add] in FR.
replace (bv_unsigned sp + -288 + Z.of_nat 8)%Z with (bv_unsigned sp + -280)%Z in FR by lia.
apply (proj1 (rw_cells_app segs _ _ (file_cells j0 j1 j2 j3 A A 0) _)) in FR.
destruct FR as [FILE FRS]. unfold file_cells in FRS. cbn [cells_size csize Nat.add] in FRS.
replace (bv_unsigned sp + -280 + Z.of_nat 232)%Z with (bv_unsigned sp + -48)%Z in FRS by lia.

lazymatch goal with |- evt ?segs_ _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply (gw_unhyp intscan_spec) with (SP := (bv_unsigned sp + -288)%Z) (F0 := (bv_unsigned sp + -280)%Z)
(A := A) (lo := lo) (str := str)
| unfold intscan_post, intscan_W; post_call segs_ mm ] end.
1:{ reflexivity. } 1:{ reflexivity. }
1:{ apply unsigned_lit. lia. } 1:{ apply unsigned_lit. lia. }
1:{ exact FILE. } 1:{ exact STR. } 1:{ exact NONUL. } 1:{ lia. } 1:{ exact ERR. } 1:{ exact TP. }
1:{ exact ST. }
1-7: lia.
1:{ assumption. }

zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 ELO w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_9 lo_10 joff_19 joff_24 e_shlim e_intscan CODE BASE4 BASER D_9 E_9 D_10 E_10 D_19 E_19 D_24 E_24 ANCH_10 LINK_19 LINK_24 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec. lia. }
rename PC into FILE. unfold file_cells in FILE.
do 7 zstep.

pose proof (le8_read segs _ _ _ GF) as RD2. zstep. clear RD2. zstep. zstep. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }

do 6 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (FR : rw_cells segs m2 (bv_unsigned sp + -288) ([CB 8%nat q0] ++ file_cells j0 j1 j2 j3 (A + x15) A x16 ++ [C8 g; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ apply (proj2 (rw_cells_app segs m2 _ _ _)). split; [exact FR0|]. cbn [cells_size csize Nat.add].
replace (bv_unsigned sp + -288 + Z.of_nat 8)%Z with (bv_unsigned sp + -280)%Z by lia.
apply (proj2 (rw_cells_app segs m2 _ _ _)). split; [exact FILE|]. unfold file_cells. cbn [cells_size csize Nat.add].
replace (bv_unsigned sp + -280 + Z.of_nat 232)%Z with (bv_unsigned sp + -48)%Z by lia. exact FRS. }
clear FR0 FILE FRS. unfold file_cells in FR. cbn [app] in FR. rename POST into ST.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (A + x16 + (A + x15 - A))%Z with (A + (x16 + x15))%Z in EP by lia.
finish. 1: exact EP. 3: exact PC3. all: lia.
Qed.

#[using="w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_54 lo_55 joff_64 joff_69 e_shlim e_intscan CODE BASE4 BASER D_54 E_54 D_55 E_55 D_64 E_64 D_69 E_69 ANCH_55 LINK_64 LINK_69 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec"] Lemma strtoll_spec : strtox_stmt strtoll_entry.
Proof. clear - w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_54 lo_55 joff_64 joff_69 e_shlim e_intscan CODE BASE4 BASER D_54 E_54 D_55 E_55 D_64 E_64 D_69 E_69 ANCH_55 LINK_64 LINK_69 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec.
unfold strtox_stmt, strtoll_entry. intros until ej. intros HSP HA HE Ha2 STR NONUL AB EP ERR TP GOTF GF ST LO LOS ELO SEP1 SEP2 SEP3 SEP4 MI.
subst SP a2.
pose proof (bytes_at_bound _ _ _ _ STR) as SB. rewrite length_app in SB. cbn [length] in SB.
pose proof (rw_cells_bound _ _ _ _ EP) as EB. cbn [cells_size csize Nat.add] in EB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof (munch_refl (strtox_W (bv_unsigned sp) E) m) as MU. pose proof (wmono_refl segs m) as WM.
unfold strtox_W in MU. gw_expose GOT_GUARD; gw_expose GUARD.
replace a0 with (Z_to_bv 64 A) by (rewrite <- HA; apply Z_to_bv_bv_unsigned).
replace a1 with (Z_to_bv 64 E) by (rewrite <- HE; apply Z_to_bv_bv_unsigned).
clear HA HE.
carve_frame 288%nat ST.
destruct (rw_cells_CB_sizes segs m [8;8;8;64;8;88;8;8;8;24;8;8;8;8;8;8;8]%nat _ _ _ FR eq_refl)
as (j0 & q1 & q2 & j1 & q3 & j2 & q4 & q5 & q6 & j3 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & FR'). clear FR. rename FR' into FR.

do 10 zstep.

zstep. pose proof (le8_read segs _ _ _ GOTF) as RD1. zstep. clear RD1.
pose proof (le8_read segs _ _ _ GF) as RD2. zstep. clear RD2.
zstep.

zstep. zstep. zstep. zstep. lit_store_fix.
zstep. zstep. zstep.

do 8 zstep. zstep. lit_store_fix. zstep. zstep. if_true. zstep. lit_store_fix. zstep.
zstep. zstep. zstep. zstep. zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.

replace (A - A)%Z with 0%Z in FR by lia.
apply (proj1 (rw_cells_app segs _ _ (file_cells j0 j1 j2 j3 A A 0) _)) in FR.
destruct FR as [FILE FRS]. unfold file_cells in FRS. cbn [cells_size csize Nat.add] in FRS.
replace (bv_unsigned sp + -288 + Z.of_nat 232)%Z with (bv_unsigned sp + -56)%Z in FRS by lia.

lazymatch goal with |- evt ?segs_ _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply (gw_unhyp intscan_spec) with (SP := (bv_unsigned sp + -288)%Z) (F0 := (bv_unsigned sp + -288)%Z)
(A := A) (lo := lo) (str := str)
| unfold intscan_post, intscan_W; post_call segs_ mm ] end.
1:{ reflexivity. } 1:{ reflexivity. }
1:{ apply unsigned_lit. lia. } 1:{ apply unsigned_lit. lia. }
1:{ exact FILE. } 1:{ exact STR. } 1:{ exact NONUL. } 1:{ lia. } 1:{ exact ERR. } 1:{ exact TP. }
1:{ exact ST. }
1-7: lia.
1:{ assumption. }

zstep. if_cases K0; zify_cond K0. { exfalso. clear - K0 ELO w_9 w_10 w_19 w_24 w_43 w_54 w_55 w_64 w_69 w_89 hi_54 lo_55 joff_64 joff_69 e_shlim e_intscan CODE BASE4 BASER D_54 E_54 D_55 E_55 D_64 E_64 D_69 E_69 ANCH_55 LINK_64 LINK_69 CODE_e_shlim RNG_GOT_GUARD RNG_GUARD LAY_lo_GUARD LAY_GOT_GUARD_RATP LAY_RATP_GUARD LAY_GUARD_RGLOBALS_TOP intscan_spec. lia. }
rename PC into FILE. unfold file_cells in FILE.
do 7 zstep.

pose proof (le8_read segs _ _ _ GF) as RD2. zstep. clear RD2. zstep. zstep. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }

do 7 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
assert (FR : rw_cells segs m2 (bv_unsigned sp + -288) (file_cells j0 j1 j2 j3 (A + x15) A x16 ++ [C8 g; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])).
{ apply (proj2 (rw_cells_app segs m2 _ _ _)). split; [exact FILE|]. unfold file_cells. cbn [cells_size csize Nat.add].
replace (bv_unsigned sp + -288 + Z.of_nat 232)%Z with (bv_unsigned sp + -56)%Z by lia. exact FRS. }
clear FILE FRS. unfold file_cells in FR. cbn [app] in FR. rename POST into ST.
release_frame FR ST (bv_unsigned sp).
zstep.
replace (A + x16 + (A + x15 - A))%Z with (A + (x16 + x15))%Z in EP by lia.
finish. 1: exact EP. 3: exact PC3. all: lia.
Qed.

End G.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1 Qfw3_c1 Q5Rg Q9A7 Q6q3 G.GwFamMalloc Lib.StepGenSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QlEo_c1.Mq0 QWxq_c1.Mq1 Qfw3_c1.Mq2 Q5Rg.Mq0.

Import Q9A7.Mq0.
Import Q91D.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSys.
Local Ltac step_ecall ::= g_step_ecall. Local Ltac mkr__step_ecall_2 := g_step_ecall.
Local Ltac sys_nret ::= g_sys_nret. Local Ltac mkr__sys_nret_3 := g_sys_nret.
Local Ltac sys_nret_raw ::= g_sys_nret_raw. Local Ltac mkr__sys_nret_raw_4 := g_sys_nret_raw.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_5 segs m := g_post_call segs m.
Open Scope bv_scope.

Definition mm_code (w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 : Z) : list Z :=
[0x00008067; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x03479813; 0x00080863; w_11; 0x01600593; 0x0180006f; 0xfff00813; 0x00185813; 0x0305ec63; w_17; 0x00c00593; 0x00b52023; 0xfff00513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067; 0x0106f813; 0x00081663; 0xff400293; 0x03c0006f; 0x00068413; 0x00078993; 0x00050493; 0x00070a13; 0x00060913; 0x00058a93; 0xf61ff0ef; 0x000a8593; 0x00090613; 0x000a0713; 0x00048513; 0x00098793; 0x00040693; 0xfff00293; 0x0de00893; 0x00050813; 0x00000073; 0xfff54593; 0x00b865b3; 0x00059a63; 0x03a69313; 0x03f35513; 0xfff50513; 0x00556533; w_58; 0xf69ff06f; 0xff010113; 0x00113423; w_62; w_63; 0x00b505b3; 0x40d00733; 0x00d585b3; 0x00a77533; 0xfff58593; 0x00e5f5b3; 0x40a585b3; 0x0e200893; 0x00000073; w_73; 0x0005051b; 0x00813083; 0x01010113; 0x00008067; 0xfa010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; w_85; w_86; 0x04e13023; 0x04f13423; 0x05013823; 0x05113c23; 0x0004b703; 0xfff00413; 0x00145793; 0x00e13423; 0x00f66a63; w_96; 0x00c00593; 0x00b52023; 0x04c0006f; 0x0026f713; 0x02070a63; 0x00068413; 0x00060993; 0x00058913; 0x00050a13; 0xe59ff0ef; 0x000a0513; 0x00090593; 0x00098613; 0x00040693; 0x04810713; 0x00e13023; 0x04013703; 0x0d800893; 0x00000073; w_116; 0x00050413; 0x0004b503; 0x00813583; 0x02b51463; 0x00040513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x06010113; 0x00008067; w_130; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00058413; 0x00050493; 0xdddff0ef; 0x0d700893; 0x00048513; 0x00040593; 0x00000073; w_142; 0x0005051b; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067]%Z.

Definition sysret_code (w_sysret_7 : Z) : list Z :=
[0xfffff5b7; 0x0015859b; 0x02b56663; 0xff010113; 0x00113423; 0x00813023; 0x40a0043b; w_sysret_7; 0x00852023; 0xfff00513; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rsysret_entry : Z).
Variables (w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 : Z).
Variables (hi_62 hi_85 : bv 20).
Variables (lo_63 lo_86 : bv 12).
Variables (joff_11 joff_17 joff_58 joff_73 joff_96 joff_116 joff_130 joff_142 : bv 21).
Variables (e_197bc : Z).
Variables (w_sysret_7 : Z).
Hypothesis CODE : code_at segs base (mm_code w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 596.
Let rmmap_entry := (base + 4)%Z.
Let rmprotect_entry := (base + 240)%Z.
Let rmunmap_entry := (base + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (Jal 1 joff_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis D_58 : decode_any (Z_to_bv 32 w_58) = Some (Jal 1 joff_58, 4%Z).
Hypothesis E_58 : is_ecall (Z_to_bv 32 w_58) = false.
Hypothesis D_62 : decode_any (Z_to_bv 32 w_62) = Some (Auipc 13 hi_62, 4%Z).
Hypothesis E_62 : is_ecall (Z_to_bv 32 w_62) = false.
Hypothesis D_63 : decode_any (Z_to_bv 32 w_63) = Some (Load SZ8 true 13 13 lo_63, 4%Z).
Hypothesis E_63 : is_ecall (Z_to_bv 32 w_63) = false.
Hypothesis D_73 : decode_any (Z_to_bv 32 w_73) = Some (Jal 1 joff_73, 4%Z).
Hypothesis E_73 : is_ecall (Z_to_bv 32 w_73) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 5 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (Load SZ8 true 9 5 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (Jal 1 joff_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (Jal 1 joff_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_142 : decode_any (Z_to_bv 32 w_142) = Some (Jal 1 joff_142, 4%Z).
Hypothesis E_142 : is_ecall (Z_to_bv 32 w_142) = false.
Hypothesis ANCH_63 : gw_anch (Z.shiftl (bv_signed hi_62) 12 + (base + 248) + bv_signed lo_63)%Z (RATP + 131776).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z RGOT_SSP.
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_17 : gw_anch (base + 68 + bv_signed joff_17)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_58 : gw_anch (base + 232 + bv_signed joff_58)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_73 : gw_anch (base + 292 + bv_signed joff_73)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_96 : gw_anch (base + 384 + bv_signed joff_96)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_116 : gw_anch (base + 464 + bv_signed joff_116)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (e_197bc + 0)%Z.
Hypothesis LINK_142 : gw_anch (base + 568 + bv_signed joff_142)%Z (rsysret_entry + 0)%Z.
Hypothesis CODE_rsysret_entry : code_at segs rsysret_entry (sysret_code w_sysret_7).
Hypothesis AL_rsysret_entry_b4 : gw_b4 rsysret_entry.
Hypothesis RNG_rsysret_entry_code : gw_br rsysret_entry 56.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition sysret_post : ltac:(gw_rebind_ty (@Q91D.Mq7.sysret_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q91D.Mq7.sysret_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q91D.Mq7.sysret_post segs) (@sysret_post) gw_tbl_0).

Hypothesis sysret_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq7.gw_all) (@Q91D.Mq7.sysret_spec) rsysret_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in exact T).
#[using="RGOT_SSP rerrno_loc_entry e_197bc rsysret_entry RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_17 E_17 D_58 E_58 D_62 E_62 D_63 E_63 D_73 E_73 D_85 E_85 D_86 E_86 D_96 E_96 D_116 E_116 D_130 E_130 D_142 E_142 ANCH_63 ANCH_86 LINK_11 LINK_17 LINK_58 LINK_73 LINK_96 LINK_116 LINK_130 LINK_142 CODE_rsysret_entry AL_rsysret_entry_b4 RNG_rsysret_entry_code CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmmap_entry rmprotect_entry rmunmap_entry sysret_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Unset Keyed Unification.
Section RC__1.

Definition rmunmap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (match a with RgDone true => True | _ => wmono segs m m' end)
/\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ match a with RgErr e => e = 12%Z | _ => True end.

#[using="rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_142 CODE BASE4 BASER D_142 E_142 LINK_142 sysret_spec rmmap_entry rmprotect_entry rmunmap_entry"] Lemma rmunmap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L : Z) (errv : word) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L ->
(0 < A)%Z -> (A + mmap_len L <= 2^64)%Z -> (0 < L < 2^64)%Z ->
(lo <= bv_unsigned sp - 48)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl segs (at_node segs) (enode (NMunmap A L) (dec_munmap A L))
(epost (rmunmap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m (seg_rom segs)).
Proof. clear - rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_142 CODE BASE4 BASER D_142 E_142 LINK_142 sysret_spec rmmap_entry rmprotect_entry rmunmap_entry segs.
intros until lo. intros ST ERR MI -> -> A0 AL L0 LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (mmap_len_ge L) as ML.
unfold rmunmap_entry. apply impl_enode.
carve_frame 32%nat ST.
do 6 step.
step. step.
do 3 step.
step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_munmap_Some _ _ _ _ Hdec) as D. clear Hdec.
destruct ans as [e|[|]].
- destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; lia.
- rewrite D. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
- rewrite D. unfold eff0. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmunmap_post, munmap_ret, rg_errno. finish; exact I.
Qed.

#[using="base rmmap_entry rmprotect_entry rmunmap_entry"] Lemma rmprotect_args : forall A L, (A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 <= A)%Z -> (0 <= L)%Z -> (A + L + 4096 <= 2^64)%Z ->
Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))) = Z_to_bv 64 A
/\ Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (A + L + 4095))) 18446744073709547520))
- bv_unsigned (Z_to_bv 64 (Z.land 18446744073709547520 (bv_unsigned (Z_to_bv 64 A))))) = Z_to_bv 64 L.
Proof. clear - base rmmap_entry rmprotect_entry rmunmap_entry.
intros A L HA HL A0 L0 B. rewrite (Z.land_comm 18446744073709547520).
rewrite (unsigned_lit A), (unsigned_lit (A + L + 4095)) by lia. rewrite !land_m4096 by lia.
assert (E1 : (A - A mod 4096 = A)%Z) by lia.
assert (E2 : ((A + L + 4095) - (A + L + 4095) mod 4096 = A + L)%Z) by (Z.div_mod_to_equations; lia).
rewrite E1, E2. rewrite !unsigned_lit by lia. split; [reflexivity|]. f_equal. lia.
Qed.

Definition rmprotect_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : range_ans) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (munmap_ret a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (rg_errno a errv)]
/\ rw_cells segs m' (RATP + 131776) [C8 (Z_to_bv 64 4096)]
/\ match a with
| RgErr e => e = 12%Z
| RgDone true => rw_cells segs m' A [CB (Z.to_nat L) (repeat (Z_to_bv 8 0) (Z.to_nat L))]
| RgDone false => True
end.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_62 lo_63 joff_73 CODE BASE4 BASER D_62 E_62 D_63 E_63 D_73 E_73 ANCH_63 LINK_73 LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 ref_ro_addr_false sysret_spec rmmap_entry rmprotect_entry rmunmap_entry"] Lemma rmprotect_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L P : Z) (errv : word) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
rw_cells segs m (RATP + 131776) [C8 (Z_to_bv 64 4096)] ->
mem_inv segs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P ->
(A mod 4096 = 0)%Z -> (L mod 4096 = 0)%Z -> (0 < A)%Z -> (0 < L)%Z -> (A + L + 4096 <= 2^64)%Z -> (0 <= P < 2^64)%Z ->
(lo <= bv_unsigned sp - 32)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(A + L <= 0x10000 \/ RIMG_HI <= A)%Z ->
(RIMG_HI <= lo)%Z -> (errno_addr tp + 4 <= (RATP + 131776) \/ (RATP + 131776) + 8 <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl segs (at_node segs) (enode (NMprotect A L P) (dec_mprotect A L))
(epost (rmprotect_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmprotect_entry) fc None m (seg_rom segs)).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_62 lo_63 joff_73 CODE BASE4 BASER D_62 E_62 D_63 E_63 D_73 E_73 ANCH_63 LINK_73 LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 ref_ro_addr_false sysret_spec rmmap_entry rmprotect_entry rmunmap_entry segs RATP RIMG_HI. gw_expose_fam RATP.
intros until lo. intros ST ERR PG MI -> -> -> AA LA A0 L0 AL PR LO SEP1 SEP2 SEP3 SEP4 SLO SEP5 TP.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + L)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
(gw_expose_fam RATP; unfold rmprotect_entry in *). apply impl_enode.
carve_frame 16%nat ST.
step. step. step. step.
do 7 step.
destruct (rmprotect_args A L AA LA ltac:(lia) ltac:(lia) AL) as [E1 E2]. rewrite E2, E1.
step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. pose proof (dec_mprotect_Some _ _ _ _ Hdec) as D. clear Hdec.
rewrite (mmap_len_aligned L LA) in D.
destruct ans as [e|[|]].
- destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
step. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; lia.
- rewrite D.
assert (ROF : forall x : word, (A <= bv_unsigned x < A + L)%Z -> ro_addr segs x = false) by (intros x Hx; apply ref_ro_addr_false; lia).
sys_nret. lazymatch goal with H : mem_inv _ _ |- _ => rename H into MI end.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish.
- rewrite D. unfold eff0. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
step. try rewrite sextw_small by lia. step. step. step. release_frame FR ST (bv_unsigned sp).
unfold rmprotect_post, munmap_ret, rg_errno. finish; exact I.
Qed.

#[using="base rmmap_entry rmprotect_entry rmunmap_entry"] Lemma land_ones64 y : (0 <= y < 2^64)%Z -> Z.land y 18446744073709551615 = y.
Proof. clear - base rmmap_entry rmprotect_entry rmunmap_entry y. intros. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition rmmap_anon_post (isnone : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z) (m : word -> option byte) (a : mmap_ans)
: machine_state -> Prop :=
fun ms' =>
match a with
| MmErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (Z_to_bv 64 (mmap_fix_errno e))]
/\ e = 12%Z
| MmOk x => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 x) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mmap_raw isnone x len m2) (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m2
/\ wmono segs m m2 /\ mem_inv segs m2
/\ stk segs (mmap_raw isnone x len m2) lo (bv_unsigned sp)
/\ rw_cells segs m2 (errno_addr tp) [C4 errv]
/\ mmap_addr_ok len avoid x = true
end.

#[using="rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_58 w_sysret_7 CODE BASE4 BASER D_58 E_58 LINK_58 CODE_rsysret_entry sysret_spec rmmap_entry rmprotect_entry rmunmap_entry"] Lemma rmmap_anon_spec : forall (isnone : bool) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(len : Z) (avoid : list (Z * Z)) (errv : word) (lo : Z),
let prot := (if isnone then 0 else 3)%Z in
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
a0 = Z_to_bv 64 0 -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 prot -> a3 = Z_to_bv 64 34 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < len < 2^63 - 1)%Z ->
(lo <= bv_unsigned sp - 80)%Z -> (alloc_ceiling <= lo)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl segs (at_node segs) (enode (NMmap 0 len prot 34) (if isnone then dec_mmap_none len avoid else dec_mmap len avoid))
(epost (rmmap_anon_post isnone ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc len avoid errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom segs)).
Proof. clear - rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_58 w_sysret_7 CODE BASE4 BASER D_58 E_58 LINK_58 CODE_rsysret_entry sysret_spec rmmap_entry rmprotect_entry rmunmap_entry segs.
intros until lo. intros prot ST ERR MI -> -> -> -> -> -> LEN LO CEIL SEP1 TP.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU1.
pose proof (wmono_refl segs m) as WM.
rewrite alloc_ceiling_val in CEIL.
assert (PR : (0 <= prot < 4)%Z) by (destruct isnone; subst prot; lia). clearbody prot.
unfold rmmap_entry. apply impl_enode.
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
step. step.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec.
assert (D : match ans with
| MmErr e => rsp = efferr e /\ e = 12%Z
| MmOk a => rsp = (if isnone then mkEffectU (Z_to_bv 64 a) [] [] [(wa a, Z_to_bv 64 (mmap_len len))] [] []
else mkEffect (Z_to_bv 64 a) [] [(wa a, Z_to_bv 64 (mmap_len len))])
/\ mmap_addr_ok len avoid a = true
end).
{ destruct isnone; [pose proof (dec_mmap_none_Some _ _ _ _ Hdec) as D | pose proof (dec_mmap_Some _ _ _ _ Hdec) as D];
destruct ans; gw_exact D. }
clear Hdec. destruct ans as [e|x].
- clear MU1. destruct D as [-> He]. unfold efferr, eff0. sys_nret.
step. step. step.
rewrite unsigned_errno_ret, zb_lxor_ones, Z.lor_0_l by lia.
if_cases K; zify_cond K.
+
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
do 10 step. release_frame FR ST (bv_unsigned sp).
unfold rmmap_anon_post, mmap_fix_errno. replace (e =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
finish; lia.
+
exfalso. rewrite ?unsigned_lit in K by lia. subst e. first [lia | cbv in K; lia | vm_compute in K; lia].
- clear MU. destruct D as [-> Hok]. pose proof (mmap_addr_ok_true _ _ _ Hok) as ((XA & X0 & XC) & XAV).
rewrite alloc_ceiling_val in XC. pose proof (mmap_len_ge len) as ML.
lazymatch goal with |- context [nret (MSsvc _ _ _ _ _ _ ?mc _) _] => rename mc into m2 end || idtac.
destruct isnone; sys_nret_raw.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
set (m' := mm);
assert (Hza : (0 <= x < 2^64)%Z) by lia; assert (Hzn : (0 <= mmap_len len < 2^64)%Z) by lia;
assert (Hzan : (x + mmap_len len <= 2^64)%Z) by lia
end.
1: pose proof (rw_cells_unmaps_other segs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_unmaps_other segs _ x (mmap_len len) Hza Hzn Hzan _ _ ST ltac:(lia)) as ST'.
2: pose proof (rw_cells_zeros_other segs _ x (mmap_len len) Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR';
pose proof (stk_zeros segs _ x (mmap_len len) Hza Hzn Hzan _ _ ST) as ST'.
all: fold m' in FR', ST'; clear FR; rename ST into ST0.
all: step; step; step.
all: rewrite zb_lxor_ones, Z.lor_0_l by (rewrite ?unsigned_lit by lia; lia); rewrite ?unsigned_lit by lia.
all: if_cases K; zify_cond K; rewrite ?land_ones64 in K by lia; [| exfalso; lia].

all: step; step; step; step; if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by lia; lia]; step.

all: do 9 step; release_frame FR' ST' (bv_unsigned sp); step.
all: apply evt_done; unfold rmmap_anon_post, mmap_raw; cbv iota.
all: do 14 eexists; eexists; split; [subst m'; reflexivity|].
all: split; [gw_exact MU1|]; split; [gw_exact WM|]; split; [gw_exact MI|]; split; [gw_exact ST'|]; split; [gw_exact ERR| gw_exact Hok].
Qed.

Definition rmmap_fixed_post {X} (R : X -> word -> bool -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A L : Z) (errv : word) (lo : Z) (m : word -> option byte) (a : X) : machine_state -> Prop :=
fun ms' => exists (r : word) (u : bool) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
R a r u /\
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (sysret_val r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m m'
/\ (u = false -> wmono segs m m')
/\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (sysret_errno r errv)].

#[using="rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_58 CODE BASE4 BASER D_58 E_58 LINK_58 sysret_spec rmmap_entry rmprotect_entry rmunmap_entry"] Lemma rmmap_fixed_spec : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(A L P : Z) (errv : word) (lo : Z),
(forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = fixed_shape A L r u) ->
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 P -> a3 = Z_to_bv 64 50 ->
a4 = Z_to_bv 64 (-1) -> a5 = Z_to_bv 64 0 ->
(0 < A)%Z -> (0 < L <= 2^62)%Z -> (A + mmap_len L < 2^64)%Z -> (0 <= P < 4)%Z ->
(lo <= bv_unsigned sp - 80)%Z ->
(errno_addr tp + 4 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= errno_addr tp)%Z ->
(A + mmap_len L <= lo \/ bv_unsigned sp <= A)%Z ->
(A + mmap_len L <= errno_addr tp \/ errno_addr tp + 4 <= A)%Z ->
(164 <= bv_unsigned tp)%Z ->
impl segs (at_node segs) (enode (NMmap A L P 50) dec)
(epost (rmmap_fixed_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L errv lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmmap_entry) fc None m (seg_rom segs)).
Proof. clear - rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 joff_58 CODE BASE4 BASER D_58 E_58 LINK_58 sysret_spec rmmap_entry rmprotect_entry rmunmap_entry segs.
intros until lo. intros DEC ST ERR MI -> -> -> -> -> -> A0 LEN AL PR LO SEP1 SEP2 SEP3 TP.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4); (A, A + mmap_len L)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (mmap_len_ge L) as ML.
unfold rmmap_entry. apply impl_enode.
carve_frame 64%nat ST.
do 8 step.
step. step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. } clear K0.
step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. } clear K1.
step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.

set (z0 := Z_to_bv 64 0). set (zm1 := Z_to_bv 64 (-1)). set (z50 := Z_to_bv 64 50).
set (zA := Z_to_bv 64 A). set (zL := Z_to_bv 64 L). set (zP := Z_to_bv 64 P).
do 6 step. step. step. do 6 step. step.
subst z0 zm1 z50 zA zL zP.
step. step. step_ecall.
split. { at_node_solve. }
intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
destruct u; unfold fixed_shape; cbv iota.
all: sys_nret.
all: step; step; step.
all: if_cases K; zify_cond K; [| exfalso; apply Z.lor_eq_0_iff in K; lia ].
all: step; call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia |]; rename PC into ST; rename POST into ERR.
all: do 10 step; release_frame FR ST (bv_unsigned sp).
all: unfold rmmap_fixed_post; apply evt_done; exists r; eexists; do 15 eexists; split; [gw_exact HR|]; split; [reflexivity|].
all: split; [ eapply munch_weaken; [|gw_exact MU]; intros y; cbn; lia |].
all: split; [ first [intros; discriminate | intros _; assumption] |].
all: split; [lazymatch goal with H : mem_inv segs ?mm |- mem_inv segs ?mm => exact H end|].
all: split; [lazymatch goal with H : stk segs ?mm ?a ?b |- stk segs ?mm _ _ => exact H end|].
all: lazymatch goal with H : rw_cells segs ?mm ?a ?c |- rw_cells segs ?mm _ _ => exact H end.
Qed.

End RC__1.

End G.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Qfw3_c1.Mq2 Q9A7.Mq0.

Import Q91D.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope bv_scope.
Open Scope Z_scope.
Local Unset Keyed Unification.
Local Abbreviation mem := (word -> option byte).
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenSys.
Local Ltac step_ecall ::= g_step_ecall. Local Ltac mkr__step_ecall_2 := g_step_ecall.
Local Ltac sys_nret ::= g_sys_nret. Local Ltac mkr__sys_nret_3 := g_sys_nret.
Local Ltac sys_nret_raw ::= g_sys_nret_raw. Local Ltac mkr__sys_nret_raw_4 := g_sys_nret_raw.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_5 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition mm_code (w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 : Z) : list Z :=
[0x00008067; 0xfc010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; 0x01513423; 0x03479813; 0x00080863; w_11; 0x01600593; 0x0180006f; 0xfff00813; 0x00185813; 0x0305ec63; w_17; 0x00c00593; 0x00b52023; 0xfff00513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x00813a83; 0x04010113; 0x00008067; 0x0106f813; 0x00081663; 0xff400293; 0x03c0006f; 0x00068413; 0x00078993; 0x00050493; 0x00070a13; 0x00060913; 0x00058a93; 0xf61ff0ef; 0x000a8593; 0x00090613; 0x000a0713; 0x00048513; 0x00098793; 0x00040693; 0xfff00293; 0x0de00893; 0x00050813; 0x00000073; 0xfff54593; 0x00b865b3; 0x00059a63; 0x03a69313; 0x03f35513; 0xfff50513; 0x00556533; w_58; 0xf69ff06f; 0xff010113; 0x00113423; w_62; w_63; 0x00b505b3; 0x40d00733; 0x00d585b3; 0x00a77533; 0xfff58593; 0x00e5f5b3; 0x40a585b3; 0x0e200893; 0x00000073; w_73; 0x0005051b; 0x00813083; 0x01010113; 0x00008067; 0xfa010113; 0x02113c23; 0x02813823; 0x02913423; 0x03213023; 0x01313c23; 0x01413823; w_85; w_86; 0x04e13023; 0x04f13423; 0x05013823; 0x05113c23; 0x0004b703; 0xfff00413; 0x00145793; 0x00e13423; 0x00f66a63; w_96; 0x00c00593; 0x00b52023; 0x04c0006f; 0x0026f713; 0x02070a63; 0x00068413; 0x00060993; 0x00058913; 0x00050a13; 0xe59ff0ef; 0x000a0513; 0x00090593; 0x00098613; 0x00040693; 0x04810713; 0x00e13023; 0x04013703; 0x0d800893; 0x00000073; w_116; 0x00050413; 0x0004b503; 0x00813583; 0x02b51463; 0x00040513; 0x03813083; 0x03013403; 0x02813483; 0x02013903; 0x01813983; 0x01013a03; 0x06010113; 0x00008067; w_130; 0xfe010113; 0x00113c23; 0x00813823; 0x00913423; 0x00058413; 0x00050493; 0xdddff0ef; 0x0d700893; 0x00048513; 0x00040593; 0x00000073; w_142; 0x0005051b; 0x01813083; 0x01013403; 0x00813483; 0x02010113; 0x00008067]%Z.

Definition sysret_code (w_sysret_7 : Z) : list Z :=
[0xfffff5b7; 0x0015859b; 0x02b56663; 0xff010113; 0x00113423; 0x00813023; 0x40a0043b; w_sysret_7; 0x00852023; 0xfff00513; 0x00813083; 0x00013403; 0x01010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rsysret_entry : Z).
Variables (w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 : Z).
Variables (hi_62 hi_85 : bv 20).
Variables (lo_63 lo_86 : bv 12).
Variables (joff_11 joff_17 joff_58 joff_73 joff_96 joff_116 joff_130 joff_142 : bv 21).
Variables (e_197bc : Z).
Variables (w_sysret_7 : Z).
Hypothesis CODE : code_at segs base (mm_code w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 596.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_17 : decode_any (Z_to_bv 32 w_17) = Some (Jal 1 joff_17, 4%Z).
Hypothesis E_17 : is_ecall (Z_to_bv 32 w_17) = false.
Hypothesis D_58 : decode_any (Z_to_bv 32 w_58) = Some (Jal 1 joff_58, 4%Z).
Hypothesis E_58 : is_ecall (Z_to_bv 32 w_58) = false.
Hypothesis D_62 : decode_any (Z_to_bv 32 w_62) = Some (Auipc 13 hi_62, 4%Z).
Hypothesis E_62 : is_ecall (Z_to_bv 32 w_62) = false.
Hypothesis D_63 : decode_any (Z_to_bv 32 w_63) = Some (Load SZ8 true 13 13 lo_63, 4%Z).
Hypothesis E_63 : is_ecall (Z_to_bv 32 w_63) = false.
Hypothesis D_73 : decode_any (Z_to_bv 32 w_73) = Some (Jal 1 joff_73, 4%Z).
Hypothesis E_73 : is_ecall (Z_to_bv 32 w_73) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 5 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (Load SZ8 true 9 5 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (Jal 1 joff_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_116 : decode_any (Z_to_bv 32 w_116) = Some (Jal 1 joff_116, 4%Z).
Hypothesis E_116 : is_ecall (Z_to_bv 32 w_116) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_142 : decode_any (Z_to_bv 32 w_142) = Some (Jal 1 joff_142, 4%Z).
Hypothesis E_142 : is_ecall (Z_to_bv 32 w_142) = false.
Hypothesis ANCH_63 : gw_anch (Z.shiftl (bv_signed hi_62) 12 + (base + 248) + bv_signed lo_63)%Z (RATP + 131776).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z RGOT_SSP.
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_17 : gw_anch (base + 68 + bv_signed joff_17)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_58 : gw_anch (base + 232 + bv_signed joff_58)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_73 : gw_anch (base + 292 + bv_signed joff_73)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_96 : gw_anch (base + 384 + bv_signed joff_96)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_116 : gw_anch (base + 464 + bv_signed joff_116)%Z (rsysret_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (e_197bc + 0)%Z.
Hypothesis LINK_142 : gw_anch (base + 568 + bv_signed joff_142)%Z (rsysret_entry + 0)%Z.
Hypothesis CODE_rsysret_entry : code_at segs rsysret_entry (sysret_code w_sysret_7).
Hypothesis AL_rsysret_entry_b4 : gw_b4 rsysret_entry.
Hypothesis RNG_rsysret_entry_code : gw_br rsysret_entry 56.
Hypothesis CODE_rerrno_loc_entry : code_at segs rerrno_loc_entry errno_loc_code.
Hypothesis AL_rerrno_loc_entry_b4 : gw_b4 rerrno_loc_entry.
Hypothesis RNG_rerrno_loc_entry_code : gw_br rerrno_loc_entry 12.
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rsysret_entry : gw_al rsysret_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition sysret_post : ltac:(gw_rebind_ty (@Q91D.Mq7.sysret_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q91D.Mq7.sysret_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@Q91D.Mq7.sysret_post segs) (@sysret_post) gw_tbl_0).

Hypothesis sysret_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@Q91D.Mq7.gw_all) (@Q91D.Mq7.sysret_spec) rsysret_entry)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_1))) in exact T).
#[using="RGOT_SSP rerrno_loc_entry e_197bc rsysret_entry RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_11 E_11 D_17 E_17 D_58 E_58 D_62 E_62 D_63 E_63 D_73 E_73 D_85 E_85 D_86 E_86 D_96 E_96 D_116 E_116 D_130 E_130 D_142 E_142 ANCH_63 ANCH_86 LINK_11 LINK_17 LINK_58 LINK_73 LINK_96 LINK_116 LINK_130 LINK_142 CODE_rsysret_entry AL_rsysret_entry_b4 RNG_rsysret_entry_code CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT LAY_ref_reserved AL_rerrno_loc_entry AL_rsysret_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ sysret_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition rmremap_entry : Z := (base + 0x138).

Definition mremap_mem (x : mremap_ans) (old oldlen newlen : Z) (m2 : mem) : mem :=
match x with
| MrErr _ => m2
| MrInPlace => if newlen <? oldlen then apply_unmaps m2 [(wa (old + newlen), Z_to_bv 64 (oldlen - newlen))]
else apply_zeros m2 [(wa (old + oldlen), Z_to_bv 64 (newlen - oldlen))]
| MrMoved a => apply_copy m2 (apply_zeros (apply_unmaps m2 [(wa old, Z_to_bv 64 oldlen)]) [(wa (a + oldlen), Z_to_bv 64 (newlen - oldlen))])
(mkCopy (wa old) (wa a) (Z_to_bv 64 oldlen))
end.

Definition mremap_ret (x : mremap_ans) (old : Z) : Z :=
match x with MrErr _ => -1 | MrInPlace => old | MrMoved a => a end.

Definition mremap_safe (x : mremap_ans) (old oldlen newlen : Z) : Prop :=
match x with
| MrErr _ => True
| MrInPlace => newlen < oldlen \/ (old + newlen <= alloc_ceiling /\ (old + newlen <= 0x10000 \/ RIMG_HI <= old + oldlen))
| MrMoved a => (a + newlen <= 0x10000 \/ RIMG_HI <= a) /\ (old + oldlen <= a \/ a + newlen <= old)
end.

Definition rmremap_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(old oldlen newlen : Z) (errv : word) (lo : Z) (m : mem) (x : mremap_ans) : machine_state -> Prop :=
fun ms' =>
match x with
| MrErr e => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m'
/\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 (Z_to_bv 64 e)]
/\ e = 12
| _ => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m2,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (mremap_ret x old)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None (mremap_mem x old oldlen newlen m2) (seg_rom segs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m2
/\ wmono segs m m2 /\ mem_inv segs m2
/\ stk segs (mremap_mem x old oldlen newlen m2) lo (bv_unsigned sp)
/\ rw_cells segs m2 (errno_addr tp) [C4 errv]
/\ match x with MrMoved a => oldlen < newlen /\ a mod 4096 = 0 /\ 0 < a /\ a + newlen <= alloc_ceiling | _ => True end
end.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_85 lo_86 joff_116 w_sysret_7 CODE BASE4 BASER D_85 E_85 D_86 E_86 D_116 E_116 ANCH_86 LINK_116 CODE_rsysret_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ref_ro_addr_false sysret_spec"] Lemma rmremap_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
(old oldlen newlen : Z) (errv canary : word) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
rw_cells segs m RGOT_SSP [C8 (Z_to_bv 64 (RATP + 131696))] ->
rw_cells segs m (RATP + 131696) [C8 canary] ->
a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 oldlen -> a2 = Z_to_bv 64 newlen -> a3 = Z_to_bv 64 1 ->
0 < old -> old + oldlen <= alloc_ceiling -> (old + oldlen <= 0x10000 \/ RIMG_HI <= old) -> 0 < oldlen -> 0 < newlen < 2^63 - 1 ->
lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
tp = Z_to_bv 64 RATP ->
evt segs (fun ms1 => at_node segs (NMremap old oldlen newlen 1) ms1 /\
forall rsp x, dec_mremap old oldlen newlen [] rsp = Some x -> mremap_safe x old oldlen newlen ->
evt segs (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old oldlen newlen errv lo m x) (nret ms1 rsp))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom segs)).
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rsysret_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_85 lo_86 joff_116 w_sysret_7 CODE BASE4 BASER D_85 E_85 D_86 E_86 D_116 E_116 ANCH_86 LINK_116 CODE_rsysret_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ref_ro_addr_false sysret_spec segs RATP RGOT_SSP RIMG_HI. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros until lo. intros ST ERR MI GOT CAN -> -> -> -> O0 OC OIMG L0 NL LO CLO TP.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : bv_unsigned tp + -164 = (RATP + -164)) by (rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; first [reflexivity | lia]).
rewrite alloc_ceiling_val in OC, CLO.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU1.
pose proof (wmono_refl segs m) as WM.
(gw_expose_fam RGOT_SSP; gw_expose_fam RATP; unfold rmremap_entry in *).
carve_frame 96%nat ST.

do 7 step. step. step. do 4 step. step. step. step. step.
step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. 2:{ exfalso. lia. }

step. step. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
step. step_ecall.
split. { at_node_solve. }
intros rsp x Hdec SAFE. pose proof (dec_mremap_Some _ _ _ _ _ _ Hdec) as [EFF D]. clear Hdec.
destruct x as [e| |na].
-  clear MU1. cbn [mremap_eff] in EFF. rewrite EFF. unfold efferr, eff0. sys_nret.
step. call_sp sysret_spec; [gw_exact ST | gw_exact ERR | gw_exact MI | lia | lia | lia | ]. rename PC into ST; rename POST into ERR.
unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.

step. step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
unfold rmremap_post. finish; lia.
-
clear MU. cbn [mremap_safe] in SAFE. cbn [mremap_eff] in EFF.
assert (XO : 0 < old < 2^64) by lia.
destruct EFF as [[LT ->]|[LT ->]]; sys_nret_raw.
+
assert (Hua : (0 <= old + newlen < 2^64)%Z) by lia. assert (Hun : (0 <= oldlen - newlen < 2^64)%Z) by lia.
assert (Huan : (old + newlen + (oldlen - newlen) <= 2^64)%Z) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_unmaps ?mc _) _) => rename mc into m2 end.
pose proof (rw_cells_unmaps_other segs _ _ _ Hua Hun Huan _ _ FR ltac:(cbn; lia)) as FR'.
pose proof (rw_cells_unmaps_other segs _ _ _ Hua Hun Huan _ _ GOT ltac:(cbn; lia)) as GOT'.
pose proof (rw_cells_unmaps_other segs _ _ _ Hua Hun Huan _ _ CAN ltac:(cbn; lia)) as CAN'.
pose proof (stk_unmaps_other segs _ _ _ Hua Hun Huan _ _ ST ltac:(lia)) as ST'.
pose proof (mem_inv_unmaps segs _ _ _ Hua Hun Huan MI) as MI'.
set (m' := apply_unmaps m2 _) in *.
clear FR GOT CAN ST. rename MI into MI2.

step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } step.

step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
step. do 6 step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. unfold rmremap_post, mremap_mem, mremap_ret. replace (newlen <? oldlen) with true by (symmetry; apply Z.ltb_lt; lia).
do 14 eexists. exists m2. split; [subst m'; reflexivity|].
split; [gw_exact MU1|]. split; [gw_exact WM|]. split; [gw_exact MI2|]. split; [gw_exact ST'|]. split; [gw_exact ERR| exact I].
+
destruct SAFE as [|[SC SI]]; [lia|].
assert (Hza : (0 <= old + oldlen < 2^64)%Z) by lia. assert (Hzn : (0 <= newlen - oldlen < 2^64)%Z) by lia.
assert (Hzan : (old + oldlen + (newlen - oldlen) <= 2^64)%Z) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_zeros ?mc _) _) => rename mc into m2 end.
pose proof (rw_cells_zeros_other segs _ _ _ Hza Hzn Hzan _ _ FR ltac:(cbn; lia)) as FR'.
pose proof (rw_cells_zeros_other segs _ _ _ Hza Hzn Hzan _ _ GOT ltac:(cbn; lia)) as GOT'.
pose proof (rw_cells_zeros_other segs _ _ _ Hza Hzn Hzan _ _ CAN ltac:(cbn; lia)) as CAN'.
pose proof (stk_zeros segs _ _ _ Hza Hzn Hzan _ _ ST) as ST'.
pose proof (mem_inv_zeros segs _ _ _ Hza Hzn Hzan MI) as MI'.
specialize (MI' ltac:(intros x Hx; apply ref_ro_addr_false; lia)).
set (m' := apply_zeros m2 _) in *.
clear FR GOT CAN ST. rename MI into MI2.
step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } step.
step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
step. do 6 step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. unfold rmremap_post, mremap_mem, mremap_ret. replace (newlen <? oldlen) with false by (symmetry; apply Z.ltb_ge; lia).
do 14 eexists. exists m2. split; [subst m'; reflexivity|].
split; [gw_exact MU1|]. split; [gw_exact WM|]. split; [gw_exact MI2|]. split; [gw_exact ST'|]. split; [gw_exact ERR| exact I].
-
clear MU. cbn [mremap_safe] in SAFE. destruct SAFE as [SI SD]. cbn [mremap_eff] in EFF. destruct EFF as [LT ->].
destruct D as ((NAL & NA0 & NAC) & _ & NNE). rewrite alloc_ceiling_val in NAC.
rewrite nret_MSsvc_cs; rewrite ?mkR_set_a0; simp_regs.
lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 (?b + ?k)%Z + Z_to_bv 64 4)%bv _ _ _ _) =>
let k' := eval vm_compute in (k + 4)%Z in rewrite (sg_pc_seq b k 4 k' eq_refl)
end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_writes (apply_copies ?mc _ _) _) _) => rename mc into m2 end.
change (apply_writes ?mm []) with mm. cbn [apply_copies fold_left].
assert (Hold : (0 <= old < 2^64)%Z) by lia. assert (Hon : (0 <= oldlen)%Z) by lia. assert (Holdhi : (old + oldlen <= 2^64)%Z) by lia.
assert (Ha0 : (0 <= na < 2^64)%Z) by lia. assert (Hnn : (oldlen < newlen < 2^64)%Z) by lia. assert (Hahi : (na + newlen <= 2^64)%Z) by lia.
pose proof (rw_cells_move_other segs m2 old oldlen na newlen Hold Hon Holdhi Ha0 Hnn Hahi SD _ _ FR ltac:(cbn; unfold move_other; lia)) as FR'.
pose proof (rw_cells_move_other segs m2 old oldlen na newlen Hold Hon Holdhi Ha0 Hnn Hahi SD _ _ GOT ltac:(cbn; unfold move_other; lia)) as GOT'.
pose proof (rw_cells_move_other segs m2 old oldlen na newlen Hold Hon Holdhi Ha0 Hnn Hahi SD _ _ CAN ltac:(cbn; unfold move_other; lia)) as CAN'.
pose proof (stk_move_other segs m2 old oldlen na newlen Hold Hon Holdhi Ha0 Hnn Hahi SD _ _ ST ltac:(lia) ltac:(lia)) as ST'.
pose proof (mem_inv_move segs m2 old oldlen na newlen Hold Hon Holdhi Ha0 Hnn Hahi SD MI ltac:(intros x Hx; apply ref_ro_addr_false; lia)) as MI'.
set (m' := apply_copy m2 _ _) in *.
clear FR GOT CAN ST. rename MI into MI2.
step. step. step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } step.
step. step. step. step. if_cases K3; zify_cond K3. { exfalso. apply K3. reflexivity. }
step. do 6 step. step. step.
release_frame FR' ST' (bv_unsigned sp).
apply evt_done. unfold rmremap_post, mremap_mem, mremap_ret.
do 14 eexists. exists m2. split; [subst m'; reflexivity|].
split; [gw_exact MU1|]. split; [gw_exact WM|]. split; [gw_exact MI2|]. split; [gw_exact ST'|]. split; [gw_exact ERR|]. lia.
Qed.

#[using="RIMG_HI gw_RDATA2_LO rerrno_loc_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_85 lo_86 joff_96 CODE BASE4 BASER D_85 E_85 D_86 E_86 D_96 E_96 ANCH_86 LINK_96 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4"] Lemma rmremap_huge_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
(old oldlen newlen : Z) (errv canary : word) (lo : Z),
stk segs m lo (bv_unsigned sp) ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
rw_cells segs m RGOT_SSP [C8 (Z_to_bv 64 (RATP + 131696))] ->
rw_cells segs m (RATP + 131696) [C8 canary] ->
a0 = Z_to_bv 64 old -> a1 = Z_to_bv 64 oldlen -> a2 = Z_to_bv 64 newlen -> a3 = Z_to_bv 64 1 ->
2^63 - 1 <= newlen < 2^64 ->
lo <= bv_unsigned sp - 112 -> alloc_ceiling <= lo ->
tp = Z_to_bv 64 RATP ->
evt segs (rmremap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc old oldlen newlen errv lo m (MrErr 12))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmremap_entry) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO rerrno_loc_entry w_11 w_17 w_58 w_62 w_63 w_73 w_85 w_86 w_96 w_116 w_130 w_142 hi_85 lo_86 joff_96 CODE BASE4 BASER D_85 E_85 D_86 E_86 D_96 E_96 ANCH_86 LINK_96 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros until lo. intros ST ERR MI GOT CAN -> -> -> -> NL LO CLO TP.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (ETP : bv_unsigned tp + -164 = (RATP + -164)) by (rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; first [reflexivity | lia]).
rewrite alloc_ceiling_val in CLO.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
(gw_expose_fam RGOT_SSP; gw_expose_fam RATP; unfold rmremap_entry in *).
carve_frame 96%nat ST.

do 7 step. step. step. do 4 step. step. step. step. step.
step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by lia. { exfalso. lia. }

step. step. step. step. step. step. step.

step. step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. }
step. do 6 step. step. step.
release_frame FR ST (bv_unsigned sp).
unfold rmremap_post. finish; lia.
Qed.

End RC__1.

End G.
End Mq3.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi QUZl Q7S0 QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1.

Export QnDM_c1.Mq0.
Export Q91D.Mq7.
Import QZAi.Mq2 QUZl Q7S0.Mq0 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope bv_scope.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Hypothesis RNG_RATP : gw_br RATP 1896.
Hypothesis LAY_lo_RATP : gw_le (gw_RDATA2_LO + 164) RATP.
Hypothesis LAY_hi_RATP : gw_le ((RATP + 132896)) RIMG_HI.
Hypothesis AL_RATP : gw_al RATP 8.
Hypothesis RNG_RDEBRUIJN : gw_br RDEBRUIJN 159.
Hypothesis LAY_lo_RDEBRUIJN : gw_le (0x10000 + 0) RDEBRUIJN.
Hypothesis LAY_hi_RDEBRUIJN : gw_le ((RDEBRUIJN + 159)) gw_RTEXT_LO.
Hypothesis AL_RDEBRUIJN : gw_al RDEBRUIJN 8.
Hypothesis RNG_RGOT_SSP : gw_br RGOT_SSP 8.
Hypothesis LAY_lo_RGOT_SSP : gw_le (RDATA_LO + 0) RGOT_SSP.
Hypothesis LAY_hi_RGOT_SSP : gw_le ((RGOT_SSP + 8)) gw_RDATA2_LO.
Hypothesis AL_RGOT_SSP : gw_al RGOT_SSP 8.
Hypothesis LAY_win_0 : gw_win (0x10000 + 1) gw_RTEXT_LO.
Hypothesis LAY_win_1 : gw_win (gw_RTEXT_LO + 1) RDATA_LO.
Hypothesis LAY_win_2 : gw_win (RDATA_LO + 1) gw_RDATA2_LO.
Hypothesis LAY_win_3 : gw_win (gw_RDATA2_LO + 1) RIMG_HI.
Hypothesis LAY_win_4 : gw_win RIMG_HI 0x1000000.
Hypothesis AL_win_RIMG_HI : gw_winal RIMG_HI 4096.
Hypothesis AL_win_RDATA_LO : gw_winal RDATA_LO 4096.
Hypothesis AL_win_gw_RTEXT_LO : gw_winal gw_RTEXT_LO 4096.
Hypothesis AL_win_gw_RDATA2_LO : gw_winal gw_RDATA2_LO 4096.
Hypothesis ROM_RSIZE_CLASSES : QZDE.ro_bytes segs (RDEBRUIJN + 32) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSIZE_CLASSES.
Hypothesis ROM_RDEBRUIJN : QZDE.ro_bytes segs RDEBRUIJN OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RDEBRUIJN.
Hypothesis ROM_RSMALL_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 128) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RSMALL_CNT.
Hypothesis ROM_RMED_CNT : QZDE.ro_bytes segs (RDEBRUIJN + 155) OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.gw_rom_RMED_CNT.
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="ROM_reservedZ"] Lemma reservedZ_ref : reservedZ segs = ref_reserved.
Proof. clear - ROM_reservedZ segs ref_reserved. exact ROM_reservedZ. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition rmrep_ctx : Prop :=
rw_cells segs m (RATP + 131968) (ctx_head_cells st)
/\ u64arr segs m ((RATP + 132048)) (actives st)
/\ u64arr segs m ((RATP + 132432)) (usages st)
/\ u8arr segs m ((RATP + 132816)) (unmap_seqs st)
/\ u8arr segs m ((RATP + 132848)) (bouncess st)
/\ rw_cells segs m ((RATP + 132880)) (ctx_tail_cells st).

Definition rmrep_globals : Prop :=
rw_cells segs m (RATP + 131960) [C4 (wz 0)]
/\ rw_cells segs m (RATP + 131731) [C1 (b8 0)]
/\ rw_cells segs m (RATP + 131776) [C8 (wz 4096)]
/\ rw_cells segs m RGOT_SSP [C8 (wz (RATP + 131696))]
/\ rw_cells segs m (RATP + 131696) [C8 rc_canary].

Definition rarea_rep (a : aptr) (ar : area) : Prop :=
rw_cells segs m (conc st a) [C8 (wz (a_check ar)); C8 (pw st (a_next ar)); C4 (wz (a_nslots ar)); C4 (wz 0)]
/\ (forall k, 0 <= k < NSLOTS ->
rw_cells segs m (conc st a + AREA_HDR + META_SIZE * k)
(meta_cells st (get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k)))))
/\ rw_cells segs m (conc st a + 4064) [CB 32 (zeros 32)].
Definition rmrep_areas : Prop :=
forall a ar, (s_areas st) !! a = Some ar -> rarea_rep a ar.

Definition rgroup_rep (b : aptr) (gh : ghdr) : Prop :=
exists w8 : byte,
rw_cells segs m (conc st b) [C8 (pw st (g_meta gh)); C1 w8]
/\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Definition rmrep_groups : Prop :=
forall b gh, (s_groups st) !! b = Some gh -> rgroup_rep b gh.

Definition rshadow_rep (rid : N) (r : region) : Prop :=
wr_at segs m (r_base r) (round_up_pg (r_len r))
/\ forall o v, 0 <= o < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v ->
bytes_at segs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
Definition rmrep_shadow : Prop :=
forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> rshadow_rep rid r.

Definition rregions_wf : Prop :=
s_reserved st = ref_reserved
/\ (forall rid r, (s_regions st) !! rid = Some r ->
0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= r_len r
/\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
/\ ranges_free ref_reserved (r_base r) (round_up_pg (r_len r)) = true)
/\ (forall rid1 r1 rid2 r2, (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= lr_lo r1)

/\ (forall a ar, (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0
/\ r_kind r <> RKGroup /\ lr_lo r <= r_base r + snd a)
/\ (forall b gh, (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0).

Definition rmrep : Prop :=
rregions_wf /\ rmrep_ctx /\ rmrep_globals /\ rmrep_areas /\ rmrep_groups /\ rmrep_shadow.

End MREP.

Definition rmrep_W (st : mstate) : list (Z * Z) :=
((RATP + 131968), (RATP + 132896))
:: map (fun kr : N * region => (r_base (snd kr), r_base (snd kr) + round_up_pg (r_len (snd kr)))) (map_to_list (s_regions st)).

#[using="Type"] Lemma rmrep_shadow_read : forall st m rid r o v,
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= o < round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v ->
ov_read_bytes segs m (wa (r_base r + o)) 1 = Some [b8 v] /\ 0 <= v < 256.
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m rid r o v (WF & _ & _ & _ & _ & SH) Hr Hk Ho Hc.
destruct (SH rid r Hr Hk) as [HW HB]. destruct (HB o v Ho Hc) as [Hm Hv]. split; [|gw_exact Hv].
rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read segs m _ [b8 v] 0 1 Hm); [lia|cbn; lia].
Qed.

#[using="Type"] Lemma rmrep_shadow_read2 : forall st m rid r o v0 v1,
rmrep st m -> (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
0 <= o -> o + 2 <= round_up_pg (r_len r) ->
cell_read (get_shadow st rid) o = Known v0 ->
cell_read (get_shadow st rid) (o + 1) = Known v1 ->
ov_read_bytes segs m (wa (r_base r + o)) 2 = Some [b8 v0; b8 v1] /\ 0 <= v0 < 256 /\ 0 <= v1 < 256.
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m rid r o v0 v1 MR Hr Hk Ho Ho2 H0 H1.
pose proof MR as (WF & _ & _ & _ & _ & SH).
destruct (SH rid r Hr Hk) as [HW HB].
destruct (HB o v0 ltac:(lia) H0) as [B0 V0]. destruct (HB (o + 1) v1 ltac:(lia) H1) as [B1 V1].
split; [|split; assumption].
assert (B : bytes_at segs m (r_base r + o) ([b8 v0] ++ [b8 v1])).
{ apply bytes_at_app. split; [gw_exact B0|]. cbn [length Z.of_nat Pos.of_succ_nat].
replace (r_base r + o + 1) with (r_base r + (o + 1)) by lia. gw_exact B1. }
rewrite <- (Z.add_0_r (r_base r + o)). apply (bytes_at_read segs m _ _ 0 2 B); [lia|cbn; lia].
Qed.

Definition rsize_classes_bytes : list byte :=
[Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 36; Z_to_bv 8 0; Z_to_bv 8 42; Z_to_bv 8 0; Z_to_bv 8 50; Z_to_bv 8 0; Z_to_bv 8 63; Z_to_bv 8 0; Z_to_bv 8 72; Z_to_bv 8 0; Z_to_bv 8 84; Z_to_bv 8 0; Z_to_bv 8 102; Z_to_bv 8 0; Z_to_bv 8 127; Z_to_bv 8 0; Z_to_bv 8 146; Z_to_bv 8 0; Z_to_bv 8 170; Z_to_bv 8 0; Z_to_bv 8 204; Z_to_bv 8 0; Z_to_bv 8 255; Z_to_bv 8 0; Z_to_bv 8 36; Z_to_bv 8 1; Z_to_bv 8 84; Z_to_bv 8 1; Z_to_bv 8 153; Z_to_bv 8 1; Z_to_bv 8 255; Z_to_bv 8 1; Z_to_bv 8 72; Z_to_bv 8 2; Z_to_bv 8 170; Z_to_bv 8 2; Z_to_bv 8 50; Z_to_bv 8 3; Z_to_bv 8 255; Z_to_bv 8 3; Z_to_bv 8 145; Z_to_bv 8 4; Z_to_bv 8 84; Z_to_bv 8 5; Z_to_bv 8 101; Z_to_bv 8 6; Z_to_bv 8 255; Z_to_bv 8 7; Z_to_bv 8 36; Z_to_bv 8 9; Z_to_bv 8 170; Z_to_bv 8 10; Z_to_bv 8 204; Z_to_bv 8 12; Z_to_bv 8 255; Z_to_bv 8 15; Z_to_bv 8 72; Z_to_bv 8 18; Z_to_bv 8 84; Z_to_bv 8 21; Z_to_bv 8 152; Z_to_bv 8 25; Z_to_bv 8 255; Z_to_bv 8 31].

#[using="RNG_RDEBRUIJN ROM_RSIZE_CLASSES"] Lemma rsize_classes_ro : forall m, mem_inv segs m -> ro_cells segs m (RDEBRUIJN + 32) [CB 96 rsize_classes_bytes].
Proof. clear - RNG_RDEBRUIJN ROM_RSIZE_CLASSES segs RDEBRUIJN.
intros m MI. pose proof RNG_RDEBRUIJN as RNG_; unfold gw_br in RNG_. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_RSIZE_CLASSES].
Qed.

#[using="RNG_RDEBRUIJN ROM_RSIZE_CLASSES"] Lemma rsize_classes_read : forall m sc, mem_inv segs m -> 0 <= sc < 48 ->
ov_read_bytes segs m (wa ((RDEBRUIJN + 32) + 2 * sc)) 2 = Some (le2 (wz (size_class sc))).
Proof. clear - RNG_RDEBRUIJN ROM_RSIZE_CLASSES segs RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros m sc MI Hsc.
destruct (rsize_classes_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
rewrite (bytes_at_read segs m (RDEBRUIJN + 32) rsize_classes_bytes (2 * sc) 2 B) by (cbn; lia).
assert (Hn : exists n, sc = Z.of_nat n /\ (n < 48)%nat) by (exists (Z.to_nat sc); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
replace (Z.to_nat (2 * Z.of_nat n)) with (2 * n)%nat by lia.
Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
do 48 (destruct n as [|n]; [solve_bytes |]). lia.
Qed.

#[using="Type"] Lemma rmrep_meta_chunk : forall st m g,
rmrep st m -> meta_slot st g ->
rw_cells segs m (conc st g) (meta_cells st (get_meta_rec st g)).
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m g MR (a & ar & k & Ha & Hk & ->).
pose proof MR as (WF & _ & _ & AR & _ & _).
destruct (AR a ar Ha) as (_ & SL & _).
destruct WF as (_ & _ & _ & WA & _). destruct (WA a ar Ha) as (r & Hr & _).
rewrite conc_aadd by (rewrite Hr; eauto).
replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. gw_exact Hk.
Qed.

#[using="Type"] Lemma rmrep_group_read : forall st m b gh,
rmrep st m -> (s_groups st) !! b = Some gh ->
ov_read_bytes segs m (wa (conc st b)) 8 = Some (le8 (pw st (g_meta gh)))
/\ exists w8 : byte, ov_read_bytes segs m (wa (conc st b + 8)) 1 = Some [w8] /\ Z.land (bv_unsigned w8) 31 = g_active_idx gh.
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m b gh MR Hb. pose proof MR as (_ & _ & _ & _ & GR & _).
destruct (GR b gh Hb) as (w8 & RW & Hw8). split.
- rewrite <- (Z.add_0_r (conc st b)). apply (rw_cells_read_at segs m _ _ 0 (C8 (pw st (g_meta gh))) 8 _ RW); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
- exists w8. split; [|gw_exact Hw8].
apply (rw_cells_read_at segs m _ _ 8 (C1 w8) 1 _ RW); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
Qed.

#[using="Type"] Lemma rmrep_area_check_read : forall st m a ar,
rmrep st m -> (s_areas st) !! a = Some ar ->
ov_read_bytes segs m (wa (conc st a)) 8 = Some (le8 (wz (a_check ar))).
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m a ar MR Ha. pose proof MR as (_ & _ & _ & AR & _ & _).
destruct (AR a ar Ha) as (HD & _ & _).
rewrite <- (Z.add_0_r (conc st a)). apply (rw_cells_read_at segs m _ _ 0 (C8 (wz (a_check ar))) 8 _ HD); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
Qed.

#[using="Type"] Lemma rmrep_ctx_secret_read : forall st m,
rmrep st m -> ov_read_bytes segs m (wa (RATP + 131968)) 8 = Some (le8 (wz (c_secret (ctx st)))).
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m (_ & (HD & _) & _).
rewrite <- (Z.add_0_r (RATP + 131968)). apply (rw_cells_read_at segs m _ _ 0 (C8 (wz (c_secret (ctx st)))) 8 _ HD); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
Qed.

#[using="LAY_ref_reserved"] Lemma rreserved_disjoint : forall b n, ranges_free ref_reserved b n = true ->
(b + n <= 0x10000 \/ gw_RTEXT_LO <= b) /\ ((b + n <= gw_RTEXT_LO \/ RDATA_LO <= b)
/\ (b + n <= RDATA_LO \/ gw_RDATA2_LO <= b) /\ (b + n <= gw_RDATA2_LO \/ RIMG_HI <= b)).
Proof. clear - LAY_ref_reserved RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved. gw_expose_win.
intros b n H. (rewrite ?LAY_ref_reserved in H; unfold ranges_free in H). cbn [forallb fst snd] in H.
unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rreserved_disjoint1 : forall b n, ranges_free ref_reserved b n = true -> 0 < n ->
b + n <= 0x10000 \/ RIMG_HI <= b.
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved RIMG_HI ref_reserved. gw_expose_win. intros b n H Hn. pose proof (rreserved_disjoint b n H). lia. Qed.

#[using="gw_RTEXT_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved"] Lemma rwr_in_image : forall st rid a len,
rregions_wf st -> wr_in st rid a len ->
((a + len <= RDATA_LO \/ gw_RDATA2_LO <= a) /\ (a + len <= gw_RDATA2_LO \/ RIMG_HI <= a)) /\ 0 <= a /\ a + len <= 2^64.
Proof. clear - gw_RTEXT_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved RIMG_HI RDATA_LO gw_RDATA2_LO. gw_expose_win.
intros st rid a len (_ & WR & _) (r & Hr & H1 & H2 & H3).
destruct (WR rid r Hr) as (B0 & _ & L0 & BC & RF). unfold alloc_ceiling in BC.
destruct (rreserved_disjoint _ _ RF) as [_ D2]. pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r). lia.
Qed.

#[using="Type"] Lemma rwr_in_other : forall st rid a len rid' r',
rregions_wf st -> wr_in st rid a len -> (s_regions st) !! rid' = Some r' -> rid' <> rid ->
a + len <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= a.
Proof. clear - segs.
intros st rid a len rid' r' (_ & _ & DJ & _) (r & Hr & H1 & H2 & H3) Hr' Hne.
destruct (DJ rid r rid' r' Hr Hr' ltac:(congruence)); lia.
Qed.

#[using="segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma rarea_lr_lo : forall st a ar r, rregions_wf st -> (s_areas st) !! a = Some ar -> (s_regions st) !! (fst a) = Some r ->
lr_lo r <= r_base r + snd a.
Proof. clear - segs RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved.
intros st a ar r (_ & _ & _ & WA & _) Ha Hr. destruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
rewrite Hr in Hr0. inversion Hr0; subst. gw_exact LO.
Qed.

#[using="Type"] Lemma rregions_disjoint_full : forall st rid1 r1 rid2 r2,
rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_kind r1 <> RKBrk -> r_kind r2 <> RKBrk ->
r_base r1 + round_up_pg (r_len r1) <= r_base r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof. clear - segs.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1 K2.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_nbrk r1 K1), (lr_lo_nbrk r2 K2) in X. gw_exact X.
Qed.

#[using="Type"] Lemma rregions_disjoint_grp : forall st rid1 r1 rid2 r2,
rregions_wf st -> (s_regions st) !! rid1 = Some r1 -> (s_regions st) !! rid2 = Some r2 -> rid1 <> rid2 ->
r_kind r1 = RKGroup ->
r_base r1 + round_up_pg (r_len r1) <= lr_lo r2 \/ r_base r2 + round_up_pg (r_len r2) <= r_base r1.
Proof. clear - segs.
intros st rid1 r1 rid2 r2 (_ & _ & DJ & _) H1 H2 NE K1.
pose proof (DJ rid1 r1 rid2 r2 H1 H2 NE) as X. rewrite (lr_lo_group r1 K1) in X. gw_exact X.
Qed.

#[using="Type"] Lemma rmrep_ctx_ext : forall st st' m,
ctx st' = ctx st -> (forall p, conc st' p = conc st p) -> rmrep_ctx st m -> rmrep_ctx st' m.
Proof. clear - RATP. gw_expose_fam RATP.
intros st st' m Hc Hconc H.
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
assert (E1 : ctx_head_cells st' = ctx_head_cells st) by (unfold ctx_head_cells; rewrite Hc, !Hpw; reflexivity).
assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. gw_exact H.
Qed.

#[using="Type"] Lemma rarea_rep_ext : forall st st' m a ar,
(forall p, conc st' p = conc st p) ->
(forall k, 0 <= k < NSLOTS -> get_meta_rec st' (aadd a (AREA_HDR + META_SIZE * k)) = get_meta_rec st (aadd a (AREA_HDR + META_SIZE * k))) ->
rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof. clear - segs.
intros st st' m a ar Hconc Hm (H1 & H2 & H3).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
unfold rarea_rep. rewrite !Hconc, Hpw. split; [gw_exact H1|]. split; [|gw_exact H3].
intros k Hk. rewrite Hmc, Hm by gw_exact Hk. apply H2. gw_exact Hk.
Qed.

#[using="Type"] Lemma rgroup_rep_ext : forall st st' m b gh,
(forall p, conc st' p = conc st p) -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof. clear - segs.
intros st st' m b gh Hconc (w8 & H1 & H2).
assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
exists w8. rewrite Hconc, Hpw. auto.
Qed.

#[using="Type"] Lemma rshadow_rep_ext : forall st st' m rid r,
get_shadow st' rid = get_shadow st rid -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. clear - segs. intros st st' m rid r Hs [H1 H2]. split; [gw_exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_ctx_frame : forall st m a bs rid,
rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_ctx st m ->
rmrep_ctx st (write_to_mem m (wa a) bs).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved RATP. gw_expose_fam RATP.
intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5 & H6).
destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
unfold rmrep_ctx. gw_expose_fam RATP. split; [|split; [|split; [|split; [|split]]]].
- apply rw_cells_frame; [gw_exact H1|lia|lia|cbn; lia].
- apply u64arr_frame; [gw_exact H2|lia|lia|rewrite L1; cbn; lia].
- apply u64arr_frame; [gw_exact H3|lia|lia|rewrite L2; cbn; lia].
- apply u8arr_frame; [gw_exact H4|lia|lia|rewrite L3; cbn; lia].
- apply u8arr_frame; [gw_exact H5|lia|lia|rewrite L4; cbn; lia].
- apply rw_cells_frame; [gw_exact H6|lia|lia|cbn; lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_globals_frame : forall st m a bs rid,
rregions_wf st -> wr_in st rid a (Z.of_nat (length bs)) -> rmrep_globals m ->
rmrep_globals (write_to_mem m (wa a) bs).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m a bs rid WF WI (H1 & H2 & H3 & H4 & H5).
destruct (rwr_in_image st rid a _ WF WI) as (D & A0 & A1).
unfold rmrep_globals. (gw_expose_fam RATP; gw_expose_fam RGOT_SSP). split; [|split; [|split; [|split]]].
- apply rw_cells_frame; [gw_exact H1|lia|lia|cbn; lia].
- apply rw_cells_frame; [gw_exact H2|lia|lia|cbn; lia].
- apply rw_cells_frame; [gw_exact H3|lia|lia|cbn; lia].
- apply rw_cells_frame; [gw_exact H4|lia|lia|cbn; lia].
- apply rw_cells_frame; [gw_exact H5|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rarea_rep_frame : forall st m a bs ar0 ar,
rregions_wf st -> (s_areas st) !! ar0 = Some ar ->
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(conc st ar0 + 4096 <= a \/ a + Z.of_nat (length bs) <= conc st ar0) ->
rarea_rep st m ar0 ar -> rarea_rep st (write_to_mem m (wa a) bs) ar0 ar.
Proof. clear - segs.
intros st m a bs ar0 ar WF Har A0 A1 D (H1 & H2 & H3).
unfold rarea_rep. split; [|split].
- apply rw_cells_frame; [gw_exact H1|lia|lia|cbn; lia].
- intros k Hk. apply rw_cells_frame; [apply H2; gw_exact Hk|lia|lia|]. unfold AREA_HDR, META_SIZE, NSLOTS in *. cbn. lia.
- apply rw_cells_frame; [gw_exact H3|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rgroup_rep_frame : forall st m a bs b gh,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(conc st b + 9 <= a \/ a + Z.of_nat (length bs) <= conc st b) ->
rgroup_rep st m b gh -> rgroup_rep st (write_to_mem m (wa a) bs) b gh.
Proof. clear - segs.
intros st m a bs b gh A0 A1 D (w8 & H1 & H2). exists w8. split; [|gw_exact H2].
apply rw_cells_frame; [gw_exact H1|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rshadow_rep_frame : forall st m a bs rid r,
0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(r_base r + round_up_pg (r_len r) <= a \/ a + Z.of_nat (length bs) <= r_base r) ->
rshadow_rep st m rid r -> rshadow_rep st (write_to_mem m (wa a) bs) rid r.
Proof. clear - segs.
intros st m a bs rid r A0 A1 D [HW HB]. split; [apply wr_at_write; gw_exact HW|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Hb Hv]. split; [|gw_exact Hv].
apply bytes_at_write_other; [gw_exact Hb|lia|lia|cbn; lia].
Qed.

#[using="Type"] Lemma rarea_conc : forall st a ar, rregions_wf st -> (s_areas st) !! a = Some ar ->
exists r, (s_regions st) !! (fst a) = Some r /\ conc st a = r_base r + snd a
/\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len r) /\ snd a mod 4096 = 0 /\ r_kind r <> RKGroup
/\ 0 < r_base r /\ r_base r mod 4096 = 0 /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof. clear - segs.
intros st a ar (_ & WR & _ & WA & _) Ha. destruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

#[using="Type"] Lemma rgroup_conc : forall st b gh, rregions_wf st -> (s_groups st) !! b = Some gh ->
exists r, (s_regions st) !! (fst b) = Some r /\ conc st b = r_base r + snd b
/\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b + 16 <= round_up_pg (r_len r) /\ snd b mod 16 = 0
/\ 0 < r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling.
Proof. clear - segs.
intros st b gh (_ & WR & _ & _ & WG) Hb. destruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_wr8 : forall st m p v r,
rmrep st m -> ticks_ok st ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p < round_up_pg (r_len r) ->
(forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> ~ (snd b <= snd p < snd b + 9)) ->
0 <= v < 256 ->
rmrep (wr8 p v st) (write_to_mem m (wa (r_base r + snd p)) [b8 v]).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m p v r MR TK Hr Hk Ho Hgrp Hv.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof (lr_lo_group r Hk) as LRr.
assert (WI : wr_in st (fst p) (r_base r + snd p) (Z.of_nat (length [b8 v]))).
{ exists r. cbn. repeat split; auto; lia. }
destruct (rwr_in_image st _ _ _ WF WI) as (D & A0 & A1). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat] in D, A1.
assert (Hconc : forall q, conc (wr8 p v st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
-  gw_exact WF.
- eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|]. eapply rmrep_ctx_frame; eauto.
- eapply rmrep_globals_frame; eauto.
- intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [gw_exact Hconc|intros; reflexivity|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
apply rarea_rep_frame; [gw_exact WF|gw_exact Ha|lia|cbn; lia| |exact (AR a ar Ha)]. rewrite Ca. cbn.
destruct (N.eq_dec (fst a) (fst p)) as [E|NE].
+ rewrite E in Hra. rewrite Hr in Hra. inversion Hra; subst ra. congruence.
+ destruct (rwr_in_other st _ _ _ _ ra WF WI Hra NE); cbn in *; lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [gw_exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
apply rgroup_rep_frame; [lia|cbn; lia| |exact (GR b gh Hb)]. rewrite Cb. cbn.
destruct (N.eq_dec (fst b) (fst p)) as [E|NE].
+ rewrite E in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb. specialize (Hgrp b gh Hb E). lia.
+ destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
- intros rid r' Hr' Hk'. cbn in Hr'.
destruct (N.eq_dec rid (fst p)) as [E|NE].
+ subst rid. rewrite Hr in Hr'. inversion Hr'; subst r'.
destruct (SH (fst p) r Hr Hk) as [HW HB]. split; [apply wr_at_write; gw_exact HW|].
intros o v' Ho' Hc.
destruct (Z.eq_dec o (snd p)) as [->|NEo].
* rewrite cell_read_wr8_same in Hc by assumption. inversion Hc; subst v'. split; [|lia].
apply bytes_at_write_same; cbn; lia.
* rewrite cell_read_wr8_other in Hc by gw_exact NEo. destruct (HB o v' Ho' Hc) as [Hb Hv']. split; [|gw_exact Hv'].
apply bytes_at_write_other; [gw_exact Hb|lia|cbn; lia|cbn; lia].
+ eapply rshadow_rep_ext; [apply get_shadow_wr8_other; gw_exact NE|].
pose proof (lr_lo_group r' Hk') as LR'.
apply rshadow_rep_frame; [lia|cbn; lia| |exact (SH rid r' Hr' Hk')].
destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_wr16 : forall st m p v r,
rmrep st m -> ticks_ok st ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 2 <= round_up_pg (r_len r) ->
(forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 2 <= snd b \/ snd b + 9 <= snd p) ->
0 <= v < 65536 ->
rmrep (wr16 p v st) (write_to_mem m (wa (r_base r + snd p)) (le2 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m p v r MR TK Hr Hk Ho Ho2 Hg Hv.
rewrite le2_split by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 (v / 256)])
with (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p) + 1) [b8 (v / 256)]).
rewrite wa_succ. unfold wr16. rewrite (wr8_mod st p v).
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (unfold aadd; cbn; lia).
replace (Z.shiftr v 8) with (v / 256) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
assert (Hd : 0 <= v / 256 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
apply (rmrep_wr8 (wr8 p (v mod 256) st) _ (aadd p 1) (v / 256) r).
- apply rmrep_wr8; auto; [lia|]. intros b gh Hb E. specialize (Hg b gh Hb E). lia.
- apply ticks_ok_wr8. gw_exact TK.
- cbn. gw_exact Hr.
- gw_exact Hk.
- cbn. lia.
- intros b gh Hb E. cbn in Hb, E |- *. specialize (Hg b gh Hb E). lia.
- gw_exact Hd.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_meta_store4 : forall st m g (f : meta -> meta) (off : nat) v,
rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
(forall mr, cell_at (meta_cells st mr) off = Some (C4 (wz (match off with 24%nat => m_avail mr | _ => m_freed mr end)))) ->
(forall mr, cell_upd (meta_cells st mr) off (C4 (wz v)) = meta_cells st (f mr)) ->
(off = 24%nat \/ off = 28%nat) ->
rmrep (upd_meta g f st) (write_to_mem m (wa (conc st g + Z.of_nat off)) (le4 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m g f off v MR (a & ar & k & Ha & Hk & Eg) Hv Hat Hupd Hoff.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LRa.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
assert (WI : wr_in st (fst a) (conc st g + Z.of_nat off) (Z.of_nat (length (le4 (wz v))))).
{ exists ra. rewrite length_le4. cbn [Z.of_nat Pos.of_succ_nat Pos.to_nat]. split; [gw_exact Hra|]. rewrite HG, Ca. destruct Hoff; subst; cbn; lia. }
assert (Hconc : forall q, conc (upd_meta g f st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- gw_exact WF.
- eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|]. eapply rmrep_ctx_frame; eauto.
- eapply rmrep_globals_frame; eauto.
- intros a' ar' Ha'. cbn in Ha'.
assert (Hpw : forall q, pw (upd_meta g f st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (upd_meta g f st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra') as LRa'.
destruct (decide (a' = a)) as [->|NEa].
+
rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw. rewrite length_le4 in *.
split; [|split].
* apply rw_cells_frame; [gw_exact HD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
* intros k' Hk'. rewrite Hmc, get_meta_rec_upd.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st g + Z.of_nat off) with (conc st a + 24 + 40 * k + Z.of_nat off) by (rewrite HG; lia).
rewrite <- Hupd. unfold le4. change (Z_to_le_bytes 4 (bv_unsigned (wz v))) with (cbytes (C4 (wz v))).
eapply rw_cells_write; [ | apply Hat | reflexivity | exact I].
rewrite Eg. replace (24 + 40 * k) with (AREA_HDR + META_SIZE * k) by first [reflexivity | (cbn; lia)]. apply SL. unfold NSLOTS. lia.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply rw_cells_frame; [apply SL; lia|lia|rewrite length_le4; cbn in *; lia|].
rewrite length_le4, HG. cbn [cells_size meta_cells csize Nat.add length]. unfold AREA_HDR, META_SIZE. destruct Hoff; subst; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; nia.
* apply rw_cells_frame; [gw_exact PD|lia|rewrite length_le4; cbn in *; lia|]. rewrite length_le4, HG. cbn. destruct Hoff; subst; cbn; lia.
+
assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; gw_exact NE]. split; [gw_exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
eapply rarea_rep_ext; [gw_exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_upd.
replace (aptr_eqb (aadd a' (AREA_HDR + META_SIZE * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd, AREA_HDR, META_SIZE. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. unfold NSLOTS in *. lia. }
apply rarea_rep_frame; [gw_exact WF|gw_exact Ha'|lia|rewrite length_le4; cbn in *; lia| |exact (AR a' ar' Ha')].
rewrite length_le4, Ca', HG, Ca. cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat].
destruct PG as [NE|[E PG]].
* destruct (rwr_in_other st _ _ _ _ ra' WF WI Hra' NE); rewrite ?HG, ?Ca in *; cbn in *; lia.
* rewrite E, Hra in Hra'. inversion Hra'; subst ra'. destruct Hoff; subst; cbn; lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [gw_exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _). pose proof (lr_lo_group rb Kb) as LRb.
apply rgroup_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (GR b gh Hb)]. rewrite Cb, length_le4. cbn.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
destruct (rwr_in_other st _ _ _ _ rb WF WI Hrb NE); cbn in *; lia.
- intros rid r' Hr' Hk'. cbn in Hr'.
eapply rshadow_rep_ext; [reflexivity|]. pose proof (lr_lo_group r' Hk') as LR'.
apply rshadow_rep_frame; [lia|rewrite length_le4; cbn in *; lia| |exact (SH rid r' Hr' Hk')]. rewrite length_le4. cbn.
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
destruct (rwr_in_other st _ _ _ _ r' WF WI Hr' NE); cbn in *; lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_meta_set_avail : forall st m g v,
rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
rmrep (upd_meta g (m_set_avail v) st) (write_to_mem m (wa (conc st g + 24)) (le4 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros. change 24 with (Z.of_nat 24).
apply (rmrep_meta_store4 st m g (m_set_avail v) 24%nat v); auto; intros; reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_meta_set_freed : forall st m g v,
rmrep st m -> meta_slot st g -> 0 <= v < 2^32 ->
rmrep (upd_meta g (m_set_freed v) st) (write_to_mem m (wa (conc st g + 28)) (le4 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros. change 28 with (Z.of_nat 28).
apply (rmrep_meta_store4 st m g (m_set_freed v) 28%nat v); auto; intros; reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved"] Lemma rmrep_set_active : forall st m sc v,
rmrep st m -> 0 <= sc < 48 ->
rmrep (set_active sc v st) (write_to_mem m (wa ((RATP + 132048) + 8 * sc)) (le8 (pw st v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m sc v MR Hsc. pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & (G1 & G2 & G3 & G4 & G5) & AR & GR & SH).
assert (Hconc : forall q, conc (set_active sc v st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
pose proof (length_le8 (pw st v)) as L8.
gw_expose_fam RATP.
split; [|split; [|split; [|split; [|split]]]].
- gw_exact WF.
- unfold rmrep_ctx.
change (ctx_head_cells (set_active sc v st)) with (ctx_head_cells st).
change (usages (set_active sc v st)) with (usages st).
change (unmap_seqs (set_active sc v st)) with (unmap_seqs st).
change (bouncess (set_active sc v st)) with (bouncess st).
assert (E6 : ctx_tail_cells (set_active sc v st) = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx set_active upd_ctx c_seq c_brk set_active_map]. destruct (c_brk (s_ctx st)); reflexivity. }
rewrite E6, actives_set_active by lia. gw_expose_fam RATP.
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
+ apply rw_cells_frame; [gw_exact C1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ replace (145104 + 80 + 8 * sc) with ((145104 + 80) + 8 * sc) by lia. apply u64arr_write; [gw_exact C2| rewrite L1; lia].
+ apply u64arr_frame; [gw_exact C3|lia|rewrite L8; lia|rewrite L8, L2; lia].
+ apply u8arr_frame; [gw_exact C4|lia|rewrite L8; lia|rewrite L8, L3; lia].
+ apply u8arr_frame; [gw_exact C5|lia|rewrite L8; lia|rewrite L8, L4; lia].
+ apply rw_cells_frame; [gw_exact C6|lia|rewrite L8; lia|rewrite L8; cbn; lia].
- (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *). split; [|split; [|split; [|split]]].
+ apply rw_cells_frame; [gw_exact G1|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [gw_exact G2|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [gw_exact G3|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [gw_exact G4|lia|rewrite L8; lia|rewrite L8; cbn; lia].
+ apply rw_cells_frame; [gw_exact G5|lia|rewrite L8; lia|rewrite L8; cbn; lia].
- intros a ar Ha. cbn in Ha. eapply rarea_rep_ext; [gw_exact Hconc|intros; reflexivity|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
destruct WF as (_ & WR & _). destruct (WR _ ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rarea_rep_frame; [exact (proj1 MR)|gw_exact Ha|lia|rewrite L8; lia| |exact (AR a ar Ha)].
rewrite L8, Ca. pose proof (round_up_pg_ge (r_len ra)). cbn. lia.
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [gw_exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
destruct WF as (_ & WR & _). destruct (WR _ rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rgroup_rep_frame; [lia|rewrite L8; lia| |exact (GR b gh Hb)]. rewrite L8, Cb. cbn. lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct WF as (_ & WR & _). destruct (WR _ r' Hr') as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
apply rshadow_rep_frame; [lia|rewrite L8; lia| |exact (SH rid r' Hr' Hk')]. rewrite L8. cbn. lia.
Qed.

#[using="Type"] Lemma rshadow_rep_le : forall st st' m rid r,
shadow_le (get_shadow st rid) (get_shadow st' rid) -> rshadow_rep st m rid r -> rshadow_rep st' m rid r.
Proof. clear - segs. intros st st' m rid r [_ HL] [HW HB]. split; [gw_exact HW|]. intros o v Ho Hc. apply HB; auto. Qed.

#[using="Type"] Lemma rmrep_upd_shadow : forall st m rid f,
rmrep st m -> ticks_ok st ->
(shadow_le (get_shadow st rid) (f (get_shadow st rid)) /\ sh_ticks (f (get_shadow st rid)) (s_tick st)) ->
rmrep (upd_shadow rid f st) m /\ ticks_ok (upd_shadow rid f st).
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m rid f MR TK [HL HT]. pose proof MR as (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (upd_shadow rid f st) q = conc st q) by (intros; reflexivity).
assert (GS : forall rid', get_shadow (upd_shadow rid f st) rid' = if N.eqb rid' rid then f (get_shadow st rid) else get_shadow st rid').
{ intros rid'. rewrite (get_shadow_unfold (upd_shadow rid f st)). unfold upd_shadow, set_shadow. cbn [s_shadow].
destruct (N.eqb_spec rid' rid); [subst; rewrite lookup_insert_eq; reflexivity| rewrite lookup_insert_ne by congruence; reflexivity]. }
split.
- split; [gw_exact WF|]. split; [eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|gw_exact CX]|]. split; [gw_exact GL|].
split; [intros a ar Ha; eapply rarea_rep_ext; [gw_exact Hconc|intros; reflexivity|exact (AR a ar Ha)]|].
split; [intros b gh Hb; eapply rgroup_rep_ext; [gw_exact Hconc|exact (GR b gh Hb)]|].
intros rid' r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_le; [|exact (SH rid' r' Hr' Hk')].
rewrite GS. destruct (N.eqb_spec rid' rid); [subst; gw_exact HL| apply shadow_le_refl].
- destruct TK as [T1 T2]. destruct HT as [HT1 HT2]. split.
+ intros rid' sh u hl ch Hs Hu Hin. cbn [s_tick upd_shadow set_shadow] in *.
pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
destruct (N.eqb_spec rid' rid); [subst sh; eapply HT1; eauto|].
unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T1; eauto| subst; rewrite lookup_empty in Hu; discriminate].
+ intros rid' sh pg t Hs Hp. cbn [s_tick upd_shadow set_shadow] in *.
pose proof (GS rid') as G. rewrite (get_shadow_unfold (upd_shadow rid f st)) in G. cbn [s_shadow upd_shadow set_shadow] in G. rewrite Hs in G. cbn in G.
destruct (N.eqb_spec rid' rid); [subst sh; eapply HT2; eauto|].
unfold get_shadow in G. destruct (s_shadow st !! rid') eqn:E; cbn in G; [subst; eapply T2; eauto| subst; rewrite lookup_empty in Hp; discriminate].
Qed.

#[using="Type"] Lemma rmrep_havoc : forall st m p n, rmrep st m -> ticks_ok st -> rmrep (havoc p n st) m /\ ticks_ok (havoc p n st).
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m p n MR TK. unfold havoc. destruct (n <=? 0); [auto|].
apply rmrep_upd_shadow; [gw_exact MR|gw_exact TK|].
pose proof (sh_ticks_of_ticks_ok st (fst p) TK) as T0.
set (sh := get_shadow st (fst p)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
destruct ((snd p + 4095) / 4096 <? (snd p + n) / 4096).
- destruct (havoc_pages_le cells hav havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T0) as [L1 T1].
set (hav1 := if snd p <? (snd p + 4095) / 4096 * 4096 then havoc_units (snd p) ((snd p + 4095) / 4096 * 4096) (s_tick st) hav else hav).
assert (S1 : shadow_le (mkShadow cells hav havp) (mkShadow cells hav1 havp) /\ sh_ticks (mkShadow cells hav1 havp) (s_tick st)).
{ subst hav1. destruct (snd p <? _); [apply havoc_units_le; gw_exact T0| split; [apply shadow_le_refl|gw_exact T0]]. }
destruct S1 as [L2 T2].
set (hav2 := if (snd p + n) / 4096 * 4096 <? snd p + n then havoc_units ((snd p + n) / 4096 * 4096) (snd p + n) (s_tick st) hav1 else hav1).
assert (S2 : shadow_le (mkShadow cells hav1 havp) (mkShadow cells hav2 havp) /\ sh_ticks (mkShadow cells hav2 havp) (s_tick st)).
{ subst hav2. destruct (_ <? snd p + n); [apply havoc_units_le; gw_exact T2| split; [apply shadow_le_refl|gw_exact T2]]. }
destruct S2 as [L3 T3].
destruct (havoc_pages_le cells hav2 havp ((snd p + 4095) / 4096) ((snd p + n) / 4096) (s_tick st) T3) as [L4 T4].
split; [|gw_exact T4]. eapply shadow_le_trans; [gw_exact L2|]. eapply shadow_le_trans; [gw_exact L3|gw_exact L4].
- apply havoc_units_le. gw_exact T0.
Qed.

#[using="Type"] Lemma rmrep_hdr_havoc : forall st m b, rmrep st m -> ticks_ok st -> rmrep (hdr_havoc b st) m /\ ticks_ok (hdr_havoc b st).
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m b MR TK. unfold hdr_havoc.
apply rmrep_upd_shadow; [gw_exact MR|gw_exact TK|].
pose proof (sh_ticks_of_ticks_ok st (fst b) TK) as T0.
set (sh := get_shadow st (fst b)) in *. destruct sh as [cells hav havp]. cbn [r_cells r_hav r_havp].
apply hav_unit_step. gw_exact T0.
Qed.

#[using="RIMG_HI gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4"] Lemma rmrep_transport_high : forall st m m' W,
rmrep st m -> munch W m m' -> wmono segs m m' -> W_high W -> rmrep st m'.
Proof. clear - RIMG_HI gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (D : forall a n, a + n <= alloc_ceiling -> disjoint_from W a n) by (intros; apply W_high_disjoint; assumption).

assert (TC : forall A cs, rw_cells segs m A cs -> A + Z.of_nat (cells_size cs) <= alloc_ceiling -> rw_cells segs m' A cs).
{ intros A cs H HB. eapply rw_cells_transport; eauto. }
split; [gw_exact WF|]. split; [|split; [|split; [|split]]].
-  destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [gw_exact C1 | gw_expose_fam RATP; cbn; lia].
+ eapply u64arr_transport; eauto. apply D. unfold actives. rewrite map_length, seq_length. gw_expose_fam RATP; cbn; lia.
+ eapply u64arr_transport; eauto. apply D. unfold usages. rewrite map_length, seq_length. gw_expose_fam RATP; cbn; lia.
+ eapply u8arr_transport; eauto. apply D. unfold unmap_seqs. rewrite map_length, seq_length. gw_expose_fam RATP; cbn; lia.
+ eapply u8arr_transport; eauto. apply D. unfold bouncess. rewrite map_length, seq_length. gw_expose_fam RATP; cbn; lia.
+ apply TC; [gw_exact C6 | gw_expose_fam RATP; cbn; lia].
-  destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
+ apply TC; [gw_exact G1 | gw_expose_fam RATP; cbn; lia].
+ apply TC; [gw_exact G2 | gw_expose_fam RATP; cbn; lia].
+ apply TC; [gw_exact G3 | gw_expose_fam RATP; cbn; lia].
+ apply TC; [gw_exact G4 | gw_expose_fam RGOT_SSP; cbn; lia].
+ apply TC; [gw_exact G5 | gw_expose_fam RATP; cbn; lia].
-  intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
split; [|split].
+ apply TC; [gw_exact A1 | cbn; lia].
+ intros k Hk. apply TC; [apply A2; gw_exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
+ apply TC; [gw_exact A3 | cbn; lia].
-  intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Sb0 & Sb1 & SbL & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
apply TC; [gw_exact R | cbn; lia].
-  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
destruct (WR rid r Hr) as (B0 & BAL & L0 & BC & _). unfold alloc_ceiling in BC.
split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply bytes_at_transport; eauto. apply D. cbn. lia.
Qed.

#[using="Type"] Lemma rmrep_set_tick : forall st m t, rmrep st m -> rmrep (set_tick t st) m.
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m t (WF & CX & GL & AR & GR & SH).
split; [gw_exact WF|]. split; [|split; [gw_exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity | intros; reflexivity | gw_exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [intros; reflexivity | intros; reflexivity | exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [intros; reflexivity | exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity | exact (SH rid r Hr Hk)].
Qed.

#[using="ref_wview_overlay ref_mrd_overlay"] Lemma rwr_at_bytes_exist : forall m a n,
wr_at segs m a n -> 0 <= n -> (a + n <= 0x10000 \/ RIMG_HI <= a) ->
exists bs, length bs = Z.to_nat n /\ bytes_at segs m a bs.
Proof. clear - ref_wview_overlay ref_mrd_overlay segs RIMG_HI. gw_expose_win.
intros m a n (A0 & An & W) Hn Himg.
assert (G : forall i, 0 <= i < n -> exists b, mrd segs m (wa (a + i)) = Some b).
{ intros i Hi. specialize (W i Hi). rewrite ref_wview_overlay in W by (rewrite wa_unsigned by lia; lia).
rewrite ref_mrd_overlay by (rewrite wa_unsigned by lia; lia).
destruct (m (wa (a + i))) as [b|]; [exists b; reflexivity| exfalso; apply W; reflexivity]. }

assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\ bytes_at segs m (a + (n - Z.of_nat k)) bs).
{ induction k as [|k IH]; intros Hk.
- exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
- destruct (IH ltac:(lia)) as (bs & L & B). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
exists (b :: bs). split; [cbn; lia|].
change (b :: bs) with ([b] ++ bs). apply bytes_at_app. split.
+ split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [|lia]. cbn. rewrite Z.add_0_r. gw_exact Hb.
+ cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. replace (a + (n - Z.of_nat (S k)) + 1) with (a + (n - Z.of_nat k)) by lia. gw_exact B. }
destruct (REC (Z.to_nat n) ltac:(lia)) as (bs & L & B). exists bs. split; [gw_exact L|].
replace (a + (n - Z.of_nat (Z.to_nat n))) with a in B by lia. gw_exact B.
Qed.

End RC__1.

End G.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenSF GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base multf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 1792.

Definition land_M32_small := Q91D.land_M32_small segs base CODE BASE4 BASER.
Definition land_ones_l := Q91D.land_ones_l segs base CODE BASE4 BASER.
Definition sra63_neg := Q91D.sra63_neg segs base CODE BASE4 BASER.
Definition sra63_negw := Q91D.sra63_negw segs base CODE BASE4 BASER.
Definition sra63_pos := Q91D.sra63_pos segs base CODE BASE4 BASER.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

#[using="CODE BASE4 BASER"] Lemma sra63_K_neg : forall x, 9223372036854775808 <= Z.land x 18446744073709551615 ->
Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = -1.
Proof.
intros x K. rewrite land_W64 in K. rewrite <- Z_to_bv_mod64. apply sra63_negw.
pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia.
Qed.
#[using="CODE BASE4 BASER"] Lemma sra63_K_pos : forall x, Z.land x 18446744073709551615 < 9223372036854775808 ->
Z.shiftr (bv_signed (Z_to_bv 64 x)) 63 = 0.
Proof.
intros x K. rewrite land_W64 in K. rewrite <- Z_to_bv_mod64. apply sra63_pos.
pose proof (Z.mod_pos_bound x (2^64) ltac:(lia)). lia.
Qed.

#[using="CODE BASE4 BASER"] Lemma ndr_lt64 : forall hi lo c,
0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 -> clz128_mirror hi lo = c ->
9223372036854775808 <= Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 ->
nd_hi hi lo = Z.lor (Z.land (hi ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615)
(Z.land ((lo ≫ 1) ≫ Z.land (Z.lxor (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295) 18446744073709551615) 63) 18446744073709551615)
/\ nd_lo hi lo = Z.land 18446744073709551615 (Z.land (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615).
Proof.
intros hi lo c Hhi Hlo Hc E K2.
unfold nd_hi, nd_lo, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
change b2z with Z.b2z. unfold_sf. zb_fold_lits.
replace (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 - 64) with (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) by lia.
decide_tests_b. split; [| reflexivity]. strip_lands. reflexivity.
Qed.
#[using="CODE BASE4 BASER"] Lemma ndr_ge64 : forall hi lo c,
0 <= hi < 2^64 -> 0 <= lo < 2^64 -> 0 <= c < 2^64 -> clz128_mirror hi lo = c ->
Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) 18446744073709551615 < 9223372036854775808 ->
nd_hi hi lo = Z.land (lo ≪ Z.land (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295) 63) 18446744073709551615
/\ nd_lo hi lo = Z.land 0 (Z.land (lo ≪ Z.land (Z.land (c - 15) 18446744073709551615) 63) 18446744073709551615).
Proof.
intros hi lo c Hhi Hlo Hc E K2.
unfold nd_hi, nd_lo, norm_denormal. rewrite E. cbv beta zeta iota delta [shl128_mirror].
change b2z with Z.b2z. unfold_sf. zb_fold_lits.
replace (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 - 64) with (Z.land (Z.land (c - 15) 18446744073709551615) 4294967295 + -64) by lia.
decide_tests_b. split; reflexivity.
Qed.

Section Norm.
Variables (sp : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -80)).
Notation ONES := (Z_to_bv 64 18446744073709551615).
Notation M48 := (Z_to_bv 64 281474976710655).

Ltac norm_tail HQ E clz sh n32 hi lo :=
let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
zstep; if_cases K2; zify_cond K2;
[ rewrite (sra63_K_neg _ K2); do 9 zstep; subst n32 sh;
destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
rewrite <- E1, <- E2; rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ
| rewrite (sra63_K_pos _ K2); do 6 zstep; subst n32 sh;
destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];

match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
rewrite <- E1, <- E2; rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ ].

#[using="CODE BASE4 BASER"] Lemma LnormA : forall (Q : machine_state -> Prop) ra gp tp t0 (h : Z) t2 s0 s1 wlo a1' a2' a3' a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t5 t6
(F : bvmap 5 word) fc (m1 : word -> option byte),
(0 <= h < 2^64)%Z ->
(forall y13 y30 y31 y8 y9,
evt segs Q
(MS (mkR ra spw gp tp t0 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) t2 y8 y9
(Z_to_bv 64 (16 - nd_clz h (bv_unsigned wlo))) a1' a2' y13 a4 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
(Z_to_bv 64 (Z.shiftr (nd_hi h (bv_unsigned wlo)) 32)) (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y30 y31)
F (Z_to_bv 64 (base + 0x5f4)) fc None m1 (seg_rom segs))) ->
evt segs Q
(MS (mkR ra spw gp tp t0 (Z_to_bv 64 h) t2 s0 s1 wlo a1' a2' a3' a4 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 wlo t5 t6)
F (Z_to_bv 64 (base + 0x3e4)) fc None m1 (seg_rom segs)).
Proof.
intros until m1. intros Rh HQ.
pose_word_ranges.
zstep. zstep. if_cases K; zify_cond K.
-
set (x := bv_unsigned wlo).
do 6 zstep. model_reg 28 x1 (Z.lor x (Z.shiftr x 1)).
do 6 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
do 10 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
do 4 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
do 3 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
do 2 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
zstep. decide_tests_b. change (Z.b2z true) with 1. zb_fold_lits.
model_reg 13 clz (Z.lor (clz64_mirror x) 64).
pose proof (clz128_hi_z h x K) as E. fold clz in E.
zstep. model_reg 30 sh (Z.land (clz - 15) 18446744073709551615).
do 3 zstep. model_reg 31 n32 (Z.land sh 4294967295).
do 2 zstep. subst x. norm_tail HQ E clz sh n32 h (bv_unsigned wlo).
- zstep.
do 6 zstep. model_reg 28 x1 (Z.lor h (Z.shiftr h 1)).
do 6 zstep. model_reg 28 x2 (Z.lor x1 (Z.shiftr x1 2)).
do 10 zstep. model_reg 28 x3 (Z.lor x2 (Z.shiftr x2 4)).
do 2 zstep. model_reg 28 x4 (Z.lor x3 (Z.shiftr x3 8)).
do 2 zstep. model_reg 28 x5 (Z.lor x4 (Z.shiftr x4 16)).
do 2 zstep. model_reg 28 x6 (Z.lor x5 (Z.shiftr x5 32)).
do 1 zstep. model_reg 28 y (Z.lxor x6 18446744073709551615).
do 4 zstep. model_reg 28 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
do 4 zstep. model_reg 28 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
do 3 zstep. model_reg 28 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
do 2 zstep. model_reg 28 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
zstep. decide_tests_b. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
model_reg 13 clz (clz64_mirror h).
pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
zstep. model_reg 30 sh (Z.land (clz - 15) 18446744073709551615).
do 3 zstep. model_reg 31 n32 (Z.land sh 4294967295).
do 2 zstep. norm_tail HQ E clz sh n32 h (bv_unsigned wlo).
Qed.

Ltac norm_tailB HQ E clz sh n32 hi lo sc1 :=
let K2 := fresh "K2" in let E1 := fresh "E" in let E2 := fresh "E" in
zstep; if_cases K2; zify_cond K2;
[ do 5 zstep; do 6 zstep; rewrite (sra63_K_neg _ K2); zb_fold_lits; subst n32 sh;
destruct (ndr_lt64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
rewrite <- E1, <- E2
| do 2 zstep; do 6 zstep; rewrite (sra63_K_pos _ K2); zb_fold_lits; subst n32 sh;
destruct (ndr_ge64 hi lo clz ltac:(zrange) ltac:(zrange) ltac:(assumption) E K2) as [E1 E2];
match type of E1 with _ = Z.land ?v _ => rewrite <- (Z_to_bv_land64 v) end;
rewrite <- E1, <- E2 ];
match goal with |- context [Z_to_bv 64 (Z.land sc1 18446744073709551615 - clz + 16)] =>
replace (Z_to_bv 64 (Z.land sc1 18446744073709551615 - clz + 16)) with (Z_to_bv 64 (sc1 - clz + 16))
by (apply Z_to_bv_eqm; rewrite land_W64; Z.div_mod_to_equations; lia) end;
rewrite <- nd_clz_eq in E; rewrite <- E; eapply HQ.

#[using="CODE BASE4 BASER"] Lemma LnormB : forall (Q : machine_state -> Prop) ra gp tp t0 t1 (h sc1 : Z) s0 s1 wlo a1' y13 y14 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m1 : word -> option byte),
(0 <= h < 2^64)%Z -> (-1024 <= sc1 <= 1024)%Z ->
(forall y13' y14' y30 y31 y8 y9,
evt segs Q
(MS (mkR ra spw gp tp t0 t1 (Z_to_bv 64 (nd_hi h (bv_unsigned wlo))) y8 y9
(Z_to_bv 64 (sc1 - nd_clz h (bv_unsigned wlo) + 16)) a1' (Z_to_bv 64 (nd_lo h (bv_unsigned wlo))) y13' y14' ONES M48 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 y30 y31)
F (Z_to_bv 64 (base + 0x80)) fc None m1 (seg_rom segs))) ->
evt segs Q
(MS (mkR ra spw gp tp t0 t1 (Z_to_bv 64 h) s0 s1 (Z_to_bv 64 sc1) a1' wlo y13 y14 ONES M48 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x5fc)) fc None m1 (seg_rom segs)).
Proof.
intros until m1. intros Rh Rsc HQ.
pose_word_ranges.
do 2 zstep. zstep. if_cases K; zify_cond K.
-
set (x := bv_unsigned wlo).
do 5 zstep. model_reg 14 x1 (Z.lor x (Z.shiftr x 1)).
do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
assert (Ec4 : c4 = clz64_mirror x). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
zstep. decide_tests_b. change (Z.b2z true) with 1. zb_fold_lits.
model_reg 13 clz (Z.lor (clz64_mirror x) 64).
pose proof (clz128_hi_z h x K) as E. fold clz in E.
zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
do 2 zstep. model_reg 31 n32 (Z.land sh 4294967295).
zstep. subst x. norm_tailB HQ E clz sh n32 h (bv_unsigned wlo) sc1.
- zstep.
do 5 zstep. model_reg 14 x1 (Z.lor h (Z.shiftr h 1)).
do 5 zstep. model_reg 14 x2 (Z.lor x1 (Z.shiftr x1 2)).
do 8 zstep. model_reg 14 x3 (Z.lor x2 (Z.shiftr x2 4)).
do 2 zstep. model_reg 14 x4 (Z.lor x3 (Z.shiftr x3 8)).
do 2 zstep. model_reg 14 x5 (Z.lor x4 (Z.shiftr x4 16)).
do 2 zstep. model_reg 14 x6 (Z.lor x5 (Z.shiftr x5 32)).
do 1 zstep. model_reg 14 y (Z.lxor x6 18446744073709551615).
do 4 zstep. model_reg 14 c1 (Z.land (y - (Z.land (Z.shiftr y 1) 6148914691236517205)) 18446744073709551615).
do 6 zstep. model_reg 14 c2 (Z.land ((Z.land c1 3689348814741910323) + (Z.land (Z.shiftr c1 2) 3689348814741910323)) 18446744073709551615).
do 4 zstep. model_reg 14 c3 (Z.land (Z.land (c2 + (Z.shiftr c2 4)) 18446744073709551615) 1085102592571150095).
do 3 zstep. model_reg 14 c4 (Z.shiftr (Z.land (c3 * 72340172838076673) 18446744073709551615) 56).
assert (Ec4 : c4 = clz64_mirror h). { symmetry. cbv delta [clz64_mirror]. sf_vocab. fold_model_lets. reflexivity. }
zstep. decide_tests_b. change (Z.b2z false) with 0. zb_fold_lits. rewrite Z.lor_0_r.
model_reg 13 clz (clz64_mirror h).
pose proof (clz128_hi_nz h (bv_unsigned wlo) K) as E. fold clz in E.
zstep. model_reg 14 sh (Z.land (clz - 15) 18446744073709551615).
do 2 zstep. model_reg 31 n32 (Z.land sh 4294967295).
zstep. norm_tailB HQ E clz sh n32 h (bv_unsigned wlo) sc1.
Qed.

End Norm.

End G.
