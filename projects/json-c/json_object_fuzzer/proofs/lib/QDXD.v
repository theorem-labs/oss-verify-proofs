(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDM_c1 Q2qa QVbl QQLG Q91D Q8QT QCa8 QZAa Lib.CodeAt Lib.StepGen Lib.StepGenSF Lib.GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QnDM_c1 Q2qa.
Import QVbl.Mq0.
Import QQLG.Mq0.
Import Q91D.Mq0.
Import Q8QT.Mq0.
Import QCa8.Mq0.

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

Definition add_Lret := QQLG.Mq0.add_Lret segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

Definition addtf3_post := Eval cbv beta delta [QCa8.Mq0.addtf3_post] in (QCa8.Mq0.addtf3_post segs).
Definition add_L184 := QCa8.Mq0.add_L184 segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.
Definition add_L0d4 := QCa8.Mq0.add_L0d4 segs base CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Ltac reg_eq_ev := first [ reflexivity | (symmetry; apply Z_to_bv_bv_unsigned) | apply Z_to_bv_bv_unsigned ].
Ltac tree_eq_ev :=
first [ reflexivity
| lazymatch goal with
| |- TNode _ _ _ = TNode _ _ _ => f_equal; tree_eq_ev
| |- Some _ = Some _ => f_equal; reg_eq_ev
| |- _ => reg_eq_ev
end ].
Ltac ms_eq_ev :=
lazymatch goal with
| |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => unfold mkR; f_equal; [ tree_eq_ev | reflexivity .. ]
end.

Ltac jump L := eapply evt_eq; [ | eapply L ]; first [ ms_eq_ev | finL ].

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

Lemma add_LM1 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
(0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
r = add_M1 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
evt segs (POST r) (ST (base + 0x80) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 HR. subst r. unfold add_M1. pose_word_ranges.
zstep. zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
-
do 3 zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
+
unfold add_M2. unfold_sfw.
do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
* jump add_L184.
* jump add_L0d4.
+ unfold add_M2. unfold_sfw.
do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
* jump add_L0d4.
* jump add_L184.
- do 3 zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
+
unfold add_M2. unfold_sfw.
do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
* jump add_L0d4.
* jump add_L184.
+ unfold add_M2. unfold_sfw.
do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
* jump add_L184.
* jump add_L0d4.
Qed.

Lemma add_L108 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
(0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
r = add_S3 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
evt segs (POST r) (ST (base + 0xf0) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S3. unfold_sfw. rewrite ?b2z_Zb2z.
do 4 zstep. zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
-
zstep. zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
+  jump add_Lret.
+ zstep. zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
*
zstep. zstep. if_cases Kbz; zify_cond Kbz; decide_tests_b.
--  jump add_Lret.
--  do 3 zstep. jump add_Lret.
* zstep. zstep. if_cases Kbz; zify_cond Kbz; decide_tests_b.
--  eapply add_LM1; finL.
--  do 3 zstep. jump add_Lret.
-
do 6 zstep. name_reg 9%Z xw.
zstep. rewrite (ltb1_eqb0 xw) by zrange_nonneg. zstep. if_cases Kx; zify_cond Kx; decide_tests_b.
+
zstep. replace (Z_to_bv 64 (Z.b2z false + -1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
change (Z.land (Z.b2z false - 1) 18446744073709551615) with 18446744073709551615%Z.
do 3 zstep. jump add_Lret.
+
zstep. zstep. zstep. replace (Z_to_bv 64 (Z.b2z true + -1)) with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; reflexivity).
change (Z.land (Z.b2z true - 1) 18446744073709551615) with 0%Z.
do 3 zstep. jump add_Lret.
Qed.

Lemma add_L0f4 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
(0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
r = add_S2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
evt segs (POST r) (ST (base + 0xdc) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S2. unfold_sfw. rewrite ?b2z_Zb2z.
zstep. zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
-
zstep. rewrite (ltb1_eqb0 (bv_unsigned wb0)) by lia. zstep. if_cases Kbl; zify_cond Kbl; decide_tests_b.
+  eapply add_L108; finL.
+  do 4 zstep. jump add_Lret.
- zstep. zstep. if_cases Kbl; zify_cond Kbl; decide_tests_b.
+  do 4 zstep. jump add_Lret.
+ eapply add_L108; finL.
Qed.

Lemma add_LS : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
(0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
r = add_S (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
evt segs (POST r) (ST (base + 0xc8) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 HR. subst r. pose_word_ranges.
unfold add_S. unfold_sfw. rewrite ?b2z_Zb2z.
zstep. zstep. zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
-
zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. if_cases Kal; zify_cond Kal; decide_tests_b.
+  eapply add_L0f4; finL.
+  do 5 zstep. jump add_Lret.
- zstep. zstep. if_cases Kal; zify_cond Kal; decide_tests_b.
+  do 5 zstep. jump add_Lret.
+ eapply add_L0f4; finL.
Qed.

Lemma add_L074 : forall x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
(0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
r = add_top2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
evt segs (POST r) (ST (base + 0x5c) fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 (Z_to_bv 64 9223653511831486464) (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_top2. unfold_sfw. rewrite ?b2z_Zb2z.
zstep. model_reg 12%Z tb (Z.land (bAbsHi + 9223653511831486464) W64).
zstep. zstep. zstep. if_cases Kt; zify_cond Kt; decide_tests_b.
-
zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
+  eapply add_LS; finL.
+ eapply add_LM1; finL.
- zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
+ eapply add_LM1; finL.
+ zstep. eapply add_LS; finL.
Qed.

Lemma add_L034 : forall x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (r : Z),
r = add_top (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) ->
evt segs (POST r) (ST (base + 0x1c) fc ra x5 x6 x7 x8 x9 wa0 wa1 wb0 wb1 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof using CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec FR FRM MI MU STK WM.
intros until r. intros HR. subst r. pose_word_ranges. unfold add_top. unfold_sfw. rewrite ?b2z_Zb2z.
do 5 zstep. name_reg 13%Z aAbsHi.
zstep. zstep. zstep. if_cases K0; zify_cond K0; decide_tests_b.
-
zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. name_reg 14%Z bAbsHi.
zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
+  eapply add_LS; finL.
+ eapply add_L074; finL.
- zstep. zstep. zstep. name_reg 14%Z bAbsHi.
zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
+ eapply add_L074; finL.
+ zstep. eapply add_LS; finL.
Qed.
End Proofs.

#[using="CODE BASE4 BASER fe_getround_spec fe_raise_inexact_spec"] Lemma addtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte),
stk segs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
mem_inv segs m ->
frm0 fc ->
evt segs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
(f128_add (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x0)) fc None m (seg_rom segs)).
Proof.
intros until m. intros ST MI FRM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
assert (SPLO : (48 <= bv_unsigned sp)%Z) by (destruct ST as [? _]; lia).
pose_word_ranges.
rewrite f128_add_split by lia.
carve_frame 48%nat ST.
do 7 zstep.
eapply add_L034; try eassumption; reflexivity.
Qed.

End G.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg Qy5Y Q4J3 QytA Qnxq QJE4 QZAi QUZl Q7S0 Ql2m QGeV Q6q3 Lib.StepGenX Lib.StepGenX2 Lib.GwFold G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq.
Export QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
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

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_1).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2)).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rreserved_disjoint1 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint1) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint1)).
Definition rmrep_wr8 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr8) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr8)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).
Definition rpres_except_of_munch : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_of_munch) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_of_munch)).
Definition rpres_except_bytes_at : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_bytes_at) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_bytes_at)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_wr32 : forall st m p v r,
rmrep st m -> ticks_ok st ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> 0 <= snd p -> snd p + 4 <= round_up_pg (r_len r) ->
(forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd p + 4 <= snd b \/ snd b + 9 <= snd p) ->
0 <= v < 2^32 ->
rmrep (wr32 p v st) (write_to_mem m (wa (r_base r + snd p)) (le4 (wz v)))
/\ ticks_ok (wr32 p v st).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved.
intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
rewrite le4_bytes by lia.
change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
(wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
(wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
rewrite !wa_succ.
unfold wr32.
assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
{ split; [|apply ticks_ok_wr8; gw_exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S1 as [M1 T1].
assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
/\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
{ split; [|apply ticks_ok_wr8; gw_exact T1].
replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [gw_exact Hr| gw_exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S2 as [M2 T2].
assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
(write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
/\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
{ split; [|apply ticks_ok_wr8; gw_exact T2].
replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [gw_exact Hr| gw_exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
destruct S3 as [M3 T3].
split; [|apply ticks_ok_wr8; gw_exact T3].
replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [gw_exact Hr| gw_exact Hk| lia| |lia].
intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none"] Lemma rrdv_mem : forall st stx m (q : aptr) r (x : byte),
rmrep st m -> get_shadow stx (fst q) = get_shadow st (fst q) -> (forall q', conc stx q' = conc st q') ->
(s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
bytes_at segs m (r_base r + snd q) [x] ->
rdv pans_mem m stx q = bv_unsigned x.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_1 LAY_win_2 LAY_ref_reserved ref_seg_rom_none segs.
intros st stx m q r x MR Hsh Hconc Hr Hk Ho Hb.
unfold rdv. rewrite Hsh. destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
- destruct (rmrep_shadow_read st m (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
pose proof (bytes_at_read segs m _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
- unfold pans_mem. rewrite Hconc, (conc_region' st q r Hr).
destruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
unfold mrd in HB |- *.
destruct (m (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
exfalso. pose proof MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). unfold alloc_ceiling in RBC.
pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="Type"] Lemma rauxv_ok_pres : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, (RATP + 131736) <= a < (RATP + 131744) -> ~ C a) ->
rauxv_ok m' B.
Proof. clear - RATP. gw_expose_fam RATP.
intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|gw_exact H]]].
- eapply rpres_except_rw_cells; [gw_exact HP| gw_exact C1|]. cbn. intros a Ha. apply HC. lia.
- eapply rpres_except_bytes_at; [gw_exact HP| gw_exact A1|]. intros a Ha. apply HB. lia.
- eapply rpres_except_bytes_at; [gw_exact HP| gw_exact A2|]. intros a Ha. apply HB. lia.
Qed.

#[using="Type"] Lemma rpres_write : forall (C : Z -> Prop) m0 m a bs,
rpres_except C m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
(forall x, a <= x < a + Z.of_nat (length bs) -> C x) ->
rpres_except C m0 (write_to_mem m (wa a) bs).
Proof. clear - segs.
intros C m0 m a bs HP Ha Hl HC x Hx HCx.
destruct (HP x Hx HCx) as [E W].
assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
{ rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
exfalso. apply HCx, HC. lia. }
split.
- rewrite NE. gw_exact E.
- intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

#[using="Type"] Lemma rpres_except_munch_frame : forall C m0 m m' W,
rpres_except C m0 m -> munch W m m' -> wmono segs m m' ->
(forall x, 0 <= x < 2^64 -> ~ C x -> outside W x) -> rpres_except C m0 m'.
Proof. clear - segs.
intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [gw_exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.

End RC__1.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1.
Export Qy5Y.Mq6.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
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

Notation gw_tbl_0 := tt.

Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rmrep_ctx_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_ctx_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_ctx_ext)).
Definition rarea_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_rep_ext)).
Definition rgroup_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_rep_ext)).
Definition rshadow_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rshadow_rep_ext) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rshadow_rep_ext)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rwr_at_bytes_exist : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rwr_at_bytes_exist) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rwr_at_bytes_exist)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ | clear - hs segs RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay].

Section RC__1.

Definition rrepfoot (st : mstate) (a : Z) : Prop :=
((RATP + 131968) <= a < (RATP + 132896)) \/ ((RATP + 131960) <= a < (RATP + 131964)) \/ ((RATP + 131731) <= a < (RATP + 131732)) \/ ((RATP + 131776) <= a < (RATP + 131784))
\/ (exists ak ar, (s_areas st) !! ak = Some ar /\ conc st ak <= a < conc st ak + 4096)
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v)
\/ (RGOT_SSP <= a < (RGOT_SSP + 8)) \/ ((RATP + 131696) <= a < (RATP + 131704)).

#[using="Type"] Lemma rrepfoot_ctx st a : (RATP + 131968) <= a < (RATP + 132896) -> rrepfoot st a. Proof. clear - RATP st a. intros; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_mlock st a : (RATP + 131960) <= a < (RATP + 131964) -> rrepfoot st a. Proof. clear - RATP st a. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_nl st a : (RATP + 131731) <= a < (RATP + 131732) -> rrepfoot st a. Proof. clear - RATP st a. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_pgsz st a : (RATP + 131776) <= a < (RATP + 131784) -> rrepfoot st a. Proof. clear - RATP st a. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. clear - st a ak ar RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. intros; do 4 right; left. exists ak, ar. auto. Qed.
#[using="Type"] Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. clear - st a b gh RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. intros; do 5 right; left. exists b, gh. auto. Qed.
#[using="Type"] Lemma rrepfoot_known st a rid r v : (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
r_base r <= a < r_base r + round_up_pg (r_len r) -> cell_read (get_shadow st rid) (a - r_base r) = Known v -> rrepfoot st a.
Proof. clear - st a rid r v RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. intros; do 6 right; left. exists rid, r, v. auto. Qed.
#[using="Type"] Lemma rrepfoot_got st a : RGOT_SSP <= a < (RGOT_SSP + 8) -> rrepfoot st a. Proof. clear - RGOT_SSP st a. intros; do 7 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_guard st a : (RATP + 131696) <= a < (RATP + 131704) -> rrepfoot st a. Proof. clear - RATP st a. intros; do 8 right; assumption. Qed.

#[using="Type"] Lemma rbytes_at_agree : forall m m' A bs,
bytes_at segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof. clear - segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros m m' A bs (H0 & H1 & HB) AG. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. gw_exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree : forall m m' A cs,
rw_cells segs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> wmono segs m m' -> rw_cells segs m' A cs.
Proof. clear - segs.
intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [gw_exact Hwf|]|].
- eapply rbytes_at_agree; [gw_exact HB|]. rewrite cells_bytes_length by assumption. gw_exact AG.
- eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree : forall m m' A ws,
u64arr segs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> wmono segs m m' -> u64arr segs m' A ws.
Proof. clear - segs.
intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
eapply rbytes_at_agree; [gw_exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. gw_exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree : forall m m' A bs,
u8arr segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> wmono segs m m' -> u8arr segs m' A bs.
Proof. clear - segs. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

#[using="RNG_RATP"] Lemma rmrep_transport_unowned : forall st m m' W,
rmrep st m -> munch W m m' -> wmono segs m m' -> ivs_avoid W (rrepfoot st) -> rmrep st m'.
Proof. clear - RNG_RATP segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' W (WF & CX & GL & AR & GR & SH) MU WM HW.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (TC : forall A cs, rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells segs m' A cs).
{ intros A cs H HP. pose proof (rw_cells_bound segs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
split; [gw_exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (u64arr_bound segs m _ _ C2) as B2. pose proof (u64arr_bound segs m _ _ C3) as B3.
pose proof (u8arr_bound segs m _ _ C4) as B4. pose proof (u8arr_bound segs m _ _ C5) as B5.
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [gw_exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. gw_expose_fam RATP. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. gw_expose_fam RATP. lia.
- destruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
+ apply TC; [gw_exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. gw_expose_fam RATP. lia.
+ apply TC; [gw_exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. gw_expose_fam RGOT_SSP. lia.
+ apply TC; [gw_exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. gw_expose_fam RATP. lia.
- intros ak ar Ha. destruct (AR ak ar Ha) as (A1 & A2 & A3).
split; [|split].
+ apply TC; [gw_exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [gw_exact Ha|lia].
+ intros k Hk. apply TC; [apply A2; gw_exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [gw_exact Ha|lia].
+ apply TC; [gw_exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [gw_exact Ha|lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
apply TC; [gw_exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [gw_exact Hb|lia].
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
+ eapply wr_at_transport; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
pose proof Bt as (B0 & B1 & _). cbn in B1.
eapply rbytes_at_agree; [gw_exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. gw_exact Hc.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_put_meta_frame : forall st m m' g mr',
rmrep st m -> meta_slot st g ->
munch [(conc st g, conc st g + META_SIZE)] m m' -> wmono segs m m' ->
rw_cells segs m' (conc st g) (meta_cells st mr') ->
rmrep (put_meta g mr' st) m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' g mr' MR (a & ar & k & Ha & Hk & Eg) MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
pose proof (round_up_pg_ge (r_len ra)) as RU.

assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
assert (TC : forall A cs, rw_cells segs m A cs ->
(A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells segs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
split; [|split; [|split; [|split; [|split]]]].
- gw_exact WF.
- eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|].
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. gw_expose_fam RATP.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
+ apply TC; [gw_exact C1 | cbn; lia].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
+ eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
+ eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
+ apply TC; [gw_exact C6 | cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5). (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
- intros a' ar' Ha'. cbn in Ha'.
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
destruct (decide (a' = a)) as [->|NEa].
+ rewrite Ha in Ha'. inversion Ha'; subst ar'.
destruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
split; [|split].
* apply TC; [gw_exact HD| cbn; lia].
* intros k' Hk'. rewrite Hmc, get_meta_rec_put.
destruct (Z.eq_dec k' k) as [->|NEk].
-- rewrite <- Eg, aptr_eqb_refl.
replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). gw_exact CH.
-- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
* apply TC; [gw_exact PD| cbn; lia].
+ assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; gw_exact NE]. split; [gw_exact E|].
assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. nia. }
assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
{ rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
- rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
eapply rarea_rep_ext; [gw_exact Hconc| |].
{ intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
destruct PG as [NE|[E PG]].
- rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
- rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
destruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
* apply TC; [gw_exact HD| cbn; lia].
* intros k0 Hk0. apply TC; [apply SL; gw_exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
* apply TC; [gw_exact PD| cbn; lia].
- intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [gw_exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
apply TC; [gw_exact R|]. cbn. rewrite Cb, HG, Ca.
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
- intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [|exact I].
assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rmrep_ctx_frame' : forall st st' m m',
rmrep st m -> munch [((RATP + 131968), (RATP + 132896))] m m' -> wmono segs m m' ->
s_regions st' = s_regions st -> s_metas st' = s_metas st -> s_areas st' = s_areas st ->
s_groups st' = s_groups st -> s_shadow st' = s_shadow st -> s_reserved st' = s_reserved st ->
rmrep_ctx st' m' -> rmrep st' m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st st' m m' (WF & CX & GL & AR & GR & SH) MU WM ER EM EA EG ES ERs CX'.
pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
assert (TC : forall A cs, rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= (RATP + 131968) \/ (RATP + 131968) + 928 <= A) -> rw_cells segs m' A cs).
{ intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
gw_expose_fam RATP.
split; [|split; [gw_exact CX'|split; [|split; [|split]]]].
- unfold rregions_wf. rewrite ER, EA, EG, ERs. gw_exact WF.
- destruct GL as (G1 & G2 & G3 & G4 & G5). (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
- intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [gw_exact Hconc| intros; apply Hgm |].
destruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len ra)).
destruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
+ apply TC; [gw_exact A1| cbn; lia].
+ intros k Hk. apply TC; [apply A2; gw_exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
+ apply TC; [gw_exact A3| cbn; lia].
- intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [gw_exact Hconc|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
pose proof (round_up_pg_ge (r_len rb)).
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8]. apply TC; [gw_exact R| cbn; lia].
- intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
destruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.

#[using="Type"] Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof. clear - segs.
intros st m p (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [gw_exact GL|split; [|split]]]].
- split; [gw_exact Hres|]. split; [gw_exact WR|]. split; [gw_exact DJ|]. split; [gw_exact WA|].
intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
- eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|gw_exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [gw_exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
eapply rgroup_rep_ext; [gw_exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof. clear - segs.
intros st m v (WF & CX & GL & AR & GR & SH).
assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
split; [gw_exact WF|]. split; [|split; [gw_exact GL|split; [|split]]].
- eapply rmrep_ctx_ext; [reflexivity|gw_exact Hconc|gw_exact CX].
- intros a ar Ha. eapply rarea_rep_ext; [gw_exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
- intros b gh Hb. eapply rgroup_rep_ext; [gw_exact Hconc|exact (GR b gh Hb)].
- intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. clear - segs. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

#[using="Type"] Lemma rmrep_active_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa ((RATP + 132048) + 8 * sc) ->
ov_read_bytes segs m a 8 = Some (le8 (pw st (active st sc))).
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m sc a (_ & (_ & C2 & _) & _) Hsc ->.
eapply u64arr_read; [gw_exact C2 | apply actives_nth; gw_exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_usage_read : forall st m sc a, rmrep st m -> 0 <= sc < 48 -> a = wa ((RATP + 132432) + 8 * sc) ->
ov_read_bytes segs m a 8 = Some (le8 (wz (usage st sc))).
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m sc a (_ & (_ & _ & C3 & _) & _) Hsc ->.
eapply u64arr_read; [gw_exact C3 | apply usages_nth; gw_exact Hsc | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_bounces_read : forall st m i a, rmrep st m -> 0 <= i < 32 -> a = wa ((RATP + 132848) + i) ->
ov_read_bytes segs m a 1 = Some [b8 (bounces st i)].
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m i a (_ & (_ & _ & _ & _ & C5 & _) & _) Hi ->.
eapply u8arr_read; [gw_exact C5 | apply bouncess_nth; gw_exact Hi | lia | reflexivity].
Qed.

#[using="Type"] Lemma rmrep_seq_read : forall st m a, rmrep st m -> a = wa ((RATP + 132880)) ->
ov_read_bytes segs m a 1 = Some [b8 (c_seq (ctx st))].
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m a (_ & (_ & _ & _ & _ & _ & C6) & _) ->.
apply (rw_cells_read_at segs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
Qed.

#[using="Type"] Lemma rmrep_fmh_read : forall st m a, rmrep st m -> a = wa ((RATP + 131984)) ->
ov_read_bytes segs m a 8 = Some (le8 (pw st (c_free_meta_head (ctx st)))).
Proof. clear - segs RATP. gw_expose_fam RATP.
intros st m a (_ & (C1 & _) & _) ->.
apply (rw_cells_read_at segs m _ _ 16 (C8 (pw st (c_free_meta_head (ctx st)))) 8 _ C1); first [ reflexivity | (f_equal; cbn; lia) | (unfold wa; f_equal; cbn; lia) ].
Qed.

#[using="Type"] Lemma rbytes_at_cons : forall m a b bs, bytes_at segs m a (b :: bs) <-> bytes_at segs m a [b] /\ bytes_at segs m (a + 1) bs.
Proof. clear - segs.
intros. change (b :: bs) with ([b] ++ bs). rewrite (bytes_at_app segs m a [b] bs). cbn [length Z.of_nat Pos.of_succ_nat Pos.to_nat]. tauto.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_ref_reserved ref_wview_overlay ref_mrd_overlay"] Lemma rmrep_group_word8 : forall st m b gh,
rmrep st m -> (s_groups st) !! b = Some gh ->
exists bs : list byte, ov_read_bytes segs m (wa (conc st b + 8)) 8 = Some bs /\ length bs = 8%nat
/\ (bv_unsigned (bv_extract 0 64 (le_bytes_to_word bs))) mod 32 = g_active_idx gh.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_ref_reserved ref_wview_overlay ref_mrd_overlay segs.
intros st m b gh MR Hb. pose proof MR as (WF & CX & GL & AR & GR & SH).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (GR b gh Hb) as (w8 & R & Hw8).
destruct (SH (fst b) r Hr Kr) as [HWr _].
pose proof WF as (_ & WR & _). destruct (WR (fst b) r Hr) as (_ & _ & _ & RC2 & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
destruct (rwr_at_bytes_exist m (conc st b + 9) 7) as (bs & Lbs & Bbs).
{ eapply wr_at_sub; [gw_exact HWr| rewrite Cb; lia | rewrite Cb; lia]. }
{ lia. }
{ rewrite Cb. lia. }
assert (B8 : bytes_at segs m (conc st b + 8) [w8]).
{ destruct R as [[_ HB] _]. cbn [cells_bytes cbytes app] in HB.
apply bytes_at_app in HB. destruct HB as [_ HB]. rewrite length_le8 in HB.
replace (conc st b + Z.of_nat 8) with (conc st b + 8) in HB by lia.
first [ apply bytes_at_app in HB; destruct HB as [HB _]; gw_exact HB | gw_exact HB ]. }
assert (B : bytes_at segs m (conc st b + 8) (w8 :: bs)).
{ apply rbytes_at_cons. split; [gw_exact B8|]. replace (conc st b + 8 + 1) with (conc st b + 9) by lia. gw_exact Bbs. }
exists (w8 :: bs).
assert (L8 : length (w8 :: bs) = 8%nat) by (cbn; lia).
split; [|split; [gw_exact L8|]].
- rewrite <- (Z.add_0_r (conc st b + 8)). rewrite (bytes_at_read segs m _ _ 0 8 B); [|lia|rewrite L8; cbn; lia].
cbn [Z.to_nat skipn]. rewrite firstn_all2 by (rewrite L8; lia). reflexivity.
- rewrite load8_le_val by gw_exact L8. cbn [map le_val]. rewrite <- Hw8.
change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
set (L := le_val (map bv_unsigned bs)). replace (256 * L) with ((8 * L) * 32) by lia.
rewrite Z_mod_plus_full. reflexivity.
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rmeta_slot_bounds : forall st m g, rmrep st m -> meta_slot st g ->
0 < conc st g /\ conc st g + 40 <= alloc_ceiling /\ (conc st g + 40 <= 0x10000 \/ RIMG_HI <= conc st g) /\ conc st g mod 4 = 0
/\ conc st g mod 4096 >= 24.
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI. gw_expose_win.
intros st m g MR (a & ar & k & Ha & Hk & Eg). pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
unfold AREA_HDR, META_SIZE, NSLOTS, alloc_ceiling in *. pose proof (round_up_pg_ge (r_len ra)).
rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.

#[using="RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved"] Lemma rgroup_bounds : forall st m b gh, rmrep st m -> (s_groups st) !! b = Some gh ->
0 <= conc st b /\ conc st b + 16 <= alloc_ceiling /\ (conc st b + 16 <= 0x10000 \/ RIMG_HI <= conc st b) /\ conc st b mod 16 = 0.
Proof. clear - RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved RIMG_HI. gw_expose_win.
intros st m b gh MR Hb. pose proof MR as (WF & _). pose proof WF as (_ & WR & _).
destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r)).
rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.

Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
(lo <= a < sp
\/ (RATP + 131968) <= a < (RATP + 132896)
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r))
\/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 8)
\/ (exists rid r v, (s_regions st) !! rid = Some r /\ r_kind r = RKGroup
/\ r_base r <= a < r_base r + round_up_pg (r_len r) /\ cell_read (get_shadow st rid) (a - r_base r) = Known v).

#[using="Type"] Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. clear - st lo sp a RATP. gw_expose_fam RATP. intros; left; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_ctx st lo sp a : (RATP + 131968) <= a < (RATP + 132896) -> rfree_fp st lo sp a.
Proof. clear - RATP st lo sp a. gw_expose_fam RATP. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> rfree_fp st lo sp a.
Proof. clear - st lo sp a rid r RATP. gw_expose_fam RATP. intros; left; right; right. exists rid, r. auto. Qed.
#[using="Type"] Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. clear - st lo sp a b gh RATP. gw_expose_fam RATP. intros; right; left. exists b, gh. auto. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved"] Lemma rfree_fp_meta : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> rfree_fp st lo sp a.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ROM_reservedZ LAY_ref_reserved RATP. gw_expose_fam RATP.
intros st m lo sp q a MR (ar & arr & k & Har & Hk & Eq) Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [gw_exact Hra | gw_exact NK | lia].
Qed.

#[using="Type"] Lemma rfree_fp_mono : forall st st' lo sp sp' a,
s_regions st' = s_regions st -> s_shadow st' = s_shadow st ->
(forall b gh, (s_groups st') !! b = Some gh -> (s_groups st) !! b = Some gh) ->
sp' <= sp ->
rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof. clear - RATP. gw_expose_fam RATP.
intros st st' lo sp sp' a ER ES HG HS H.
assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; gw_exact H |].
right; right. destruct H as (rid & r & H1 & H2 & H3). exists rid, r. rewrite <- ER. auto.
- right; left. destruct H as (b & gh & H1 & H2). exists b, gh. rewrite <- Hconc. auto.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). exists rid, r, v.
rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch' : forall C W m m',
munch W m m' -> wmono segs m m' ->
(forall lo hi, In (lo, hi) W -> forall x, lo <= x < hi -> C x) ->
rpres_except C m m'.
Proof. clear - segs.
intros C W m m' MU WM HW. eapply rpres_except_of_munch; [gw_exact MU | gw_exact WM |].
intros a _ HC. eapply outside_of_cover; eauto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_cov : forall C W m m',
munch W m m' -> wmono segs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. clear - segs. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono segs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.

Hypothesis WIN : forall lo hi, In (lo, hi) W -> (RATP + 131968) <= lo /\ hi <= (RATP + 131968) + 928.

#[using="MU WIN"] Lemma rctxW_avoid : forall A n, (A + n <= (RATP + 131968) \/ (RATP + 131968) + 928 <= A) \/ (forall lo hi, In (lo, hi) W -> A + n <= lo \/ hi <= A) ->
0 <= A -> A + n <= 2^64 -> agree_on m m' A n.
Proof. clear - MU WIN RATP st st' m m' W MR WM ER EM EA EG ES ERs. gw_expose_fam RATP. first [clear ERs | gw_hide ERs | idtac]; first [clear ES | gw_hide ES | idtac]; first [clear EG | gw_hide EG | idtac]; first [clear EA | gw_hide EA | idtac]; first [clear EM | gw_hide EM | idtac]; first [clear ER | gw_hide ER | idtac]; first [clear WM | gw_hide WM | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide W; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac].
intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
clear - WIN HD Ha RATP. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- destruct HD as [HD|HD].
+ pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
+ pose proof (HD lo hi ltac:(left; reflexivity)). lia.
- apply IH.
+ intros lo' hi' Hin. apply WIN. right; gw_exact Hin.
+ destruct HD as [HD|HD]; [left; gw_exact HD| right]. intros lo' hi' Hin. apply HD. right; gw_exact Hin.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW :
(rw_cells segs m' (RATP + 131968) (ctx_head_cells st') \/ (ctx_head_cells st' = ctx_head_cells st /\ forall lo hi, In (lo, hi) W -> (RATP + 132048) <= lo \/ hi <= (RATP + 131968))) ->
(u64arr segs m' ((RATP + 132048)) (actives st') \/ (actives st' = actives st /\ forall lo hi, In (lo, hi) W -> (RATP + 132432) <= lo \/ hi <= (RATP + 132048))) ->
(u64arr segs m' ((RATP + 132432)) (usages st') \/ (usages st' = usages st /\ forall lo hi, In (lo, hi) W -> (RATP + 132816) <= lo \/ hi <= (RATP + 132432))) ->
(u8arr segs m' ((RATP + 132816)) (unmap_seqs st') \/ (unmap_seqs st' = unmap_seqs st /\ forall lo hi, In (lo, hi) W -> (RATP + 132848) <= lo \/ hi <= (RATP + 132816))) ->
(u8arr segs m' ((RATP + 132848)) (bouncess st') \/ (bouncess st' = bouncess st /\ forall lo hi, In (lo, hi) W -> (RATP + 132880) <= lo \/ hi <= (RATP + 132848))) ->
(rw_cells segs m' ((RATP + 132880)) (ctx_tail_cells st') \/ (ctx_tail_cells st' = ctx_tail_cells st /\ forall lo hi, In (lo, hi) W -> (RATP + 132896) <= lo \/ hi <= (RATP + 132880))) ->
rmrep st' m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved m MR MU WM ER EM EA EG ES ERs WIN segs RATP st st' m' W. gw_expose_fam RATP. try gw_hide W; try gw_hide m'; try gw_hide st'; first [clear st | gw_hide st | idtac].
intros H1 H2 H3 H4 H5 H6.
pose proof MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
assert (CX' : rmrep_ctx st' m').
{ unfold rmrep_ctx. split; [|split; [|split; [|split; [|split]]]].
- destruct H1 as [H|[-> HD]]; [gw_exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H2 as [H|[-> HD]]; [gw_exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H3 as [H|[-> HD]]; [gw_exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H4 as [H|[-> HD]]; [gw_exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H5 as [H|[-> HD]]; [gw_exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
- destruct H6 as [H|[-> HD]]; [gw_exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| gw_expose_fam RATP; lia| gw_expose_fam RATP; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
eapply rmrep_ctx_frame'; [gw_exact MR | | gw_exact WM | gw_exact ER | gw_exact EM | gw_exact EA | gw_exact EG | gw_exact ES | gw_exact ERs | gw_exact CX'].
eapply munch_weaken; [|gw_exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
clear - WIN Hx RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved segs RATP. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
- pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
- apply IH. intros lo' hi' Hin. apply WIN. right; gw_exact Hin.
Qed.
End CTXFRAME.

Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0v a1v a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

End RC__1.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q4J3.Mq3 QPjm.Mq4.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Open Scope Z_scope.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rfree_sym rmalloc_sym : Z).
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
Hypothesis AL_rfree_sym : gw_al rfree_sym 4.
Hypothesis AL_rmalloc_sym : gw_al rmalloc_sym 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rfree_sym rmalloc_sym RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rfree_sym AL_rmalloc_sym ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition RMALLOC_SYM : Z := rmalloc_sym.
Definition RFREE_SYM : Z := rfree_sym.
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.

Definition ralloc_static (a : Z) : Prop :=
((RATP + 131968) <= a < (RATP + 132896)) \/ ((RATP + -164) <= a < (RATP + -164 + 4)).

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
/\ HINV_from ref_reserved rc_secret st (ps_brk s) LB0.

#[using="Type"] Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof. clear - segs. intros s s' LB m (st & LB0 & HP & H1 & H2 & H3) E1 E2. exists st, LB0. rewrite E1, E2. auto 6. Qed.

#[using="Type"] Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof. clear - segs.
intros s LB LB' m (st & LB0 & HP & H1 & H2 & H3) P. exists st, LB0. split; [|auto].
eapply Permutation.Permutation_trans; [gw_exact HP| gw_exact P].
Qed.

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
SP <= a \/ (RDATA_LO <= a < RIMG_HI /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof. clear - RATP. gw_expose_fam RATP. intros LB SP m a _ _. auto. Qed.

#[using="Type"] Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof. clear - RATP. gw_expose_fam RATP.
intros LB SP m1 m2 m3 H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2].
split; [congruence| auto].
Qed.

#[using="Type"] Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof. clear - RATP. gw_expose_fam RATP.
intros LB LB' SP SP' m m' H HS HL a Ha Hc. apply H; [gw_exact Ha|].
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; gw_exact Hc| right; right].
exists b. split; [apply HL; gw_exact Hb| gw_exact Hr].
Qed.

Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
SP <= A
\/ (RDATA_LO <= A /\ A + n <= RIMG_HI /\ (A + n <= (RATP + 131728) \/ (RATP + 131968) + 928 <= A) /\ (A + n <= (RATP + -164) \/ (RATP + -164) + 4 <= A)
/\ (A + n <= (RATP + 131696) \/ (RATP + 131696) + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
\/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

#[using="gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2"] Lemma rclient_range_addr : forall LB SP A n a,
rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof. clear - gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2 RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros LB SP A n a HR Ha. (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rclient_range, rclient_addr, ralloc_static in *).
destruct HR as [H|[H|(b & Hb & H1 & H2)]]; [left; lia| right; left; lia| right; right; exists b; split; [gw_exact Hb|lia]].
Qed.

#[using="gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2"] Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
rheap_pres LB SP m m' -> bytes_at segs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
bytes_at segs m' A bs.
Proof. clear - gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros LB SP m m' A bs HP (H0 & H1 & HB) HR. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [gw_exact HR|lia])) as [E _].
rewrite E. reflexivity.
Qed.

#[using="gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2"] Lemma rheap_pres_wr_at : forall LB SP m m' A n,
rheap_pres LB SP m m' -> wr_at segs m A n -> rclient_range LB SP A n -> wr_at segs m' A n.
Proof. clear - gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros LB SP m m' A n HP (H0 & H1 & HW) HR. split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [gw_exact HR|lia])) as [_ W].
apply W. apply HW. gw_exact Hi.
Qed.

#[using="gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2"] Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
rheap_pres LB SP m m' -> rw_cells segs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
rw_cells segs m' A cs.
Proof. clear - gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros LB SP m m' A cs HP [[Hwf HB] HW] HR. split; [split; [gw_exact Hwf|]|].
- eapply rheap_pres_bytes_at; eauto. rewrite cells_bytes_length by assumption. gw_exact HR.
- eapply rheap_pres_wr_at; eauto.
Qed.

#[using="gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2"] Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
rheap_pres LB SP m m' -> u8arr segs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
u8arr segs m' A xs.
Proof. clear - gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_2 segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros LB SP m m' A xs HP H HR. apply (u8arr_of_rw_cells segs m' A (length xs)).
eapply rheap_pres_rw_cells; [gw_exact HP| apply rw_cells_of_u8arr; gw_exact H|].
cbn [cells_size csize]. rewrite Nat.add_0_r. gw_exact HR.
Qed.

#[using="Type"] Lemma rheap_pres_stk : forall LB SP m m' lo hi,
rheap_pres LB SP m m' -> stk segs m lo hi -> SP <= lo -> stk segs m' lo hi.
Proof. clear - segs RATP. gw_expose_fam RATP.
intros LB SP m m' lo hi HP ST HS. destruct ST as (H0 & H1 & HW). split; [gw_exact H0|]. split; [gw_exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. gw_exact Hb.
Qed.

Definition rblock_range (A n : Z) : Prop :=
0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ RIMG_HI <= A).

Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
alloc_ceiling <= fst iv
\/ (RDATA_LO <= fst iv /\ snd iv <= RIMG_HI /\ (snd iv <= (RATP + 131728) \/ (RATP + 131968) + 928 <= fst iv)
/\ (snd iv <= (RATP + 131696) \/ (RATP + 131696) + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
\/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init_s rc_secret (reservedZ segs)).

#[using="Type"] Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof. clear - segs. intros; left; assumption. Qed.
#[using="Type"] Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init_s rc_secret (reservedZ segs)) -> raddr_exposed s n.
Proof. clear - segs. intros; right; assumption. Qed.

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (n lo B : Z) (m : mem)
(r : option bptr) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv']
/\ rauxv_ok m' B
/\ rheap_pres LB (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ match r with
| None => a0 = Z_to_bv 64 0 /\ errv' = Z_to_bv 64 12 /\ RHEAP s' LB m'
| Some p => exists A junk,
a0 = Z_to_bv 64 A /\ rblock_range A n
/\ RHEAP s' ((p, A, n) :: LB) m'
/\ rw_cells segs m' A [CB (Z.to_nat n) junk]
/\ (raddr_exposed s n -> A = ptr_addr s' p)
/\ (forall g idx, (s_slots (ps_m s')) !! (fst p) = Some (g, idx) ->
is_allzero_ctrl (get_meta_rec (ps_m s') g) = true -> junk = zeros (Z.to_nat n))
end.

Definition rmalloc_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (n lo B : Z) (errv : word),
RHEAP s LB m ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
implM segs (raw_malloc n) s
(rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom segs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
(r : unit) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv]
/\ rauxv_ok m' B
/\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
/\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
RHEAP s LB m -> In (p, A, n) LB ->
rauxv_ok m B -> bv_unsigned sp <= B ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 A ->
implM segs (raw_free p) s
(rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom segs)).

Definition rfree_null_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
a0 = Z_to_bv 64 0 ->
evt segs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom segs)).

End RC__1.

End G.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq1.

Import ListNotations. Unset Keyed Unification. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_amo_step AMO ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_amo_step_1 AMO. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_2. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.g_anchor_rw_any ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__g_anchor_rw_any_0. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.mkr__sg_zstep_4.
Local Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt StepGen StepGenSF GwCallee.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Section G.
Variables (segs : list Segment) (base : Z).
Hypothesis CODE : code_at segs base divtf3_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 2308.

Hypothesis mulhu_shl32 : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.mulhu_shl32 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524]%Z in exact T).

Definition shl_shr_32 := QCa8.Mq1.shl_shr_32 segs base CODE BASE4 BASER mulhu_shl32.
Definition divtf3_core1 := QCa8.Mq1.divtf3_core1 segs base CODE BASE4 BASER mulhu_shl32.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_mid2_pc := (base + 0x358)%Z.

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia. Qed.

Definition divtf3_mid2 (sp gp tp w4 sgw w6 a6 : word) (F : bvmap 5 word) (fc : bv 32)
(ea eb aSigHi bSigHi scale x_hi x_lo : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi (bv_unsigned w4)) (E_A3 (bv_unsigned w4)) (E_A4 (bv_unsigned w4)) = (q_hi, q_lo)
/\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
/\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 (base + 0x358)) fc None m (seg_rom segs).

Section Core2.
Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma divtf3_core2 : forall (x_hi x_lo : Z) (ra sp gp tp sgw a5 a6 y21 y22 s10 s11 : word)
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
(0 <= x_hi < 2^64)%Z -> (0 <= x_lo < 2^64)%Z ->
evt segs (divtf3_mid2 sp gp tp w4 sgw w6 a6 F fc ea eb aSigHi bSigHi scale x_hi x_lo m)
(MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
(Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
(Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
(Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
(Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
F (Z_to_bv 64 (base + 0x218)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI Ra Rb Rsc Rx_hi Rx_lo.
pose_word_ranges.

cbv beta delta [E_p3 E_p42 E_X4 E_X4sh E_X3 E_A2sh E_A1 E_A2 E_A3 E_A4 E_aLoTop E_aHi2n E_aHi2 E_aSigHiI E_bSigHiI E_a2Lo E_expM1].
name_as aSigHiI (Z.lor aSigHi 281474976710656). name_as bSigHiI (Z.lor bSigHi 281474976710656).
name_as aLoTop (Z.shiftr aLo 63). name_as a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
name_as aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615). name_as aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
name_as A1 (Z.shiftr aHi2 32). name_as A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
name_as A3 (Z.shiftr a2Lo 32). name_as A4 (Z.land a2Lo 4294967294).
name_as X3 (Z.shiftr x_lo 32). name_as X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615). name_as X4 (Z.shiftr X4sh 32).
name_as p31 (Z.land (X3 * A1) 18446744073709551615). name_as p32 (Z.land (X3 * A2) 18446744073709551615).
name_as p33 (Z.land (X3 * A3) 18446744073709551615). name_as p34 (Z.land (X3 * A4) 18446744073709551615).
name_as p42 (Z.land (X4 * A2) 18446744073709551615).

do 1 zstep. model_reg 22 p41 (Z.land (X4 * A1) 18446744073709551615).
do 1 zstep. model_reg 26 p43 (Z.land (X4 * A3) 18446744073709551615).
do 1 zstep. model_reg 27 p44 (Z.land (X4 * A4) 18446744073709551615).
do 1 zstep. model_reg 21 s2a (Z.land (p42 + p33) 18446744073709551615).
do 1 zstep. model_reg 23 X1 (Z.shiftr x_hi 32).
do 1 zstep. model_reg 25 X2sh (Z.land (Z.shiftl x_hi 32) 18446744073709551615).
do 1 zstep. model_reg 26 sum1 (Z.land (p34 + p43) 18446744073709551615).
do 1 zstep. model_reg 19 c2a (Z.b2z (s2a <? p42)).
do 1 zstep. model_reg 20 p11 (Z.land (X1 * A1) 18446744073709551615).
do 1 zstep. model_reg 18 p12 (Z.land (A2 * X1) 18446744073709551615).
do 1 zstep. model_reg 1 p13 (Z.land (A3 * X1) 18446744073709551615).
do 1 zstep. model_reg 23 p14 (Z.land (A4 * X1) 18446744073709551615).
do 1 zstep. model_reg 15 X2 (Z.shiftr X2sh 32).
do 1 zstep. cbv delta [X2sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_hi 4294967295) with X2 by (cbv delta [X2 X2sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_hi 32) 18446744073709551615) with X2sh.
do 0 zstep. model_reg 9 p22 (Z.land (X2 * A2) 18446744073709551615).
do 1 zstep. model_reg 24 c1 (Z.b2z (sum1 <? p34)).
do 1 zstep. model_reg 25 sum1Shr32 (Z.shiftr sum1 32).
do 1 zstep. model_reg 26 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
do 1 zstep. model_reg 8 p21 (Z.land (X2 * A1) 18446744073709551615).
do 1 zstep. model_reg 31 p23 (Z.land (X2 * A3) 18446744073709551615).
do 1 zstep. model_reg 15 p24 (Z.land (X2 * A4) 18446744073709551615).
do 1 zstep. model_reg 23 s3a (Z.land (p41 + p14) 18446744073709551615).
do 1 zstep. model_reg 24 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
do 1 zstep. model_reg 27 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
do 1 zstep. model_reg 1 s4a (Z.land (p31 + p13) 18446744073709551615).
do 1 zstep. model_reg 15 sum2 (Z.land (s2a + p24) 18446744073709551615).
do 1 zstep. model_reg 28 c3a (Z.b2z (s3a <? p41)).
do 1 zstep. model_reg 30 s3b (Z.land (s3a + p32) 18446744073709551615).
do 1 zstep. model_reg 18 sum5 (Z.land (p21 + p12) 18446744073709551615).
do 1 zstep. model_reg 22 r0c (Z.b2z (lo_lo <? sum1Shl32)).
do 1 zstep. model_reg 24 sum1Mid (Z.lor sum1Shr32 c1Shl32).
do 1 zstep. model_reg 29 c4a (Z.b2z (s4a <? p31)).
do 1 zstep. model_reg 9 sum4 (Z.land (s4a + p22) 18446744073709551615).
do 1 zstep. model_reg 21 c2b (Z.b2z (sum2 <? s2a)).
do 1 zstep. model_reg 23 c3b (Z.b2z (s3b <? s3a)).
do 1 zstep. model_reg 31 sum3 (Z.land (s3b + p23) 18446744073709551615).
do 1 zstep. model_reg 8 c5 (Z.b2z (sum5 <? p21)).
do 1 zstep. model_reg 24 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
do 1 zstep. model_reg 22 nr0c (Z.lxor r0c 18446744073709551615).
do 1 zstep. model_reg 25 sum5Shr32 (Z.shiftr sum5 32).
do 1 zstep. model_reg 18 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
do 1 zstep. model_reg 26 c4b (Z.b2z (sum4 <? s4a)).
do 1 zstep. model_reg 29 hh1 (Z.land (c4a + p11) 18446744073709551615).
do 1 zstep. model_reg 19 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
do 1 zstep. model_reg 28 c3ab (Z.land (c3a + c3b) 18446744073709551615).
do 1 zstep. model_reg 30 c3c (Z.b2z (sum3 <? s3b)).
do 1 zstep. model_reg 15 cr1a (Z.b2z (r1a <? sum2)).
do 1 zstep. model_reg 20 sum3Shr32 (Z.shiftr sum3 32).
do 1 zstep. model_reg 31 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
do 1 zstep. model_reg 8 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
do 1 zstep. model_reg 29 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
do 1 zstep. model_reg 18 m1 (Z.land (sum4 + sum5Shl32) 18446744073709551615).
do 1 zstep. model_reg 28 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
do 1 zstep. model_reg 31 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
do 1 zstep. model_reg 30 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
do 1 zstep. model_reg 8 cm1 (Z.b2z (m1 <? sum4)).
do 1 zstep. model_reg 19 m2 (Z.land (m1 + sum2Hi) 18446744073709551615).
do 1 zstep. model_reg 28 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
do 1 zstep. model_reg 9 cr1b (Z.b2z (r1 <? r1a)).
do 1 zstep. model_reg 21 ltc (Z.b2z (nr0c <? r1)).
do 1 zstep. model_reg 31 eqx (Z.lxor r1 nr0c).
do 1 zstep. model_reg 29 hh3 (Z.land (hh2 + sum5MidHi) 18446744073709551615).
do 1 zstep. model_reg 30 cm2 (Z.b2z (m2 <? m1)).
do 1 zstep. model_reg 15 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
do 2 zstep. model_reg 28 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
do 1 zstep. model_reg 29 hh4 (Z.land (hh3 + cm1) 18446744073709551615).
zstep.
replace (Z_to_bv 64 (Z.b2z (eqx <? 1) + -1)) with (Z_to_bv 64 (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615))
by (rewrite Z_to_bv_land64, ltb1_eqb0 by lia; f_equal; lia).
model_reg 31 neMask (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615).
zstep. model_reg 29 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
do 1 zstep. model_reg 28 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
zstep. model_reg 30 carry (Z.land neMask ltc).
zstep. model_reg 31 cm3 (Z.b2z (m3 <? m2)).
do 1 zstep. model_reg 15 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
do 1 zstep. model_reg 29 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
do 1 zstep. model_reg 28 cm4 (Z.b2z (m4 <? m3)).
zstep. model_reg 30 q_lo (Z.land (m4 + carry) 18446744073709551615).
zstep. model_reg 28 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
zstep. model_reg 15 cm5 (Z.b2z (q_lo <? m4)).
zstep. model_reg 28 q_hi (Z.land (hh7 + cm5) 18446744073709551615).
do 2 zstep.
apply evt_done. unfold divtf3_mid2.
exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
split.
{ change (divc_wide x_hi x_lo A1 A2 A3 A4 = (q_hi, q_lo)).
cbv beta delta [divc_wide]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
split. { exact Rq_hi. } split. { exact Rq_lo. }
reflexivity.
Time Qed.

Definition divtf3_midC (sp gp tp sgw a6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
(forall sgn, div_core sgn ea eb aSigHi aLo bSigHi bLo scale
= divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo))
/\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
/\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop aLo)) (Z_to_bv 64 (E_aHi2 aSigHi))
y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo aLo)) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 (base + 0x358)) fc None m (seg_rom segs).

#[using="CODE BASE4 BASER mulhu_shl32"] Lemma divtf3_core12 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
(F : bvmap 5 word) fc (m : word -> option byte),
mem_inv segs m ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
evt segs (divtf3_midC sp gp tp sgw a6 F fc m)
(MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m (seg_rom segs)).
Proof.
intros until m. intros MI Ra Rb Rsc.
eapply evt_cut. { eapply divtf3_core1; eauto. }
intros ms1 P. destruct P as (xh' & xl' & y21 & y22 & EQ1 & Rxh & Rxl & ->).
eapply evt_mono. { eapply divtf3_core2; eauto. }
intros ms2 P2. destruct P2 as (q_hi & q_lo & y1 & y8 & y9 & y18 & y19 & y20 & z21 & z22 & y23 & y24 & y25 & y26 & y27 & y31 & HW & Rqh & Rql & ->).
unfold divtf3_midC. exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
split. { intros sgn. rewrite EQ1. cbv beta delta [DCW]. rewrite HW. reflexivity. }
split. { exact Rqh. } split. { exact Rql. }
reflexivity.
Qed.
End Core2.

End G.
