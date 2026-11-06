(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7 QZAi QqdR QnDM_c1 QVbl QQLG QDXD QkTt Q91D QCa8 Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.GwCallee Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q9A7.Mq1.
Import QZAi.Mq1 QZAi QqdR.
Import QnDM_c1.
Import QVbl.Mq2.
Import QQLG.Mq2.
Import QQLG.Mq3.
Import QQLG.Mq4.
Import QQLG.Mq1.
Import QVbl.Mq0.
Import QQLG.Mq0.
Import QDXD.Mq0.
Import QkTt.Mq1.
Import Q91D.
Import QCa8.
Import QVbl.
Import QQLG.Mq6.
Import QQLG.Mqa.
Import QQLG.Mq5.
Import QVbl.Mq4.
Import QVbl.Mq3.
Import QQLG.Mq7.

Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_step_core ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_step_core_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen.sg_zstep ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX.mkr__sg_zstep_4. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core.
Local Ltac zstep ::= sg_zstep. Local Ltac mkr__zstep_1 := sg_zstep.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Local Open Scope Z_scope.

Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.
Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64, wrap64, ONES64. rewrite land_W64. apply Z.mod_pos_bound. lia. Qed.

Definition canon (x : Z) : Z := lo64 x + 2^64 * hi64 x.
Lemma mk128_canon : forall x, mk128 (hi64 x) (lo64 x) = canon x.
Proof.
intros. unfold mk128, canon. pose proof (lo64_range x). pose proof (hi64_range x).
rewrite Z.shiftl_mul_pow2 by lia. rewrite lor_disjoint_add; [lia|].
- apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 64).
+ rewrite Z.mul_pow2_bits_low by lia. reflexivity.
+ replace (Z.testbit (lo64 x) i) with false; [apply Bool.andb_false_r|].
symmetry. destruct (Z.eq_dec (lo64 x) 0) as [->|]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.
Lemma canon_small : forall x, 0 <= x < 2^128 -> canon x = x.
Proof.
intros x Hx. unfold canon, lo64, hi64, wrap64, ONES64. rewrite !land_W64, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small (x / 2^64)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.div_mod x (2^64) ltac:(lia)). lia.
Qed.
Lemma canon_range : forall x, 0 <= canon x < 2^128.
Proof. intros. unfold canon. pose proof (lo64_range x). pose proof (hi64_range x). lia. Qed.

Lemma ulit_lo64 : forall x, bv_unsigned (Z_to_bv 64 (lo64 x)) = lo64 x.
Proof. intros. apply unsigned_lit. apply lo64_range. Qed.
Lemma ulit_hi64 : forall x, bv_unsigned (Z_to_bv 64 (hi64 x)) = hi64 x.
Proof. intros. apply unsigned_lit. apply hi64_range. Qed.

Local Open Scope bv_scope.

Lemma sext32_idem : forall z, sext32 (sext32 z) = sext32 z.
Proof. intros. apply sext32_congr. apply sext32_low. Qed.

Lemma lo64_flip_sign : forall x, lo64 (Z.lxor x F128_SIGNBIT) = lo64 x.
Proof.
intros. unfold lo64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z.
apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 127 i); [lia|]. now rewrite Bool.xorb_false_r.
- rewrite Z.ones_spec_high by lia. now rewrite !Bool.andb_false_r.
Qed.
Lemma hi64_flip_sign : forall x, hi64 (Z.lxor x F128_SIGNBIT) = Z.lxor (hi64 x) 9223372036854775808.
Proof.
intros. unfold hi64, wrap64, ONES64, F128_SIGNBIT. change 18446744073709551615%Z with (Z.ones 64).
change 0x80000000000000000000000000000000%Z with (2^127)%Z. change 9223372036854775808%Z with (2^63)%Z.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !Z.land_spec, !Z.shiftr_spec, Z.lxor_spec, !Z.pow2_bits_eqb by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite !Bool.andb_true_r.
destruct (Z.eqb_spec 127 (i + 64)), (Z.eqb_spec 63 i); try lia; reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !Bool.andb_false_r. destruct (Z.eqb_spec 63 i); [lia|reflexivity].
Qed.

Section G.
Variables (segs : list Segment).
Variables (e_extenddftf2 e_signbitl e_fpclassifyl e_frexpl e_letf2 e_multf3 e_floatsitf e_subtf3 e_addtf3 e_fixunstfsi e_floatunsitf e_divtf3 : Z).

Definition fixunstfsi_post := Eval cbv beta delta [QQLG.Mq2.fixunstfsi_post] in (QQLG.Mq2.fixunstfsi_post segs).

Definition floatsitf_post := ltac:(let t := eval cbv beta delta [QQLG.Mq3.floatsitf_post] in (QQLG.Mq3.floatsitf_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in exact t).

Definition floatunsitf_post := ltac:(let t := eval cbv beta delta [QQLG.Mq4.floatunsitf_post] in (QQLG.Mq4.floatunsitf_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in exact t).

Definition extenddftf2_post := ltac:(let t := eval cbv beta delta [QQLG.Mq1.extenddftf2_post] in (QQLG.Mq1.extenddftf2_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in exact t).

Definition addtf3_post := ltac:(let t := eval cbv beta delta [QkTt.Mq1.addtf3_post] in (QkTt.Mq1.addtf3_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in exact t).

Definition multf3_post := ltac:(let t := eval cbv beta delta [QCa8.multf3_post] in (QCa8.multf3_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in exact t).
Definition multf3_stmt := ltac:(let t := eval cbv beta delta [QCa8.multf3_stmt] in (QCa8.multf3_stmt segs e_multf3) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in exact t).

Definition divtf3_post := ltac:(let t := eval cbv beta delta [QVbl.divtf3_post] in (QVbl.divtf3_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in exact t).
Definition divtf3_stmt := ltac:(let t := eval cbv beta delta [QVbl.divtf3_stmt] in (QVbl.divtf3_stmt segs e_divtf3) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let t := gw_subst t (QVbl.divtf3_post segs) divtf3_post in exact t).

Definition letf2_post := ltac:(let t := eval cbv beta delta [QQLG.Mq6.letf2_post] in (QQLG.Mq6.letf2_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let t := gw_subst t (QVbl.divtf3_post segs) divtf3_post in let t := gw_subst t (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in exact t).
Definition frexpl_post := ltac:(let t := eval cbv beta delta [QQLG.Mq6.frexpl_post] in (QQLG.Mq6.frexpl_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let t := gw_subst t (QVbl.divtf3_post segs) divtf3_post in let t := gw_subst t (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let t := gw_subst t (QQLG.Mq6.letf2_post segs) letf2_post in exact t).

Definition signbitl_post := ltac:(let t := eval cbv beta delta [QQLG.Mqa.signbitl_post] in (QQLG.Mqa.signbitl_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let t := gw_subst t (QVbl.divtf3_post segs) divtf3_post in let t := gw_subst t (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let t := gw_subst t (QQLG.Mq6.letf2_post segs) letf2_post in let t := gw_subst t (QQLG.Mq6.frexpl_post segs) frexpl_post in exact t).

Definition fpclassifyl_post := ltac:(let t := eval cbv beta delta [QQLG.Mq5.fpclassifyl_post] in (QQLG.Mq5.fpclassifyl_post segs) in let t := gw_subst t (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let t := gw_subst t (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let t := gw_subst t (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let t := gw_subst t (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let t := gw_subst t (QkTt.Mq1.addtf3_post segs) addtf3_post in let t := gw_subst t (QCa8.multf3_post segs) multf3_post in let t := gw_subst t (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let t := gw_subst t (QVbl.divtf3_post segs) divtf3_post in let t := gw_subst t (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let t := gw_subst t (QQLG.Mq6.letf2_post segs) letf2_post in let t := gw_subst t (QQLG.Mq6.frexpl_post segs) frexpl_post in let t := gw_subst t (QQLG.Mqa.signbitl_post segs) signbitl_post in exact t).

Hypothesis letf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QVbl.Mq2.letf2_spec segs e_letf2) 3%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (QVbl.Mq2.letf2_post segs) letf2_post in exact T).

Hypothesis fixunstfsi_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq2.gw_all) (@QQLG.Mq2.fixunstfsi_spec) e_fixunstfsi)) in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis floatsitf_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq3.floatsitf_spec segs e_floatsitf) 3%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis floatunsitf_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq4.gw_all) (@QQLG.Mq4.floatunsitf_spec) e_floatunsitf)) in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis extenddftf2_spec : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.Mq1.extenddftf2_spec segs e_extenddftf2) 3%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis addtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QDXD.Mq0.addtf3_spec segs e_addtf3) 5%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in let T := gw_subst T (QDXD.Mq0.addtf3_post segs) addtf3_post in exact T).

Hypothesis subtf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QkTt.Mq1.subtf3_spec segs e_subtf3) 4%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis multf3_spec : gw_hyp ltac:(let T := gw_callee_type0 (QCa8.multf3_spec segs e_multf3) 3%nat in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis frexpl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq6.gw_all) (@QQLG.Mq6.frexpl_spec) e_frexpl)) in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis signbitl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mqa.gw_all) (@QQLG.Mqa.signbitl_spec) e_signbitl)) in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

Hypothesis fpclassifyl_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QQLG.Mq5.gw_all) (@QQLG.Mq5.fpclassifyl_spec) e_fpclassifyl)) in let T := gw_subst T (QQLG.Mq2.fixunstfsi_post segs) fixunstfsi_post in let T := gw_subst T (QQLG.Mq3.floatsitf_post segs) floatsitf_post in let T := gw_subst T (QQLG.Mq4.floatunsitf_post segs) floatunsitf_post in let T := gw_subst T (QQLG.Mq1.extenddftf2_post segs) extenddftf2_post in let T := gw_subst T (QkTt.Mq1.addtf3_post segs) addtf3_post in let T := gw_subst T (QCa8.multf3_post segs) multf3_post in let T := gw_subst T (QCa8.multf3_stmt segs e_multf3) multf3_stmt in let T := gw_subst T (QVbl.divtf3_post segs) divtf3_post in let T := gw_subst T (QVbl.divtf3_stmt segs e_divtf3) divtf3_stmt in let T := gw_subst T (QQLG.Mq6.letf2_post segs) letf2_post in let T := gw_subst T (QQLG.Mq6.frexpl_post segs) frexpl_post in let T := gw_subst T (QQLG.Mqa.signbitl_post segs) signbitl_post in let T := gw_subst T (QQLG.Mq5.fpclassifyl_post segs) fpclassifyl_post in exact T).

#[using="letf2_spec fixunstfsi_spec floatsitf_spec floatunsitf_spec extenddftf2_spec addtf3_spec subtf3_spec multf3_spec frexpl_spec signbitl_spec fpclassifyl_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Open Scope Z_scope.

#[using="Type"] Lemma lo64_canon : forall x, lo64 (canon x) = lo64 x.
Proof. intros. unfold canon. apply lo64_words. apply lo64_range. Qed.
#[using="Type"] Lemma hi64_canon : forall x, hi64 (canon x) = hi64 x.
Proof. intros. unfold canon. apply hi64_words; [apply lo64_range | apply hi64_range]. Qed.

#[using="Type"] Lemma f128_mul_canon : forall a b, f128_mul (canon a) (canon b) = f128_mul a b.
Proof. intros. unfold f128_mul. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma f128_div_canon : forall a b, f128_div (canon a) (canon b) = f128_div a b.
Proof. intros. unfold f128_div. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma f128_add_canon : forall a b, f128_add (canon a) (canon b) = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma f128_add_canon_l : forall a b, f128_add (canon a) b = f128_add a b.
Proof. intros. unfold f128_add. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma f128_sub_canon : forall a b, f128_sub (canon a) (canon b) = f128_sub a b.
Proof. intros. unfold f128_sub. rewrite !lo64_canon, !hi64_canon. apply f128_add_canon_l. Qed.
#[using="Type"] Lemma f128_le_canon : forall a b, f128_le (canon a) (canon b) = f128_le a b.
Proof. intros. unfold f128_le. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma fixunstfsi_a0_canon : forall a, fixunstfsi_a0 (canon a) = fixunstfsi_a0 a.
Proof. intros. unfold fixunstfsi_a0. rewrite !lo64_canon, !hi64_canon. reflexivity. Qed.

Local Open Scope bv_scope.

Definition leaf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

Definition leaf1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [] m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="letf2_spec"] Lemma letf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X Y : Z),
mem_inv segs m ->
evt segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X Y) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_letf2 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - letf2_spec segs e_letf2.
intros until Y. intros MI. eapply evt_mono. { eapply letf2_spec. exact MI. }
intros ms' P. unfold letf2_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_le_canon in P. exact P.
Qed.

#[using="letf2_spec"] Lemma letf2_callv0 : forall ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv segs m ->
evt segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_le X F128_ZERO) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 0) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_letf2 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - letf2_spec segs e_letf2. intros. change (Z_to_bv 64 0) with (Z_to_bv 64 (lo64 0)) at 1. change (Z_to_bv 64 0) with (Z_to_bv 64 (hi64 0)) at 1. apply letf2_callv. assumption. Qed.

#[using="fixunstfsi_spec"] Lemma fixunstfsi_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv segs m ->
evt segs (leaf1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fixunstfsi_a0 X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_fixunstfsi + 0x0)) fc None m (seg_rom segs)).
Proof. clear - fixunstfsi_spec segs e_fixunstfsi.
intros until X. intros MI. eapply evt_mono. { eapply fixunstfsi_spec. exact MI. }
intros ms' P. unfold fixunstfsi_post in P. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fixunstfsi_a0_canon in P. exact P.
Qed.

#[using="floatsitf_spec"] Lemma floatsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v i : Z),
mem_inv segs m -> (0 <= v < 2^64)%Z -> v = sext32 i ->
evt segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_floatsitf + 0x0)) fc None m (seg_rom segs)).
Proof. clear - floatsitf_spec segs e_floatsitf.
intros until i. intros MI Hv Hi. eapply evt_mono. { eapply floatsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hi. }
intros ms' P. exact P.
Qed.

#[using="floatsitf_spec"] Lemma floatsitf_callp : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (i : Z),
mem_inv segs m -> (0 <= i < 2^31)%Z ->
evt segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_i32 i) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_floatsitf + 0x0)) fc None m (seg_rom segs)).
Proof. clear - floatsitf_spec segs e_floatsitf. intros until i. intros MI Hi. apply floatsitf_callv; [exact MI | lia |]. rewrite sext32_small by lia. reflexivity. Qed.

#[using="floatunsitf_spec"] Lemma floatunsitf_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (v u : Z),
mem_inv segs m -> (0 <= v < 2^64)%Z -> v = sext32 u ->
evt segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 u) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_floatunsitf + 0x0)) fc None m (seg_rom segs)).
Proof. clear - floatunsitf_spec segs e_floatunsitf.
intros until u. intros MI Hv Hu. eapply evt_mono. { eapply floatunsitf_spec; [exact MI|]. rewrite unsigned_lit by lia. exact Hu. }
intros ms' P. exact P.
Qed.
#[using="floatunsitf_spec"] Lemma floatunsitf_callfix : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (Y : Z),
mem_inv segs m ->
evt segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (f128_of_u32 (f128_to_u32 Y)) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fixunstfsi_a0 Y)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_floatunsitf + 0x0)) fc None m (seg_rom segs)).
Proof. clear - floatunsitf_spec segs e_floatunsitf.
intros until Y. intros MI. apply floatunsitf_callv; [exact MI | |].
- unfold fixunstfsi_a0. apply sext32_range.
- unfold f128_to_u32, M32. rewrite sext32_landM32. unfold fixunstfsi_a0. symmetry. apply sext32_idem.
Qed.

#[using="extenddftf2_spec"] Lemma extenddftf2_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (D : Z),
mem_inv segs m -> (0 <= D < 2^64)%Z ->
evt segs (leaf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bvmap_set 10 (Z_to_bv 64 D) F) fc (f128_of_d D) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 10 (Z_to_bv 64 D) F) (Z_to_bv 64 (e_extenddftf2 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - extenddftf2_spec segs e_extenddftf2.
intros until D. intros MI HD. eapply evt_mono. { eapply extenddftf2_spec. exact MI. }
intros ms' P. unfold extenddftf2_post in P. rewrite freg_get_same, unsigned_lit in P by lia. exact P.
Qed.

Definition call2_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(K : Z) (R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - K, q)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - K) q.

#[using="multf3_spec"] Lemma multf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk segs m (q - 80) q -> mem_inv segs m -> (4096 <= q < 2^64)%Z ->
evt segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 80 (f128_mul X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_multf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - multf3_spec segs e_multf3.
intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (multf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold multf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_mul_canon in P. exact P.
Qed.

#[using="Type"] Lemma divtf3_callq : divtf3_stmt -> forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk segs m (q - 112) q -> mem_inv segs m -> (4096 <= q < 2^64)%Z ->
evt segs (call2_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 112 (f128_div X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_divtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - segs e_divtf3.
intros DS. intros until Y. intros ST MI Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (DS ra (Z_to_bv 64 q)); rewrite ?Eq; eauto; lia. }
intros ms' P. unfold divtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64, !mk128_canon, f128_div_canon in P. exact P.
Qed.

Definition calla_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(R : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc' None m' (seg_rom segs)
/\ munch [(q - 48, q)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ frm0 fc'
/\ stk segs m' (q - 48) q.

#[using="addtf3_spec"] Lemma addtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk segs m (q - 48) q -> mem_inv segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_add X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_addtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - addtf3_spec segs e_addtf3.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (addtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_add_canon in P. exact P.
Qed.

#[using="subtf3_spec"] Lemma subtf3_callq : forall ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q X Y : Z),
stk segs m (q - 48) q -> mem_inv segs m -> frm0 fc -> (48 <= q < 2^64)%Z ->
evt segs (calla_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F (f128_sub X Y) m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 (lo64 Y)) (Z_to_bv 64 (hi64 Y)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_subtf3 + 0x0)) fc None m (seg_rom segs)).
Proof. clear - subtf3_spec segs e_subtf3.
intros until Y. intros ST MI FRM Hq.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
eapply evt_mono. { eapply (subtf3_spec ra (Z_to_bv 64 q)); rewrite ?Eq; eauto. }
intros ms' P. unfold addtf3_post in P. rewrite !Eq, !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. change (lo64 Y + 2 ^ 64 * hi64 Y)%Z with (canon Y) in P.
rewrite f128_sub_canon in P. exact P.
Qed.

Definition frexpl_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(P x E : Z) (rest : list cell) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x' e' t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 x')) (Z_to_bv 64 (hi64 x')) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(q - 32, q); (P, P + 4)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' (q - 32) q
/\ rw_cells segs m' P (C4 (Z_to_bv 64 e') :: rest)
/\ frexpl FREXPL_FUEL x E = Some (x', e').

#[using="frexpl_spec"] Lemma frexpl_callq : forall ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (q P X E : Z) (rest : list cell),
stk segs m (q - 32) q -> mem_inv segs m ->
rw_cells segs m P (C4 (Z_to_bv 64 E) :: rest) ->
(P + 4 + Z.of_nat (cells_size rest) <= q - 32 \/ q <= P)%Z -> (32 <= q < 2^64)%Z -> (0 <= P < 2^64)%Z ->
(Z.land (Z.shiftr (hi64 X) 48) 0x7fff <> 0%Z \/ f128_le X F128_ZERO = 0%Z) ->
evt segs (frexpl_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P (canon X) E rest m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) (Z_to_bv 64 P) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_frexpl + 0x0)) fc None m (seg_rom segs)).
Proof. clear - frexpl_spec segs e_frexpl.
intros until rest. intros ST MI CE SEP Hq HP PRE.
assert (Eq : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
assert (Ep : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; lia).
pose proof (rw_cells_bound _ _ _ _ CE) as BR. cbn [cells_size csize] in BR.
apply (proj1 (rw_cells_app segs _ _ [_] _)) in CE. destruct CE as [CE CR]. cbn [cells_size csize Nat.add] in CR.
change (Z.of_nat 4) with 4%Z in CR.
eapply evt_mono.
{ eapply (frexpl_spec ra (Z_to_bv 64 q)); rewrite ?Eq, ?Ep, ?ulit_lo64, ?ulit_hi64; eauto; try lia.
cbv zeta. change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X). rewrite hi64_canon.
unfold F128_ZERO in *. rewrite <- (f128_le_canon X 0) in PRE. replace (canon 0) with 0%Z in PRE by reflexivity. exact PRE. }
intros ms' Q. unfold frexpl_post in Q. rewrite !Eq, !Ep, !ulit_lo64, !ulit_hi64 in Q.
destruct Q as (x' & e' & t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & CE' & HF).
unfold frexpl_postq. exists x', e'. repeat (lazymatch goal with |- ex _ => eexists end).
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split; [|exact HF].
apply (proj2 (rw_cells_app segs _ _ [_] _)). split; [exact CE'|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 4) with 4%Z.
eapply rw_cells_transport; [exact CR | exact MU | exact WM |]. cbn [disjoint_from]. split; [lia|]. split; [lia|exact I].
Qed.

#[using="Type"] Lemma signbitl_canon : forall x, signbitl (canon x) = signbitl x.
Proof. intros. unfold signbitl. rewrite hi64_canon. reflexivity. Qed.
#[using="Type"] Lemma fpclassifyl_canon : forall x, fpclassifyl (canon x) = fpclassifyl x.
Proof. intros. unfold fpclassifyl. rewrite lo64_canon, hi64_canon. reflexivity. Qed.

Definition signbitl_postv (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' =>
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.
#[using="signbitl_spec"] Lemma signbitl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv segs m ->
evt segs (signbitl_postv ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (signbitl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_signbitl + 0x0)) fc None m (seg_rom segs)).
Proof. clear - signbitl_spec segs e_signbitl.
intros until X. intros MI. eapply evt_mono. { eapply signbitl_spec. exact MI. }
intros ms' P. unfold signbitl_post, signbitl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite signbitl_canon in P. exact P.
Qed.

Definition fpclassifyl_postv (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (r : Z) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists a1 a2 a3,
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom segs)
/\ munch [] m m /\ wmono segs m m /\ mem_inv segs m.
#[using="fpclassifyl_spec"] Lemma fpclassifyl_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : word -> option byte) (X : Z),
mem_inv segs m ->
evt segs (fpclassifyl_postv ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (fpclassifyl X) m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 X)) (Z_to_bv 64 (hi64 X)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (e_fpclassifyl + 0x0)) fc None m (seg_rom segs)).
Proof. clear - fpclassifyl_spec segs e_fpclassifyl.
intros until X. intros MI. eapply evt_mono. { eapply fpclassifyl_spec. exact MI. }
intros ms' P. unfold fpclassifyl_post, fpclassifyl_postv in *. rewrite !ulit_lo64, !ulit_hi64 in P.
change (lo64 X + 2 ^ 64 * hi64 X)%Z with (canon X) in P. rewrite fpclassifyl_canon in P. exact P.
Qed.

End G.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Qfw3_c1 QlEo_c1 Q5Rg Q2qa Qy5Y Q4J3 QytA Qnxq QJE4 QUZl Q7S0 Ql2m QGeV QLsg Q8QT Q6q3 Lib.StepGenX2 Lib.GwFold G.GwFamMalloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QkTt.Mq5.
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
Variables (ralloc_slot_entry : Z).
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
Hypothesis AL_ralloc_slot_entry : gw_al ralloc_slot_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_0)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_0).
Definition rauxv_ok : ltac:(gw_rebind_ty (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rauxv_ok segs RATP RC__) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq5.rauxv_ok segs RATP RC__) (@rauxv_ok) gw_tbl_1).
Definition ralloc_fp : ltac:(gw_rebind_ty (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.ralloc_fp RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq5.ralloc_fp RATP) (@ralloc_fp) (gw_ent (@QCa8.Mq5.ralloc_fp RATP) (@ralloc_fp) gw_tbl_2)).
Definition rmalloc_fp : ltac:(gw_rebind_ty (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QkTt.Mq5.rmalloc_fp RATP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rmalloc_fp RATP RC__) (@rmalloc_fp) gw_tbl_3).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_4)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_5))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_6))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_7))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_8))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_9))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_10))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_11))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_12))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_13))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_14)).
Notation gw_tbl_15 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_14))).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_15)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved ralloc_slot_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_ralloc_slot_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Definition RAS_STACK (sc : Z) : Z := 288 + 144 * Z.max 0 (27 - sc).

#[using="Type"] Lemma RAS_STACK_ge sc : 288 <= RAS_STACK sc.
Proof. clear - sc. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_le sc : 0 <= sc -> RAS_STACK sc <= 4176.
Proof. clear - sc. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_mono a b : a <= b -> RAS_STACK b <= RAS_STACK a.
Proof. clear - a b. unfold RAS_STACK. lia. Qed.
#[using="Type"] Lemma RAS_STACK_nest sc j : sc < j -> j <= 26 -> RAS_STACK j + 144 <= RAS_STACK sc.
Proof. clear - sc j. unfold RAS_STACK. lia. Qed.

Definition ras_post (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ ((idx = -1 /\ errv' = Z_to_bv 64 12)
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)

/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition ralloc_slot_stmt (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop)
(as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop) : Prop :=
forall (fuel : nat) (R : Type) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
as_pre st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells segs m (errno_addr tp) [C4 errv] -> mem_inv segs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post as_inv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom segs)).

End RC__1.

End G.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 QytA Q4J3.Mq4 Q4J3.Mq2 QJE4.Mq1.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
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

Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_0)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rbytes_at_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rbytes_at_agree) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rbytes_at_agree)).
Definition rrw_cells_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rrw_cells_agree) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rrw_cells_agree)).
Definition ru64arr_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.ru64arr_agree) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.ru64arr_agree)).
Definition ru8arr_agree : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.ru8arr_agree) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.ru8arr_agree)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="Type"] Lemma rbytes_at_zeros_sub m A n off k :
bytes_at segs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at segs m (A + off) (zeros k).
Proof. clear - segs m A n off k.
intros (H0 & H1 & HB) Hoff Hk. rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

#[using="Type"] Lemma rrw_cells_of_zeros m A n off cs :
bytes_at segs m A (zeros n) -> wr_at segs m A (Z.of_nat n) ->
cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
rw_cells segs m (A + off) cs.
Proof. clear - segs m A n off cs.
intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [gw_exact WF| |].
- rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
- eapply wr_at_sub; [gw_exact HW| lia| lia].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rmrep_set_area_next : forall st m m' a ar p,
rmrep st m -> (s_areas st) !! a = Some ar -> is_Some ((s_regions st) !! (fst p)) ->
munch [(conc st a + 8, conc st a + 16)]%Z m m' -> wmono segs m m' ->
rw_cells segs m' (conc st a) [C8 (wz (a_check ar)); C8 (wz (conc st p)); C4 (wz (a_nslots ar)); C4 (wz 0)] ->
rmrep (set_areas (<[a := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st)) st) m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' a ar p MR Ha Hp MU WM CH.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC.
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
assert (AG : forall A cs, rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells segs m' A cs).
{ intros A cs H HD. pose proof (rw_cells_bound segs m A cs H). eapply rrw_cells_agree; [gw_exact H| | gw_exact WM].
intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
split; [|split; [|split; [|split; [|split]]]].
-  split; [gw_exact Hres|]. split; [gw_exact WR|]. split; [gw_exact DJ|]. split; [| gw_exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
-  destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
change (ctx_tail_cells st') with (ctx_tail_cells st).
split; [apply AG; [gw_exact C1| cbn; gw_expose_fam RATP; lia]|].
split; [eapply ru64arr_agree; [gw_exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; gw_expose_fam RATP; lia); rewrite actives_length in Hx; cbn; gw_expose_fam RATP; lia| gw_exact WM]|].
split; [eapply ru64arr_agree; [gw_exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; gw_expose_fam RATP; lia); rewrite usages_length in Hx; cbn; gw_expose_fam RATP; lia| gw_exact WM]|].
split; [eapply ru8arr_agree; [gw_exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; gw_expose_fam RATP; lia); rewrite unmap_seqs_length in Hx; cbn; gw_expose_fam RATP; lia| gw_exact WM]|].
split; [eapply ru8arr_agree; [gw_exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; gw_expose_fam RATP; lia); rewrite bouncess_length in Hx; cbn; gw_expose_fam RATP; lia| gw_exact WM]|].
apply AG; [gw_exact C6| cbn; gw_expose_fam RATP; lia].
-  destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
split; [apply AG; [gw_exact G1| cbn; gw_expose_fam RATP; lia]|]. split; [apply AG; [gw_exact G2| cbn; gw_expose_fam RATP; lia]|].
split; [apply AG; [gw_exact G3| cbn; gw_expose_fam RATP; lia]|]. split; [apply AG; [gw_exact G4| cbn; gw_expose_fam RGOT_SSP; lia]|]. apply AG; [gw_exact G5| cbn; gw_expose_fam RATP; lia].
-  intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st).
assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
destruct (decide (a' = a)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. destruct (AR a ar Ha) as (A1 & A2 & A3).
split; [unfold pw; cbn [oconc]; rewrite Hconc; gw_exact CH|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; gw_exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
* apply AG; [gw_exact A3| cbn; lia].
+ rewrite lookup_insert_ne in Ha' by congruence. destruct (AR a' ar' Ha') as (A1 & A2 & A3).
destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
{ destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
- rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
Z.div_mod_to_equations. lia.
- pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
change (pw st' (a_next ar')) with (pw st (a_next ar')).
split; [apply AG; [gw_exact A1| cbn; lia]|]. split.
* intros k Hk. rewrite MC. apply AG; [apply A2; gw_exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
* apply AG; [gw_exact A3| cbn; lia].
-  intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| gw_exact Hw8].
rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [gw_exact R|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
-  intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
+ eapply wr_at_transport; [gw_exact HWr| gw_exact WM].
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| gw_exact V].
eapply rbytes_at_agree; [gw_exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); unfold alloc_ceiling in RC; pose proof (round_up_pg_ge (r_len r)); lia).
assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

#[using="Type"] Lemma rmrep_new_area : forall st m (p : aptr) r chk,
rmrep st m -> (s_areas st) !! p = None ->
(s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(forall k, 0 <= k < NSLOTS -> (s_metas st) !! (aadd p (AREA_HDR + META_SIZE * k)) = None) ->
rw_cells segs m (conc st p) [C8 (wz chk); C8 (wz 0); C4 (wz NSLOTS); C4 (wz 0)] ->
(forall k, 0 <= k < NSLOTS -> rw_cells segs m (conc st p + AREA_HDR + META_SIZE * k) (meta_cells st meta0)) ->
rw_cells segs m (conc st p + 4064) [CB 32 (zeros 32)] ->
rmrep (set_areas (<[p := mkArea chk None NSLOTS]> (s_areas st)) st) m.
Proof. clear - segs.
intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
set (st' := set_areas _ st).
assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
split; [|split; [|split; [|split; [|split]]]].
- split; [gw_exact Hres|]. split; [gw_exact WR|]. split; [gw_exact DJ|]. split; [| gw_exact WG].
intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
+ exists r. repeat split; assumption.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
- gw_exact CX.
- gw_exact GL.
- intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
destruct (decide (a' = p)) as [->|NE].
+ rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
split; [gw_exact HDR|]. split; [| gw_exact PAD].
intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. gw_exact Hk.
+ rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
- gw_exact GR.
- gw_exact SH.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved"] Lemma rfresh_page_avoids : forall st m (p : aptr) r a,
rmrep st m -> (s_regions st) !! (fst p) = Some r -> r_kind r <> RKGroup ->
0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) -> snd p mod 4096 = 0 -> lr_lo r <= r_base r + snd p ->
(s_areas st) !! p = None ->
conc st p <= a < conc st p + 4096 -> ~ rrepfoot st a.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 ROM_reservedZ LAY_ref_reserved RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
pose proof (conc_region' st p r Hr) as Cp.
destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). unfold alloc_ceiling in RBC.
pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
+ rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
assert (NEo : snd ak <> snd p).
{ intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
Z.div_mod_to_equations. lia.
+ pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
- destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
- destruct C as (rid & rg & v & Hrg & Krg & Hin & _).
assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
- gw_expose_fam RGOT_SSP. lia.
- gw_expose_fam RATP. lia.
Qed.

End RC__1.

End G.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq4.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QCa8.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition free_code (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z) : list Z :=
[0x1c050463; 0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00050493; 0x1ac000ef; 0x02053583; 0xffd4c683; 0x00c5d613; 0x01f6f413; 0x00060e63; 0x01f5f613; 0x00061a63; 0xfffff637; 0x00c5f633; 0xff060613; 0x0200006f; 0x0055d613; w_21; 0x07e67613; w_23; 0x00c70633; 0x00065603; 0x00461613; 0x01053703; 0x028607b3; 0x0a000813; 0x00c70633; 0x00f607b3; 0x00c78613; 0x0056d713; 0x0306e663; 0x00500693; 0x00d70463; 0x00000023; 0x0087e703; 0x00400693; 0x00e6e463; 0x00000023; 0x0077c683; 0x00068463; 0x00000023; 0x409606b3; 0x00e6f463; 0x00000023; 0x40e606b3; 0x0006c683; 0x00068463; 0x00000023; 0x00064603; 0x00060463; 0x00000023; 0x00100613; 0x00200693; 0xfff00713; 0x00b696bb; 0x01c50593; 0x0086163b; 0xfee48ea3; 0xfe049f23; 0xfff6869b; w_64; 0x01c52783; 0x01852803; 0x00f86833; 0x00c878b3; 0x00088463; 0x00000023; w_71; 0x02078863; 0x00c8083b; 0x02d80463; 0x00c7883b; 0x06088e63; 0x1605a8af; 0x00f89663; 0x1f05a2af; 0xfe029ae3; 0x0008889b; 0xfaf89ee3; 0x0640006f; 0x00088e63; w_85; w_86; 0x00050493; 0x00058513; w_89; 0x00048513; 0x00040593; 0x16c000ef; 0x00050413; 0x00058493; w_95; w_96; w_97; 0x02048463; w_99; 0x00050913; 0x00052983; 0x00040513; 0x00048593; w_104; 0x01392023; 0x0080006f; 0x0105a023; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z).
Variables (hi_21 hi_64 hi_85 hi_95 : bv 20).
Variables (lo_23 lo_71 lo_86 lo_96 : bv 12).
Variables (joff_89 joff_97 joff_99 joff_104 : bv 21).
Hypothesis CODE : code_at segs base (free_code w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 460.
Let rfree_entry := (base + 0)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Auipc 14 hi_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (OpImm ALU_ADD 14 14 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Auipc 14 hi_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis D_71 : decode_any (Z_to_bv 32 w_71) = Some (Load SZ1 false 17 14 lo_71, 4%Z).
Hypothesis E_71 : is_ecall (Z_to_bv 32 w_71) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 11 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (OpImm ALU_ADD 11 11 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_89 : decode_any (Z_to_bv 32 w_89) = Some (Jal 1 joff_89, 4%Z).
Hypothesis E_89 : is_ecall (Z_to_bv 32 w_89) = false.
Hypothesis D_95 : decode_any (Z_to_bv 32 w_95) = Some (Auipc 10 hi_95, 4%Z).
Hypothesis E_95 : is_ecall (Z_to_bv 32 w_95) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (OpImm ALU_ADD 10 10 lo_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Jal 1 joff_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_99 : decode_any (Z_to_bv 32 w_99) = Some (Jal 1 joff_99, 4%Z).
Hypothesis E_99 : is_ecall (Z_to_bv 32 w_99) = false.
Hypothesis D_104 : decode_any (Z_to_bv 32 w_104) = Some (Jal 1 joff_104, 4%Z).
Hypothesis E_104 : is_ecall (Z_to_bv 32 w_104) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_21) 12 + (base + 84) + bv_signed lo_23)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_71 : gw_anch (Z.shiftl (bv_signed hi_64) 12 + (base + 256) + bv_signed lo_71)%Z (RATP + 131731).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z (RATP + 131960).
Hypothesis ANCH_96 : gw_anch (Z.shiftl (bv_signed hi_95) 12 + (base + 380) + bv_signed lo_96)%Z (RATP + 131960).
Hypothesis LINK_89 : gw_anch (base + 356 + bv_signed joff_89)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_97 : gw_anch (base + 388 + bv_signed joff_97)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_99 : gw_anch (base + 396 + bv_signed joff_99)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_104 : gw_anch (base + 416 + bv_signed joff_104)%Z (rmunmap_entry + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))).
Definition rget_meta_post : ltac:(gw_rebind_ty (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QCa8.Mq4.rget_meta_post segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QCa8.Mq4.rget_meta_post segs) (@rget_meta_post) gw_tbl_10).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_11).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_12)).

Hypothesis sllw1_word' : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.sllw1_word') (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).
Hypothesis rget_meta_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.rget_meta_spec) (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_13))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).

Definition rmrep_shadow_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_shadow_read) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_shadow_read)).
Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).
Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rmrep_wr8 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr8) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr8)).
Definition rmrep_wr16 : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_wr16) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_wr16)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_trans : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_trans) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_trans)).

Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

#[using="rerrno_loc_entry rmunmap_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rfree_entry rmunmap_entry sllw1_word' rget_meta_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold alloc_ceiling, UNIT, IB in *; lia.
Section RC__1.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma zx32_wz x : 0 <= x < 2^32 -> zx32 (wz x) = wz x.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry x. intros. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma meta_word_sc2 mr : mw_ok mr -> Z.land (Z.shiftr (meta_word mr) 5) 126 = 2 * m_sizeclass mr.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry mr.
intros (LI & FB & SCR & ML).
assert (E : 126 = Z.ldiff (Z.ones 7) (Z.ones 1)) by first [reflexivity | (cbn; lia)]. rewrite E, land_ldiff_distr.
rewrite Z.land_ones, Z.ldiff_ones_r, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
change (2^7) with 128. change (2^1) with 2. change (2^5) with 32. unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with (m_last_idx mr + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr) * 32) by lia.
rewrite Z.div_add, (Z.div_small (m_last_idx mr)) by lia.
replace (0 + (m_freeable mr + 2 * m_sizeclass mr + 128 * m_maplen mr)) with ((m_freeable mr + 2 * m_sizeclass mr) + m_maplen mr * 128) by lia.
rewrite Z.mod_add, Z.mod_small by lia.
replace (m_freeable mr + 2 * m_sizeclass mr) with (m_freeable mr + m_sizeclass mr * 2) by lia.
rewrite Z.div_add, Z.div_small by lia. lia.
Qed.

#[using="base rvm_wait_entry rfree_entry rmunmap_entry"] Lemma meta_word_pg mr : mw_ok mr -> meta_word mr - meta_word mr mod 4096 = 4096 * m_maplen mr.
Proof. clear - base rvm_wait_entry rfree_entry rmunmap_entry mr.
intros (LI & FB & SCR & ML). unfold meta_word.
replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)
with ((m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr) + m_maplen mr * 4096) by lia.
rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Definition rfhead_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) (st1 : mstate) (g : aptr) (idx li : Z) : machine_state -> Prop :=
fun ms' => exists x1 x5 x6 x7 junk m',
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (li + 1) - 1))) (Z_to_bv 64 (Z.shiftl (bv_signed hi_64) 12 + (base + 256))) x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x104)) fc None m' (seg_rom segs)
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ rw_cells segs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rmrep st1 m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE D_64 E_64 LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved sllw1_word' rfree_entry rmunmap_entry"] Lemma rfree_head3 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (b3 lo8 hi E rsv : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
rmrep st m0 -> mem_inv segs m0 -> ticks_ok st ->
stk segs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells segs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono segs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 ->
r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
0 <= rsv <= E - (r_base r + po) -> bytes_at segs m0 (E - rsv) [b8 0] -> bytes_at segs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt segs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 E) a3 (wz rsv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb4)) fc None m0 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE D_64 E_64 LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved sllw1_word' rfree_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until rsv. intros po idx mr st1 MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL HK3 HK2 HK1 LI FBL SC ML B3 ELO EHI RSV RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
pose proof (munch_refl [(r_base r + po - 3, r_base r + po)]%Z m0) as MU. pose proof (wmono_refl segs m0) as WM.
pose proof (bytes_at_read segs m0 _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
pose proof (bytes_at_read segs m0 _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.

st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }

st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }

change (Z_to_bv 64 E) with (wa E).
st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }

st1. st1. st1. st1. st1. st1.
rewrite (unsigned_lit idx) by lia. rewrite sllw1_word' by lia. rewrite (wz_unsigned (meta_word mr)) by (unfold meta_word; lia).

pose proof MR1 as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (SOK3 : store_ok segs mX (wa (bv_unsigned a0 + -3)) 1 = true)
by (replace (bv_unsigned a0 + -3) with (r_base r + (po - 3)) by lia; apply (wr_at_store_ok segs mX _ _ (po - 3) 1 HWr); cbn; lia) end.
st1.
pose proof (rmrep_wr8 st _ (aadd p (-3)) 255 r MR1 TK Hr Hk ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR2.
cbn [aadd snd] in MR2. fold po in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -3))) [b8 255])
by (rewrite le1_neg1; f_equal; unfold wa; f_equal; lia) end.
store_done.
pose proof (ticks_ok_wr8 st (aadd p (-3)) 255 TK) as TK2.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof MR2 as (_ & _ & _ & _ & _ & SH2); destruct (SH2 (fst p) r Hr Hk) as [HWr2 _]; clear SH2;
assert (SOK2 : store_ok segs mX (wa (bv_unsigned a0 + -2)) 2 = true)
by (replace (bv_unsigned a0 + -2) with (r_base r + (po - 2)) by lia; apply (wr_at_store_ok segs mX _ _ (po - 2) 2 HWr2); cbn; lia) end.
st1.
pose proof (rmrep_wr16 _ _ (aadd p (-2)) 0 r MR2 TK2 Hr Hk ltac:(cbn; lia) ltac:(cbn; lia)
ltac:(intros b gh' Hb Hfb; cbn [aadd snd]; destruct (HCLR b gh' Hb Hfb); lia) ltac:(lia)) as MR3.
cbn [aadd snd] in MR3. fold po in MR3. fold st1 in MR3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (po + -2))) (le2 (wz 0)))
by (f_equal; unfold wa; f_equal; lia) end.
store_done. clear MR2 TK2 HWr HWr2.

st1. rewrite (all_word (meta_word mr)) by (unfold meta_word; lia).
replace (meta_word mr mod 32) with (m_last_idx mr) by (unfold meta_word; Z.div_mod_to_equations; lia).
st1.

apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
2:{ cbn [ivs_covered]. split; [|exact I].
intros x Hx. right. right. exists (fst p), r.
assert (CASES : x - r_base r = po - 3 \/ x - r_base r = po - 2 \/ x - r_base r = po - 1) by lia.
destruct CASES as [E1|[E1|E1]]; [exists b3| exists lo8| exists hi]; rewrite E1; (split; [gw_exact Hr|]); (split; [gw_exact Hk|]); (split; [lia|]); assumption. }
apply evt_done. unfold rfhead_post.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
do 6 eexists.
split; [reflexivity|].
split; [eapply rpres_except_trans; [gw_exact PE0| gw_exact MU]|]. split; [gw_exact WM0|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|]. gw_exact MR3.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE D_64 E_64 LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved sllw1_word' rfree_entry rmunmap_entry"] Lemma rfree_head2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (x1 : word) F fc
(m m0 : word -> option byte) (junk : list byte) (lo : Z) st (p : aptr) r g (base_ : aptr) (b3 lo8 hi r32 : Z),
let po := snd p in
let idx := Z.land b3 31 in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base_ + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m0 -> mem_inv segs m0 -> ticks_ok st ->
stk segs m0 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells segs m0 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rpres_except (rfree_fp st lo (bv_unsigned sp)) m m0 -> wmono segs m m0 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 -> 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
meta_slot st g -> m_mem mr = Some base_ -> fst base_ = fst p -> 0 <= snd base_ ->
cell_read (get_shadow st (fst p)) (po - 3) = Known b3 -> cell_read (get_shadow st (fst p)) (po - 2) = Known lo8 -> cell_read (get_shadow st (fst p)) (po - 1) = Known hi ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
0 <= b3 < 256 -> idx <= m_last_idx mr ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at segs m0 (E - 4) (le4 (wz r32)) /\ bytes_at segs m0 (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at segs m0 (E - rsv) [b8 0] -> bytes_at segs m0 E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt segs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6c)) fc None m0 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE D_64 E_64 LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved sllw1_word' rfree_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until r32. intros po idx mr st1 stride E rsv0 rsv MR1 MI TK ST LO SLO FR PE0 WM0 Hr Hk HP AL P16 PHI MSL Hmem FB SB0 HK3 HK2 HK1
AV FRD LI FBL SC ML B3 Hidx S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR1 as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (HB : conc st base_ = r_base r + snd base_) by (apply conc_region'; rewrite FB; gw_exact Hr).
assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
unfold alloc_ceiling, UNIT, IB in *.
pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m0 g MR1 MSL) as MM.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.

st1. st1. st1. st1. st1. st1. st1. cbn [oconc].
replace (conc st base_ + stride + stride * idx + 12) with E by (unfold E; lia).
fold rsv0.

st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
-
replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[gw_exact MR1| gw_exact MI| gw_exact TK| gw_exact ST| unfold alloc_ceiling; lia| lia| gw_exact FR| gw_exact PE0| gw_exact WM0| gw_exact Hr| gw_exact Hk| gw_exact HP| gw_exact AL| lia| lia
| gw_exact MSL| gw_exact HK3| gw_exact HK2| gw_exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| gw_exact RB0r| gw_exact RE0| gw_exact HCLR].
-
destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
pose proof (bytes_at_read segs m0 _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
replace (E - 4) with (conc st base_ + stride + stride * idx + 8) in RD4 by (unfold E; lia).
pose proof (bytes_at_read segs m0 _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
replace (E - 5) with (conc st base_ + stride + stride * idx + 7) in RD5 by (unfold E; lia).

st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }

st1.
rewrite zx32_wz by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }

st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned). rewrite Egw.
subst mr.
eapply (rfree_head3 ra sp gp tp t0 t1 t2 s0 s1 a0 _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m m0 junk lo st p r g b3 lo8 hi E rsv);
[gw_exact MR1| gw_exact MI| gw_exact TK| gw_exact ST| unfold alloc_ceiling; lia| lia| gw_exact FR| gw_exact PE0| gw_exact WM0| gw_exact Hr| gw_exact Hk| gw_exact HP| gw_exact AL| lia| lia
| gw_exact MSL| gw_exact HK3| gw_exact HK2| gw_exact HK1| lia| lia| lia| lia| lia| lia| lia| lia| gw_exact RB0r| gw_exact RE0| gw_exact HCLR].
Qed.

#[using="RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 lo_23 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 ANCH_23 LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved sllw1_word' rget_meta_spec rfree_entry rmunmap_entry"] Lemma rfree_head : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(lo : Z) st (p : aptr) r g gh ar (b3 lo8 hi r32 : Z),
let sh := get_shadow st (fst p) in
let po := snd p in
let off16 := lo8 + 256 * hi in
let idx := Z.land b3 31 in
let base_ := aadd p (- (UNIT * off16) - UNIT) in
let mr := get_meta_rec st g in
let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
let stride := get_stride mr in
let E := conc st base_ + UNIT + stride * idx + stride - IB in
let rsv0 := Z.shiftr b3 5 in
let rsv := if 160 <=? b3 then r32 else rsv0 in
rmrep st m -> mem_inv segs m -> ticks_ok st ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
(s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup ->
bv_unsigned a0 = r_base r + po -> po mod 16 = 0 ->
16 <= po -> 16 * off16 + 16 <= po -> po + 16 <= round_up_pg (r_len r) ->
cell_read sh (po - 4) = Known 0 -> cell_read sh (po - 3) = Known b3 ->
cell_read sh (po - 2) = Known lo8 -> cell_read sh (po - 1) = Known hi ->
(s_groups st) !! base_ = Some gh -> g_meta gh = Some g -> meta_slot st g -> 0 <= snd g ->
m_mem mr = Some base_ ->
(s_areas st) !! (area_of g) = Some ar -> a_check ar = c_secret (ctx st) ->
0 <= m_avail mr < 2^32 -> 0 <= m_freed mr < 2^32 -> 0 <= c_secret (ctx st) < 2^64 ->
0 <= m_last_idx mr < 32 -> 0 <= m_freeable mr < 2 -> 0 <= m_sizeclass mr < 64 -> 0 <= m_maplen mr < 2^40 ->
idx <= m_last_idx mr -> Z.testbit (m_avail mr) idx = false -> Z.testbit (m_freed mr) idx = false ->
(m_sizeclass mr < 48 -> size_class (m_sizeclass mr) * idx <= off16 < size_class (m_sizeclass mr) * (idx + 1)) ->
(48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
(m_maplen mr <> 0 -> off16 <= m_maplen mr * 256 - 1) ->

(m_maplen mr = 0 \/ m_last_idx mr <> 0 -> m_sizeclass mr < 48) ->
UNIT <= stride -> r_base r + po <= E -> E + 1 <= r_base r + round_up_pg (r_len r) ->
(160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at segs m (E - 4) (le4 (wz r32)) /\ bytes_at segs m (E - 5) [b8 0]) ->
rsv <= E - (r_base r + po) -> bytes_at segs m (E - rsv) [b8 0] -> bytes_at segs m E [b8 0] ->
(forall b gh', (s_groups st) !! b = Some gh' -> fst b = fst p -> po <= snd b \/ snd b + 16 <= po) ->
evt segs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom segs)).
Proof. clear - RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_21 lo_23 CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 ANCH_23 LAY_lo_RATP LAY_hi_RATP RNG_RDEBRUIJN LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_RSIZE_CLASSES ROM_reservedZ LAY_ref_reserved sllw1_word' rget_meta_spec rfree_entry rmunmap_entry segs base RATP. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until r32. intros sh po off16 idx base_ mr st1 stride E rsv0 rsv MR MI TK ST LO SLO Hr Hk HP AL P16 PLO PHI HK4 HK3 HK2 HK1 Hgh Hg MSL G0 Hmem Har Hchk
AV FRD SE LI FBL SC ML Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 ELO EHI BIG RSVLE RB0r RE0 HCLR.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr). pose proof (rreserved_disjoint _ _ RFr) as [DR1 DR2].
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MUs.
pose proof (wmono_refl segs m) as WM.
assert (IDX : 0 <= idx < 32).
{ unfold idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
destruct (rmrep_shadow_read st m (fst p) r (po - 3) b3 MR Hr Hk ltac:(lia) HK3) as [_ B3].
assert (RSV0 : 0 <= rsv0 < 8).
{ unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
assert (RSVR : 0 <= rsv < 2^32).
{ unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
assert (FB : fst base_ = fst p) by first [reflexivity | (cbn; lia)].
assert (HB : conc st base_ = r_base r + snd base_) by (apply conc_region'; rewrite FB; gw_exact Hr).
assert (SB0 : 0 <= snd base_) by (unfold base_; cbn; unfold UNIT; lia).

revert BIG RB0r RE0.
unfold rfree_entry, alloc_ceiling, UNIT, IB in *. intros BIG RB0r RE0.

st1. if_cases K0; zify_cond K0. { exfalso. lia. }
carve_frame 48%nat ST.
st1. st1. st1. st1. st1. st1. st1.

st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR1 : rmrep st mX) by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MUs | gw_exact WM |]; intros l h [E1|[]]; inversion E1; subst; unfold alloc_ceiling; lia) end.
eapply evt_cut.
{ eapply rget_meta_spec with (st := st) (p := p) (r := r) (g := g) (gh := gh) (ar := ar) (b3 := b3) (lo := lo8) (hi := hi).
all: try eassumption. all: try lia. }
intros ms' (ga2 & ga3 & ga4 & ga5 & ->).
try g_ret_pc_any.

pose proof (rmeta_slot_bounds st _ g MR1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (rmrep_meta_chunk st mX g MR1 MSL) as MM;
destruct (rmrep_shadow_read st mX (fst p) r (po - 3) b3 MR1 Hr Hk ltac:(lia) HK3) as [R3 _] end.
fold mr in MM. unfold meta_cells in MM. rewrite Hmem in MM. cbn [pw oconc] in MM.
replace (r_base r + (po - 3)) with (bv_unsigned a0 + -3) in R3 by lia.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. clearbody gw.
assert (MW : mw_ok mr) by (unfold mw_ok; lia).
pose proof (meta_word_range mr MW) as MWR. pose proof (meta_word_maplen mr MW) as MW12.
pose proof (meta_word_last_idx mr MW) as MW31. pose proof (meta_word_sc2 mr MW) as MWS. pose proof (meta_word_pg mr MW) as MWP.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (K2 : forall a4v a5v a6v, evt segs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 (base + 0x24)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 (wz (conc st g)) (wz (meta_word mr))
(Z_to_bv 64 stride) (wz b3) a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x6c)) fc None mX (seg_rom segs))) end.
{ intros a4v a5v a6v.
lazymatch type of MUs with munch ?W _ _ => assert (DJ : forall A n, A + n <= lo -> disjoint_from W A n) by (intros A n HA; cbn; lia) end.
lazymatch type of MUs with munch ?W m ?mY =>
assert (PE0 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m mY)
by (apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp)) W); [gw_exact MUs| gw_exact WM|];
cbn [ivs_covered]; split; [|exact I]; intros x Hx; apply rfree_fp_stack; lia) end.
subst rsv rsv0 E stride mr.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
eapply (rfree_head2 ra sp gp tp t0 t1 t2 s0 s1 a0 a4v a5v a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ F fc m mX _ lo st p r g base_ b3 lo8 hi r32) end;
[gw_exact MR1| assumption| gw_exact TK| gw_exact ST| ulia| ulia| gw_exact FR| gw_exact PE0| gw_exact WM| gw_exact Hr| gw_exact Hk| gw_exact HP| gw_exact AL| ulia| ulia
| gw_exact MSL| gw_exact Hmem| gw_exact FB| gw_exact SB0| gw_exact HK3| gw_exact HK2| gw_exact HK1| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia| ulia
| intros Hb3; destruct (BIG Hb3) as (X1 & X2 & X3 & X4); split; [gw_exact X1|]; split; [gw_exact X2|]; split;
(eapply bytes_at_transport; [eassumption| gw_exact MUs| apply DJ; cbn; try rewrite length_le4; ulia])
| ulia
| gw_exact RB0r
| gw_exact RE0
| gw_exact HCLR]. }

st1. st1. st1. st1. fold idx. rewrite MW12.
assert (Egw : gw = wz (conc st g)) by (rewrite <- HG; unfold wz; symmetry; apply Z_to_bv_bv_unsigned).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (KS : forall a2v a4v, (m_maplen mr = 0 \/ m_last_idx mr <> 0) ->
evt segs (rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m st1 g idx (m_last_idx mr))
(MS (mkR (Z_to_bv 64 (base + 0x24)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0 gw (wz (meta_word mr))
a2v (wz b3) a4v ga5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x50)) fc None mX (seg_rom segs))) end.
{ intros a2v a4v COND. specialize (SC48 COND).
assert (STR : stride = 16 * size_class (m_sizeclass mr)).
{ unfold stride, get_stride. destruct COND as [C|C]; [rewrite (proj2 (Z.eqb_eq _ _) C), andb_false_r; reflexivity|].
rewrite (proj2 (Z.eqb_neq _ _) C). reflexivity. }

assert (MW5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64) by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
st1. st1. st1. try rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite MWS. st1. st1.
replace ((RDEBRUIJN + 32) + m_sizeclass mr * 2) with ((RDEBRUIJN + 32) + 2 * m_sizeclass mr) by lia.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (RS' : ov_read_bytes segs mX (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * m_sizeclass mr)) 2 = Some (le2 (wz (size_class (m_sizeclass mr))))) end.
{ replace (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * m_sizeclass mr)) with (wa ((RDEBRUIJN + 32) + 2 * m_sizeclass mr)) by ((gw_expose_fam RDEBRUIJN; unfold wa); f_equal; lia).
apply rsize_classes_read; [assumption| lia]. }
pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZ.
st1. try rewrite (Z.mod_small (size_class (m_sizeclass mr))) by lia.
st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
replace (Z_to_bv 64 (size_class (m_sizeclass mr) * 16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
rewrite Egw. apply K2. }

st1. if_cases Km; zify_cond Km; rewrite ?unsigned_lit in Km by lia.
- apply KS. left. gw_exact Km.
-
st1. rewrite MW31. st1. if_cases Kl; zify_cond Kl; rewrite ?unsigned_lit in Kl by lia.
+ apply KS. right. gw_exact Kl.
+
st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
replace (Z_to_bv 64 (4096 * m_maplen mr + -16)) with (Z_to_bv 64 stride).
2:{ unfold stride, get_stride. rewrite (proj2 (Z.eqb_eq _ _) Kl). replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. f_equal. unfold UNIT. lia. }
rewrite Egw. apply K2.
Qed.

End RC__1.

End G.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 QDUx.Mq5.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QCa8.Mq4.
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

Definition free_code (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z) : list Z :=
[0x1c050463; 0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00050493; 0x1ac000ef; 0x02053583; 0xffd4c683; 0x00c5d613; 0x01f6f413; 0x00060e63; 0x01f5f613; 0x00061a63; 0xfffff637; 0x00c5f633; 0xff060613; 0x0200006f; 0x0055d613; w_21; 0x07e67613; w_23; 0x00c70633; 0x00065603; 0x00461613; 0x01053703; 0x028607b3; 0x0a000813; 0x00c70633; 0x00f607b3; 0x00c78613; 0x0056d713; 0x0306e663; 0x00500693; 0x00d70463; 0x00000023; 0x0087e703; 0x00400693; 0x00e6e463; 0x00000023; 0x0077c683; 0x00068463; 0x00000023; 0x409606b3; 0x00e6f463; 0x00000023; 0x40e606b3; 0x0006c683; 0x00068463; 0x00000023; 0x00064603; 0x00060463; 0x00000023; 0x00100613; 0x00200693; 0xfff00713; 0x00b696bb; 0x01c50593; 0x0086163b; 0xfee48ea3; 0xfe049f23; 0xfff6869b; w_64; 0x01c52783; 0x01852803; 0x00f86833; 0x00c878b3; 0x00088463; 0x00000023; w_71; 0x02078863; 0x00c8083b; 0x02d80463; 0x00c7883b; 0x06088e63; 0x1605a8af; 0x00f89663; 0x1f05a2af; 0xfe029ae3; 0x0008889b; 0xfaf89ee3; 0x0640006f; 0x00088e63; w_85; w_86; 0x00050493; 0x00058513; w_89; 0x00048513; 0x00040593; 0x16c000ef; 0x00050413; 0x00058493; w_95; w_96; w_97; 0x02048463; w_99; 0x00050913; 0x00052983; 0x00040513; 0x00048593; w_104; 0x01392023; 0x0080006f; 0x0105a023; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z).
Variables (hi_21 hi_64 hi_85 hi_95 : bv 20).
Variables (lo_23 lo_71 lo_86 lo_96 : bv 12).
Variables (joff_89 joff_97 joff_99 joff_104 : bv 21).
Hypothesis CODE : code_at segs base (free_code w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 460.
Let rnontrivial_free_entry := (base + 732)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Auipc 14 hi_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (OpImm ALU_ADD 14 14 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Auipc 14 hi_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis D_71 : decode_any (Z_to_bv 32 w_71) = Some (Load SZ1 false 17 14 lo_71, 4%Z).
Hypothesis E_71 : is_ecall (Z_to_bv 32 w_71) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 11 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (OpImm ALU_ADD 11 11 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_89 : decode_any (Z_to_bv 32 w_89) = Some (Jal 1 joff_89, 4%Z).
Hypothesis E_89 : is_ecall (Z_to_bv 32 w_89) = false.
Hypothesis D_95 : decode_any (Z_to_bv 32 w_95) = Some (Auipc 10 hi_95, 4%Z).
Hypothesis E_95 : is_ecall (Z_to_bv 32 w_95) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (OpImm ALU_ADD 10 10 lo_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Jal 1 joff_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_99 : decode_any (Z_to_bv 32 w_99) = Some (Jal 1 joff_99, 4%Z).
Hypothesis E_99 : is_ecall (Z_to_bv 32 w_99) = false.
Hypothesis D_104 : decode_any (Z_to_bv 32 w_104) = Some (Jal 1 joff_104, 4%Z).
Hypothesis E_104 : is_ecall (Z_to_bv 32 w_104) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_21) 12 + (base + 84) + bv_signed lo_23)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_71 : gw_anch (Z.shiftl (bv_signed hi_64) 12 + (base + 256) + bv_signed lo_71)%Z (RATP + 131731).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z (RATP + 131960).
Hypothesis ANCH_96 : gw_anch (Z.shiftl (bv_signed hi_95) 12 + (base + 380) + bv_signed lo_96)%Z (RATP + 131960).
Hypothesis LINK_89 : gw_anch (base + 356 + bv_signed joff_89)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_97 : gw_anch (base + 388 + bv_signed joff_97)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_99 : gw_anch (base + 396 + bv_signed joff_99)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_104 : gw_anch (base + 416 + bv_signed joff_104)%Z (rmunmap_entry + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_0))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))).
Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_10).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_11)).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_region : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_region) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_region)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).

#[using="rerrno_loc_entry rmunmap_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rnontrivial_free_entry rmunmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

#[using="base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rnontrivial_free_entry rmunmap_entry"] Lemma rfree_fp_meta0 : forall st st0 m lo sp q a, rmrep st m -> meta_slot st q -> s_regions st0 = s_regions st ->
conc st q <= a < conc st q + 40 -> rfree_fp st0 lo sp a.
Proof. clear - base RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry ROM_reservedZ LAY_ref_reserved rnontrivial_free_entry rmunmap_entry.
intros st st0 m lo sp q a MR (ar & arr & k & Har & Hk & Eq) ER Ha. pose proof MR as (WF & _).
destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply rfree_fp_region; [rewrite ER; gw_exact Hra | gw_exact NK | lia].
Qed.

Definition rftriv_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (C : Z -> Prop) (m : word -> option byte) (st' : mstate) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ rpres_except C m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 lo_71 CODE D_71 E_71 ANCH_71 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rnontrivial_free_entry rmunmap_entry"] Lemma rfree_triv : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st0 st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
let st' := upd_meta g (m_set_freed (m_freed mr + bit idx)) st in
rmrep st m -> mem_inv segs m -> meta_slot st g ->
s_regions st = s_regions st0 -> s_areas st = s_areas st0 ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
m_freed mr <> 0 -> Z.lor (m_freed mr) (m_avail mr) + bit idx <> mask_upto (m_last_idx mr) ->
rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt segs (rftriv_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (rfree_fp st0 lo (bv_unsigned sp)) m st')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 (Z.shiftl (bv_signed hi_64) 12 + (base + 256))) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x104)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 lo_71 CODE D_71 E_71 ANCH_71 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved rnontrivial_free_entry rmunmap_entry segs base hi_64 RATP. gw_expose_fam RATP.
intros until idx. intros mr st' MR MI MSL ER EA HF HA HL HI TF TA Hfz Hall FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl segs m) as WM.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by gw_exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true.

st1.

step. if_cases K2; zify_cond K2.
{ exfalso. apply Hfz. apply (proj1 (sxv_zero (m_freed mr) ltac:(lia))). first [gw_exact K2 | rewrite wz_unsigned in K2 by assumption; gw_exact K2]. }
clear K2.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by gw_exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
{ exfalso. apply Hall. unfold bit, mask_upto. apply (proj1 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
rewrite !wz_unsigned in K3 by apply sxv_range. gw_exact K3. }
clear K3 RSUM.

step. rewrite (wz_unsigned (sxv (2 ^ idx))), (wz_unsigned (sxv (m_freed mr))) by assumption.
rewrite (Z.add_comm (sxv (m_freed mr)) (sxv (2 ^ idx))). rewrite addw_word.
step. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
clear K4 RL.

step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep st' mX) end.
{ unfold st'. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [gw_exact MR | gw_exact MSL | gw_exact MUg | gw_exact WM |].
rewrite HG in MM.
eapply rw_cells_congr; [ | | | gw_exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
unfold bit. rewrite (free_store_val (m_freed mr) idx) by (assumption || lia). reflexivity.
- reflexivity.
- cbn. tauto. }
clear MUg MM.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z mX) as MUs;
pose proof (wmono_refl segs mX) as WMs end.
step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [gw_exact MR' | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st0 lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply rfree_fp_stack. lia.
- intros x Hx. eapply (rfree_fp_meta0 st st0 m lo (bv_unsigned sp) g); [gw_exact MR | gw_exact MSL | symmetry; gw_exact ER | lia]. }
finish.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 lo_71 CODE D_71 E_71 ANCH_71 LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved rnontrivial_free_entry rmunmap_entry"] Lemma rfree_tocall : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
(m : word -> option byte) (st : mstate) (g : aptr) (idx : Z),
let mr := get_meta_rec st g in
rmrep st m -> mem_inv segs m -> meta_slot st g ->
0 <= m_freed mr < 2^32 -> 0 <= m_avail mr < 2^32 -> 0 <= m_last_idx mr < 32 -> 0 <= idx <= m_last_idx mr ->
Z.testbit (m_freed mr) idx = false -> Z.testbit (m_avail mr) idx = false ->
(m_freed mr = 0 \/ Z.lor (m_freed mr) (m_avail mr) + bit idx = mask_upto (m_last_idx mr)) ->
evt segs (fun ms' => exists x2 x3 x4 x5 x6 x7,
ms' = MS (mkR (Z_to_bv 64 (base + 0x174)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(Z_to_bv 64 (conc st g)) (Z_to_bv 64 idx) x2 x3 x4 x5 x6 x7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rnontrivial_free_entry) fc None m (seg_rom segs))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 idx) a0
(wz (conc st g)) (Z_to_bv 64 (conc st g + 28)) (wz (sxv (2 ^ idx))) (wz (sxv (2 ^ (m_last_idx mr + 1) - 1))) (Z_to_bv 64 (Z.shiftl (bv_signed hi_64) 12 + (base + 256))) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x104)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 lo_71 CODE D_71 E_71 ANCH_71 LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_ref_reserved rnontrivial_free_entry rmunmap_entry segs base hi_64 RATP. gw_expose_fam RATP.
intros until idx. intros mr MR MI MSL HF HA HL HI TF TA HNT.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ g MR MSL) as (GB0 & GB1 & GB2 & GB4 & _).
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. fold mr in MM. unfold meta_cells in MM.
set (gw := wz (conc st g)) in *. assert (HG : bv_unsigned gw = conc st g) by (subst gw; apply wz_unsigned; lia).
rewrite <- HG in MM. replace (Z_to_bv 64 (conc st g + 28)) with (Z_to_bv 64 (bv_unsigned gw + 28)) by (rewrite HG; reflexivity).
replace (Z_to_bv 64 (conc st g)) with gw by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
clearbody gw.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (_ & NL & _).
pose proof (sxv_range (2 ^ idx)) as RS. pose proof (sxv_range (m_freed mr)) as RF. pose proof (sxv_range (m_avail mr)) as RA'.
pose proof (sxv_range (2 ^ (m_last_idx mr + 1) - 1)) as RALL.
(gw_expose_fam RATP; unfold alloc_ceiling in *).

step. step. rewrite !sx32_wz_sxv by lia.

step. rewrite (wz_unsigned (sxv (m_freed mr))), (wz_unsigned (sxv (m_avail mr))) by assumption.
rewrite (Z.lor_comm (sxv (m_avail mr)) (sxv (m_freed mr))).
pose proof (lor_range64 (sxv (m_freed mr)) (sxv (m_avail mr)) RF RA') as RL.

step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by gw_exact RL.
rewrite (Z.land_comm _ (sxv (2 ^ idx))).
rewrite (free_assert_ok (m_freed mr) (m_avail mr) idx) by (assumption || lia).

step. if_true. st1.

step. if_cases K2; zify_cond K2.
-
st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
-
step. rewrite (wz_unsigned (sxv (2 ^ idx))) by assumption.
rewrite (unsigned_lit (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) by gw_exact RL.
rewrite (Z.add_comm (Z.lor _ _) (sxv (2 ^ idx))). rewrite addw_word.
pose proof (sxv_range (sxv (2 ^ idx) + Z.lor (sxv (m_freed mr)) (sxv (m_avail mr)))) as RSUM.
step. if_cases K3; zify_cond K3.
+ st1. if_cases K4; zify_cond K4. 2:{ exfalso. first [apply K4; reflexivity | rewrite wz_unsigned in K4 by lia; lia | idtac "K4 form?"]. }
st1. st1.
apply evt_done. do 6 eexists. reflexivity.
+ exfalso. destruct HNT as [Hz|Hall].
* apply K2. rewrite ?wz_unsigned by apply sxv_range. rewrite Hz. reflexivity.
* apply K3. rewrite ?wz_unsigned by apply sxv_range.
apply (proj2 (free_all_test (m_freed mr) (m_avail mr) idx (m_last_idx mr) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
unfold bit, mask_upto in Hall. gw_exact Hall.
Qed.

End RC__1.

End G.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 QDUx.Mq6.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QCa8.Mq4.
Import Q8QT.Mq2.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope bv_scope.
Open Scope Z_scope.

Definition free_code (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z) : list Z :=
[0x1c050463; 0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00050493; 0x1ac000ef; 0x02053583; 0xffd4c683; 0x00c5d613; 0x01f6f413; 0x00060e63; 0x01f5f613; 0x00061a63; 0xfffff637; 0x00c5f633; 0xff060613; 0x0200006f; 0x0055d613; w_21; 0x07e67613; w_23; 0x00c70633; 0x00065603; 0x00461613; 0x01053703; 0x028607b3; 0x0a000813; 0x00c70633; 0x00f607b3; 0x00c78613; 0x0056d713; 0x0306e663; 0x00500693; 0x00d70463; 0x00000023; 0x0087e703; 0x00400693; 0x00e6e463; 0x00000023; 0x0077c683; 0x00068463; 0x00000023; 0x409606b3; 0x00e6f463; 0x00000023; 0x40e606b3; 0x0006c683; 0x00068463; 0x00000023; 0x00064603; 0x00060463; 0x00000023; 0x00100613; 0x00200693; 0xfff00713; 0x00b696bb; 0x01c50593; 0x0086163b; 0xfee48ea3; 0xfe049f23; 0xfff6869b; w_64; 0x01c52783; 0x01852803; 0x00f86833; 0x00c878b3; 0x00088463; 0x00000023; w_71; 0x02078863; 0x00c8083b; 0x02d80463; 0x00c7883b; 0x06088e63; 0x1605a8af; 0x00f89663; 0x1f05a2af; 0xfe029ae3; 0x0008889b; 0xfaf89ee3; 0x0640006f; 0x00088e63; w_85; w_86; 0x00050493; 0x00058513; w_89; 0x00048513; 0x00040593; 0x16c000ef; 0x00050413; 0x00058493; w_95; w_96; w_97; 0x02048463; w_99; 0x00050913; 0x00052983; 0x00040513; 0x00048593; w_104; 0x01392023; 0x0080006f; 0x0105a023; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 : Z).
Variables (hi_21 hi_64 hi_85 hi_95 : bv 20).
Variables (lo_23 lo_71 lo_86 lo_96 : bv 12).
Variables (joff_89 joff_97 joff_99 joff_104 : bv 21).
Hypothesis CODE : code_at segs base (free_code w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 460.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Auipc 14 hi_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_23 : decode_any (Z_to_bv 32 w_23) = Some (OpImm ALU_ADD 14 14 lo_23, 4%Z).
Hypothesis E_23 : is_ecall (Z_to_bv 32 w_23) = false.
Hypothesis D_64 : decode_any (Z_to_bv 32 w_64) = Some (Auipc 14 hi_64, 4%Z).
Hypothesis E_64 : is_ecall (Z_to_bv 32 w_64) = false.
Hypothesis D_71 : decode_any (Z_to_bv 32 w_71) = Some (Load SZ1 false 17 14 lo_71, 4%Z).
Hypothesis E_71 : is_ecall (Z_to_bv 32 w_71) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 11 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_86 : decode_any (Z_to_bv 32 w_86) = Some (OpImm ALU_ADD 11 11 lo_86, 4%Z).
Hypothesis E_86 : is_ecall (Z_to_bv 32 w_86) = false.
Hypothesis D_89 : decode_any (Z_to_bv 32 w_89) = Some (Jal 1 joff_89, 4%Z).
Hypothesis E_89 : is_ecall (Z_to_bv 32 w_89) = false.
Hypothesis D_95 : decode_any (Z_to_bv 32 w_95) = Some (Auipc 10 hi_95, 4%Z).
Hypothesis E_95 : is_ecall (Z_to_bv 32 w_95) = false.
Hypothesis D_96 : decode_any (Z_to_bv 32 w_96) = Some (OpImm ALU_ADD 10 10 lo_96, 4%Z).
Hypothesis E_96 : is_ecall (Z_to_bv 32 w_96) = false.
Hypothesis D_97 : decode_any (Z_to_bv 32 w_97) = Some (Jal 1 joff_97, 4%Z).
Hypothesis E_97 : is_ecall (Z_to_bv 32 w_97) = false.
Hypothesis D_99 : decode_any (Z_to_bv 32 w_99) = Some (Jal 1 joff_99, 4%Z).
Hypothesis E_99 : is_ecall (Z_to_bv 32 w_99) = false.
Hypothesis D_104 : decode_any (Z_to_bv 32 w_104) = Some (Jal 1 joff_104, 4%Z).
Hypothesis E_104 : is_ecall (Z_to_bv 32 w_104) = false.
Hypothesis ANCH_23 : gw_anch (Z.shiftl (bv_signed hi_21) 12 + (base + 84) + bv_signed lo_23)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_71 : gw_anch (Z.shiftl (bv_signed hi_64) 12 + (base + 256) + bv_signed lo_71)%Z (RATP + 131731).
Hypothesis ANCH_86 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_86)%Z (RATP + 131960).
Hypothesis ANCH_96 : gw_anch (Z.shiftl (bv_signed hi_95) 12 + (base + 380) + bv_signed lo_96)%Z (RATP + 131960).
Hypothesis LINK_89 : gw_anch (base + 356 + bv_signed joff_89)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_97 : gw_anch (base + 388 + bv_signed joff_97)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_99 : gw_anch (base + 396 + bv_signed joff_99)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_104 : gw_anch (base + 416 + bv_signed joff_104)%Z (rvm_wait_entry + 524)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_0))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))).
Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_10).
Definition rrepfoot : ltac:(gw_rebind_ty (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QkTt.Mq4.rrepfoot RATP RGOT_SSP) (@rrepfoot) (gw_ent (@QDXD.Mq2.rrepfoot RATP RGOT_SSP) (@rrepfoot) gw_tbl_11)).

Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + 460)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_12))) in let T := gw_fold_pcs T base (460)%Z [0; 244]%Z in exact T).

Definition rreserved_disjoint : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rreserved_disjoint) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rreserved_disjoint)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_transport_unowned : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_transport_unowned) constr:(gw_tbl_12)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_transport_unowned)).

#[using="rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_21 E_21 D_23 E_23 D_64 E_64 D_71 E_71 D_85 E_85 D_86 E_86 D_89 E_89 D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_23 ANCH_71 ANCH_86 ANCH_96 LINK_89 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmunmap_entry runlock_spec"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rffin_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (W : list (Z * Z)) (m : word -> option byte) (st : mstate) (errv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch W m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ rw_cells segs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="RIMG_HI gw_RDATA2_LO rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_95 lo_96 joff_97 CODE BASE4 BASER D_95 E_95 D_96 E_96 D_97 E_97 ANCH_96 LINK_97 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 runlock_spec rmunmap_entry"] Lemma rfree_fin0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt segs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz 0) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x174)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO rvm_wait_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_95 lo_96 joff_97 CODE BASE4 BASER D_95 E_95 D_96 E_96 D_97 E_97 ANCH_96 LINK_97 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 runlock_spec rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until errv. intros TP MR MI FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
(gw_expose_fam RATP; unfold alloc_ceiling in *). subst tp.
rewrite (unsigned_lit RATP) in ERR by lia. change (RATP + -164) with (RATP + -164) in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| gw_exact LK]. }
intros ms' ->.
try g_ret_pc_any.

st1. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MU | gw_exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [| gw_exact MR2].
rewrite (unsigned_lit RATP) by lia. change (RATP + -164) with (RATP + -164). gw_exact ERR.
Qed.

Definition rfmun_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (junk : list byte) (m : word -> option byte) (st : mstate) (errv bw lw : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR (Z_to_bv 64 (base + 0x1a4)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw bw lw a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) (sx32 errv) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmunmap_entry) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ rw_cells segs m' (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ rw_cells segs m' (errno_addr tp) [C4 errv]
/\ rmrep st m'.

#[using="RIMG_HI gw_RDATA2_LO rerrno_loc_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_95 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 runlock_spec"] Lemma rfree_tomunmap : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra bw q0 q1 : word) F fc
(m : word -> option byte) (junk : list byte) (lo len : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv segs m -> 0 < len < 2^64 ->
rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells segs m (errno_addr tp) [C4 errv] ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt segs (rfmun_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo junk m st errv bw (wz len))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 q0 q1 bw (wz len) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x174)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO rerrno_loc_entry runlock_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 hi_95 lo_96 joff_97 joff_99 joff_104 CODE BASE4 BASER D_95 E_95 D_96 E_96 D_97 E_97 D_99 E_99 D_104 E_104 ANCH_96 LINK_97 LINK_99 LINK_104 CODE_rerrno_loc_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 runlock_spec segs base RATP. gw_expose_fam RATP.
intros until errv. intros TP MR MI HL FR ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof MR as (WF & CX & GL & AR & GR & SH). destruct GL as (LK & NL & _).
(gw_expose_fam RATP; unfold alloc_ceiling in *). subst tp.
rewrite (unsigned_lit RATP) in ERR by lia. change (RATP + -164) with (RATP + -164) in ERR.

st1. st1. st1. st1.

st1.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| gw_exact LK]. }
intros ms' ->.
try g_ret_pc_any.

st1. if_cases K; zify_cond K. { exfalso. rewrite wz_unsigned in K by lia. lia. }

st1. st1. st1. st1.
try g_ret_pc_any.

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX)
by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MU | gw_exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
apply evt_done. unfold rfmun_post. do 14 eexists. split; [rewrite (unsigned_lit RATP) by lia; reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [gw_exact FR|].
split; [rewrite (unsigned_lit RATP) by lia; change (RATP + -164) with (RATP + -164); gw_exact ERR| gw_exact MR2].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved rmunmap_entry"] Lemma rerrno_avoids_repfoot : forall st m a, rmrep st m -> (RATP + -164) <= a < (RATP + -164 + 4) -> ~ rrepfoot st a.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_ref_reserved rmunmap_entry RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m a MR Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- gw_expose_fam RATP. lia.
- destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
destruct (WR _ _ Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len ra)). lia.
- destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC).
destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. pose proof (round_up_pg_ge (r_len rb)). lia.
- destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2]. lia.
- gw_expose_fam RGOT_SSP. lia.
- gw_expose_fam RATP. lia.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmunmap_entry"] Lemma rmrep_transport_frame_errno : forall st m m' (sp : Z),
rmrep st m -> munch [(sp - 48, sp); ((RATP + -164), (RATP + -164 + 4))]%Z m m' -> wmono segs m m' -> alloc_ceiling <= sp - 48 -> rmrep st m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmunmap_entry segs RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' sp MR MU WM HS. eapply rmrep_transport_unowned; [gw_exact MR | gw_exact MU | gw_exact WM |].
apply ivs_avoid_cons; [| apply ivs_avoid_cons; [| apply ivs_avoid_nil]].
- intros a Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). unfold alloc_ceiling in HS.
intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ gw_expose_fam RATP. lia.
+ destruct C as (ak & ar & Hak & Hin).
destruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (b & gh & Hb & Hin).
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RB0 & RBC). unfold alloc_ceiling in RBC. lia.
+ destruct C as (rid & r & v & Hr & Hk & Hin & HC).
destruct (WR _ _ Hr) as (_ & _ & _ & RBC & _). unfold alloc_ceiling in RBC. lia.
+ gw_expose_fam RGOT_SSP. lia.
+ gw_expose_fam RATP. lia.
- intros a Ha. eapply rerrno_avoids_repfoot; [gw_exact MR | gw_exact Ha].
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmunmap_entry"] Lemma rfree_fin1 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 ra ew bw lw e' : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (errv : word),
tp = Z_to_bv 64 RATP ->
rmrep st m -> mem_inv segs m ->
rw_cells segs m (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
le4 ew = le4 errv ->
rw_cells segs m (errno_addr tp) [C4 e'] ->
stk segs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
evt segs (rffin_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo [(bv_unsigned sp - 48, bv_unsigned sp); ((RATP + -164), (RATP + -164 + 4))]%Z m st errv)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 bw lw a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (errno_addr tp)) ew s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 (base + 0x1a4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry w_21 w_23 w_64 w_71 w_85 w_86 w_89 w_95 w_96 w_97 w_99 w_104 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 LAY_ref_reserved rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until errv. intros TP MR MI FR EW ERR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); ((RATP + -164), (RATP + -164 + 4))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
(gw_expose_fam RATP; unfold alloc_ceiling in *). subst tp.
rewrite (unsigned_lit RATP) in ERR by lia. change (RATP + -164) with (RATP + -164) in ERR.
rewrite (unsigned_lit RATP) by lia. change (RATP + -164) with (RATP + -164).

st1.

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st mX) by (eapply (rmrep_transport_frame_errno st m mX (bv_unsigned sp)); [gw_exact MR | gw_exact MU | gw_exact WM | unfold alloc_ceiling; lia]) end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rffin_post. do 16 eexists. split; [reflexivity|].
split; [gw_exact MU|]. split; [gw_exact WM|]. split; [assumption|]. split; [gw_exact ST|]. split; [| gw_exact MR2].
rewrite (unsigned_lit RATP) by lia. change (RATP + -164) with (RATP + -164).
eapply rw_cells_congr; [| | | gw_exact ERR]; [cbn [cells_bytes cbytes app]; rewrite EW; reflexivity| reflexivity| cbn; tauto].
Qed.

End RC__1.

End G.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlQE QPjm QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0.

Import Q2qa.Mq1 Qy5Y.Mq4 QlQE Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 QFkE.
Export QJE4.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
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

Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_0).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_1)))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_2)))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_3)))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_4)))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_5)))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_6)))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_7)))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_8)))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_9)))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_10)))).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_11)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

#[using="Type"] Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof. clear - st pf lo sp sp' a.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; gw_exact H| right; right; gw_exact H].
- right; left. gw_exact H.
- right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
exists rid, r, w. auto.
Qed.

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. clear - st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. clear - st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. clear - q st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; try gw_hide st'; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. clear - p st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by gw_exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. clear - rid' st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; try gw_hide st'; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. clear - q st rid st' PTR. first [clear PTR | gw_hide PTR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof. clear - PTR q st rid st'. first [clear st' | gw_hide st' | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear st | gw_hide st | idtac].
destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof. clear - PTR st rid st'. try gw_hide st'; first [clear rid | gw_hide rid | idtac]; try gw_hide st.
destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof. clear - PTR st rid st'. try gw_hide st'; first [clear rid | gw_hide rid | idtac]; try gw_hide st.
destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof. clear - PTR st rid st'. try gw_hide st'; first [clear rid | gw_hide rid | idtac]; try gw_hide st.
destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by gw_exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof. clear - PTR m st rid st'. try gw_hide st'; first [clear rid | gw_hide rid | idtac]; try gw_hide st.
intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
split; [|split; [|split; [|split; [|split]]]].
- split; [gw_exact Hres|]. split; [|split; [|split]].
+ intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
+ intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
+ intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
+ intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
- unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). gw_exact CX.
- gw_exact GL.
- intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
unfold rarea_rep. rewrite (rconc_drop a) by gw_exact Pa. rewrite rpw_drop by gw_exact Pn. split; [gw_exact A1|]. split; [| gw_exact A3].
intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. gw_exact Hk.
- intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
rewrite (rconc_drop b) by gw_exact Pb. rewrite rpw_drop by gw_exact Pm. auto.
- intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

#[using="Type"] Lemma rptrs_in_norid st2 LB c rid r m :
KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
(s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
(forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
ci_mptrs st2 ->
ptrs_in (fun x => x <> rid) st2.
Proof. clear - st2 LB c rid r m.
intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
{ intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
{ intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
- apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
- apply NGr. gw_exact M1.
- apply NGr. gw_exact M2.
- apply NGr. gw_exact M3.
- apply NGr. gw_exact M4.
- intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
- destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
- intros g. split; [| split].
+ apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
+ apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
+ destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
- intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b gh Hb. split; [exact (NOG b gh Hb)|].
destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End RC__1.

End G.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq8.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QCa8.Mq4.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QCa8.Mq3.
Import QDXD.Mq1.
Import QkTt.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.
Open Scope Z_scope.

Definition malloc_code (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0xffffe5b7; 0xfff5859b; 0x0015d593; 0x02b56a63; w_11; 0x00c00593; 0x00b52023; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x00008067; 0x00050413; 0x00020537; 0xfec5051b; w_26; w_27; 0x06a46663; 0x01440993; 0x00300613; 0x02200693; 0xfff00713; 0xfff00913; 0x00000513; 0x00098593; 0x00000793; w_37; 0xfb2500e3; 0x00050a13; w_40; w_41; 0x00050863; w_43; w_44; w_45; 0x3984c503; 0x0ff00593; 0x0cb51063; 0x3404bc23; 0x3604b023; 0x3604b423; 0x3604b823; 0x00100513; 0x0ac0006f; 0x00340513; 0x09d00593; w_57; 0x00455a13; w_59; 0x10b46263; 0x001a0513; 0x077cb5b7; 0x0025561b; 0x00a66633; 0x0015551b; 0x53158593; 0x00a66633; 0x0026561b; 0x00a66533; 0x00455613; 0x00a66533; 0x00855613; 0x00a66533; 0x02151613; 0x03165613; 0x00a66533; 0x00150613; 0xfff54513; 0x00a67533; 0x02b50533; 0x01b5551b; 0x00a98533; 0x00054503; 0x07900593; w_85; 0x00251513; 0x07c54513; 0x40a585b3; 0x00159693; w_90; 0x00d586b3; 0x0006d603; 0x06ca6063; 0x07a00613; 0x05c0006f; 0x00150513; 0x38a48c23; 0xba1ff0ef; 0x0c050063; 0x00050913; 0x00000993; 0x01453823; 0x00aa3023; 0x00001537; 0xfe05051b; 0x00a405b3; 0x03358593; 0x8005f593; 0x00a5e533; 0x02a93023; 0x00092e23; 0x00092c23; 0x0144a503; 0x00150513; 0x00a4aa23; 0x1540006f; 0x07800613; 0x40a60633; 0x00161513; 0x00a58533; 0x00055503; 0x00aa3533; 0x00154513; 0x00a66a33; w_125; w_126; 0x00050863; w_128; w_129; w_130; 0x000a059b; 0x00359513; 0x00a48533; 0x05853903; 0x08091e63; 0x00600613; 0x08c58a63; 0xffca059b; 0x01b00613; 0x08b66463; 0x001a7593; 0x00059663; 0x1d853503; 0x02050463; 0x00000913; 0x07c0006f; w_147; w_148; w_149; 0x000a0513; 0x00098593; w_152; 0xdd5ff06f; 0x001a6513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b603; 0x1d85b583; 0x00060a63; 0x01862683; 0x00069863; 0x01c62603; 0x00061463; 0x00358593; 0x00d00613; 0x00c5e463; 0x000a0513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b903; 0x00050a13; 0x00090663; 0x01892503; 0x0080006f; 0x00000513; 0x40a005bb; 0x00b575b3; 0x02058863; 0x40a0063b; 0x077cb6b7; 0x00c57633; 0x53168693; 0x02d60633; 0x01b6561b; 0x00c98633; 0x00064983; 0x40b5053b; 0x00a92c23; 0x0280006f; 0x000a091b; 0x00090513; 0x00040593; 0x064000ef; 0x04054863; 0x00050993; 0x00391913; 0x01248933; 0x05893903; 0x0144aa03; 0x00048513; w_203; 0x00090513; 0x00098593; 0x00040613; 0x000a0693; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x0b90006f; w_216; w_217; w_218; 0xccdff06f]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let renframe_entry := (base + 3092)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rmunmap_entry + 0)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition runlock_post : ltac:(gw_rebind_ty (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QCa8.Mq4.runlock_post segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QCa8.Mq4.runlock_post segs) (@runlock_post) gw_tbl_0).
Definition ren3_post : ltac:(gw_rebind_ty (@QCa8.Mq3.ren3_post segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq3.ren3_post segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QCa8.Mq3.ren3_post segs) (@ren3_post) gw_tbl_1).
Definition rimplT : ltac:(gw_rebind_ty (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rimplT segs RC__) constr:(gw_tbl_2)).
#[global] Arguments rimplT {R}%_type_scope o t s Q%_function_scope ms.
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq3.rimplT segs RC__) (@rimplT) (gw_ent (@QCa8.Mq5.rimplT segs RC__) (@rimplT) gw_tbl_2)).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq1.rpres_except segs) (@rpres_except) (gw_ent (@QkTt.Mq3.rpres_except segs) (@rpres_except) (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_3))))).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_4))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_5))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_6))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_7))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_8))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_9))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_10))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_11))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_12))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_13)).
Notation gw_tbl_14 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_13))))))).

Hypothesis runlock_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq4.gw_all) (@QCa8.Mq4.runlock_spec) (base + -1984)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (-1984)%Z [0; 244]%Z in exact T).

Hypothesis renframe_walk : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty (@QCa8.Mq3.gw_all) (@QCa8.Mq3.renframe_walk) (base + 3092)%Z)) in let T := constr:(ltac:(gw_fold_exact T constr:(gw_tbl_14))) in let T := gw_fold_pcs T base (3092)%Z [0; 36; 64; 124; 184; 220]%Z in exact T).

Definition rmrep_havoc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_havoc) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_havoc)).

Definition rimplT_ret : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_ret) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_ret)).
#[global] Arguments rimplT_ret {R}%_type_scope o r s Q%_function_scope ms _.
Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.
Definition rpres_except_refl : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_refl) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_refl)).
Definition rpres_except_rw_cells : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_rw_cells) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_rw_cells)).
Definition rpres_except_stk : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rpres_except_stk) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rpres_except_stk)).

Definition rimplT_rd8 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd8) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd8)).
#[global] Arguments rimplT_rd8 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.
Definition rimplT_rd16 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq3.rimplT_rd16) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq3.rimplT_rd16)).
#[global] Arguments rimplT_rd16 {R}%_type_scope o st q k%_function_scope s Q%_function_scope ms _.

Definition renframe_mrep : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.renframe_mrep) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.renframe_mrep)).
Definition rpres_enframe : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rpres_enframe) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rpres_enframe)).
Definition rmeta_chunk_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rmeta_chunk_facts) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rmeta_chunk_facts)).
Definition rslot_facts : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rslot_facts) constr:(gw_tbl_14)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rslot_facts)).

#[using="RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ renframe_entry rmmap_entry rmunmap_entry runlock_spec renframe_walk"] Lemma gw_all : True. Proof. exact I. Qed.

Tactic Notation "gw_clear_keep" ne_hyp_list(hs) := first [clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ renframe_entry runlock_spec renframe_walk | clear - hs segs base w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay renframe_entry runlock_spec renframe_walk].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1.

#[using="rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP runlock_spec renframe_entry rmmap_entry rmunmap_entry"] Lemma renf_glue_walk : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' nw gw iw rav s0v s1v s2v s3v s4v : word)
F fc (m : mem) (st : mstate),
rw_cells segs m (RATP + 131968) (ctx_head_cells st) ->
rw_cells segs m (RATP + 131960) [C4 (wz 0)] ->
rw_cells segs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
48 <= bv_unsigned sp ->
0 <= c_mmap_counter (ctx st) < 2^32 ->
evt segs (fun ms' => ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v gw iw nw (wz (sxv (c_mmap_counter (ctx st)))) a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 renframe_entry) fc None m (seg_rom segs))
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 nw (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7 gw iw s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP runlock_spec renframe_entry rmmap_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until st. intros CH LK FR SP48 CTR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
gw_expose_fam RATP. unfold ctx_head_cells in CH.

step. rewrite sx32_wz_sxv by lia.

step. step.
eapply evt_cut.
{ eapply runlock_spec; rewrite unsigned_lit by lia; [reflexivity| gw_exact LK]. }
intros ms' ->.
try g_ret_pc_any.

do 12 step.
apply evt_done. unfold renframe_entry. reflexivity.
Qed.

#[using="base rvm_wait_entry renframe_entry rmmap_entry rmunmap_entry"] Lemma bytes_at_enframe_user : forall m4 P0 stride off n k B bs,
0 <= off -> 0 <= n -> 16 * off + n + 4 <= stride -> 4 <= P0 -> P0 + stride <= 2^64 ->
bytes_at segs m4 (P0 + 16 * off) bs -> Z.of_nat (length bs) <= n ->
bytes_at segs (renframe_tail_mem (renframe_off_mem m4 P0 off) (P0 + 16 * off) (P0 + stride - 4) n k ((P0 + 16 * off - B - 16) / 16)) (P0 + 16 * off) bs.
Proof. clear - base rvm_wait_entry renframe_entry rmmap_entry rmunmap_entry segs.
intros m4 P0 stride off n k B bs OFF0 N0 FIT P4 PS HB LEN.
assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
assert (HO : bytes_at segs (renframe_off_mem m4 P0 off) (P0 + 16 * off) bs).
{ unfold renframe_off_mem. destruct (Z.eqb_spec off 0); [gw_exact HB|].
apply bytes_at_write_other; [| lia | cbn; lia | cbn; lia].
apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [gw_exact HB| lia | cbn; lia | cbn; lia]. }
unfold renframe_tail_mem. cbv zeta.
set (mE := write_to_mem (write_to_mem (renframe_off_mem m4 P0 off) _ _) _ _).
assert (HE : bytes_at segs mE (P0 + 16 * off) bs).
{ subst mE. apply bytes_at_write_other; [| lia | rewrite L2; lia | rewrite L2; lia].
apply bytes_at_write_other; [gw_exact HO| lia | cbn; lia | cbn; lia]. }
clearbody mE.
set (rsv := P0 + stride - 4 - (P0 + 16 * off) - n).
set (mF := if rsv =? 0 then _ else _).
assert (HF : bytes_at segs mF (P0 + 16 * off) bs).
{ subst mF. destruct (Z.eqb_spec rsv 0); [gw_exact HE|]. apply bytes_at_write_other; [gw_exact HE| lia | cbn; lia | cbn; lia]. }
clearbody mF.
set (mG := if 5 <=? rsv then _ else _).
assert (HG : bytes_at segs (fst mG) (P0 + 16 * off) bs /\ 0 <= snd mG <= 5).
{ subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
- split; [|lia]. apply bytes_at_write_other; [| lia | rewrite L4; lia | rewrite L4; lia].
apply bytes_at_write_other; [gw_exact HF| lia | cbn; lia | cbn; lia].
- split; [gw_exact HF| lia]. }
clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
apply bytes_at_write_other; [gw_exact HG| lia | cbn; lia | cbn; lia].
Qed.

Definition renf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (o m0 m1 : mem) (C : Z -> Prop) (st1 : mstate) (g b : aptr) (idx n : Z)
(r : mstate * optr) (ms' : machine_state) : Prop :=
exists st' p t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
r = (st', Some p)
/\ ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (conc st' p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp)
/\ rmrep st' m' /\ ticks_ok st' /\ rpres_except C m0 m'
/\ enf_leaf o st1 g b idx n st' p
/\ (forall bs, bytes_at segs m1 (conc st' p) bs -> Z.of_nat (length bs) <= n -> bytes_at segs m' (conc st' p) bs).

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay runlock_spec renframe_walk renframe_entry rmmap_entry rmunmap_entry"] Lemma renf_implT :
forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' ra s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32)
(o m0 m1 : mem) (s : PState) (st1 : mstate) (g b : aptr) (r : region) (idx n lo : Z) (C : Z -> Prop),
let mr := get_meta_rec st1 g in
let stride := get_stride mr in
let ctr := c_mmap_counter (ctx st1) in
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 ->
mem_inv segs m1 -> stk segs m1 lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 ->
rw_cells segs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rpres_except C m0 m1 -> (forall a, lo <= a < bv_unsigned sp -> C a) ->
(forall a, r_base r + snd b + 16 + stride * idx - 4 <= a < r_base r + snd b + 16 + stride * idx + stride - 4 -> C a) ->
0 <= ctr < 2^32 ->
slot_ok st1 g b r idx n ->
rimplT o (enframe_full st1 g idx n ctr (fun st2 p => ret (havoc p n st2, Some p))) s
(fun res s' ms' => s' = s /\ renf_post ra sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc lo o m0 m1 C st1 g b idx n res ms')
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
a0 a1 a2 a3 a4 a5 a6 a7 (pw st1 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x324)) fc None m1 (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay runlock_spec renframe_walk renframe_entry rmmap_entry rmunmap_entry segs base RATP. gw_expose_fam RATP.
intros until C. intros mr stride ctr MR TK UA MI ST CLO LO FR PE CST CSL CTR SO.
destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16, AVr, FRr, FBr, MPL, SCr.
fold stride in SPAN, S16, SMOD, S31, NS, NOGRP, HDR0, Q16.
assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
{ eapply Z.le_trans; [|gw_exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
clear SPAN. rename SPAN1 into SPAN.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.

destruct (rslot_facts st1 m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN S16 B16 SMOD HDR0)
as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1).
fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND.
pose proof (rmeta_chunk_facts st1 m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG).
unfold alloc_ceiling in RC, GC.
set (G := conc st1 g) in *.
pose proof (GDJ (fst b) r Hr Hk) as GR.
change (get_meta_rec st1 g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM.
set (B := conc st1 b) in *.
pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.

pose proof (bytes_at_read segs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
pose proof (bytes_at_read segs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
pose proof (bytes_at_read segs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
rewrite Z.add_0_r in RD4.
replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.

unfold enframe_full, enframe_read_off. change (get_meta_rec st1 g) with mr. fold stride. cbv zeta.
assert (Hp0 : slot_start' mr idx = (fst b, snd b + (16 + stride * idx))).
{ unfold slot_start'. rewrite Hmem. cbn [default from_option id]. unfold aadd, UNIT. cbn [fst snd]. fold stride. reflexivity. }
rewrite Hp0. unfold aadd. cbn [fst snd].
apply rimplT_rd8. rewrite E3.
change ((stride - IB - n) / UNIT) with ((stride - 4 - n) / 16). set (slack := (stride - 4 - n) / 16).
set (K := fun off : Z => let '(st2, p) := enframe_at st1 g idx n off in @ret (mstate * optr) (havoc p n st2, Some p)).
set (off0 := if bv_unsigned x3 =? 0 then Z.land ctr 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255).
set (off := fold_off off0 slack).
assert (OFF0 : 0 <= off0 < 256).
{ subst off0. destruct (bv_unsigned x3 =? 0).
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
- split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
assert (SL0 : 0 <= slack) by (subst slack; apply Z.div_pos; lia).
pose proof (fold_off_le_slack off0 slack OFF0 SL0) as OFF. fold off in OFF.
assert (FIT : 16 * off + n + 4 <= stride) by (subst slack; Z.div_mod_to_equations; lia).
match goal with |- rimplT _ _ _ ?Q ?ms =>
assert (GOAL : rimplT o (K off) s Q ms) end.
2:{ assert (OFFa : bv_unsigned x3 = 0 -> fold_off (Z.land ctr 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_eq _ _) E0). reflexivity. }
assert (OFFb : bv_unsigned x3 <> 0 -> fold_off (Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) slack = off).
{ intros E0. unfold off, off0. rewrite (proj2 (Z.eqb_neq _ _) E0). reflexivity. }
clearbody off.
destruct (Z.eqb_spec (bv_unsigned x3) 0) as [E0|NE0]; cbn [negb].
- rewrite (OFFa E0). gw_exact GOAL.
- apply rimplT_rd16. unfold aadd; cbn [fst snd]. rewrite E2, E1. rewrite (OFFb NE0). gw_exact GOAL. }
subst K. cbv beta. rewrite surj_pair_let. apply rimplT_ret.

pose proof MR as (WF' & CX & GL & _). destruct GL as (LK & _). destruct CX as (CH & _).
eapply evt_cut.
{ eapply (renf_glue_walk sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra' (Z_to_bv 64 n) (pw st1 (Some g)) (wz idx) ra s0v s1v s2v s3v s4v F fc m1 st1);
[gw_exact CH| gw_exact LK| gw_exact FR| lia| gw_exact CTR]. }
intros ms' ->.
unfold renframe_entry.
eapply evt_mono.
{ eapply (renframe_walk ra sp gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (pw st1 (Some g)) (Z_to_bv 64 n)
(pw st1 (m_prev mr)) (pw st1 (m_next mr)) F fc m1 B stride n idx ctr (m_avail mr) (m_freed mr)
(m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
all: lazymatch goal with
| |- rw_cells _ _ (bv_unsigned (pw _ _)) _ => unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia; gw_exact MM
| |- mem_inv _ _ => gw_exact MI
| |- wr_at _ _ _ _ => gw_exact WRs
| |- ov_read_bytes _ _ _ 2 = _ => gw_exact RD2
| |- ov_read_bytes _ _ _ _ = Some [b8 0] => gw_exact RD4
| |- ov_read_bytes _ _ _ _ = _ => gw_exact RD3
| |- bv_unsigned (Z_to_bv 64 _) = _ => apply unsigned_lit; lia
| |- _ => idtac end.
all: try (unfold pw; cbn [oconc]; fold G; rewrite (wz_unsigned G) by lia).
all: try lia.
- subst stride. unfold get_stride, UNIT. reflexivity.
- intros off' O1 O2. pose proof (Q16 off' O1 O2). lia. }

intros ms' PO. cbv beta in PO. unfold ren3_post in PO.
destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI').
split; [reflexivity|].
fold slack in EM. fold off0 in EM. fold off in EM. fold slack off0 off.
set (res := enframe_at st1 g idx n off) in *.

assert (S31n : stride - 4 - n < 2^31) by lia.
destruct (renframe_mrep st1 m1 g b r idx n off MR TK Hmem Hr Hk B0 ltac:(clear - IDX LI32 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay runlock_spec renframe_walk renframe_entry rmmap_entry rmunmap_entry segs base RATP; lia) ltac:(unfold stride, mr in SPAN; clear - SPAN S16 RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay runlock_spec renframe_walk renframe_entry rmmap_entry rmunmap_entry segs base RATP; lia) S16 S31n NOGRP (proj1 OFF) N0 FIT (Q16 off (proj1 OFF) FIT))
as (MRr & TKr & CONCr & FSTr & SNDr).
fold stride B res in MRr, TKr, CONCr, FSTr, SNDr.
change (conc st1 b) with B in MRr, CONCr. change (get_stride (get_meta_rec st1 g)) with stride in MRr, CONCr, SNDr.
fold res in MRr, TKr, CONCr, FSTr, SNDr.
set (P0 := B + 16 + stride * idx) in *.
rewrite <- EM in MRr.
destruct (rmrep_havoc (fst res) m' (snd res) n MRr TKr) as [MR' TK'].

assert (PE0 : rpres_except (fun a => P0 - 4 <= a < P0 + stride - 4) m1 m').
{ rewrite EM. apply (rpres_enframe _ m1 m1 P0 stride off n idx B (rpres_except_refl _ _) (proj1 OFF) N0 FIT); [unfold P0; lia| unfold P0; lia|].
intros x Hx. gw_exact Hx. }
assert (ST' : stk segs m' lo (bv_unsigned sp + -48)).
{ eapply rpres_except_stk; [gw_exact PE0| gw_exact ST|]. intros a Ha. cbv beta. unfold P0. lia. }
assert (FR' : rw_cells segs m' (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
{ eapply rpres_except_rw_cells; [gw_exact PE0| gw_exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. intros a Ha. cbv beta. unfold P0. lia. }
release_frame FR' ST' (bv_unsigned sp).
unfold renf_post. exists (havoc (snd res) n (fst res)), (snd res). do 14 eexists. exists m'.
split; [reflexivity|].
split. { unfold wz. rewrite conc_havoc. rewrite <- CONCr. unfold res. rewrite conc_enframe_at. reflexivity. }
split; [gw_exact MI'|]. split; [gw_exact ST'|]. split; [gw_exact MR'|]. split; [gw_exact TK'|].
split.
{ rewrite EM. apply (rpres_enframe C m0 m1 _ stride off n idx B PE (proj1 OFF) N0 FIT); [unfold B; lia| unfold B; lia|].
intros x Hx. apply CSL. unfold B in Hx. lia. }
split.
{ exists off. split; [exact (proj1 OFF)|]. split; [gw_exact FIT|].
split. { clear - FSTr SNDr RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO rvm_wait_entry runlock_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_203 CODE BASE4 BASER D_203 E_203 LINK_203 RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved ref_wview_overlay ref_seg_rom_none ref_mrd_overlay runlock_spec renframe_walk renframe_entry rmmap_entry rmunmap_entry segs base RATP. destruct (snd res) as [p1 p2]. cbn [fst snd] in FSTr, SNDr. subst. reflexivity. }
split; [reflexivity|]. split; [reflexivity|].
unfold off, off0, slack, enf_off0. fold mr. fold stride. rewrite E3, E2, E1. reflexivity. }

assert (EC : conc (fst res) (snd res) = P0 + 16 * off) by (unfold res at 1; rewrite conc_enframe_at; gw_exact CONCr).
intros bs HB LEN. rewrite conc_havoc, EC in HB |- *. rewrite EM.
apply (bytes_at_enframe_user m1 P0 stride off n _ B bs (proj1 OFF) N0 FIT); [unfold P0, B; lia| unfold P0, B; lia| gw_exact HB| gw_exact LEN].
Qed.

End RC__1.

End G.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA Qnxq QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import QLsg QDUx.Mq9.
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

Definition malloc_code (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x01413023; 0xffffe5b7; 0xfff5859b; 0x0015d593; 0x02b56a63; w_11; 0x00c00593; 0x00b52023; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x00008067; 0x00050413; 0x00020537; 0xfec5051b; w_26; w_27; 0x06a46663; 0x01440993; 0x00300613; 0x02200693; 0xfff00713; 0xfff00913; 0x00000513; 0x00098593; 0x00000793; w_37; 0xfb2500e3; 0x00050a13; w_40; w_41; 0x00050863; w_43; w_44; w_45; 0x3984c503; 0x0ff00593; 0x0cb51063; 0x3404bc23; 0x3604b023; 0x3604b423; 0x3604b823; 0x00100513; 0x0ac0006f; 0x00340513; 0x09d00593; w_57; 0x00455a13; w_59; 0x10b46263; 0x001a0513; 0x077cb5b7; 0x0025561b; 0x00a66633; 0x0015551b; 0x53158593; 0x00a66633; 0x0026561b; 0x00a66533; 0x00455613; 0x00a66533; 0x00855613; 0x00a66533; 0x02151613; 0x03165613; 0x00a66533; 0x00150613; 0xfff54513; 0x00a67533; 0x02b50533; 0x01b5551b; 0x00a98533; 0x00054503; 0x07900593; w_85; 0x00251513; 0x07c54513; 0x40a585b3; 0x00159693; w_90; 0x00d586b3; 0x0006d603; 0x06ca6063; 0x07a00613; 0x05c0006f; 0x00150513; 0x38a48c23; 0xba1ff0ef; 0x0c050063; 0x00050913; 0x00000993; 0x01453823; 0x00aa3023; 0x00001537; 0xfe05051b; 0x00a405b3; 0x03358593; 0x8005f593; 0x00a5e533; 0x02a93023; 0x00092e23; 0x00092c23; 0x0144a503; 0x00150513; 0x00a4aa23; 0x1540006f; 0x07800613; 0x40a60633; 0x00161513; 0x00a58533; 0x00055503; 0x00aa3533; 0x00154513; 0x00a66a33; w_125; w_126; 0x00050863; w_128; w_129; w_130; 0x000a059b; 0x00359513; 0x00a48533; 0x05853903; 0x08091e63; 0x00600613; 0x08c58a63; 0xffca059b; 0x01b00613; 0x08b66463; 0x001a7593; 0x00059663; 0x1d853503; 0x02050463; 0x00000913; 0x07c0006f; w_147; w_148; w_149; 0x000a0513; 0x00098593; w_152; 0xdd5ff06f; 0x001a6513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b603; 0x1d85b583; 0x00060a63; 0x01862683; 0x00069863; 0x01c62603; 0x00061463; 0x00358593; 0x00d00613; 0x00c5e463; 0x000a0513; 0x0005059b; 0x00359593; 0x00b485b3; 0x0585b903; 0x00050a13; 0x00090663; 0x01892503; 0x0080006f; 0x00000513; 0x40a005bb; 0x00b575b3; 0x02058863; 0x40a0063b; 0x077cb6b7; 0x00c57633; 0x53168693; 0x02d60633; 0x01b6561b; 0x00c98633; 0x00064983; 0x40b5053b; 0x00a92c23; 0x0280006f; 0x000a091b; 0x00090513; 0x00040593; 0x064000ef; 0x04054863; 0x00050993; 0x00391913; 0x01248933; 0x05893903; 0x0144aa03; 0x00048513; w_203; 0x00090513; 0x00098593; 0x00040613; 0x000a0693; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x00013a03; 0x03010113; 0x0b90006f; w_216; w_217; w_218; 0xccdff06f]%Z.

Definition errno_loc_code : list Z :=
[0x00020513; 0xf5c50513; 0x00008067]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (rerrno_loc_entry rvm_wait_entry rlock_entry runlock_entry : Z).
Variables (w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 : Z).
Variables (hi_26 hi_40 hi_43 hi_57 hi_85 hi_125 hi_128 hi_147 hi_216 : bv 20).
Variables (lo_27 lo_41 lo_44 lo_59 lo_90 lo_126 lo_129 lo_148 lo_217 : bv 12).
Variables (joff_11 joff_37 joff_45 joff_130 joff_149 joff_152 joff_203 joff_218 : bv 21).
Hypothesis CODE : code_at segs base (malloc_code w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 880.
Let rmalloc_entry := (base + 0)%Z.
Let rmmap_entry := (rvm_wait_entry + 4)%Z.
Let rmunmap_entry := (rvm_wait_entry + 524)%Z.
Hypothesis D_11 : decode_any (Z_to_bv 32 w_11) = Some (Jal 1 joff_11, 4%Z).
Hypothesis E_11 : is_ecall (Z_to_bv 32 w_11) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 11 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 9 11 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_37 : decode_any (Z_to_bv 32 w_37) = Some (Jal 1 joff_37, 4%Z).
Hypothesis E_37 : is_ecall (Z_to_bv 32 w_37) = false.
Hypothesis D_40 : decode_any (Z_to_bv 32 w_40) = Some (Auipc 10 hi_40, 4%Z).
Hypothesis E_40 : is_ecall (Z_to_bv 32 w_40) = false.
Hypothesis D_41 : decode_any (Z_to_bv 32 w_41) = Some (Load SZ1 false 10 10 lo_41, 4%Z).
Hypothesis E_41 : is_ecall (Z_to_bv 32 w_41) = false.
Hypothesis D_43 : decode_any (Z_to_bv 32 w_43) = Some (Auipc 10 hi_43, 4%Z).
Hypothesis E_43 : is_ecall (Z_to_bv 32 w_43) = false.
Hypothesis D_44 : decode_any (Z_to_bv 32 w_44) = Some (OpImm ALU_ADD 10 10 lo_44, 4%Z).
Hypothesis E_44 : is_ecall (Z_to_bv 32 w_44) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis D_57 : decode_any (Z_to_bv 32 w_57) = Some (Auipc 12 hi_57, 4%Z).
Hypothesis E_57 : is_ecall (Z_to_bv 32 w_57) = false.
Hypothesis D_59 : decode_any (Z_to_bv 32 w_59) = Some (OpImm ALU_ADD 19 12 lo_59, 4%Z).
Hypothesis E_59 : is_ecall (Z_to_bv 32 w_59) = false.
Hypothesis D_85 : decode_any (Z_to_bv 32 w_85) = Some (Auipc 12 hi_85, 4%Z).
Hypothesis E_85 : is_ecall (Z_to_bv 32 w_85) = false.
Hypothesis D_90 : decode_any (Z_to_bv 32 w_90) = Some (OpImm ALU_ADD 11 12 lo_90, 4%Z).
Hypothesis E_90 : is_ecall (Z_to_bv 32 w_90) = false.
Hypothesis D_125 : decode_any (Z_to_bv 32 w_125) = Some (Auipc 10 hi_125, 4%Z).
Hypothesis E_125 : is_ecall (Z_to_bv 32 w_125) = false.
Hypothesis D_126 : decode_any (Z_to_bv 32 w_126) = Some (Load SZ1 false 10 10 lo_126, 4%Z).
Hypothesis E_126 : is_ecall (Z_to_bv 32 w_126) = false.
Hypothesis D_128 : decode_any (Z_to_bv 32 w_128) = Some (Auipc 10 hi_128, 4%Z).
Hypothesis E_128 : is_ecall (Z_to_bv 32 w_128) = false.
Hypothesis D_129 : decode_any (Z_to_bv 32 w_129) = Some (OpImm ALU_ADD 10 10 lo_129, 4%Z).
Hypothesis E_129 : is_ecall (Z_to_bv 32 w_129) = false.
Hypothesis D_130 : decode_any (Z_to_bv 32 w_130) = Some (Jal 1 joff_130, 4%Z).
Hypothesis E_130 : is_ecall (Z_to_bv 32 w_130) = false.
Hypothesis D_147 : decode_any (Z_to_bv 32 w_147) = Some (Auipc 10 hi_147, 4%Z).
Hypothesis E_147 : is_ecall (Z_to_bv 32 w_147) = false.
Hypothesis D_148 : decode_any (Z_to_bv 32 w_148) = Some (OpImm ALU_ADD 10 10 lo_148, 4%Z).
Hypothesis E_148 : is_ecall (Z_to_bv 32 w_148) = false.
Hypothesis D_149 : decode_any (Z_to_bv 32 w_149) = Some (Jal 1 joff_149, 4%Z).
Hypothesis E_149 : is_ecall (Z_to_bv 32 w_149) = false.
Hypothesis D_152 : decode_any (Z_to_bv 32 w_152) = Some (Jal 1 joff_152, 4%Z).
Hypothesis E_152 : is_ecall (Z_to_bv 32 w_152) = false.
Hypothesis D_203 : decode_any (Z_to_bv 32 w_203) = Some (Jal 1 joff_203, 4%Z).
Hypothesis E_203 : is_ecall (Z_to_bv 32 w_203) = false.
Hypothesis D_216 : decode_any (Z_to_bv 32 w_216) = Some (Auipc 10 hi_216, 4%Z).
Hypothesis E_216 : is_ecall (Z_to_bv 32 w_216) = false.
Hypothesis D_217 : decode_any (Z_to_bv 32 w_217) = Some (OpImm ALU_ADD 10 10 lo_217, 4%Z).
Hypothesis E_217 : is_ecall (Z_to_bv 32 w_217) = false.
Hypothesis D_218 : decode_any (Z_to_bv 32 w_218) = Some (Jal 1 joff_218, 4%Z).
Hypothesis E_218 : is_ecall (Z_to_bv 32 w_218) = false.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131960).
Hypothesis ANCH_41 : gw_anch (Z.shiftl (bv_signed hi_40) 12 + (base + 160) + bv_signed lo_41)%Z (RATP + 131731).
Hypothesis ANCH_44 : gw_anch (Z.shiftl (bv_signed hi_43) 12 + (base + 172) + bv_signed lo_44)%Z (RATP + 131960).
Hypothesis ANCH_59 : gw_anch (Z.shiftl (bv_signed hi_57) 12 + (base + 228) + bv_signed lo_59)%Z RDEBRUIJN.
Hypothesis ANCH_90 : gw_anch (Z.shiftl (bv_signed hi_85) 12 + (base + 340) + bv_signed lo_90)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_126 : gw_anch (Z.shiftl (bv_signed hi_125) 12 + (base + 500) + bv_signed lo_126)%Z (RATP + 131731).
Hypothesis ANCH_129 : gw_anch (Z.shiftl (bv_signed hi_128) 12 + (base + 512) + bv_signed lo_129)%Z (RATP + 131960).
Hypothesis ANCH_148 : gw_anch (Z.shiftl (bv_signed hi_147) 12 + (base + 588) + bv_signed lo_148)%Z (RATP + 131960).
Hypothesis ANCH_217 : gw_anch (Z.shiftl (bv_signed hi_216) 12 + (base + 864) + bv_signed lo_217)%Z (RATP + 131960).
Hypothesis LINK_11 : gw_anch (base + 44 + bv_signed joff_11)%Z (rerrno_loc_entry + 0)%Z.
Hypothesis LINK_37 : gw_anch (base + 148 + bv_signed joff_37)%Z (rmmap_entry + 0)%Z.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_130 : gw_anch (base + 520 + bv_signed joff_130)%Z (rlock_entry + 0)%Z.
Hypothesis LINK_149 : gw_anch (base + 596 + bv_signed joff_149)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_152 : gw_anch (base + 608 + bv_signed joff_152)%Z (rmunmap_entry + 0)%Z.
Hypothesis LINK_203 : gw_anch (base + 812 + bv_signed joff_203)%Z (runlock_entry + 0)%Z.
Hypothesis LINK_218 : gw_anch (base + 872 + bv_signed joff_218)%Z (runlock_entry + 0)%Z.
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
Hypothesis ROM_reservedZ : QGeV.reservedZ segs = ref_reserved.
Hypothesis LAY_ref_reserved : ref_reserved = (cons (0x10000, gw_RTEXT_LO - 0x10000) (cons (gw_RTEXT_LO, RDATA_LO - gw_RTEXT_LO) (cons (RDATA_LO, gw_RDATA2_LO - RDATA_LO) (cons (gw_RDATA2_LO, RIMG_HI - gw_RDATA2_LO) nil))))%Z.
Hypothesis AL_rerrno_loc_entry : gw_al rerrno_loc_entry 4.
Hypothesis AL_rvm_wait_entry : gw_al rvm_wait_entry 4.
Hypothesis AL_rlock_entry : gw_al rlock_entry 4.
Hypothesis AL_runlock_entry : gw_al runlock_entry 4.
Hypothesis ref_find_segment_none : forall z n, (1 <= n)%Z -> (z + n <= 0x10000 \/ RIMG_HI <= z)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment segs z n = None.
Hypothesis ref_ro_addr_false : forall x : LinuxProcessSemantics.Riscv.Prelude.word, (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.ro_addr segs x = false.
Hypothesis ref_memory_read_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word) n, (1 <= Z.of_N n)%Z -> (stdpp.bitvector.definitions.bv_unsigned x + Z.of_N n <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.memory_read segs x n = None.
Hypothesis ref_wview_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview segs m x = m x.
Hypothesis ref_seg_rom_none : forall (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QsjA.seg_rom segs x = None.
Hypothesis ref_mrd_overlay : forall m (x : LinuxProcessSemantics.Riscv.Prelude.word), (stdpp.bitvector.definitions.bv_unsigned x + 1 <= 0x10000 \/ RIMG_HI <= stdpp.bitvector.definitions.bv_unsigned x)%Z -> QZDE.mrd segs m x = m x.
Context {RC__ : Q6q3.RunConsts}.

Notation gw_tbl_0 := tt.

Definition rsize_classes_read : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rsize_classes_read) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rsize_classes_read)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_0)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

#[using="RDEBRUIJN rerrno_loc_entry rmmap_entry rmunmap_entry rlock_entry runlock_entry RATP RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved rvm_wait_entry CODE BASE4 BASER D_11 E_11 D_26 E_26 D_27 E_27 D_37 E_37 D_40 E_40 D_41 E_41 D_43 E_43 D_44 E_44 D_45 E_45 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 D_128 E_128 D_129 E_129 D_130 E_130 D_147 E_147 D_148 E_148 D_149 E_149 D_152 E_152 D_203 E_203 D_216 E_216 D_217 E_217 D_218 E_218 ANCH_27 ANCH_41 ANCH_44 ANCH_59 ANCH_90 ANCH_126 ANCH_129 ANCH_148 ANCH_217 LINK_11 LINK_37 LINK_45 LINK_130 LINK_149 LINK_152 LINK_203 LINK_218 CODE_rerrno_loc_entry AL_rerrno_loc_entry_b4 RNG_rerrno_loc_entry_code RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved AL_rerrno_loc_entry AL_rvm_wait_entry AL_rlock_entry AL_runlock_entry ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__ rmalloc_entry rmmap_entry rmunmap_entry"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
Section RC__1.

Definition rDB32 : Z := 125613361.
Definition rdbi (k : Z) : Z := ((2 ^ k * rDB32) mod 2^32) / 2^27.

#[using="base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rdbi_range k : 0 <= rdbi k < 32.
Proof. clear - base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry k. unfold rdbi. pose proof (Z.mod_pos_bound (2^k * rDB32) (2^32) ltac:(lia)). Z.div_mod_to_equations. nia. Qed.

Definition rdebruijn_bytes : list byte :=
[Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 28; Z_to_bv 8 2; Z_to_bv 8 29; Z_to_bv 8 14; Z_to_bv 8 24; Z_to_bv 8 3; Z_to_bv 8 30; Z_to_bv 8 22; Z_to_bv 8 20; Z_to_bv 8 15; Z_to_bv 8 25; Z_to_bv 8 17; Z_to_bv 8 4; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 27; Z_to_bv 8 13; Z_to_bv 8 23; Z_to_bv 8 21; Z_to_bv 8 19; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 26; Z_to_bv 8 12; Z_to_bv 8 18; Z_to_bv 8 6; Z_to_bv 8 11; Z_to_bv 8 5; Z_to_bv 8 10; Z_to_bv 8 9].

#[using="base rvm_wait_entry RNG_RDEBRUIJN ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rdebruijn_ro : forall m, mem_inv segs m -> ro_cells segs m RDEBRUIJN [CB 32 rdebruijn_bytes].
Proof. clear - base rvm_wait_entry RNG_RDEBRUIJN ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry segs RDEBRUIJN.
intros m MI. pose proof RNG_RDEBRUIJN as RNG_; unfold gw_br in RNG_. split.
- cbn. split; [reflexivity|exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply ro_bytes_at; [exact MI | lia | cbn; lia | exact ROM_RDEBRUIJN].
Qed.

#[using="base rvm_wait_entry RNG_RDEBRUIJN ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rdebruijn_read : forall m k, mem_inv segs m -> 0 <= k < 32 ->
ov_read_bytes segs m (wa (RDEBRUIJN + rdbi k)) 1 = Some [b8 k].
Proof. clear - base rvm_wait_entry RNG_RDEBRUIJN ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry segs RDEBRUIJN. gw_expose_fam RDEBRUIJN.
intros m k MI Hk.
destruct (rdebruijn_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
pose proof (rdbi_range k) as R.
rewrite (bytes_at_read segs m RDEBRUIJN rdebruijn_bytes (rdbi k) 1 B) by (cbn; lia).
assert (Hn : exists n, k = Z.of_nat n /\ (n < 32)%nat) by (exists (Z.to_nat k); split; [lia|lia]).
destruct Hn as (n & -> & Hn).
Ltac solve_db := vm_compute; reflexivity.
do 32 (destruct n as [|n]; [solve_db |]). lia.
Qed.

#[using="base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry"] Lemma mul_srliw27 k : 0 <= k < 32 ->
bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 (2 ^ k * rDB32)))) 27) = rdbi k.
Proof. clear - base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry k.
intros Hk. unfold rdbi.
assert (P : 0 < 2 ^ k <= 2 ^ 31) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]).
rewrite unsigned_lit by (unfold rDB32; nia).
change (bv_wrap 32 (2 ^ k * rDB32)) with ((2 ^ k * rDB32) mod 2^32).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (Z.mod_pos_bound (2 ^ k * rDB32) (2^32) ltac:(lia)).
apply swrap32_small. Z.div_mod_to_equations. nia.
Qed.

Definition rclz_v4 (x : Z) : Z :=
let v1 := Z.lor (Z.shiftr x 2) x in
let v2 := Z.lor v1 (Z.shiftr x 1) in
let w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1) in
let w3 := Z.lor (Z.shiftr w2 4) w2 in
Z.lor (Z.shiftr w3 8) w3.
Definition rclz_pow (x : Z) : Z := Z.land (rclz_v4 x + 1) (Z.lxor (rclz_v4 x) 18446744073709551615).
Definition rclz_fn (x : Z) : bool := (rclz_pow x =? 2 ^ Z.log2 x) && (rclz_v4 x <? 2 ^ 13).
#[using="Type"] Lemma rclz_check_true : forallb rclz_fn (zseq 11 8181) = true.
Proof. clear - segs. vm_compute. reflexivity. Qed.
#[using="base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rclz_pow_eq x : 11 <= x < 8192 -> rclz_pow x = 2 ^ Z.log2 x /\ 0 <= rclz_v4 x < 2 ^ 13.
Proof. clear - base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry x.
intros Hx. pose proof (forallb_zseq rclz_fn 11 8181 x rclz_check_true ltac:(lia) ltac:(lia)) as X. unfold rclz_fn in X.
apply andb_prop in X. destruct X as [X1 X2].
apply Z.eqb_eq in X1. apply Z.ltb_lt in X2. split; [gw_exact X1| split; [|gw_exact X2]].
unfold rclz_v4. repeat first [apply Z.lor_nonneg; split | apply Z.shiftr_nonneg]; lia.
Qed.

#[using="base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry"] Lemma lxor_4k_124 k : 3 <= k <= 12 -> Z.lxor (k * 4) 124 = 124 - 4 * k.
Proof. clear - base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry k. intros Hk. assert (H : k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; reflexivity. Qed.

#[using="base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry"] Lemma lor_even_1 a : 0 <= a -> Z.even a = true -> Z.lor a 1 = a + 1.
Proof. clear - base rvm_wait_entry rmalloc_entry rmmap_entry rmunmap_entry a. intros Ha He.
assert (D : Z.land a 1 = 0). { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2. rewrite Zeven_mod in He. apply Z.eqb_eq in He. gw_exact He. }
rewrite <- Z.lxor_lor by gw_exact D. rewrite <- Z.add_nocarry_lxor by gw_exact D. reflexivity. Qed.

Definition rentry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a0 a1 a2 a3 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0 a1 a2 a3 a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 (size_to_class n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x20c)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_57 hi_85 hi_125 lo_27 lo_59 lo_90 lo_126 CODE D_26 E_26 D_27 E_27 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 ANCH_27 ANCH_59 ANCH_90 ANCH_126 LAY_hi_RATP RNG_RDEBRUIJN ROM_RSIZE_CLASSES ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rmalloc_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD ->
stk segs m lo (bv_unsigned sp) -> RIMG_HI <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv segs m ->
rw_cells segs m (RATP + 131731) [C1 (b8 0)] ->
evt segs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 hi_57 hi_85 hi_125 lo_27 lo_59 lo_90 lo_126 CODE D_26 E_26 D_27 E_27 D_57 E_57 D_59 E_59 D_85 E_85 D_90 E_90 D_125 E_125 D_126 E_126 ANCH_27 ANCH_59 ANCH_90 ANCH_126 LAY_hi_RATP RNG_RDEBRUIJN ROM_RSIZE_CLASSES ROM_RDEBRUIJN rmalloc_entry rmmap_entry rmunmap_entry segs RATP RIMG_HI base RDEBRUIJN. gw_expose_fam RATP; gw_expose_fam RDEBRUIJN.
intros until n. intros HA N ST ILO LO MI NL. subst a0.
pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
(gw_expose_fam RATP; unfold rmalloc_entry in *).
step. carve_frame 48%nat ST. step. step. step. step. step. step.

step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step. step.
step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.

step. step. step. step. step.
rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).

assert (LOCKJ : forall (a0' a1' a2' a3' : word) (sc : Z) (mj : mem),
sc = size_to_class n ->
mem_inv segs mj -> rw_cells segs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk segs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono segs m mj -> rw_cells segs mj (RATP + 131731) [C1 (b8 0)] ->
evt segs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) a0' a1' a2' a3' a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 sc) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1f4)) fc None mj (seg_rom segs))).
{ intros a0' a1' a2' a3' sc mj -> MIj FRj STj MUj WMj NLj.
step. step. rewrite ?zxb_b8 by lia. step. if_cases KL; zify_cond KL. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in KL by lia. lia. }
apply evt_done. (gw_expose_fam RATP; gw_expose_fam RDEBRUIJN; unfold rentry_post). do 5 eexists. split; [reflexivity|].
split; [gw_exact FRj|]. split; [gw_exact STj|]. split; [gw_exact MUj|]. split; [gw_exact WMj| gw_exact MIj]. }
step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
-
apply LOCKJ; try assumption.
rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
-
assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
destruct (rclz_pow_eq x XR) as [PW RV4].

step.
step. rewrite (unsigned_lit x), srliw_small by lia.
pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
step. rewrite (unsigned_lit x), srliw_small by lia.
step.
step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
assert (EW4 : w4 = rclz_v4 x) by first [reflexivity | (cbn; lia)].

step. step. step.
rewrite (unsigned_lit w4), (Z.shiftl_mul_pow2 w4) by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
rewrite (unsigned_lit 0), Z.lor_0_l by lia.

step. step. rewrite (unsigned_lit w4) by lia.
step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
set (k := Z.log2 x) in *.
assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
assert (EK : k = Z.log2 x) by first [reflexivity | (cbn; lia)]. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
assert (EX : x = q + 1) by first [reflexivity | (cbn; lia)]. clearbody x.
assert (K13 : 3 <= k <= 12) by (apply LG; lia).

step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
step. rewrite (mul_srliw27 k) by lia.
pose proof (rdbi_range k) as DR.
step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv segs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; gw_expose_fam RDEBRUIJN end.
step. rewrite ?zxb_b8 by lia. clear DBR.

step. step. step. rewrite (wz_unsigned k), (Z.shiftl_mul_pow2 k) by lia. change (2 ^ 2) with 4.
step.
rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
replace (124 - 4 * k) with (120 - i) by lia.
assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
{ unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
clearbody i. clear EK.
pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.

step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
step. rewrite (unsigned_lit (i + 1)), (Z.shiftl_mul_pow2 (i + 1)) by lia. change (2 ^ 1) with 2.
step. step. replace ((RDEBRUIJN + 32) + (i + 1) * 2) with ((RDEBRUIJN + 32) + 2 * (i + 1)) by lia.
lazymatch goal with HI : mem_inv segs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; gw_expose_fam RDEBRUIJN end.

step. rewrite ?zx16_wz by lia. clear RS1.

assert (J1 : forall (i1 c : Z) (mj : mem),
i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
mem_inv segs mj -> rw_cells segs mj (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk segs mj lo (bv_unsigned sp + -48) ->
munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m mj -> wmono segs m mj -> rw_cells segs mj (RATP + 131731) [C1 (b8 0)] ->
evt segs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960))
(Z_to_bv 64 (120 - i)) (Z_to_bv 64 (RDEBRUIJN + 32)) (Z_to_bv 64 c) (Z_to_bv 64 ((RDEBRUIJN + 32) + 2 * (i + 1))) a4 a5 a6 a7
s2 (Z_to_bv 64 RDEBRUIJN) (Z_to_bv 64 q) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x1d8)) fc None mj (seg_rom segs))).
{ intros i1 c mj Hi1 Hc MIj FRj STj MUj WMj NLj.
assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
{ subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
destruct I1R as [I1R I1E].
pose proof (size_class_range i1 ltac:(lia)) as SR2.

step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
step. rewrite (unsigned_lit i1), (Z.shiftl_mul_pow2 i1) by lia. change (2 ^ 1) with 2.
step. replace ((RDEBRUIJN + 32) + i1 * 2) with ((RDEBRUIJN + 32) + 2 * i1) by lia.
pose proof (rsize_classes_read mj i1 MIj ltac:(lia)) as RS2. gw_expose_fam RDEBRUIJN.
step. rewrite ?zx16_wz by lia. clear RS2.

step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
step. step.
destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
* rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
* rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
apply LOCKJ; try assumption. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
+
step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
+
step. step. eapply J1; try eassumption; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Definition rentry_big_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) (n : Z) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 (RATP + 131960)) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x74)) fc None m' (seg_rom segs)
/\ rw_cells segs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
/\ stk segs m' lo (bv_unsigned sp + -48)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'.

#[using="rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 lo_27 CODE D_26 E_26 D_27 E_27 ANCH_27 rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rentry_big_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z),
a0 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
stk segs m lo (bv_unsigned sp) -> RIMG_HI <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv segs m ->
evt segs (rentry_big_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m n)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).
Proof. clear - rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 hi_26 lo_27 CODE D_26 E_26 D_27 E_27 ANCH_27 rmalloc_entry rmmap_entry rmunmap_entry segs RIMG_HI RATP. gw_expose_fam RATP.
intros until n. intros HA N ST ILO LO MI. subst a0. unfold MMAP_THRESHOLD in N.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. 2:{ exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.
step. step. step. step. step.
step. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
clear K1.
apply evt_done. (gw_expose_fam RATP; unfold rentry_big_post). do 2 eexists. split; [reflexivity|].
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -48) _ |- _ => split; [gw_exact H|] end.
repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rentry_ovf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists a1 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ stk segs m' lo (bv_unsigned sp)
/\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ rw_cells segs m' (errno_addr tp) [C4 (Z_to_bv 64 12)].

#[using="rerrno_loc_entry rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_11 CODE BASE4 BASER D_11 E_11 LINK_11 CODE_rerrno_loc_entry RNG_RATP LAY_hi_RATP rmalloc_entry rmmap_entry rmunmap_entry"] Lemma rentry_ovf_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n : Z) (errv : word),
a0 = Z_to_bv 64 n -> 2^63 - 4097 <= n < 2^64 ->
stk segs m lo (bv_unsigned sp) -> RIMG_HI <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv segs m ->
rw_cells segs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
evt segs (rentry_ovf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom segs)).
Proof. clear - rerrno_loc_entry rvm_wait_entry w_11 w_26 w_27 w_37 w_40 w_41 w_43 w_44 w_45 w_57 w_59 w_85 w_90 w_125 w_126 w_128 w_129 w_130 w_147 w_148 w_149 w_152 w_203 w_216 w_217 w_218 joff_11 CODE BASE4 BASER D_11 E_11 LINK_11 CODE_rerrno_loc_entry RNG_RATP LAY_hi_RATP rmalloc_entry rmmap_entry rmunmap_entry segs RATP RIMG_HI. gw_expose_fam RATP.
intros until errv. intros HA N ST ILO LO MI ERR TP. subst a0.
assert (ETP : bv_unsigned tp + -164 = (RATP + -164)) by (rewrite TP; gw_expose_fam RATP; rewrite unsigned_lit by lia; first [reflexivity | lia]).
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU. pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold rmalloc_entry.
step. carve_frame 48%nat ST. step. step. step. step. step. step.
step. step. step.
step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
clear K0.

step. step. step. step.

step. step. step. step. step. step. step. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold rentry_ovf_post. do 2 eexists. split; [reflexivity|].
split; [gw_exact ST|]. split; [gw_exact MU|]. split; [gw_exact WM|]. split; [gw_exact MI|].
lazymatch goal with H : rw_cells segs m2 (bv_unsigned tp + -164) _ |- _ => exact H end.
Qed.

End RC__1.

End G.
End Mq8.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import Q2qa.Mq1 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2.
Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
Import Q6q3.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwFold.
Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.G.GwFamMalloc.
Local Ltac step_core segs R F pc fc rv m ro ::= gw_rom_norm; sg_step_core; gw_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := gw_rom_norm; sg_step_core; gw_pc_norm.
Local Ltac zstep ::= gw_rom_norm; sg_zstep; gw_pc_norm. Local Ltac mkr__zstep_1 := gw_rom_norm; sg_zstep; gw_pc_norm.
Local Ltac amo_step AMO ::= g_amo_step AMO. Local Ltac mkr__amo_step_2 AMO := g_amo_step AMO.
Open Scope bv_scope.
Open Scope Z_scope.

Definition ntf_code (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z) : list Z :=
[0xfa010113; 0x04113c23; 0x04813823; 0x04913423; 0x05213023; 0x03313c23; w_6; w_7; 0x0004b603; 0x02c13823; 0x02053783; 0x01c52603; 0x01852683; 0x00100713; 0x00b715bb; 0x03479713; 0x00c6e6b3; 0x0207f813; 0x03a75613; 0x10080863; 0x00b6873b; 0x00200813; 0x00f8183b; 0xfff8081b; 0x0f071e63; 0x02f00713; w_26; w_27; 0x0ac76263; 0x01f7f713; 0x00c7d893; w_31; w_32; 0x00088e63; 0x00071c63; 0xfffff2b7; 0x0057f7b3; 0xff078793; 0x02089063; 0x0780006f; 0x0057d793; 0x07e7f793; 0x00f807b3; 0x0007d783; 0x00479793; 0x06088063; 0x00161893; 0x01180833; 0x00085803; 0x00481813; 0x0507e663; 0x00853783; 0x04a79263; 0xff960793; 0x01f00813; 0x02f86c63; 0x00f907b3; 0x3707c783; 0x06400813; 0x0307e463; 0x00361793; 0x00f907b3; 0x1d07b783; 0x00371813; 0x00e80833; 0x00980813; 0x0507ea63; 0x01200793; 0x04e7e663; 0x00853683; 0x10068863; 0x03000593; 0x00b66463; 0x00000023; 0x00361593; 0x00b905b3; 0x0505b603; 0x08a68463; 0x00053703; 0x00d73423; 0x00053683; 0x00853703; 0x00d73023; 0x0505b683; 0x06a69a63; 0x00853683; 0x0680006f; 0x01c50713; 0x22069063; 0x03000693; 0x00d66463; 0x00000023; 0x00361613; w_93; w_94; 0x00c686b3; 0x0506b603; 0x1ea60e63; 0x00853783; 0x00078463; 0x00000023; 0x00053783; 0x00078463; 0x00000023; 0x1c060863; 0x00c53423; 0x00063603; 0x00c53023; 0x00a63423; 0x00853603; 0x1c40006f; 0x00000693; 0x04d5b823; 0x00053023; 0x00053423; 0x04a61e63; 0x0505b583; 0x04058a63; 0x0185a603; 0x00060463; 0x00000023; 0x0105b603; 0x00864603; 0x00200693; 0x00c6963b; 0x01c58693; 0x40c0073b; 0x0006a783; 0x00e7f833; 0x1606a8af; 0x00f89663; 0x1f06a2af; 0xfe029ae3; 0x0008889b; 0xfef892e3; 0xfff60613; 0x00c7f633; 0x00c5ac23; 0x02053603; 0x03461593; 0x03a5d593; 0x02f00693; 0x02b6e263; 0x00359693; 0x00d906b3; 0x1d06b703; 0xfff64613; 0xfe066613; 0x00c70633; 0x1cc6b823; 0x02053603; 0x00c65613; 0x02061a63; 0x01053403; 0x00050993; 0x00040513; 0xc81ff0ef; 0x0109b583; 0xffd44603; 0x0005b023; 0x01f67593; 0xd7dff0ef; 0x00050613; 0x00098513; 0x0540006f; 0x39094603; 0x0ff00693; 0x00d61e63; 0x34093823; 0x34093c23; 0x36093023; 0x36093423; 0x00100613; 0x0080006f; 0x00160613; 0xff958593; 0x01f00693; 0x38c90823; 0x00b6e663; 0x00b905b3; 0x34c58823; 0x02053583; 0x01053603; 0xfffff6b7; 0x00d5f5b3; 0x00013423; 0x00013823; 0x00013c23; 0x02013023; 0x02013423; 0x01013683; 0x00d53423; 0x00813683; 0x00d53023; 0x01813683; 0x00d53823; 0x02013683; 0x00d53c23; 0x02813683; 0x02d53023; 0x00853683; 0x00068463; 0x00000023; 0x00053683; 0x00068463; 0x00000023; 0x01093683; 0x02068063; 0x00d53423; 0x0006b683; 0x00d53023; 0x00a6b423; 0x00853903; 0x00a93023; 0x0500006f; 0x00a53023; 0x00a53423; 0x01090913; 0x00a93023; 0x03c0006f; 0x05068613; 0x00a53023; 0x00a53423; 0x00a63023; 0x00072503; 0x00b56633; 0x160726af; 0x00a69663; 0x1ec727af; 0xfe079ae3; 0x0006869b; 0xfea692e3; 0x00000613; 0x00000593; 0x0004b503; 0x03013683; 0x02d51263; 0x00060513; 0x05813083; 0x05013403; 0x04813483; 0x04013903; 0x03813983; 0x06010113; 0x00008067; w_245]%Z.

Section G.
Variables (segs : list LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment) (base : Z).
Variables (RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO : Z).
Variable ref_reserved : list (Z * Z).
Variables (w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 : Z).
Variables (hi_6 hi_26 hi_31 hi_93 : bv 20).
Variables (lo_7 lo_27 lo_32 lo_94 : bv 12).
Variables (joff_245 : bv 21).
Variables (e_197bc : Z).
Hypothesis CODE : code_at segs base (ntf_code w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 984.
Hypothesis D_6 : decode_any (Z_to_bv 32 w_6) = Some (Auipc 12 hi_6, 4%Z).
Hypothesis E_6 : is_ecall (Z_to_bv 32 w_6) = false.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Load SZ8 true 9 12 lo_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 16 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (OpImm ALU_ADD 18 16 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_31 : decode_any (Z_to_bv 32 w_31) = Some (Auipc 16 hi_31, 4%Z).
Hypothesis E_31 : is_ecall (Z_to_bv 32 w_31) = false.
Hypothesis D_32 : decode_any (Z_to_bv 32 w_32) = Some (OpImm ALU_ADD 16 16 lo_32, 4%Z).
Hypothesis E_32 : is_ecall (Z_to_bv 32 w_32) = false.
Hypothesis D_93 : decode_any (Z_to_bv 32 w_93) = Some (Auipc 13 hi_93, 4%Z).
Hypothesis E_93 : is_ecall (Z_to_bv 32 w_93) = false.
Hypothesis D_94 : decode_any (Z_to_bv 32 w_94) = Some (OpImm ALU_ADD 13 13 lo_94, 4%Z).
Hypothesis E_94 : is_ecall (Z_to_bv 32 w_94) = false.
Hypothesis D_245 : decode_any (Z_to_bv 32 w_245) = Some (Jal 1 joff_245, 4%Z).
Hypothesis E_245 : is_ecall (Z_to_bv 32 w_245) = false.
Hypothesis ANCH_7 : gw_anch (Z.shiftl (bv_signed hi_6) 12 + (base + 24) + bv_signed lo_7)%Z RGOT_SSP.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z (RATP + 131968).
Hypothesis ANCH_32 : gw_anch (Z.shiftl (bv_signed hi_31) 12 + (base + 124) + bv_signed lo_32)%Z (RDEBRUIJN + 32).
Hypothesis ANCH_94 : gw_anch (Z.shiftl (bv_signed hi_93) 12 + (base + 372) + bv_signed lo_94)%Z (RATP + 131968).
Hypothesis LINK_245 : gw_anch (base + 980 + bv_signed joff_245)%Z (e_197bc + 0)%Z.
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

Definition rfree_fp : ltac:(gw_rebind_ty (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rfree_fp RATP) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QDXD.Mq2.rfree_fp RATP) (@rfree_fp) gw_tbl_0).
Definition rpres_except : ltac:(gw_rebind_ty (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@QCa8.Mq5.rpres_except segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QDXD.Mq2.rpres_except segs) (@rpres_except) (gw_ent (@QCa8.Mq5.rpres_except segs) (@rpres_except) gw_tbl_1)).
Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_2)))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_3)))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_4)))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_5)))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_6)))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_7)))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_8)))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_9)))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_10)).
Notation gw_tbl_11 := (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_10)))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_11)).
Notation gw_tbl_12 := (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_11)))).
Definition rntf_ret_post : ltac:(gw_rebind_ty (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)) := ltac:(gw_rebind_tm (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_12)).
Notation gw_tbl_13 := (gw_ent (@QDXD.Mq2.rntf_ret_post segs RATP RGOT_SSP ref_reserved RC__) (@rntf_ret_post) gw_tbl_12).

Definition rmrep_meta_chunk : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_meta_chunk) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_meta_chunk)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rmrep_transport_high : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rmrep_transport_high) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rmrep_transport_high)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_put_meta_frame : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_put_meta_frame) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_put_meta_frame)).
Definition rmeta_slot_bounds : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmeta_slot_bounds) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmeta_slot_bounds)).
Definition rfree_fp_stack : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_stack) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_stack)).
Definition rfree_fp_ctx : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_ctx) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_ctx)).
Definition rfree_fp_meta : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rfree_fp_meta) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rfree_fp_meta)).
Definition rpres_except_of_munch_cov : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rpres_except_of_munch_cov) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rpres_except_of_munch_cov)).
Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_13)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

#[using="RGOT_SSP e_197bc RATP RDEBRUIJN RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved CODE BASE4 BASER D_6 E_6 D_7 E_7 D_26 E_26 D_27 E_27 D_31 E_31 D_32 E_32 D_93 E_93 D_94 E_94 D_245 E_245 ANCH_7 ANCH_27 ANCH_32 ANCH_94 LINK_245 RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1.

Definition rntf_frame (junk : list byte) (s3 s2 s1 s0 ra : word) : list cell :=
[CB 48 junk; C8 rc_canary; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End RC__1.

Ltac rmeta_open cq MUq WMq :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(cq, cq + 40)]%Z mX) as MUq;
pose proof (wmono_refl segs mX) as WMq end.

Ltac rmeta_close MRold MSq MUq WMq CH st' MRnew :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRnew : rmrep st' mX)
by (eapply rmrep_put_meta_frame; [gw_exact MRold | gw_exact MSq | gw_exact MUq | gw_exact WMq |];
eapply rw_cells_congr; [ | | | gw_exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear MUq WMq CH end.

Ltac rmeta_chunk MR MSq CH :=
pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
rewrite ?get_meta_rec_put_same in CH;
rewrite ?conc_put_meta, ?pw_put_meta in CH;
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0
m_set_prev m_set_next m_set_mem m_set_avail m_set_freed Z.mul Z.add] in CH;
rewrite ?meta_word_meta0 in CH; unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.
Section RC__2.

#[using="RIMG_HI gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4"] Lemma rntf_ret : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (raw s0o s1o s2o s3o : word) st st' (lo : Z),
rmrep st' m -> mem_inv segs m ->
s1 = Z_to_bv 64 (RATP + 131696) ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
munch ((bv_unsigned sp - 96, bv_unsigned sp) :: W) m0 m -> wmono segs m0 m ->
ivs_covered (rfree_fp st lo (bv_unsigned sp)) W ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st' a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x3a8)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_4 segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR' MI S1 FR ST LO LOLE MU WM COV.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
(gw_expose_fam RATP; unfold alloc_ceiling, rntf_frame in *). subst s1.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl segs m) as WMs.
st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [gw_exact MR' | gw_exact MUs | gw_exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MR' MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [|gw_exact WM|].
2:{ cbn [ivs_covered]. split; [|gw_exact COV]. intros x Hx. apply rfree_fp_stack. lia. }
finish.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_aor : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (i lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g ->
a1 = wz (sxv (2 ^ i)) -> 0 <= i < 32 ->
s1 = Z_to_bv 64 (RATP + 131696) ->
0 <= m_freed (get_meta_rec st g) < 2^32 ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (aor_st st g i) (wz 0) (wz 0))
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (conc st g + 28)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x380)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL A1 HI S1 HF FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40)]%Z m) as MU.
pose proof (munch_refl [(conc st g, conc st g + META_SIZE)]%Z m) as MUg. unfold META_SIZE in MUg.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR as (WF & _). pose proof MSL as MS0. destruct MS0 as (ar0 & arr0 & k0 & Har0 & Hk0 & Eg0).
destruct (rarea_conc st ar0 arr0 WF Har0) as (ra0 & Hra0 & Ca0 & Sa00 & Sa01 & SaL0 & NK0 & RB00 & RBAL0 & RBC0).
assert (HGA : conc st g = conc st ar0 + (24 + 40 * k0)) by (rewrite Eg0, conc_aadd by (rewrite Hra0; eauto); reflexivity).
unfold alloc_ceiling, NSLOTS in *.
assert (GB : 0 <= conc st g /\ conc st g + 40 <= lo) by lia.
pose proof (rmrep_meta_chunk st m g MR MSL) as MM. unfold meta_cells in MM.
set (mr := get_meta_rec st g) in *.
pose proof (sxv_range (2 ^ i)) as RS. pose proof (sxv_range (m_freed mr)) as RF.
assert (AMO : amo_aligned AW (Z_to_bv 64 (conc st g + 28)) = true).
{ apply amo_aligned_intro; [lia|]. rewrite HGA, Ca0. Z.div_mod_to_equations. lia. }
subst a1.
st1. rewrite sx32_wz_sxv by lia. st1.
amo_step AMO. rewrite ?sx32_wz_sxv by lia.
st1. if_false.
amo_step AMO.
st1. if_false.
st1. rewrite ?sextw_sxv0, ?sextw_sxv1. st1. if_false.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR' : rmrep (aor_st st g i) mX) end.
{ unfold aor_st. rewrite upd_meta_put. eapply rmrep_put_meta_frame; [gw_exact MR | gw_exact MSL | gw_exact MUg | gw_exact WM |].
eapply rw_cells_congr; [ | | | gw_exact MM].
- unfold meta_cells. cbn [cells_bytes cbytes m_set_freed m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen].
rewrite (Z.lor_comm (sxv (m_freed mr)) (sxv (2 ^ i))).
rewrite (le4_lor_sxv (m_freed mr) (2 ^ i)); [reflexivity | lia |].
split; [apply Z.pow_nonneg; lia | apply Z.pow_lt_mono_r; lia].
- reflexivity.
- cbn. tauto. }
clear MUg MM.

st1. st1.
eapply rntf_ret; [gw_exact MR' | assumption | gw_exact S1 | gw_exact FR | gw_exact ST | unfold alloc_ceiling; lia | lia | gw_exact MU | gw_exact WM |].
cbn [ivs_covered]. split; [|exact I]. intros x Hx. eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
Qed.

#[using="Type"] Lemma rntf_frame_remerge : forall m A (j0 : list byte) (z1 z2 z3 z4 z5 : word) rest,
rw_cells segs m A (CB 8 j0 :: C8 z1 :: C8 z2 :: C8 z3 :: C8 z4 :: C8 z5 :: rest) ->
rw_cells segs m A (CB 48 (j0 ++ le8 z1 ++ le8 z2 ++ le8 z3 ++ le8 z4 ++ le8 z5) :: rest).
Proof. clear - segs.
intros m A j0 z1 z2 z3 z4 z5 rest H. pose proof H as [[WF _] _]. destruct WF as [L0 WFr]. cbn in L0.
eapply rw_cells_congr; [| | | gw_exact H].
- cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
- reflexivity.
- split; [| destruct WFr as (_ & _ & _ & _ & _ & X); gw_exact X]. cbn [cell_wf]. rewrite !length_app, !length_le8, L0. reflexivity.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved"] Lemma rntf_fm : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
(m : word -> option byte) (junk : list byte) (raw s0o s1o s2o s3o : word) st (g : aptr) (lo : Z),
rmrep st m -> mem_inv segs m -> meta_slot st g ->
fm_facts st g ->
s1 = Z_to_bv 64 (RATP + 131696) ->
rw_cells segs m (bv_unsigned sp + -96) (rntf_frame junk s3o s2o s1o s0o raw) ->
stk segs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt segs (rntf_ret_post raw sp gp tp s0o s1o s2o s3o s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m (fm_st st g) a2 a1)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (RATP + 131968)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x2e4)) fc None m (seg_rom segs)).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO w_6 w_7 w_26 w_27 w_31 w_32 w_93 w_94 w_245 CODE RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved segs base RATP. gw_expose_fam RATP.
intros until lo. intros MR MI MSL FMF S1 FR ST LO LOLE.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (conc st g, conc st g + 40); ((RATP + 131968), (RATP + 132896))]%Z m) as MU.
pose proof (wmono_refl segs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st m g MR MSL) as GB.
pose proof FR as [[[LJ _] _] _]. cbn in LJ.
(gw_expose_fam RATP; unfold alloc_ceiling, rntf_frame in *).
rmeta_chunk MR MSL CH.

pose proof MR as (_ & (C1 & _) & _). (gw_expose_fam RATP; unfold ctx_head_cells in C1).
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MUs.

st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MRf : rmrep st mX)
by (eapply rmrep_transport_high; [gw_exact MR | gw_exact MUs | gw_exact WM | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs.

rmeta_open (conc st g) MUg WMg.
st1. st1.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C4 ?va; C4 ?vf; ?c5] =>
assert (CH' : rw_cells segs mX A [c0; c1; c2; CB 8 (le4 va ++ le4 vf); c5])
by (eapply rw_cells_congr; [ | | | gw_exact CH]; [cbn [cells_bytes cbytes app]; rewrite <- ?app_assoc; reflexivity | reflexivity | cbn -[le4 app]; rewrite ?app_length, ?length_le4; cbn; tauto]);
clear CH; rename CH' into CH
end end.
st1. st1.
st1. st1.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
lazymatch type of CH with rw_cells _ _ ?A [?c0; ?c1; ?c2; C8 ?z; ?c5] =>
assert (CH' : rw_cells segs mX A [c0; c1; c2; C4 (wz 0); C4 (wz 0); c5])
by (eapply rw_cells_congr; [ | | | gw_exact CH]; [reflexivity | reflexivity | cbn; tauto]);
clear CH; rename CH' into CH
end end.
rmeta_close MRf MSL MUg WMg CH (put_meta g meta0 st) MR0.
set (st0 := put_meta g meta0 st) in MR0.
assert (MSL0 : meta_slot st0 g) by (apply meta_slot_put_meta; gw_exact MSL).

rmeta_chunk MR0 MSL0 CH0.
st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
clear CH0 K1 K2.

st1. destruct (c_free_meta_head (ctx st)) as [head|] eqn:FMH.
-
destruct (FMF head FMH) as (NEh & MSh & pv & Hpv & NEp & MSp).
pose proof (rmeta_slot_bounds st m head MR MSh) as HB. pose proof (rmeta_slot_bounds st m pv MR MSp) as PB.
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_next (Some head) meta0) st0) MRa.
set (stA := put_meta g (m_set_next (Some head) meta0) st0) in MRa.
assert (MSha : meta_slot stA head) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSh).
assert (MSga : meta_slot stA g) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSL).
assert (MSpa : meta_slot stA pv) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSp).

rmeta_chunk MRa MSha CHh. rewrite get_meta_rec_put_other in CHh by gw_exact NEh.
unfold st0 in CHh. rewrite get_meta_rec_put_other in CHh by gw_exact NEh. rewrite Hpv in CHh. cbn [oconc] in CHh.
st1.
clear CHh.

rmeta_open (conc st g) MUg WMg.
rmeta_chunk MRa MSga CH.
st1.
rmeta_close MRa MSga MUg WMg CH (put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) stA) MR1.
unfold stA in MR1. rewrite put_meta_put_meta_same in MR1. clear MRa MSha MSga MSpa stA.
set (st1 := put_meta g (m_set_prev (Some pv) (m_set_next (Some head) meta0)) st0) in MR1.
assert (MSh1 : meta_slot st1 head) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSh).
assert (MSg1 : meta_slot st1 g) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSL).
assert (MSp1 : meta_slot st1 pv) by (apply meta_slot_put_meta, meta_slot_put_meta; gw_exact MSp).

munch_grow MU (conc st pv, conc st pv + 40). munch_grow MU (conc st head, conc st head + 40).
rmeta_open (conc st pv) MUp WMp.
rmeta_chunk MR1 MSp1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (gw_exact NEp).
st1.
rmeta_close MR1 MSp1 MUp WMp CH (put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) MR2.
set (st2 := put_meta pv (m_set_next (Some g) (get_meta_rec st pv)) st1) in MR2.
assert (MSh2 : meta_slot st2 head) by (apply meta_slot_put_meta; gw_exact MSh1).
assert (MSg2 : meta_slot st2 g) by (apply meta_slot_put_meta; gw_exact MSg1).

rmeta_chunk MR2 MSg2 CH. unfold st2 in CH. rewrite get_meta_rec_put_other in CH by (intros E; apply NEp; symmetry; gw_exact E).
unfold st1 in CH. rewrite get_meta_rec_put_same in CH.
cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen meta_word meta0 m_set_prev m_set_next Z.mul Z.add oconc] in CH.
st1. clear CH.

rmeta_open (conc st head) MUh WMh.
rmeta_chunk MR2 MSh2 CH.
st1.
rmeta_close MR2 MSh2 MUh WMh CH (put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2) MR3.
assert (EQ3 : fm_st st g = put_meta head (m_set_prev (Some g) (get_meta_rec st2 head)) st2).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_link.
rewrite !upd_meta_put. rewrite (get_meta_rec_put_other st g meta0 head NEh), Hpv. cbn iota. rewrite !upd_meta_put.
rewrite get_meta_rec_put_same.
rewrite (get_meta_rec_put_other (put_meta g meta0 st) g _ pv NEp). rewrite (get_meta_rec_put_other st g meta0 pv NEp).
reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [gw_exact MR3 | assumption | gw_exact S1 | gw_exact FR' | gw_exact ST | unfold alloc_ceiling; lia | lia | gw_exact MU | gw_exact WM |].
cbn [ivs_covered]. gw_expose_fam RATP. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSh | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSp | lia].
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia.
-
unfold pw, wz; cbn [oconc]. st1. if_cases K; zify_cond K. 2:{ exfalso. rewrite ?unsigned_lit in K by lia. lia. }
clear K.
rmeta_open (conc st g) MUg WMg.
rmeta_chunk MR0 MSL0 CH.
st1. st1.
rmeta_close MR0 MSL0 MUg WMg CH (put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) MRb.
set (stB := put_meta g (m_set_prev (Some g) (m_set_next (Some g) meta0)) st0) in MRb.

clear C1. pose proof MRb as (_ & (C1 & _) & _). (gw_expose_fam RATP; unfold ctx_head_cells in C1). rewrite FMH in C1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [((RATP + 131984), (RATP + 131992))]%Z mX) as MUc; pose proof (wmono_refl segs mX) as WMc end.
gw_expose_fam RATP.
st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (set_head LFree (Some g) stB) mX) end.
{ eapply (rmrep_ctx_frameW stB _ _ _ _ MRb MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- left. (gw_expose_fam RATP; unfold ctx_head_cells). cbn [ctx set_head upd_ctx s_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 4. cbn [oconc]. unfold wz at 4. gw_exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. gw_expose_fam RATP. lia. }
clear MUc WMc C1.
assert (EQ3 : fm_st st g = set_head LFree (Some g) stB).
{ unfold fm_st, queue_st. cbn [get_head]. rewrite ctx_put_meta, FMH. unfold fm_single. rewrite upd_meta_put. fold st0. rewrite get_meta_rec_put_same. reflexivity. }
rewrite <- EQ3 in MR3. clear EQ3.

st1.
lazymatch goal with H : rw_cells segs _ (bv_unsigned sp + -96) _ |- _ => apply rntf_frame_remerge in H; rename H into FR' end.
eapply rntf_ret; [gw_exact MR3 | assumption | gw_exact S1 | gw_exact FR' | gw_exact ST | unfold alloc_ceiling; lia | lia | gw_exact MU | gw_exact WM |].
cbn [ivs_covered]. gw_expose_fam RATP. repeat split; intros x Hx.
+ eapply rfree_fp_meta; [gw_exact MR | gw_exact MSL | lia].
+ apply rfree_fp_ctx. gw_expose_fam RATP. lia.
Qed.

End RC__2.

End G.
End Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.

Import Q2qa.Mq1 QytA QJE4.Mq4 Qy5Y.Mq5.
Export QWTl.Mq5.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import Q8QT.Mq4.
Import QCa8.Mq5.
Import QDXD.Mq2.
Import QkTt.Mq3.
Import QkTt.Mq4.
Import QDXD.Mq1.
Import QkTt.Mq5.
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

Definition rarea_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rarea_rep segs) constr:(gw_tbl_0)).
Notation gw_tbl_1 := (gw_ent (@QkTt.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq1.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq4.rarea_rep segs) (@rarea_rep) (gw_ent (@QkTt.Mq3.rarea_rep segs) (@rarea_rep) (gw_ent (@QDXD.Mq2.rarea_rep segs) (@rarea_rep) (gw_ent (@QCa8.Mq5.rarea_rep segs) (@rarea_rep) (gw_ent (@Q8QT.Mq4.rarea_rep segs) (@rarea_rep) gw_tbl_0))))))).
Definition rmrep_areas : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_areas segs) constr:(gw_tbl_1)).
Notation gw_tbl_2 := (gw_ent (@QkTt.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq1.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq4.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QkTt.Mq3.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QDXD.Mq2.rmrep_areas segs) (@rmrep_areas) (gw_ent (@QCa8.Mq5.rmrep_areas segs) (@rmrep_areas) (gw_ent (@Q8QT.Mq4.rmrep_areas segs) (@rmrep_areas) gw_tbl_1))))))).
Definition rmrep_ctx : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_ctx segs RATP) constr:(gw_tbl_2)).
Notation gw_tbl_3 := (gw_ent (@QkTt.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq1.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QkTt.Mq3.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QDXD.Mq2.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@QCa8.Mq5.rmrep_ctx segs RATP) (@rmrep_ctx) (gw_ent (@Q8QT.Mq4.rmrep_ctx segs RATP) (@rmrep_ctx) gw_tbl_2))))))).
Definition rmrep_globals : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) constr:(gw_tbl_3)).
Notation gw_tbl_4 := (gw_ent (@QkTt.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq1.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QkTt.Mq3.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QDXD.Mq2.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@QCa8.Mq5.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) (gw_ent (@Q8QT.Mq4.rmrep_globals segs RATP RGOT_SSP RC__) (@rmrep_globals) gw_tbl_3))))))).
Definition rgroup_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rgroup_rep segs) constr:(gw_tbl_4)).
Notation gw_tbl_5 := (gw_ent (@QkTt.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq1.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq4.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QkTt.Mq3.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QDXD.Mq2.rgroup_rep segs) (@rgroup_rep) (gw_ent (@QCa8.Mq5.rgroup_rep segs) (@rgroup_rep) (gw_ent (@Q8QT.Mq4.rgroup_rep segs) (@rgroup_rep) gw_tbl_4))))))).
Definition rmrep_groups : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_groups segs) constr:(gw_tbl_5)).
Notation gw_tbl_6 := (gw_ent (@QkTt.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq1.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq4.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QkTt.Mq3.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QDXD.Mq2.rmrep_groups segs) (@rmrep_groups) (gw_ent (@QCa8.Mq5.rmrep_groups segs) (@rmrep_groups) (gw_ent (@Q8QT.Mq4.rmrep_groups segs) (@rmrep_groups) gw_tbl_5))))))).
Definition rshadow_rep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rshadow_rep segs) constr:(gw_tbl_6)).
Notation gw_tbl_7 := (gw_ent (@QkTt.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq1.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq4.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QkTt.Mq3.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QDXD.Mq2.rshadow_rep segs) (@rshadow_rep) (gw_ent (@QCa8.Mq5.rshadow_rep segs) (@rshadow_rep) (gw_ent (@Q8QT.Mq4.rshadow_rep segs) (@rshadow_rep) gw_tbl_6))))))).
Definition rmrep_shadow : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep_shadow segs) constr:(gw_tbl_7)).
Notation gw_tbl_8 := (gw_ent (@QkTt.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq1.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq4.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QkTt.Mq3.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QDXD.Mq2.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@QCa8.Mq5.rmrep_shadow segs) (@rmrep_shadow) (gw_ent (@Q8QT.Mq4.rmrep_shadow segs) (@rmrep_shadow) gw_tbl_7))))))).
Definition rregions_wf : ltac:(gw_rebind_ty (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rregions_wf ref_reserved RC__) constr:(gw_tbl_8)).
Notation gw_tbl_9 := (gw_ent (@QkTt.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq1.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QkTt.Mq3.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QDXD.Mq2.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@QCa8.Mq5.rregions_wf ref_reserved RC__) (@rregions_wf) (gw_ent (@Q8QT.Mq4.rregions_wf ref_reserved RC__) (@rregions_wf) gw_tbl_8))))))).
Definition rmrep : ltac:(gw_rebind_ty (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)) := ltac:(gw_rebind_tm (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) constr:(gw_tbl_9)).
Notation gw_tbl_10 := (gw_ent (@QkTt.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq1.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QkTt.Mq3.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QDXD.Mq2.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@QCa8.Mq5.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) (gw_ent (@Q8QT.Mq4.rmrep segs RATP RGOT_SSP ref_reserved RC__) (@rmrep) gw_tbl_9))))))).

Definition rarea_lr_lo : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_lr_lo) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_lr_lo)).
Definition rshadow_rep_ext : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rshadow_rep_ext) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rshadow_rep_ext)).
Definition rarea_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rarea_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rarea_conc)).
Definition rgroup_conc : ltac:(gw_ctx_fold_ty2 (@Q8QT.Mq4.rgroup_conc) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@Q8QT.Mq4.rgroup_conc)).

Definition rimplT_from_evt : ltac:(gw_ctx_fold_ty2 (@QCa8.Mq5.rimplT_from_evt) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QCa8.Mq5.rimplT_from_evt)).
#[global] Arguments rimplT_from_evt {R}%_type_scope o t s Q%_function_scope ms _.

Definition rmrep_ctx_frameW : ltac:(gw_ctx_fold_ty2 (@QDXD.Mq2.rmrep_ctx_frameW) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QDXD.Mq2.rmrep_ctx_frameW)).

Definition rreserved_disjoint2 : ltac:(gw_ctx_fold_ty2 (@QkTt.Mq5.rreserved_disjoint2) constr:(gw_tbl_10)) := ltac:(gw_ctx_fold_tm2 (@QkTt.Mq5.rreserved_disjoint2)).

#[using="RATP RDEBRUIJN RGOT_SSP RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO ref_reserved RNG_RATP LAY_lo_RATP LAY_hi_RATP AL_RATP RNG_RDEBRUIJN LAY_lo_RDEBRUIJN LAY_hi_RDEBRUIJN AL_RDEBRUIJN RNG_RGOT_SSP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP AL_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 AL_win_RIMG_HI AL_win_RDATA_LO AL_win_gw_RTEXT_LO AL_win_gw_RDATA2_LO ROM_RSIZE_CLASSES ROM_RDEBRUIJN ROM_RSMALL_CNT ROM_RMED_CNT ROM_reservedZ LAY_ref_reserved ref_find_segment_none ref_ro_addr_false ref_memory_read_none ref_wview_overlay ref_seg_rom_none ref_mrd_overlay RC__"] Lemma gw_all : True. Proof. exact I. Qed.

Section RC__1.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. clear - Hconc p st st' P HP Hctx Hmetas. first [clear Hmetas | gw_hide Hmetas | idtac]; first [clear Hctx | gw_hide Hctx | idtac]; first [clear HP | gw_hide HP | idtac]; first [clear P | gw_hide P | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac]. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by gw_exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. clear - Hmetas g st st' P HP Hconc Hctx. first [clear Hctx | gw_hide Hctx | idtac]; first [clear Hconc | gw_hide Hconc | idtac]; first [clear HP | gw_hide HP | idtac]; first [clear P | gw_hide P | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac]. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof. clear - P HP Hconc g st st' Hctx Hmetas. first [clear Hmetas | gw_hide Hmetas | idtac]; first [clear Hctx | gw_hide Hctx | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac].
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

#[using="P HP Hconc Hctx"] Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof. clear - P HP Hconc Hctx m st st' Hmetas. first [clear Hmetas | gw_hide Hmetas | idtac]; try gw_hide st'; try gw_hide st.
intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
assert (E1 : ctx_head_cells st' = ctx_head_cells st).
{ unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
assert (E2 : actives st' = actives st).
{ unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
{ unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
rewrite (Hconc (rid, off)) by gw_exact H7. reflexivity. }
unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. gw_exact H.
Qed.

#[using="P HP Hconc Hmetas"] Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof. clear - P HP Hconc Hmetas m a ar st st' Hctx. first [clear Hctx | gw_hide Hctx | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac].
intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
destruct (H9 a ar Ha) as [Pa Pn].
unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [gw_exact A1|]. split; [|gw_exact A3].
intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. gw_exact Hk.
Qed.

#[using="P HP Hconc"] Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof. clear - P HP Hconc m b gh st st' Hctx Hmetas. first [clear Hmetas | gw_hide Hmetas | idtac]; first [clear Hctx | gw_hide Hctx | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear st | gw_hide st | idtac].
intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

#[using="Type"] Lemma rbytes_at_agree m m' A bs : bytes_at segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at segs m' A bs.
Proof. clear - segs m m' A bs.
intros (H0 & H1 & HB) AG. split; [gw_exact H0|]. split; [gw_exact H1|]. intros i Hi.
unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. gw_exact Hi.
Qed.

#[using="Type"] Lemma rwr_at_agree m m' A n : wr_at segs m A n -> agree_on m m' A n -> wr_at segs m' A n.
Proof. clear - segs m m' A n.
intros (H0 & H1 & HW) AG. split; [gw_exact H0|]. split; [gw_exact H1|]. intros i Hi.
unfold wview. rewrite (AG (A + i)) by lia. apply HW. gw_exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree m m' A cs : rw_cells segs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof. clear - segs m m' A cs.
intros [[Hwf HB] HW] AG. split; [split; [gw_exact Hwf|]|].
- eapply rbytes_at_agree; [gw_exact HB|]. rewrite cells_bytes_length by assumption. gw_exact AG.
- eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree m m' A ws : u64arr segs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof. clear - segs m m' A ws.
intros [HB HW] AG. split.
- eapply rbytes_at_agree; [gw_exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. gw_exact AG.
- eapply rwr_at_agree; [gw_exact HW|]. gw_exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree m m' A bs : u8arr segs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. clear - segs m m' A bs. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

#[using="Type"] Lemma rmrep_agree : forall st m m',
rmrep st m ->
agree_on m m' (RATP + 131960) 4 -> agree_on m m' (RATP + 131728) 0x490 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' (RATP + 131696) 8 ->
(forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
(forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
(forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
rmrep st m'.
Proof. clear - RATP RGOT_SSP. gw_expose_fam RATP; gw_expose_fam RGOT_SSP.
intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
split; [gw_exact WF|]. split; [|split; [|split; [|split]]].
- destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
gw_expose_fam RATP.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [gw_exact C1|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [gw_exact C2|]. rewrite L1. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [gw_exact C3|]. rewrite L2. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [gw_exact C4|]. rewrite L3. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [gw_exact C5|]. rewrite L4. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact C6|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5). (gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]].
+ eapply rrw_cells_agree; [gw_exact G1|]. eapply agree_on_sub; [gw_exact AGL| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact G2|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact G3|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact G4|]. eapply agree_on_sub; [gw_exact AGS1| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact G5|]. eapply agree_on_sub; [gw_exact AGS2| lia| cbn; lia].
- intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
split; [|split].
+ eapply rrw_cells_agree; [gw_exact A1|]. eapply agree_on_sub; [gw_exact AG| lia| cbn; lia].
+ intros k Hk. eapply rrw_cells_agree; [apply A2; gw_exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [gw_exact AG| lia| lia].
+ eapply rrw_cells_agree; [gw_exact A3|]. eapply agree_on_sub; [gw_exact AG| lia| cbn; lia].
- intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
eapply rrw_cells_agree; [gw_exact R|]. cbn. exact (AGG b gh Hb).
- intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply rbytes_at_agree; [gw_exact Bt|]. cbn. eapply agree_on_sub; [gw_exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. clear - st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. clear - st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. rewrite rnr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. clear - r0 q st m m' x len k rid L st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof. clear - q r st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; try gw_hide rid; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite rnr_lookup_new in H. inversion H. auto.
- right. rewrite rnr_lookup_old in H by gw_exact NE. auto.
Qed.
#[using="r0"] Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. clear - r0 q st m m' x len k rid L st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
#[using="r0"] Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof. clear - r0 off st m m' x len k rid L st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
#[using="Type"] Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof. clear - q st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="RC__ st m' rid L ZF"] Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof. clear - RC__ st m' rid L ZF m x len k r0 st' MR PT FRr FRs X0 XA LEN XC RF AG. first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; try gw_hide r0; try gw_hide k; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m | gw_hide m | idtac]. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

#[using="RC__ rid RF"] Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof. clear - RC__ rid RF q r st m m' x len k L r0 st' MR PT FRr FRs X0 XA LEN XC AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; try gw_hide st.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="segs RATP RGOT_SSP m m' rid L r0 MR PT X0 XA LEN XC RF ZF"] Lemma rnr_regions_wf : rregions_wf st'.
Proof. clear - segs RATP RGOT_SSP m m' rid L r0 MR PT X0 XA LEN XC RF ZF ref_reserved st x len k st' FRr FRs AG. first [clear AG | gw_hide AG | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; try gw_hide x; first [clear st | gw_hide st | idtac].
pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RFimg : ranges_free ref_reserved x L = true).
{ apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. gw_exact HI. }
split; [gw_exact RS|]. split; [|split; [|split]].
- intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+ unfold r0. cbn. fold L. repeat split; try lia. gw_exact RFimg.
+ exact (WR q r H).
- intros q1 r1 q2 r2 H1 H2 NE.
destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
+ congruence.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
+ cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
+ exact (DJ q1 r1 q2 r2 H1' H2' NE).
- intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists r. rewrite rnr_lookup_old by gw_exact Pa. auto.
- intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists r. rewrite rnr_lookup_old by gw_exact Pb. auto.
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF"] Lemma rmrep_new_region : rmrep st' m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_4 ROM_reservedZ LAY_ref_reserved m rid L r0 MR PT FRs X0 XA LEN XC RF AG ZF RATP RGOT_SSP ref_reserved st m' x len k st' FRr. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. first [clear FRr | gw_hide FRr | idtac]; try gw_hide st'; first [clear k | gw_hide k | idtac]; try gw_hide len; try gw_hide x; try gw_hide m'; try gw_hide st.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
{ intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. gw_exact HI. }
rewrite LAY_ref_reserved in RI.
pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
pose proof (round_up_pg_ge len) as LG. fold L in LG. unfold alloc_ceiling in XC.

assert (MR1 : rmrep st m').
{ eapply rmrep_agree; [gw_exact MR| | | | | | |].
- intros a Ha. apply AG; gw_expose_fam RATP; lia.
- intros a Ha. apply AG; gw_expose_fam RATP; lia.
- intros a Ha. apply AG; gw_expose_fam RGOT_SSP; lia.
- intros a Ha. apply AG; gw_expose_fam RATP; lia.
- intros a ar Ha a0 Ha0.
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
unfold alloc_ceiling in RBC. apply AG; lia.
- intros b gh Hb a0 Ha0.
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). unfold alloc_ceiling in RBC. apply AG; lia.
- intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). unfold alloc_ceiling in BC.
pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; gw_exact Hq).
split; [gw_exact rnr_regions_wf|]. split; [|split; [gw_exact GL1|split; [|split]]].
- eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). gw_exact CX1.
- intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [gw_exact Ha|]. exact (AR1 a ar Ha).
- intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [gw_exact Hb|]. exact (GR1 b gh Hb).
- intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
+
cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
split.
* split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
* intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
+ eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

#[using="Type"] Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. clear - st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros H. gw_exact H. Qed.

#[using="Type"] Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. clear - P st m m' x len k rid L r0 st' MR PT FRr FRs X0 XA LEN XC RF AG ZF. first [clear ZF | gw_hide ZF | idtac]; first [clear AG | gw_hide AG | idtac]; first [clear RF | gw_hide RF | idtac]; first [clear XC | gw_hide XC | idtac]; first [clear LEN | gw_hide LEN | idtac]; first [clear XA | gw_hide XA | idtac]; first [clear X0 | gw_hide X0 | idtac]; first [clear FRs | gw_hide FRs | idtac]; first [clear FRr | gw_hide FRr | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r0 | gw_hide r0 | idtac]; first [clear L | gw_hide L | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear k | gw_hide k | idtac]; first [clear len | gw_hide len | idtac]; first [clear x | gw_hide x | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros H. gw_exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
((RATP + 131960) <= a < (RATP + 131964) \/ (RATP + 131728) <= a < (RATP + 132896) \/ RGOT_SSP <= a < (RGOT_SSP + 8) \/ (RATP + 131696) <= a < (RATP + 131704)
\/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).

#[using="Type"] Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof. clear - st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. reflexivity. Qed.
#[using="Type"] Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof. clear - q rq st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r | gw_hide r | idtac]; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. clear - q st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. clear - q st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; first [clear st' | gw_hide st' | idtac]; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. clear - q st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide st'; first [clear r | gw_hide r | idtac]; first [clear rid | gw_hide rid | idtac]; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac]. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved m r MR Hr PT AG"] Lemma rmrep_drop_region : rmrep st' m'.
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO LAY_lo_RATP LAY_hi_RATP LAY_lo_RGOT_SSP LAY_hi_RGOT_SSP LAY_win_0 LAY_win_1 LAY_win_2 LAY_win_3 LAY_win_4 ROM_reservedZ LAY_ref_reserved m r MR Hr PT AG RATP RGOT_SSP st m' rid st'. gw_expose_fam RATP; gw_expose_fam RGOT_SSP. try gw_hide st'; try gw_hide rid; try gw_hide m'; try gw_hide st.
pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; gw_exact Hq).
destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). unfold alloc_ceiling in BC.
assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
split; [|split; [|split; [|split; [|split]]]].
-
split; [gw_exact RS|]. split; [|split; [|split]].
+ intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
+ intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
+ intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
exists ra. rewrite rdr_lookup_old by gw_exact Pa. auto.
+ intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
exists rb. rewrite rdr_lookup_old by gw_exact Pb. auto.
-
eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ RDATA_LO <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= RDATA_LO \/ RIMG_HI <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [gw_exact RFr| lia]]. }
assert (AGC : agree_on m m' (RATP + 131728) 0x490).
{ intros a Ha. gw_expose_fam RATP. apply AG; [lia| lia| right; left; gw_expose_fam RATP; lia]. }
gw_expose_fam RATP.
split; [|split; [|split; [|split; [|split]]]].
+ eapply rrw_cells_agree; [gw_exact C1|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [gw_exact C2|]. rewrite L1. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru64arr_agree; [gw_exact C3|]. rewrite L2. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [gw_exact C4|]. rewrite L3. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply ru8arr_agree; [gw_exact C5|]. rewrite L4. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
+ eapply rrw_cells_agree; [gw_exact C6|]. eapply agree_on_sub; [gw_exact AGC| lia| cbn; lia].
- destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ RDATA_LO <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= RDATA_LO \/ RIMG_HI <= r_base r)) \/ round_up_pg (r_len r) = 0).
{ destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; apply rreserved_disjoint2; [gw_exact RFr| lia]]. }
(gw_expose_fam RATP; gw_expose_fam RGOT_SSP; unfold rmrep_globals in *).
split; [|split; [|split; [|split]]].
+ eapply rrw_cells_agree; [gw_exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
+ eapply rrw_cells_agree; [gw_exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [gw_exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
+ eapply rrw_cells_agree; [gw_exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
+ eapply rrw_cells_agree; [gw_exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
- intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [gw_exact Ha|].
destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
pose proof (rarea_lr_lo st a ar ra WF Ha Hra). unfold alloc_ceiling in RBC.
assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
assert (AGA : agree_on m m' (conc st a) 4096).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [gw_exact Hra|]. lia. }
destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
+ eapply rrw_cells_agree; [gw_exact A1|]. eapply agree_on_sub; [gw_exact AGA| lia| cbn; lia].
+ intros k0 Hk0. eapply rrw_cells_agree; [apply A2; gw_exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [gw_exact AGA| lia| lia].
+ eapply rrw_cells_agree; [gw_exact A3|]. eapply agree_on_sub; [gw_exact AGA| lia| cbn; lia].
- intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
eapply (rgroup_rep_extP st st' _ PT Hconc); [gw_exact Hb|].
destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). unfold alloc_ceiling in RBC.
destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|gw_exact Hw8].
eapply rrw_cells_agree; [gw_exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
right; right; right; right. exists (fst b), rb. split; [gw_exact Hrb|]. lia.
- intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
eapply rshadow_rep_ext; [apply rdr_shadow; gw_exact NE|].
destruct (WR q rq H) as (Bq & _ & _ & BCq & _). unfold alloc_ceiling in BCq.
pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
{ intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [gw_exact H|]. lia. }
destruct (SH q rq H Hk) as [HWr HB]. split.
+ eapply rwr_at_agree; eauto.
+ intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|gw_exact Hv].
eapply rbytes_at_agree; [gw_exact Bt|]. cbn. eapply agree_on_sub; [gw_exact AGR| lia| lia].
Qed.

#[using="Type"] Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof. clear - st m m' rid r st' MR Hr PT AG. first [clear AG | gw_hide AG | idtac]; first [clear PT | gw_hide PT | idtac]; first [clear Hr | gw_hide Hr | idtac]; first [clear MR | gw_hide MR | idtac]; try gw_hide st'; first [clear r | gw_hide r | idtac]; try gw_hide rid; first [clear m' | gw_hide m' | idtac]; first [clear m | gw_hide m | idtac]; first [clear st | gw_hide st | idtac].
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

#[using="Type"] Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
rmrep st m -> (s_groups st) !! b = None ->
(s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
rw_cells segs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
rmrep (put_group b (Some g) ai st) m.
Proof. clear - segs.
intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
pose proof WF as (RS & WR & DJ & WA & WG).
split; [|split; [gw_exact CX|split; [gw_exact GL|split; [gw_exact AR|split; [|gw_exact SH]]]]].
- split; [gw_exact RS|]. split; [gw_exact WR|]. split; [gw_exact DJ|]. split; [gw_exact WA|].
intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
+ rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
- intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
destruct (decide (b' = b)) as [->|NE].
+ rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [gw_exact R| gw_exact Hw8].
+ rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

#[using="RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved"] Lemma rmrep_set_mmap_counter : forall st m v,
rmrep st m -> 0 <= v < 2^32 ->
rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa ((RATP + 131980))) (le4 (wz v))).
Proof. clear - RIMG_HI RDATA_LO gw_RTEXT_LO gw_RDATA2_LO RNG_RATP LAY_lo_RATP LAY_hi_RATP LAY_hi_RGOT_SSP LAY_win_1 LAY_win_2 LAY_ref_reserved RATP segs. gw_expose_fam RATP.
intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
pose proof (length_le4 (wz v)) as L4.
pose proof (munch_write [((RATP + 131980), (RATP + 131984))] m m ((RATP + 131980)) (le4 (wz v)) (munch_refl _ m)
ltac:(gw_expose_fam RATP; lia) ltac:(rewrite L4; gw_expose_fam RATP; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
pose proof (wmono_write segs m m (wa ((RATP + 131980))) (le4 (wz v)) (wmono_refl segs m)) as WM.
eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
- intros lo hi [E|[]]; inversion E; subst. gw_expose_fam RATP. lia.
- left.
pose proof (rw_cells_write segs m (RATP + 131968) (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
replace ((RATP + 131968) + Z.of_nat 12) with ((RATP + 131980)) in W by first [reflexivity | (cbn; lia)].
unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. gw_exact W.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
- right. split; [| intros lo hi [E|[]]; inversion E; subst; gw_expose_fam RATP; lia].
unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End RC__1.

End G.
End Mqa.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQLG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQLG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q91D.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q91D.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QVbl.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCa8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCa8.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDXD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDXD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkTt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkTt.

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

Hypothesis land_ones_l : gw_hyp ltac:(let T := gw_callee_type0 (Q91D.land_ones_l segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524; 700; 720; 752; 768; 1412; 1424; 1436]%Z in exact T).

Hypothesis mulhu_shl32 : gw_hyp ltac:(let T := gw_callee_type0 (QQLG.mulhu_shl32 segs (base + -4832)%Z) 3%nat in let T := gw_fold_pcs T base (-4832)%Z [0; 128; 524]%Z in exact T).

Definition ltb1_eqb0 := @QDXD.ltb1_eqb0 segs base CODE BASE4 BASER mulhu_shl32.
Definition divtf3_core12 := @QDXD.divtf3_core12 segs base CODE BASE4 BASER mulhu_shl32.

Definition divtf3_post := Eval cbv beta delta [QkTt.divtf3_post] in (QkTt.divtf3_post segs).
Definition div_round_DRr := @QkTt.div_round_DRr segs base CODE BASE4 BASER mulhu_shl32.
Definition subw_amt := @QkTt.subw_amt segs base CODE BASE4 BASER mulhu_shl32.
Definition if_ltb_t := @QkTt.if_ltb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_ltb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_ltb_f := @QkTt.if_ltb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_ltb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_leb_t := @QkTt.if_leb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_leb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_leb_f := @QkTt.if_leb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_leb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_eqb_t := @QkTt.if_eqb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_eqb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_eqb_f := @QkTt.if_eqb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_eqb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nltb_t := @QkTt.if_nltb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nltb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nltb_f := @QkTt.if_nltb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nltb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nleb_t := @QkTt.if_nleb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nleb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_nleb_f := @QkTt.if_nleb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_nleb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_neqb_t := @QkTt.if_neqb_t segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_neqb_t {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition if_neqb_f := @QkTt.if_neqb_f segs base CODE BASE4 BASER mulhu_shl32.
Arguments if_neqb_f {T}%_type_scope x%_Z_scope y%_Z_scope A B _.
Definition Lzero := @QkTt.Lzero segs base CODE BASE4 BASER mulhu_shl32.
Definition Linf := @QkTt.Linf segs base CODE BASE4 BASER mulhu_shl32.
Definition Lround := @QkTt.Lround segs base CODE BASE4 BASER mulhu_shl32.
Ltac decide_ifs ::=
repeat (match goal with
| |- context [if (?x <? ?y) then ?A else ?B] => first [rewrite (if_ltb_t x y A B) by lia | rewrite (if_ltb_f x y A B) by lia]
| |- context [if negb (?x <? ?y) then ?A else ?B] => first [rewrite (if_nltb_t x y A B) by lia | rewrite (if_nltb_f x y A B) by lia]
| |- context [if (?x <=? ?y) then ?A else ?B] => first [rewrite (if_leb_t x y A B) by lia | rewrite (if_leb_f x y A B) by lia]
| |- context [if negb (?x <=? ?y) then ?A else ?B] => first [rewrite (if_nleb_t x y A B) by lia | rewrite (if_nleb_f x y A B) by lia]
| |- context [if (?x =? ?y) then ?A else ?B] => first [rewrite (if_eqb_t x y A B) by lia | rewrite (if_eqb_f x y A B) by lia]
| |- context [if negb (?x =? ?y) then ?A else ?B] => first [rewrite (if_neqb_t x y A B) by lia | rewrite (if_neqb_f x y A B) by lia]
end).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= g_step_fast.
Local Ltac zsimp ::= zsimp_fast.

Section Walk.
Variables (sp sgw w6 : word).
Notation spw := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation sgn := (bv_unsigned sgw).
Notation bLo := (bv_unsigned w6).

Ltac hyp :=
match goal with
| H : mem_inv _ ?m |- mem_inv _ ?m => exact H
| H : munch ?W ?m ?m' |- munch ?W ?m ?m' => exact H
| H : wmono _ ?m ?m' |- wmono _ ?m ?m' => exact H
| H : stk _ ?m ?lo ?hi |- stk _ ?m ?lo ?hi => exact H
| H : rw_cells _ ?m ?A _ |- rw_cells _ ?m ?A _ => exact H
| H : (?a <= ?b)%Z |- (?a <= ?b)%Z => exact H
| H : (?a <= ?x < ?b)%Z |- (?a <= ?x < ?b)%Z => exact H
| |- (_ <= _ <= _)%Z => lia
| |- (0 <= _ < _)%Z => first [zrange2 | lia]
end.
Ltac join L := eapply L; try hyp.

Ltac flag_join n G body K :=
set (G := body);
let w := getreg n in
lazymatch w with Z_to_bv 64 ?e =>
replace (Z_to_bv 64 e) with (Z_to_bv 64 G)
by (subst G; first [ rewrite (proj2 (Z.eqb_eq _ _) K) | rewrite (proj2 (Z.eqb_neq _ _) K) ]; first [ reflexivity | f_equal; zeq ])
end;
let RG := fresh "R" G in assert (RG : 0 <= G < 18446744073709551616) by (subst G; apply zr_b2z).

#[using="CODE BASE4 BASER land_ones_l mulhu_shl32"] Lemma L6r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wE q1Hi q1Lo resHi resLo aDHi aDLo bHi : Z)
y1 y5 y8 y9 y10 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q1Hi < 2^64)%Z -> (0 <= q1Lo < 2^64)%Z -> (0 <= resHi < 2^64)%Z -> (0 <= resLo < 2^64)%Z ->
(0 <= aDHi < 2^64)%Z -> (0 <= aDLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
(-122484 <= wE <= 32766)%Z ->
R = DC6 sgn wE q1Hi q1Lo resHi resLo aDHi aDLo bHi bLo ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp y5 (Z_to_bv 64 resLo) (Z_to_bv 64 resHi) y8 y9 y10 sgw w6 (Z_to_bv 64 bHi) (Z_to_bv 64 aDLo)
(Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aDHi)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q1Hi) (Z_to_bv 64 wE) (Z_to_bv 64 q1Lo) y31)
F (Z_to_bv 64 (base + 0x494)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 RwE HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K; sgn_cond K.
-
do 2 zstep. if_cases K2; zify_cond K2; signed_lits_in K2.
+ join Lzero. rewrite HR. apply DC6_tiny. lia.
+ do 6 zstep. rewrite !subw_amt by lia. unland. rewrite !landM32_id by lia.
zstep. if_cases K3; zify_cond K3; sgn_cond K3.
*
do 5 zstep. unland.
model_reg 10 absLo (Z.lor (Z.shiftr q1Lo (Z.land (1 - wE) 63))
(Z.land (Z.shiftl (Z.land (Z.shiftl q1Hi 1) 18446744073709551615) (Z.land (Z.lxor (1 - wE) 18446744073709551615) 63)) 18446744073709551615)).
rng absLo.
zstep. unland. model_reg 15 absHi0 (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absHi0.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (srai63_mask (1 - wE + -64)) by lia. decide_ifs. rewrite land_ones_l by zrange2.
zstep. if_cases K4; zify_cond K4; sgn_cond K4.
--
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
--
do 2 zstep. unland. model_reg 17 aSHi (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615). rng aSHi.
zstep. change (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615) with aSHi.
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * absHi0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (shr63_nonneg (wE + 48)), ?Z.land_0_l by lia.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (0 <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (0 - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
*
do 2 zstep. unland. model_reg 10 absLo (Z.shiftr q1Hi (Z.land (1 - wE) 63)). rng absLo.
zstep. unland.
zstep. rewrite !signed_of_Z by lia. do 3 zstep. rewrite !landM32_id by lia.
zstep. rewrite (shr63_nonneg (1 - wE + -64)), ?Z.land_0_l by lia.
zstep. if_cases K4; zify_cond K4; sgn_cond K4; [ | exfalso; lia ].
do 5 zstep. unland. model_reg 17 aSHi (Z.lor (Z.land (Z.shiftl aDHi (Z.land (wE + 112) 63)) 18446744073709551615)
(Z.shiftr (Z.shiftr aDLo 1) (Z.land (Z.lxor (wE + 112) 18446744073709551615) 63))). rng aSHi.
zstep. model_reg 14 aSLo0 (Z.land (Z.shiftl aDLo (Z.land (wE + 112) 63)) 18446744073709551615).
zstep.
zstep. model_reg 5 pb1 (Z.land (bLo * 0) 18446744073709551615).
zstep. model_reg 6 pb2 (Z.shiftr (bLo * absLo) 64). mulhu_rng pb2.
zstep. model_reg 7 pb3 (Z.land (bHi * absLo) 18446744073709551615).
zstep. rewrite !signed_of_Z by lia. rewrite (srai63_mask (wE + 48)) by lia. decide_ifs. rewrite land_ones_l by zrange2. model_reg 14 aSLo aSLo0.
zstep. model_reg 16 qbLo (Z.land (bLo * absLo) 18446744073709551615).
zstep. model_reg 6 qh1 (Z.land (pb2 + pb3) 18446744073709551615).
zstep. model_reg 7 qb2Lo (Z.land (Z.shiftl qbLo 1) 18446744073709551615).
zstep. model_reg 5 qbHi (Z.land (qh1 + pb1) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (aSLo <? qb2Lo)).
zstep. model_reg 17 d1 (Z.land (aSHi - bor) 18446744073709551615).
do 3 zstep. model_reg 16 qb2Hi (Z.lor (Z.land (Z.shiftl qbHi 1) 18446744073709551615) (Z.shiftr qbLo 63)).
zstep. model_reg 16 r2Hi (Z.land (d1 - qb2Hi) 18446744073709551615).
zstep. model_reg 14 r2Lo (Z.land (aSLo - qb2Lo) 18446744073709551615).
zstep. model_reg 17 odd (Z.land absLo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ do 2 zstep | zstep ].
all: flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1.
all: join Lround.
all: rewrite HR, DC6_denorm by lia; cbv beta delta [DC6d]; sf_vocab; fold_dc6;
rewrite div_round_DRr; sf_vocab; fold_model_lets2; first [ reflexivity | decide_ifs; reflexivity ].
-
assert (K' : 0 < wE) by (rewrite land_W64 in K0, K1; Z.div_mod_to_equations; lia). clear K0 K1.
do 2 zstep. unland.
model_reg 14 fracHi (Z.land q1Hi 281474976710655).
do 4 zstep. unland. model_reg 15 absHi (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi). rng absHi.
zstep. model_reg 16 r2Hi (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)). rng r2Hi.
zstep. model_reg 14 r2Lo (Z.land (Z.shiftl resLo 1) 18446744073709551615).
zstep. model_reg 17 odd (Z.land q1Lo 1).
zstep. model_reg 14 r3Lo (Z.land (odd + r2Lo) 18446744073709551615).
zstep. model_reg 17 rc (Z.b2z (r3Lo <? odd)).
zstep. model_reg 16 r3Hi (Z.land (r2Hi + rc) 18446744073709551615).
zstep. if_cases K1; zify_cond K1; [ zstep | do 2 zstep ];
flag_join 17%Z gt1 (Z.b2z (if r3Hi =? bHi then bLo <? r3Lo else bHi <? r3Hi)) K1;
(join Lround;
rewrite HR, DC6_normal, div_round_DRr by lia; unland;
change (Z.land q1Hi 281474976710655) with fracHi;
change (Z.lor (Z.land (Z.shiftl wE 48) 18446744073709551615) fracHi) with absHi;
change (Z.lor (Z.land (Z.shiftl resHi 1) 18446744073709551615) (Z.shiftr resLo 63)) with r2Hi;
change (Z.land (Z.shiftl resLo 1) 18446744073709551615) with r2Lo;
fold_model_lets2; reflexivity).
Time Qed.

#[using="CODE BASE4 BASER land_ones_l mulhu_shl32"] Lemma L5r : forall ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (w4 : word) (expM1 q_hi q_lo aSigHiI bSigHiI aHi2 aLoTop a2Lo : Z)
y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= q_hi < 2^64)%Z -> (0 <= q_lo < 2^64)%Z -> (0 <= aSigHiI < 2^64)%Z -> (0 <= bSigHiI < 2^64)%Z ->
(0 <= aHi2 < 2^64)%Z -> (0 <= aLoTop < 2^64)%Z -> (0 <= a2Lo < 2^64)%Z ->
(-20000 <= expM1 <= 60000)%Z ->
R = divc_tail sgn expM1 q_hi q_lo (bv_unsigned w4) aSigHiI bSigHiI bLo aHi2 aLoTop a2Lo ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp (Z_to_bv 64 expM1) (Z_to_bv 64 aLoTop) (Z_to_bv 64 aHi2) y8 y9 w4 sgw w6
(Z_to_bv 64 bSigHiI) (Z_to_bv 64 a2Lo) (Z_to_bv 64 (Z.shiftr q_hi 49)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 aSigHiI)
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 q_hi) (Z_to_bv 64 (expM1 + 1)) (Z_to_bv 64 q_lo) y31)
F (Z_to_bv 64 (base + 0x358)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO R1 R2 R3 R4 R5 R6 R7 Rexp HR.
pose_word_ranges.
zstep. if_cases K; zify_cond K.
-
do 3 zstep. model_reg 28 q1Hi (Z.shiftr q_hi 1). rng q1Hi.
zstep. model_reg 5 aTop (Z.land (Z.shiftl (bv_unsigned w4) 48) 18446744073709551615).
zstep. model_reg 30 q1Lo (Z.lor (Z.shiftr q_lo 1) (Z.land (Z.shiftl q_hi 63) 18446744073709551615)). rng q1Lo.
zstep. model_reg 14 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 14 d1 (Z.land (aTop - pq1) 18446744073709551615).
zstep. model_reg 5 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 15 sh (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 14 d2 (Z.land (d1 - sh) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+ rewrite <- (Z_to_bv_bv_unsigned w4). join L6r. all: try lia.
rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
-
assert (Rbit : 0 <= Z.shiftr q_hi 48 <= 1).
{ rewrite !Z.shiftr_div_pow2 in * by lia. Z.div_mod_to_equations. lia. }
zstep. name_as bit112 (Z.shiftr q_hi 48).
zstep. zstep. rewrite (ltb1_eqb0 bit112) by lia. model_reg 31 sh (Z.b2z (bit112 =? 0)).
assert (Rsh' : 0 <= sh <= 1) by (cbv delta [sh]; destruct (bit112 =? 0); cbn; lia).
zstep. rewrite (land63_id sh) by lia.
zstep. zstep.
assert (Hamt : Z.land (Z.lxor sh 63) 63 = Z.lxor sh 63) by (cbv delta [sh]; destruct (bit112 =? 0); reflexivity).
rewrite Hamt.
zstep. unland. model_reg 28 q1Hi (Z.lor (Z.land (Z.shiftl q_hi sh) 18446744073709551615) (Z.shiftr (Z.shiftr q_lo 1) (Z.lxor sh 63))). rng q1Hi.
zstep. rewrite (land63_id sh) by lia. model_reg 30 q1Lo (Z.land (Z.shiftl q_lo sh) 18446744073709551615).
zstep. if_cases Kb; zify_cond Kb.
*
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
*
zstep.
zstep. model_reg 17 aDHi (Z.lor aHi2 aLoTop). rng aDHi.
zstep. model_reg 10 aTop (Z.land (Z.shiftl (bv_unsigned w4) 49) 18446744073709551615).
zstep. model_reg 15 pq2 (Z.land (q1Lo * bSigHiI) 18446744073709551615).
zstep. model_reg 6 pq3 (Z.shiftr (q1Lo * bLo) 64). mulhu_rng pq3.
zstep. model_reg 7 pq1 (Z.land (q1Hi * bLo) 18446744073709551615).
zstep. model_reg 15 sh2 (Z.land (pq3 + pq2) 18446744073709551615).
zstep. model_reg 6 qbLo (Z.land (q1Lo * bLo) 18446744073709551615).
zstep. model_reg 10 d1 (Z.land (aTop - sh2) 18446744073709551615).
zstep. model_reg 15 bor (Z.b2z (negb (qbLo =? 0))).
zstep. model_reg 6 resLo (Z.land (0 - qbLo) 18446744073709551615).
zstep. model_reg 10 d2 (Z.land (d1 - pq1) 18446744073709551615).
zstep. model_reg 7 resHi (Z.land (d2 - bor) 18446744073709551615).
do 4 zstep. zstep. if_cases Kov; zify_cond Kov; signed_lits_in Kov.
+  join Linf. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. reflexivity.
+ zstep. join L6r. all: try lia. rewrite HR, divc_tail_arms. sf_vocab. decide_ifs. fold_dc6. f_equal; lia.
Time Qed.

#[using="CODE BASE4 BASER land_ones_l mulhu_shl32"] Lemma divtf3_core : forall ra gp tp (w3 w4 w5 : word) (scale ea eb : Z) s0 s1 a3 a4 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 y1
y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
(F : bvmap 5 word) fc (m m1 : word -> option byte) j R,
mem_inv segs m1 ->
munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m1 -> wmono segs m m1 ->
stk segs m1 (bv_unsigned sp - 112) (bv_unsigned sp + -112) ->
rw_cells segs m1 (bv_unsigned sp + -112) (saved12 s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra j) ->
(4096 <= bv_unsigned sp)%Z ->
(0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
R = div_core sgn ea eb (bv_unsigned w3) (bv_unsigned w4) (bv_unsigned w5) bLo scale ->
evt segs (divtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc R m)
(MS (mkR y1 spw gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) y8 y9 w4 sgw w6 a3 a4 a5 (Z_to_bv 64 281474976710655) w3
y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 scale) t4 t5 t6)
F (Z_to_bv 64 (base + 0x88)) fc None m1 (seg_rom segs)).
Proof.
intros until R. intros MI MU WM ST FR SPLO Ra Rb Rsc HR.
pose_word_ranges.
eapply evt_cut. { eapply (divtf3_core12 w3 w4 w5 w6 ea eb scale); eauto. }
intros ms' P.
destruct P as (q_hi & q_lo & z1 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z31 & EQ & Rqh & Rql & ->).
rewrite EQ in HR.
eapply L5r; try eassumption; try exact HR.
all: try (cbv beta delta [E_aSigHiI E_bSigHiI E_aHi2 E_aLoTop E_a2Lo]; zrange).
cbv beta delta [E_expM1]. lia.
Qed.
End Walk.

End G.
