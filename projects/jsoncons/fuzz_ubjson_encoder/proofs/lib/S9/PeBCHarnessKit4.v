(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk SeqExec ShapeAlg HeapIface HeapIfaceA HeapIfaceAEx AxSymExec3 AsanPlanSoundSums L5Defs L5Kn L5KnA L5Core L5CoreKit L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFactsA PmSpecsA PeSpecsAb PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCSinkA PeCModel PeCModelA PeCFrameA PeBCHarnessStmts PeBCHarnessKit PeBCHarnessKit2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBHK4.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation parser_at := (PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA).

Lemma u64_of_zeros (M : word -> option byte) a n o : PM.zeros_at M a n -> a <= o -> o + 8 <= a + n -> 0 <= o -> o + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M o 0.
Proof.
  intros Z0 H1 H2 H3 H4. apply L5SAR.u64_of_zeros_at; [| lia| lia]. intros i Hi. replace (o + i) with (a + (o - a + i)) by lia. apply Z0. lia.
Qed.
Lemma u32_of_zeros (M : word -> option byte) a n o : PM.zeros_at M a n -> a <= o -> o + 4 <= a + n -> 0 <= o -> o + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M o 0.
Proof.
  intros Z0 H1 H2 H3 H4. unfold L5.u32_at. change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0 : byte) 4).
  apply APSX.rdn_overlay_all. rewrite L5.unsigned_lit by lia. cbn. lia.
  intros i Hi. rewrite L5.unsigned_lit by lia. replace (o + i) with (a + (o - a + i)) by lia. apply Z0. cbn in Hi. lia.
Qed.
Lemma defined_of_zeros (M : word -> option byte) a n : PM.zeros_at M a n -> L5.defined M a n.
Proof. intros Z0 i Hi. rewrite (Z0 i Hi). discriminate. Qed.

Section WithL.
Variables (L : asan_layout) (ar : asan_run) (P : PESKA.sink_policyA).

Lemma sink0A_intro (M : word -> option byte) o :
  L5.u64_at RSEGS M o 0 -> L5.u64_at RSEGS M (o + 8) 0 -> L5.u64_at RSEGS M (o + 16) 0 -> L5.defined M o 24 -> PMSPA.accA M o 24 ->
  PESKA.sink_atA RSEGS L ar P M o PESK.sink0.
Proof.
  intros A0 A1 A2 D AC. unfold PESKA.sink_atA. cbn [PESK.sk_b PESK.sk_z PESK.sk_c PESK.sink0]. rewrite Z.add_0_r.
  repeat match goal with |- _ /\ _ => split end; try assumption; try (left; reflexivity); try (intros; lia).
Qed.

Lemma enc0A_intro (M : word -> option byte) ov fb :
  L5.u64_at RSEGS M ov (pe_vt EE) -> L5.u64_at RSEGS M (ov + 8) (fb + 432) -> L5.u32_at RSEGS M (ov + 16) 1024 ->
  L5.u64_at RSEGS M (ov + 24) 0 -> L5.u64_at RSEGS M (ov + 32) 0 -> L5.u64_at RSEGS M (ov + 40) 0 -> L5.u32_at RSEGS M (ov + 48) 0 ->
  L5.defined M ov 56 -> PMSPA.accA M ov 56 ->
  PECA.enc_atA RSEGS EE L ar M ov fb PEC.enc0.
Proof.
  intros A0 A1 A2 A3 A4 A5 A6 D AC. unfold PECA.enc_atA, PESK.o_sink.
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth PEC.enc0 PEC.ecap length Z.of_nat Z.eqb pe_off_sink EE PeCLayoutB.EADDR_B].
  cbn [UbjRef.MAX_DEPTH Z.mul Z.add Pos.mul Pos.add]. rewrite ?Z.mul_0_r, ?Z.add_0_r.
  repeat match goal with |- _ /\ _ => split end; try assumption; try exact I; unfold UbjRef.MAX_DEPTH; intros; lia.
Qed.
End WithL.

Section K.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.

Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PEBHK2.hf F.
Variables (slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte).
Hypothesis S1 : ahl_ceil ar <= slo.
Hypothesis S2 : BIGSHADOW_HI <= slo.
Hypothesis FR : forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Hypothesis WP : PEBHK2.pfoot F slo shi Wp.
Let oav := PEBHK2.oav Wp.
Let BP := fun p c (Hin : In (p, c) LBx) => PEBHK2.blk_piece L ar C SCFG HI HIok LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF HFF S1 S2 FR WP.

Lemma blk_rng p c : In (p, c) LBx -> 0 <= p /\ p + c <= 2 ^ 64.
Proof. intros Hin. destruct (PEBHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ HH Hin) as (Q0 & _ & _ & _ & _ & Q47 & _). lia. Qed.

Lemma parser_keep_piece op ois st : incl (PM.parser_own st) LBx -> 0 <= op -> op + 384 <= 2 ^ 47 -> oav op 384 ->
  parser_at M1 op ois st -> parser_at M2 op ois st.
Proof.
  intros INC H0 H1 OA PA.
  assert (IQ : In (PM.sr_qc (PM.p_src st), PM.CHUNK) LBx) by (apply INC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (IV : In (PM.p_b st, 32 * 2 ^ PM.p_k st) LBx) by (apply INC; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  destruct (blk_rng _ _ IQ) as [Q1 Q2]. destruct (blk_rng _ _ IV) as [V1 V2].
  apply (PMFA.parser_at_agreeA RSEGS AD M1 M2 op ois st); [lia| lia| exact (PEBHK.agA_frame M1 M2 Wp op 384 FR H0 ltac:(lia) OA)| lia| lia| exact (BP _ _ IQ)| lia| lia| exact (BP _ _ IV)| | exact PA].
  intros c n p E1. apply BP. apply INC. unfold PM.parser_own, PM.vs_own. rewrite E1. right; right; left. reflexivity.
Qed.
Lemma hse0_piece : oav (F + 432) 24 -> oav (F + 496) 56 -> PEBCH.hse0 L ar P F M1 -> PEBCH.hse0 L ar P F M2.
Proof.
  intros O1 O2 (SK & EN). pose proof HFF as (F8 & F0 & F1 & FB). split.
  - apply (PECFA.sink_atA_agree RSEGS L ar M1 M2 P (F + 432) PESK.sink0); [lia| lia| exact (PEBHK.agA_frame M1 M2 Wp (F + 432) 24 FR ltac:(lia) ltac:(lia) O1)| cbn; lia| exact SK].
  - apply (PECFA.enc_atA_agree RSEGS EE L ar M1 M2 (F + 496) F PEC.enc0); [lia| lia| exact (PEBHK.agA_frame M1 M2 Wp (F + 496) 56 FR ltac:(lia) ltac:(lia) O2)| cbn; lia| exact EN].
Qed.
End Objs.

Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : PEBHK2.hf F.
Variables (LBc : list (Z * Z)) (FFc : list fframe) (spc scrc : Z) (Wc : list L5.range) (M1 M2 : word -> option byte) (f : fframe).
Hypothesis AH : L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2.
Hypothesis WF : PEBHK2.wfi F Wc.
Hypothesis Hf : In f FFc.
Hypothesis HfF : ff_addr f = F /\ ff_bytes (ff_class f) = 2048.
Let BC := fun p c (Hin : In (p, c) LBx) (Hc : In (p, c) LBc) => PEBHK2.blk_callee L ar C SCFG HI LY HIok LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH Hin HF HFF AH Hc WF.
Let ffc := PEBHK2.ffc L ar F HFF LBc FFc spc scrc Wc M1 M2 f AH WF Hf HfF.

Lemma blk_rngc p c : In (p, c) LBx -> 0 <= p /\ p + c <= 2 ^ 64.
Proof. intros Hin. destruct (PEBHK.blk_facts L ar C SCFG HI HIok _ _ _ _ _ _ _ _ _ HH Hin) as (Q0 & _ & _ & _ & _ & Q47 & _). lia. Qed.

Lemma parser_keep_callee op ois st : incl (PM.parser_own st) LBx -> incl (PM.parser_own st) LBc -> F + 32 <= op -> op + 384 <= F + 2040 ->
  PEBHK2.wapart Wc op 384 -> parser_at M1 op ois st -> parser_at M2 op ois st.
Proof.
  intros INC INCc H0 H1 OA PA. pose proof HFF as (F8 & F0 & F1 & FB).
  assert (IQ : In (PM.sr_qc (PM.p_src st), PM.CHUNK) LBx) by (apply INC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (IV : In (PM.p_b st, 32 * 2 ^ PM.p_k st) LBx) by (apply INC; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  assert (IQc : In (PM.sr_qc (PM.p_src st), PM.CHUNK) LBc) by (apply INCc; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (IVc : In (PM.p_b st, 32 * 2 ^ PM.p_k st) LBc) by (apply INCc; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  destruct (blk_rngc _ _ IQ) as [Q1 Q2]. destruct (blk_rngc _ _ IV) as [V1 V2].
  apply (PMFA.parser_at_agreeA RSEGS AD M1 M2 op ois st); [lia| lia| exact (ffc op 384 H0 H1 OA)| lia| lia| exact (BC _ _ IQ IQc)| lia| lia| exact (BC _ _ IV IVc)| | exact PA].
  intros c n p E1. apply BC; [apply INC| apply INCc]; unfold PM.parser_own, PM.vs_own; rewrite E1; right; right; left; reflexivity.
Qed.
Lemma hse0_callee : PEBHK2.wapart Wc (F + 432) 24 -> PEBHK2.wapart Wc (F + 496) 56 -> PEBCH.hse0 L ar P F M1 -> PEBCH.hse0 L ar P F M2.
Proof.
  intros O1 O2 (SK & EN). pose proof HFF as (F8 & F0 & F1 & FB). split.
  - apply (PECFA.sink_atA_agree RSEGS L ar M1 M2 P (F + 432) PESK.sink0); [lia| lia| exact (ffc (F + 432) 24 ltac:(lia) ltac:(lia) O1)| cbn; lia| exact SK].
  - apply (PECFA.enc_atA_agree RSEGS EE L ar M1 M2 (F + 496) F PEC.enc0); [lia| lia| exact (ffc (F + 496) 56 ltac:(lia) ltac:(lia) O2)| cbn; lia| exact EN].
Qed.
End ObjsC.
End K.
End PEBHK4.
