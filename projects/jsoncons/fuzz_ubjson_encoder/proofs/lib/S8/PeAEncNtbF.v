(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrame PeCFrameA PeEncKit PeACReset1 PeAEncNtbSpec PeAEncNtbFSpec PeAEncNtbFP PeFPSteps.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b0c08_b0c0c Ea0_code_b0c94_b0c98 Ea0_code_b0cc0_b0cc4 Ea0_code_b0d84_b0d88.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEAENTBF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).
Abbreviation SBL := 2147450880.

Definition CSW : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma wid (w : word) : w = Z_to_bv 64 (bv_unsigned w). Proof. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma wrng (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> L5.writable RSEGS M a n -> L5.writable RSEGS M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Definition wrunAF (pc0 lra FR CUR KB : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp rr o : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 rr ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487168 + FR <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - FR) FR -> 4096 <= rr <= 140737488355320 -> rr mod 8 = 0 ->
    (2147446784 + 17592186048512 <= rr \/ rr + 8 <= 2147446784) -> L5KA.zeros_at M (rr / 8 + SBL) 1 -> L5.u64_at RSEGS M rr o ->
    (rr + 8 <= sp - FR \/ (sp - FR) + FR <= rr) -> 4096 <= o <= 140737488355304 -> o mod 8 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - FR <= i < sp - FR + FR) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R pc0 M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSW -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 lra /\ getr R' (reg 2) = Z_to_bv 64 (sp - FR) /\ getr R' (reg 8) = Z_to_bv 64 rr /\ getr R' (reg 9) = Z_to_bv 64 KB
      /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (sp - 41) /\ getr R' (reg 18) = Z_to_bv 64 (sp + CUR) /\ getr R' (reg 19) = Z_to_bv 64 (rr / 8 + SBL)
      /\ L5.u64_at RSEGS M' (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M' (sp - 32) (bv_unsigned (getr R (reg 18)))
      /\ L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8)))
      /\ L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 1))).

Definition wrunM (lra FR CUR KB : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp rr o cnt cur nb a0v a1v a2v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= o < 2 ^ 64 -> 0 <= cnt < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= nb < 2 ^ 64 ->
    0 <= a0v < 2 ^ 64 -> 0 <= a1v < 2 ^ 64 -> 0 <= a2v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - FR) -> getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 9) = Z_to_bv 64 cnt -> getr R (reg 10) = Z_to_bv 64 a0v ->
    getr R (reg 11) = Z_to_bv 64 a1v -> getr R (reg 12) = Z_to_bv 64 a2v -> getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 (rr / 8 + SBL) ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487168 + FR <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - FR) FR -> 4096 <= rr <= 140737488355320 -> rr mod 8 = 0 ->
    (2147446784 + 17592186048512 <= rr \/ rr + 8 <= 2147446784) -> L5KA.zeros_at M (rr / 8 + SBL) 1 -> L5.u64_at RSEGS M rr o ->
    (rr + 8 <= sp - FR \/ (sp - FR) + FR <= rr) -> 4096 <= o <= 140737488355304 -> o mod 8 = 0 ->
    2 <= cnt <= KB -> 4096 <= cur <= 140737488355326 -> 2 - KB - CUR <= sp - cur <= - CUR -> L5.u8_at RSEGS M (cur + 1) nb -> 0 <= nb <= 255 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 41 <= i < sp - 41 + 1) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R lra M) (mst fx' R' 0xaf02c M')
      /\ (forall j, In j CSW -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 lra /\ getr R' (reg 2) = Z_to_bv 64 (sp - FR) /\ getr R' (reg 8) = Z_to_bv 64 rr /\ getr R' (reg 9) = Z_to_bv 64 (cnt - 1)
      /\ getr R' (reg 10) = Z_to_bv 64 o /\ getr R' (reg 11) = Z_to_bv 64 (sp - 41) /\ getr R' (reg 18) = Z_to_bv 64 (cur + 1) /\ getr R' (reg 19) = Z_to_bv 64 (rr / 8 + SBL).

Definition wrunL (lra FR : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp rr cur r s0v s1v s2v s3v a0v a1v a2v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= rr < 2 ^ 64 -> 0 <= cur < 2 ^ 64 -> 0 <= r < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 -> 0 <= s2v < 2 ^ 64 -> 0 <= s3v < 2 ^ 64 ->
    0 <= a0v < 2 ^ 64 -> 0 <= a1v < 2 ^ 64 -> 0 <= a2v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - FR) -> getr R (reg 8) = Z_to_bv 64 rr -> getr R (reg 9) = Z_to_bv 64 1 -> getr R (reg 10) = Z_to_bv 64 a0v ->
    getr R (reg 11) = Z_to_bv 64 a1v -> getr R (reg 12) = Z_to_bv 64 a2v -> getr R (reg 18) = Z_to_bv 64 cur -> getr R (reg 19) = Z_to_bv 64 (rr / 8 + SBL) ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 SBL -> L5.u32_at RSEGS M 1317376 1 -> 140735332487168 + FR <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - FR) FR ->
    L5.u64_at RSEGS M (sp - 8) r -> L5.u64_at RSEGS M (sp - 16) s0v -> L5.u64_at RSEGS M (sp - 24) s1v -> L5.u64_at RSEGS M (sp - 32) s2v -> L5.u64_at RSEGS M (sp - 40) s3v ->
    L5.ra_ok r ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (mst fx R lra M) (mst fx' R' r M')
      /\ (forall j, In j CSW -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 s0v /\ getr R' (reg 9) = Z_to_bv 64 s1v /\ getr R' (reg 18) = Z_to_bv 64 s2v /\ getr R' (reg 19) = Z_to_bv 64 s3v.

Ltac wrun_tacM M_conc :=
  intros fx R M sp rr o cnt cur nb a0v a1v a2v H1 H2 H3 H4 H5 H6 H7 H8 H9 G2 G8 G9 G10 G11 G12 G18 G19 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18;
  let P := fresh "P" in
  pose proof (M_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | 35%nat => cnt | 36%nat => cur | 40%nat => nb | 41%nat => o
      | 55%nat => a0v | 56%nat => a1v | 57%nat => a2v | _ => 0 end)) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEAENTBFP.aligned; assumption | lia]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T9 & T10 & T11 & T18 & C41);
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [exact MS1|];
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T1|]; split; [rewrite (KS1 2%nat) by inl; exact G2|]; split; [rewrite (KS1 8%nat) by inl; exact G8|];
  split; [first [exact T9 | rewrite T9; f_equal; lia]|]; split; [exact T10|]; split; [exact T11|]; split; [exact T18|];
  rewrite (KS1 19%nat) by inl; exact G19.

Ltac wrun_tacL L_conc RETPC W_S F_S D_S :=
  intros fx R M sp rr cur r s0v s1v s2v s3v a0v a1v a2v H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 G2 G8 G9 G10 G11 G12 G18 G19 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 RA;
  let P := fresh "P" in
  pose proof (L_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | 36%nat => cur | 44%nat => r | 45%nat => s0v | 46%nat => s1v | 47%nat => s2v | 48%nat => s3v
      | 55%nat => a0v | 56%nat => a1v | 57%nat => a2v | _ => 0 end)) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEAENTBFP.aligned; assumption | lia]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T18 & T19);
  let Hr1 := fresh "Hr1" in let Hr2 := fresh "Hr2" in pose proof RA as (Hr1 & Hr2);
  let MSR := fresh "MSR" in
  pose proof (PMK.ret_to RSEGS fx1 R1 M1 RETPC W_S r F_S eq_refl D_S T1 ltac:(lia) Hr2) as MSR;
  exists fx1, R1, M1; split; [exact MG1|]; split; [exact FRZ1|]; split; [eapply msteps_trans; [exact MS1| exact MSR]|];
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T2|]; split; [exact T8|]; split; [exact T9|]; split; [exact T18| exact T19].

Ltac wrun_tacAF A1_conc A2_conc FMVPC W_F F_F D_F :=
  intros fx R M sp rr o H1 H2 H3 G2 G10 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13;
  let P := fresh "P" in
  pose proof (A1_conc fx R M (fun j => match j with 2%nat => sp | 43%nat => rr | _ => 0 end)) as P; cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEAENTBFP.aligned; assumption | lia]);
  let KS1 := fresh "KS1" in
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T2 & T8 & T10 & S40 & S32 & S24 & S16 & S8);

  let v := fresh "v" in let Hv := fresh "Hv" in let MSF := fresh "MSF" in
  destruct (PEFX.fmv_xf_run RSEGS fx1 R1 M1 FMVPC W_F _ _ _ F_F eq_refl D_F ltac:(first [left; reflexivity | right; reflexivity]) eq_refl ltac:(clear; lia) ltac:(clear; lia)) as (v & Hv & MSF);
  rewrite L5K.rl11 in MSF;

  let AG := fresh "AG" in
  lazymatch type of FRZ1 with forall i, _ -> ~ (?lo <= i < ?hi) -> _ =>
    assert (AG : forall a n, (a + n <= lo \/ hi <= a) -> 0 <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M1 a n)
      by (intros a n Ha Ha0 Ha1 i Hi; apply FRZ1; [clear - Hi Ha0 Ha1; lia| clear - Hi Ha; lia]) end;
  let P2 := fresh "P2" in
  pose proof (A2_conc fx1 (regupd R1 (reg 11) (Z_to_bv 64 v)) M1 (fun j => match j with 2%nat => sp | 43%nat => rr | 41%nat => o | 56%nat => v | 57%nat => bv_unsigned (getr R1 (reg 12)) | _ => 0 end)) as P2;
  cbn beta iota in P2;
  L5SAR.feed P2 ltac:(first [ assumption | unfold PEAENTBFP.aligned; assumption | apply wrng
    | rewrite PEFX.regupd_same_idx by (clear; lia); reflexivity
    | rewrite PEFX.regupd_other_idx by (clear; lia); first [assumption | apply wid]
    | intros i Hi; rewrite FRZ1; [apply K0; exact Hi | clear - Hi; lia | clear - Hi K3; lia]
    | apply (L5C.u64_at_agree RSEGS M M1); [apply AG; [clear - K3 K6 K11; lia| clear - K6; lia| clear - K6; lia] | clear - K6; lia | clear - K6; lia | assumption]
    | apply (PMF.u32_at_agree RSEGS M M1); [apply AG; clear - K3; lia | clear; lia | clear; lia | assumption]
    | apply (writable_grows M M1); [exact MG1 | assumption]
    | apply (L5KA.zeros_at_agree1 M M1); [intros i Hi; apply FRZ1; [clear - Hi K6; lia | clear - Hi K6 K3; lia] | assumption]
    | lia ]);
  let KS2 := fresh "KS2" in
  destruct P2 as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & T1 & T9 & T10' & T11 & T18 & T19);
  exists fx2, R2, M2; split; [exact (mem_grows_trans M M1 M2 MG1 MG2)|];
  split; [intros i Hi Hn; rewrite (FRZ2 i Hi) by (clear - Hn; lia); apply FRZ1; [exact Hi| exact Hn]|];
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSF| exact MS2]]|];
  split; [intros j Hj; rewrite (KS2 j) by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl);
          rewrite PEFX.regupd_other_idx by (revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; lia);
          apply KS1; revert Hj; clear; intros Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T1|]; split; [rewrite (KS2 2%nat) by inl; rewrite PEFX.regupd_other_idx by (clear; lia); exact T2|];
  split; [rewrite (KS2 8%nat) by inl; rewrite PEFX.regupd_other_idx by (clear; lia); exact T8|]; split; [exact T9|]; split; [exact T10'|]; split; [exact T11|];
  split; [first [exact T18 | rewrite T18; f_equal; lia]|]; split; [exact T19|];
  assert (AGS : forall a w, sp - 40 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a w -> L5.u64_at RSEGS M2 a w)
    by (intros a w Ha1 Ha2 U; apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; [clear - Hi Ha1 Ha2 H1 K3; lia| clear - Hi Ha1 Ha2; lia]| clear - Ha1 K3; lia| clear - Ha2 H1; lia| exact U]);
  split; [apply AGS; [clear; lia| clear; lia| exact S40]|]; split; [apply AGS; [clear; lia| clear; lia| exact S32]|]; split; [apply AGS; [clear; lia| clear; lia| exact S24]|];
  split; [apply AGS; [clear; lia| clear; lia| exact S16]| apply AGS; [clear; lia| clear; lia| exact S8]].
Lemma f32_runA : wrunAF 0xb0c38 0xb0cc0 48 (-48) 4. Proof. unfold wrunAF. wrun_tacAF PEAENTBFP.antbf32A1_conc PEAENTBFP.antbf32A2_conc 0xb0c58 W_b0c08 F_b0c08 D_b0c08. Qed.
Lemma f32_runM : wrunM 0xb0cc0 48 (-48) 4. Proof. unfold wrunM. wrun_tacM PEAENTBFP.antbf32M_conc. Qed.
Lemma f32_runL : wrunL 0xb0cc0 48. Proof. unfold wrunL. wrun_tacL PEAENTBFP.antbf32L_conc 0xb0ce4 W_b0c94 F_b0c94 D_b0c94. Qed.
Lemma f64_runA : wrunAF 0xb0cf0 0xb0db0 64 (-56) 8. Proof. unfold wrunAF. wrun_tacAF PEAENTBFP.antbf64A1_conc PEAENTBFP.antbf64A2_conc 0xb0d10 W_b0cc0 F_b0cc0 D_b0cc0. Qed.
Lemma f64_runM : wrunM 0xb0db0 64 (-56) 8. Proof. unfold wrunM. wrun_tacM PEAENTBFP.antbf64M_conc. Qed.
Lemma f64_runL : wrunL 0xb0db0 64. Proof. unfold wrunL. wrun_tacL PEAENTBFP.antbf64L_conc 0xb0dd4 W_b0d84 F_b0d84 D_b0d84. Qed.

Lemma u8_at_of_defined (M : word -> option byte) a : 0 <= a < 2 ^ 64 -> M (Z_to_bv 64 a) <> None -> exists b, 0 <= b <= 255 /\ L5.u8_at RSEGS M a b.
Proof.
  intros Ha D. destruct (M (Z_to_bv 64 a)) as [b|] eqn:E; [|exfalso; exact (D eq_refl)].
  exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb. split; [lia|].
  unfold L5.u8_at. cbn [rdn]. rewrite E. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis PO : PESKA.sink_policyA_ok L P.
Let LYa := PMA.ly_as0 L C LY.

Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.

Lemma ffroomA_mono h h' FF LK LK2 : PMSPA.ffroomA h FF LK -> incl LK2 LK -> NoDup (map ff_addr (FF ++ LK2)) -> h' <= h -> PMSPA.ffroomA h' FF LK2.
Proof.
  intros FR0 INC ND Hh kk Hk. specialize (FR0 kk Hk). rewrite L5SAR.ff_count_app in FR0. rewrite L5SAR.ff_count_app.
  pose proof (L5SAR.ff_count_incl kk LK2 LK INC (L5SAR.nodup_of_map_app_r FF LK2 ND)) as C2. lia.
Qed.

Section Writer.
Variables (pc0 lra FR CUR KB : Z).
Hypothesis WA : wrunAF pc0 lra FR CUR KB.
Hypothesis WM : wrunM lra FR CUR KB.
Hypothesis WL : wrunL lra FR.
Hypothesis HFR : FR = 48 \/ FR = 64.
Hypothesis HKB : 1 <= KB <= 8.
Hypothesis HCUR : - FR <= CUR /\ CUR + KB <= -41.
Hypothesis RAOK : L5.ra_ok lra.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
          (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (rr o sp r h : Z) (k : PESK.sink).
Hypothesis HH : ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 2.
Hypothesis FRM : PMSPA.ffroomA 2 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis SP16 : sp mod 16 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 rr.
Hypothesis RRO : L5.u64_at RSEGS M rr o.
Hypothesis ALrr : rr mod 8 = 0.
Hypothesis AOrr : PMSPA.aobjA FF rr 8.
Hypothesis ACCrr : PMSPA.accA M rr 8.
Hypothesis RRdj : o + 24 <= rr \/ rr + 8 <= o.
Hypothesis SKA : PESKA.sink_atA RSEGS L ar P M o k.
Hypothesis AOo : PMSPA.aobjA FF o 24.
Hypothesis ALo : o mod 8 = 0.
Hypothesis HBh : PESKA.spa_hb P h.
Hypothesis ZKB : PESK.sk_z k + KB <= h.
Hypothesis CRED : PMSP.credit_le (PESKA.spa_pot P (PESK.sk_c k)) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (cr' : credit) (k' : PESK.sink),
        regs_preserved R R' -> PESK.sk_z k' = PESK.sk_z k + KB -> PESKA.sink_atA RSEGS L ar P M' o k' ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 2) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c k')) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own k' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.

Let Ws : list L5.range := [(o, 24)].
Definition csw (Ri : bvmap 5 word) : Prop := forall j, In j CSW -> getr Ri (reg j) = getr R (reg j).

Local Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 2) with 16384 in ASTK, STKSH; change (16384 / 8) with 2048 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2); pose proof RAOK as (Hra1 & Hra2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _).

Lemma SPd8 d : d mod 8 = 0 -> (sp - d) mod 8 = 0.
Proof.
  intros Hd. pose proof (Z.div_mod sp 16 ltac:(lia)) as E0. rewrite SP16, Z.add_0_r in E0. pose proof (Z.div_mod d 8 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
  rewrite E0, E1. replace (16 * (sp / 16) - 8 * (d / 8)) with ((2 * (sp / 16) - d / 8) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma ws_wapp : PMKA.wapp Ws.
Proof.
  entry_facts. pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 16384 HH (PMKA.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as (_ & OBIG & _).
  unfold Ws. apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG. lia.
Qed.

Definition inv (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit) (ki : PESK.sink) (j : Z) : Prop :=
  L5.u64_at RSEGS Mi (sp - 8) r /\ L5.u64_at RSEGS Mi (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS Mi (sp - 24) (bv_unsigned (getr R (reg 9)))
  /\ L5.u64_at RSEGS Mi (sp - 32) (bv_unsigned (getr R (reg 18))) /\ L5.u64_at RSEGS Mi (sp - 40) (bv_unsigned (getr R (reg 19)))
  /\ L5CA.astk ar Mi sp 16384 /\ shadow_zero Mi (sp - 16384) 2048
  /\ model_rt model mdi /\ L5CA.amodel_ok Awi mdi /\ incl LKi LK /\ incl Aw Awi
  /\ ri_inv HI (PESK.sink_own ki ++ LBX) FF LKi cri Awi Mi (vml_of mdi)
  /\ PESKA.sink_atA RSEGS L ar P Mi o ki /\ PESK.sk_z ki = PESK.sk_z k + j /\ L5.u64_at RSEGS Mi rr o /\ PMSPA.accA Mi rr 8
  /\ L5SAR.ek L ar LBX FF sp 16384 Ws M Mi /\ L5SAR.dk L ar LBX FF sp 16384 M Mi
  /\ PMSP.credit_keep cr cri (PESKA.spa_pot P (PESK.sk_c k)) (PESKA.spa_pot P (PESK.sk_c ki)).

Lemma inv_scratch Mi Mj mdi mdj LKi Awi cri ki j lo hi : inv Mi mdi LKi Awi cri ki j -> sp - FR <= lo -> hi <= sp - 40 ->
  mem_grows Mi Mj -> (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> Mj (Z_to_bv 64 i) = Mi (Z_to_bv 64 i)) ->
  ri_inv HI (PESK.sink_own ki ++ LBX) FF LKi cri Awi Mj (vml_of mdj) -> L5CA.amodel_ok Awi mdj -> model_rt mdi mdj ->
  inv Mj mdj LKi Awi cri ki j.
Proof.
  intros (T8 & T16 & T24 & T32 & T40 & ASTKi & SZi & MRTi & AMi & ILKi & IAWi & HHi & SKAi & ZJ & RRi & ACCi & EKi & DKi & CKi) Hlo Hhi MG FRZ HHj AMj MRTj.
  entry_facts.
  set (LBi := PESK.sink_own ki ++ LBX) in *.
  assert (EK1 : L5SAR.ek L ar LBi FF sp 16384 [] Mi Mj).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LBi FF LKi cri Awi Mi Mj _ sp 16384 [] lo hi HHi SPT); [clear - Hlo SLO HFR; lia| clear - Hlo HFR; lia| clear - Hhi; lia| exact FRZ]. }
  assert (BRBi : forall x, In x LBi -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (FRBi : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHi).
  assert (SV : forall a0 v, sp - 40 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mi a0 v -> L5.u64_at RSEGS Mj a0 v).
  { intros a0 v H1 H2 Uv. apply (L5C.u64_at_agree RSEGS Mi Mj); [| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact Uv]. intros i Hi. apply FRZ; [clear - Hi H1 H2 SLO SHI SPT; lia| clear - Hi H1 Hhi; lia]. }
  unfold inv. split; [apply SV; [lia|lia|exact T8]|]. split; [apply SV; [lia|lia|exact T16]|]. split; [apply SV; [lia|lia|exact T24]|].
  split; [apply SV; [lia|lia|exact T32]|]. split; [apply SV; [lia|lia|exact T40]|].
  split; [exact (L5SAR.astk_grows ar Mi Mj sp 16384 ASTKi MG)|].
  split; [apply (PMKA.stksh_keepA L ar LBi FF sp 16384 [] Mi Mj EK1 PMKA.wapp_nil (sp - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZi]|].
  split; [exact (L5LZ.model_rt_trans model mdi mdj MRTi MRTj)|]. split; [exact AMj|]. split; [exact ILKi|]. split; [exact IAWi|]. split; [exact HHj|].
  split; [apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 16384 [] Mi Mj EK1 PMKA.wapp_nil FRBi BRBi P o ki AOo); [intros i _ r0 []| unfold LBi; apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKAi]|].
  split; [exact ZJ|].
  split; [apply (PMKA.u64_keepA RSEGS L ar LBi FF sp 16384 [] Mi Mj EK1 PMKA.wapp_nil FRBi rr o AOrr); [intros i _ r0 []| exact RRi]|].
  split; [exact (PMKA.acc_keepA' L ar LBi FF sp 16384 [] Mi Mj EK1 PMKA.wapp_nil FRBi rr 8 AOrr ACCi)|].
  split; [apply (L5SAR.ek_trans L ar LBX FF sp 16384 Ws M Mi Mj EKi); apply (L5SAR.ek_W L ar LBX FF sp 16384 Ws [] Mi Mj); [exact (PMKA.ek_sublb L ar LBi LBX FF sp 16384 [] Mi Mj ltac:(unfold LBi; apply incl_appr; apply incl_refl) EK1)| intros a0 _ r0 []]|].
  split; [exact (L5SAR.dk_trans L ar LBX FF sp 16384 M Mi Mj DKi (L5SAR.dk_grows L ar LBX FF sp 16384 Mi Mj MG))| exact CKi].
Qed.

Lemma pbw (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq :
  inv Mq mdq LKq Awq crq kq j -> 0 <= j -> j + 1 <= KB ->
  getr Rq (reg 1) = Z_to_bv 64 lra -> getr Rq (reg 2) = Z_to_bv 64 (sp - FR) ->
  getr Rq (reg 10) = Z_to_bv 64 o -> getr Rq (reg 11) = Z_to_bv 64 (sp - 41) -> csw Rq ->
  (forall (fx2 : FPState) R2 M2 md2 LK2 Aw2 cr2 k2, inv M2 md2 LK2 Aw2 cr2 k2 (j + 1) -> regs_preserved Rq R2 ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R2 lra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq 0xaf02c Mq mdq) K.
Proof.
  intros INV J0 J1 Q1 Q2 Q10 Q11 QCS KX. entry_facts.
  pose proof INV as (T8 & T16 & T24 & T32 & T40 & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & SKAq & ZJ & RRq & ACCq & EKq & DKq & CKq).
  set (LBq := PESK.sink_own kq ++ LBX) in HHq.
  assert (BRBq : forall x, In x LBq -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  assert (FRBq : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFq & _).
  pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq o 24 sp 16384 HHq (PMKA.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & K4 & K5) & KBIG & _).
  pose proof SKAq as (_ & _ & _ & _ & _ & KZCq & KCAPq & KC0q & KBLKq).
  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutA.EADDR_A] in PBX.
  apply (PBX PMODE fxq Rq Mq mdq K LBX FF LKq Awq crq o (sp - 41) (sp - FR) lra kq HHq AMq K0); clear PBX.
  {
    split; [rewrite L5K.rl1; exact Q1|]. split; [exact RAOK|]. split; [rewrite L5K.rl2; exact Q2|].
    split; [rewrite L5K.rl3; rewrite (QCS 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (QCS 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar Mq Mq sp 16384 FR 12288 ASTKq); [intros w D; exact D| clear - HFR; lia| clear; lia| clear - HFR; lia|].
      destruct HFR as [-> | ->]; [replace (sp - 48) with (sp + (-3) * 16) by lia| replace (sp - 64) with (sp + (-4) * 16) by lia]; rewrite Z_mod_plus_full; exact SP16.
    - apply (PMKA.shadow_zero_sub Mq (sp - 16384) 2048); [apply SPd8; reflexivity| replace (sp - FR - 12288) with (sp - (FR + 12288)) by lia; apply SPd8; clear - HFR; destruct HFR as [-> | ->]; reflexivity| clear - HFR; lia| clear - HFR; lia| clear; lia| exact SZq]. }
  { apply (ffroomA_mono 2 0 FF LK LKq FRM ILKq NDFq). clear; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS HFR; lia. }
  { rewrite L5K.rl10. exact Q10. }
  { rewrite L5K.rl11. exact Q11. }
  { exact SKAq. }
  { exact AOo. }
  { exact ALo. }
  {
    split; [apply (L5.defined_sub Mq (sp - 16384) 16384 (sp - 41) 1 SDEFq); clear - HFR; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero Mq (sp - 16384) 2048 (sp - 41) SZq); [apply SPd8; reflexivity| clear; lia| clear; lia]|].
    split; [right; clear - K2 SLO; lia|]. left. split; [clear - HFR; lia| clear - SHI; lia]. }
  { intros ZC. apply (PESKA.spao_next L P PO (PESK.sk_c kq) h KCAPq); [intros Hc; exact (proj1 (proj2 (proj2 (proj2 (proj2 (KBLKq Hc))))))| exact HBh| clear - ZC ZJ ZKB J0 J1; lia]. }
  { unfold PMSP.credit_le, PMSP.credit_keep in CRED, CKq |- *. clear - CRED CKq. lia. }
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2. set (k2 := PESK.sk_push kq b2) in *.
  assert (OWs : forall a0, sp - 16384 <= a0 < sp -> L5.outside Ws a0).
  { intros a0 Ha0 r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 K2 SLO; lia. }
  assert (FRAME12 : forall a0, sp - FR <= a0 < sp -> M2 (Z_to_bv 64 a0) = Mq (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT HFR; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT HFR; lia| intros Y; clear - Ha0 Y; lia].
    - apply OWs. clear - Ha0 HFR; lia. }
  assert (EK12 : L5SAR.ek L ar LBX FF sp 16384 Ws Mq M2).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 16384 (sp - FR) 12288 Ws Ws Mq M2 HP2); [clear - HFR; lia| clear - HFR; lia| intros a0 _ O; exact O]. }
  assert (DK12 : L5SAR.dk L ar LBX FF sp 16384 Mq M2) by (apply (L5SAR.dk_callee L ar LBX [] FF [] sp 16384 (sp - FR) 12288 Ws Mq M2 HP2); clear - HFR; lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 16384).
  { apply (PMKA.astk_after_ahpres L ar LBX FF Mq M2 sp 16384 (sp - FR) 12288 Ws ASTKq HP2); [clear - HFR; lia| clear - HFR; lia| clear; lia| exact STOP]. }
  pose proof ws_wapp as WAPP.
  assert (SZ2 : shadow_zero M2 (sp - 16384) 2048).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 16384 Ws Mq M2 EK12 WAPP (sp - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact SZq]. }
  assert (SV : forall a0 v, sp - 40 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS M2 a0 v).
  { intros a0 v H1 H2 U. apply (L5C.u64_at_agree RSEGS Mq M2); [intros i Hi; apply FRAME12; clear - Hi H1 H2 HFR; lia| clear - H1 SLO SPT; lia| clear - H2 SHI SPT; lia| exact U]. }
  apply (KX fx2 R2 M2 md2 LK2 Aw2 cr2 k2); [| exact RP2].
  unfold inv. split; [apply SV; [lia|lia|exact T8]|]. split; [apply SV; [lia|lia|exact T16]|]. split; [apply SV; [lia|lia|exact T24]|].
  split; [apply SV; [lia|lia|exact T32]|]. split; [apply SV; [lia|lia|exact T40]|].
  split; [exact ASTK2|]. split; [exact SZ2|].
  split; [exact (L5LZ.model_rt_trans model mdq md2 MRTq MRT2)|]. split; [exact AM2|].
  split; [intros x Hx; apply ILKq; apply ILK2; exact Hx|]. split; [intros x Hx; apply IAW2; apply IAWq; exact Hx|].
  split; [exact HH2|]. split; [exact SKA2|].
  split; [unfold k2, PESK.sk_push; destruct (PESK.sk_z kq <? PESK.sk_c kq); cbn [PESK.sk_z]; clear - ZJ; lia|].
  split; [apply (PMKA.u64_keepA RSEGS L ar LBX FF sp 16384 Ws Mq M2 EK12 WAPP FRBq rr o AOrr); [| exact RRq]; intros i Hi r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi RRdj; lia|].
  split; [exact (PMKA.acc_keepA' L ar LBX FF sp 16384 Ws Mq M2 EK12 WAPP FRBq rr 8 AOrr ACCq)|].
  split; [exact (L5SAR.ek_trans L ar LBX FF sp 16384 Ws M Mq M2 EKq EK12)|].
  split; [exact (L5SAR.dk_trans L ar LBX FF sp 16384 M Mq M2 DKq DK12)|].
  unfold PMSP.credit_keep in CKq, CK2 |- *. clear - CKq CK2. lia.
Qed.

Lemma loop (m : nat) : forall (j : Z) (fxq : FPState) Rq Mq mdq LKq Awq crq kq,
  Z.of_nat m = KB - 1 - j -> 0 <= j ->
  inv Mq mdq LKq Awq crq kq (j + 1) ->
  getr Rq (reg 2) = Z_to_bv 64 (sp - FR) -> getr Rq (reg 8) = Z_to_bv 64 rr -> getr Rq (reg 9) = Z_to_bv 64 (KB - j) ->
  getr Rq (reg 18) = Z_to_bv 64 (sp + CUR + j) -> getr Rq (reg 19) = Z_to_bv 64 (rr / 8 + SBL) -> csw Rq ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Rq lra Mq mdq) K.
Proof.
  induction m as [|m IH]; intros j fxq Rq Mq mdq LKq Awq crq kq Hm J0 INV Q2 Q8 Q9 Q18 Q19 QCS.
  -
    assert (JE : j = KB - 1) by (clear - Hm; lia). entry_facts.
    pose proof INV as (T8 & T16 & T24 & T32 & T40 & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & SKAq & ZJ & RRq & ACCq & EKq & DKq & CKq).
    pose proof AMq as (Mhq & MIq). pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
    set (LBq := PESK.sink_own kq ++ LBX) in HHq.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & _).
    set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
    pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
    pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
    assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
    assert (CSBv : L5.u64_at RSEGS MV 1317368 SBL) by (apply (proj2 (L5A.u64_at_vis H Mq 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
    assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H Mq 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
    pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 16384 FR HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR).
    assert (SVV : forall a0 v, sp - 40 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS Mq a0 v -> L5.u64_at RSEGS MV a0 v).
    { intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H Mq a0 v (VIS a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). exact U. }
    pose proof (SVV (sp - 8) r ltac:(lia) ltac:(lia) T8) as Y8. pose proof (SVV (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Y16. pose proof (SVV (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Y24.
    pose proof (SVV (sp - 32) _ ltac:(lia) ltac:(lia) T32) as Y32. pose proof (SVV (sp - 40) _ ltac:(lia) ltac:(lia) T40) as Y40.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8. pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9.
    pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18. pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19.
    pose proof (bv_unsigned_in_range 64 (getr Rq (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr Rq (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr Rq (reg 12))) as B12.
    change (bv_modulus 64) with (2 ^ 64) in B8, B9, B18, B19, B10, B11, B12.
    assert (G10 : getr Rq (reg 10) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 10)))) by (symmetry; apply PMPK.word_id).
    assert (G11 : getr Rq (reg 11) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 11)))) by (symmetry; apply PMPK.word_id).
    assert (G12 : getr Rq (reg 12) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 12)))) by (symmetry; apply PMPK.word_id).
    assert (RR0 : 0 <= rr < 2 ^ 64) by (pose proof (PMKA.aobjA_bounds FF (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HHq) rr 8 AOrr); lia).
    rewrite JE in Q9, Q18. replace (KB - (KB - 1)) with 1 in Q9 by (clear; lia).
    unfold PMSPA.cfg.
    destruct (WL fxq Rq MV sp rr (sp + CUR + (KB - 1)) r (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))) (bv_unsigned (getr R (reg 18))) (bv_unsigned (getr R (reg 19)))
                 (bv_unsigned (getr Rq (reg 10))) (bv_unsigned (getr Rq (reg 11))) (bv_unsigned (getr Rq (reg 12))))
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T2 & T8' & T9' & T18' & T19');
      [ clear - SLO SHI SPT; lia | exact RR0 | clear - SLO SHI SPT HCUR HKB HFR; lia | clear - Hr1; lia | exact B8 | exact B9 | exact B18 | exact B19 | exact B10 | exact B11 | exact B12
      | exact Q2 | exact Q8 | exact Q9 | exact G10 | exact G11 | exact G12 | exact Q18 | exact Q19 | exact IC0 | exact CSBv | exact CUARv | clear - SLO SHI SPT HFR; lia | exact SP16 | exact SWR
      | exact Y8 | exact Y16 | exact Y24 | exact Y32 | exact Y40 | exact RAok |].
    apply (L5SAR.apiece_ro L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq lra R3 r M3v K HHq AMq MS3 MG3 FRZ3).
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree Mq M3 AG3) as EM. subst M3.
    apply (KONT fx3 R3 Mq md3 LKq Awq crq kq).
    + apply L5SAR.preserved_by_index. intros jj Hj. unfold L5SAR.cs_all in Hj.
      repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8'; apply PMPK.word_id | rewrite T9'; apply PMPK.word_id | rewrite T18'; apply PMPK.word_id
                                              | rewrite T19'; apply PMPK.word_id | rewrite (KS3 _) by inl; apply QCS; inl ] |]). destruct Hj.
    + rewrite ZJ, JE. clear; lia.
    + exact SKAq.
    + change (PMSPA.pm_scr 2) with 16384. exact (L5SAR.ahpres_of L ar LBX FF sp 16384 _ M Mq EKq SDEFq DKq).
    + exact CKq.
    + exact (L5LZ.model_rt_trans model mdq md3 MRTq MRT3).
    + exact ILKq.
    + exact IAWq.
    + exact AM3.
    + exact HH3.
  -
    assert (JB : j + 1 <= KB - 1) by (clear - Hm; lia). entry_facts.
    pose proof INV as (T8 & T16 & T24 & T32 & T40 & ASTKq & SZq & MRTq & AMq & ILKq & IAWq & HHq & SKAq & ZJ & RRq & ACCq & EKq & DKq & CKq).
    pose proof AMq as (Mhq & MIq). pose proof ASTKq as (_ & _ & _ & _ & SDEFq & _).
    set (LBq := PESK.sink_own kq ++ LBX) in HHq.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq HHq) as (HOFF & VIS & VIMG & VFS & _).
    set (H := ahid Awq mdq) in *. set (MV := mrestrict H Mq) in *.
    pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HHq) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
    pose proof (L5A.statics_facts L C Mq LYa ST) as (GOT & CSB & CUAR & _).
    assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
    assert (CSBv : L5.u64_at RSEGS MV 1317368 SBL) by (apply (proj2 (L5A.u64_at_vis H Mq 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
    assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H Mq 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
    pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LKq crq Awq Mq mdq sp 16384 FR HHq ASTKq ltac:(clear - HFR; lia)) as (_ & _ & SWR).
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq rr 8 sp 16384 HHq (PMKA.aobj_of_aobjA FF rr 8 AOrr ALrr) ltac:(lia) ltac:(reflexivity))
      as ((R1' & R2' & R3' & R4' & R5') & RBIG & RDEF & RVIS & _).
    pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq o 24 sp 16384 HHq (PMKA.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity))
      as ((K1 & K2 & K3 & K4 & K5) & _).
    assert (RROv : L5.u64_at RSEGS MV rr o) by (apply (proj2 (L5A.u64_at_vis H Mq rr o RVIS ltac:(lia) ltac:(lia))); exact RRq).
    pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LKq crq Awq Mq mdq rr 8 HHq AOrr ALrr ltac:(lia) ltac:(reflexivity) ACCq) as ZRR.
    unfold SB in ZRR. change (8 / 8) with 1 in ZRR. fold H MV in ZRR.
    pose proof (bv_unsigned_in_range 64 (getr Rq (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr Rq (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr Rq (reg 12))) as B12.
    change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12.
    assert (G10 : getr Rq (reg 10) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 10)))) by (symmetry; apply PMPK.word_id).
    assert (G11 : getr Rq (reg 11) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 11)))) by (symmetry; apply PMPK.word_id).
    assert (G12 : getr Rq (reg 12) = Z_to_bv 64 (bv_unsigned (getr Rq (reg 12)))) by (symmetry; apply PMPK.word_id).

    assert (DB : Mq (Z_to_bv 64 (sp + CUR + j + 1)) <> None).
    { replace (sp + CUR + j + 1) with (sp - 16384 + (16384 + CUR + j + 1)) by (clear; lia). apply SDEFq. clear - J0 JB HCUR HKB HFR; lia. }
    destruct (u8_at_of_defined Mq (sp + CUR + j + 1) ltac:(clear - SLO SHI SPT J0 JB HCUR HKB HFR; lia) DB) as (nb & NB & NBat).
    assert (NBv : L5.u8_at RSEGS MV (sp + CUR + j + 1) nb).
    { apply (proj2 (L5A.u8_at_vis H Mq (sp + CUR + j + 1) nb (VIS (sp + CUR + j + 1) 1 ltac:(clear - SLO HCUR J0 HFR; lia) ltac:(clear - SHI SPT HCUR JB; lia)) ltac:(clear - SLO SPT HCUR J0 HFR; lia) ltac:(clear - SHI SPT HCUR JB; lia))). exact NBat. }
    unfold PMSPA.cfg.
    destruct (WM fxq Rq MV sp rr o (KB - j) (sp + CUR + j) nb (bv_unsigned (getr Rq (reg 10))) (bv_unsigned (getr Rq (reg 11))) (bv_unsigned (getr Rq (reg 12))))
      as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8' & T9' & T10' & T11' & T18' & T19');
      [ clear - SLO SHI SPT; lia | clear - R1' R3'; lia | clear - K1 K3; lia | clear - J0 JB HKB; lia | clear - SLO SHI SPT HCUR J0 JB HKB HFR; lia | clear - NB; lia
      | exact B10 | exact B11 | exact B12
      | exact Q2 | exact Q8 | exact Q9 | exact G10 | exact G11 | exact G12 | exact Q18 | exact Q19 | exact IC0 | exact CSBv | exact CUARv | clear - SLO SHI SPT HFR; lia | exact SP16 | exact SWR
      | clear - R1' R3'; lia | exact ALrr | exact RBIG | exact ZRR | exact RROv | clear - R2' SLO HFR; lia | clear - K1 K3; lia | exact ALo
      | clear - J0 JB; lia | clear - SLO SHI SPT HCUR J0 JB HFR; lia | clear - HCUR J0 JB; lia | exact NBv | exact NB |].
    apply (L5SAR.apiece L ar C HI LYa HIok LBq FF LKq crq Awq Mq mdq fxq fx3 Rq lra R3 0xaf02c M3v (fun a0 => sp - 41 <= a0 < sp - 41 + 1) K HHq AMq MS3 MG3).
    { intros a0 Ha0 Hn. apply FRZ3; [exact Ha0| exact Hn]. }
    { intros a0 Ha0 Wa. split.
      - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      - clear - Wa SLO SPT; lia. }
    intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (INV3 : inv M3 md3 LKq Awq crq kq (j + 1)).
    { apply (inv_scratch Mq M3 mdq md3 LKq Awq crq kq (j + 1) (sp - 41) (sp - 40) INV ltac:(clear - HFR; lia) ltac:(clear; lia) MGM3); [| exact HH3| exact AM3| exact MRT3].
      intros i Hi Ni. apply FR3; [exact Hi| clear - Ni; lia]. }
    apply (pbw (j + 1) fx3 R3 M3 md3 LKq Awq crq kq INV3 ltac:(clear - J0; lia) ltac:(clear - JB; lia) T1 T2 T10' T11').
    { intros jj Hj. rewrite (KS3 jj Hj). exact (QCS jj Hj). }
    intros fx4 R4 M4 md4 LK4 Aw4 cr4 k4 INV4 RP4.
    apply (IH (j + 1) fx4 R4 M4 md4 LK4 Aw4 cr4 k4 ltac:(clear - Hm; lia) ltac:(clear - J0; lia)).
    + replace (j + 1 + 1) with (j + 2) by (clear; lia). replace (j + 1 + 1) with (j + 2) in INV4 by (clear; lia). exact INV4.
    + rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl. exact T2.
    + rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl. exact T8'.
    + rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl. rewrite T9'. f_equal. clear; lia.
    + rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl. rewrite T18'. f_equal. clear; lia.
    + rewrite (L5SAR.cs_of_preserved R3 R4 19 RP4) by inl. exact T19'.
    + intros jj Hj. rewrite (L5SAR.cs_of_preserved R3 R4 jj RP4) by (clear - Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). rewrite (KS3 jj Hj). exact (QCS jj Hj).
Qed.

Lemma writer_core : srealizes RSEGS SCFG (PMSPA.cfg RSEGS R pc0 M model) K.
Proof.
  entry_facts. pose proof AM as (Mh & MI).
  pose proof A10 as B10. rewrite L5K.rl10 in B10.
  set (LB := PESK.sink_own k ++ LBX) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & _).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 SBL) by (apply (proj2 (L5A.u64_at_vis H M 1317368 SBL (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 16384 FR HH ASTK ltac:(clear - HFR; lia)) as (_ & _ & SWR).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model rr 8 sp 16384 HH (PMKA.aobj_of_aobjA FF rr 8 AOrr ALrr) ltac:(lia) ltac:(reflexivity))
    as ((R1' & R2' & R3' & R4' & R5') & RBIG & RDEF & RVIS & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 16384 HH (PMKA.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity))
    as ((K1 & K2 & K3 & K4 & K5) & _).
  assert (RROv : L5.u64_at RSEGS MV rr o) by (apply (proj2 (L5A.u64_at_vis H M rr o RVIS ltac:(lia) ltac:(lia))); exact RRO).
  pose proof (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model rr 8 HH AOrr ALrr ltac:(lia) ltac:(reflexivity) ACCrr) as ZRR.
  unfold SB in ZRR. change (8 / 8) with 1 in ZRR. fold H MV in ZRR.

  destruct (WA fx R MV sp rr o) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & S40 & S32 & S24 & S16 & S8);
    [ clear - SLO SHI SPT; lia | clear - R1' R3'; lia | clear - K1 K3; lia | exact Rsp | exact B10 | exact IC0 | exact CSBv | exact CUARv
    | clear - SLO SHI SPT HFR; lia | exact SP16 | exact SWR | clear - R1' R3'; lia | exact ALrr | exact RBIG | exact ZRR | exact RROv | clear - R2' SLO HFR; lia
    | clear - K1 K3; lia | exact ALo |].
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 0xaf02c M1v (fun a0 => sp - FR <= a0 < sp - FR + FR) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT HFR; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT HFR; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.

  assert (Hr : bv_unsigned (getr R (reg 1)) = r) by (rewrite Rra; apply L5.unsigned_lit; clear - Hr1; lia).
  assert (RB : forall a0 v, sp - 40 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1v a0 v -> L5.u64_at RSEGS M1 a0 v).
  { intros a0 v Ha1 Ha2 U. apply (proj1 (L5A.u64_at_vis H M1 a0 v (VIS a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). rewrite VIS1. exact U. }

  assert (EK01n : L5SAR.ek L ar LB FF sp 16384 [] M M1).
  { apply (PMKA.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 16384 [] (sp - FR) (sp - FR + FR) HH SPT); [clear - SLO HFR; lia| clear - HFR; lia| clear; lia| exact FR1]. }
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INV1 : inv M1 md1 LK Aw cr k 0).
  { unfold inv. split; [rewrite <- Hr; apply RB; [lia|lia|exact S8]|]. split; [apply RB; [lia|lia|exact S16]|]. split; [apply RB; [lia|lia|exact S24]|].
    split; [apply RB; [lia|lia|exact S32]|]. split; [apply RB; [lia|lia|exact S40]|].
    split; [exact (L5SAR.astk_grows ar M M1 sp 16384 ASTK MGM1)|].
    split; [apply (PMKA.stksh_keepA L ar LB FF sp 16384 [] M M1 EK01n PMKA.wapp_nil (sp - 16384) 2048); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SPd8; reflexivity| clear; lia| exact STKSH]|].
    split; [exact MRT1|]. split; [exact AM1|]. split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact HH1|].
    split; [apply (PECFA.sink_keepA RSEGS L ar LB FF sp 16384 [] M M1 EK01n PMKA.wapp_nil FRB BRB P o k AOo); [intros i _ r0 []| unfold LB; apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKA]|].
    split; [clear; lia|].
    split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp 16384 [] M M1 EK01n PMKA.wapp_nil FRB rr o AOrr); [intros i _ r0 []| exact RRO]|].
    split; [exact (PMKA.acc_keepA' L ar LB FF sp 16384 [] M M1 EK01n PMKA.wapp_nil FRB rr 8 AOrr ACCrr)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 16384 Ws [] M M1); [exact (PMKA.ek_sublb L ar LB LBX FF sp 16384 [] M M1 ltac:(unfold LB; apply incl_appr; apply incl_refl) EK01n)| intros a0 _ r0 []]|].
    split; [apply L5SAR.dk_grows; exact MGM1|]. unfold PMSP.credit_keep. clear. lia. }

  apply (pbw 0 fx1 R1 M1 md1 LK Aw cr k INV1 ltac:(clear; lia) ltac:(clear - HKB; lia) T1 T2 T10 T11 KS1).
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 k2 INV2 RP2.

  apply (loop (Z.to_nat (KB - 1)) 0 fx2 R2 M2 md2 LK2 Aw2 cr2 k2 ltac:(clear - HKB; lia) ltac:(clear; lia)).
  - exact INV2.
  - rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl. exact T2.
  - rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl. exact T8.
  - rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl. rewrite T9. f_equal. clear; lia.
  - rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl. rewrite T18. f_equal. clear; lia.
  - rewrite (L5SAR.cs_of_preserved R1 R2 19 RP2) by inl. exact T19.
  - intros jj Hj. rewrite (L5SAR.cs_of_preserved R1 R2 jj RP2) by (clear - Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl). exact (KS1 jj Hj).
Qed.
End Call.

Lemma writer_ok : PENTBAF.ntbf_specA RSEGS AD L ar HI pc0 KB P.
Proof.
  unfold PENTBAF.ntbf_specA. intros PMODE fx R M model K LBX FF LK Aw cr rr o sp r h k HH AM K0 ENT FRM FRS SP16 A10 RRO ALrr AOrr ACCrr RRdj SKA AOo ALo HBh ZKB CRED KONT.
  exact (writer_core PMODE fx R M model K LBX FF LK Aw cr rr o sp r h k HH AM K0 ENT FRM FRS SP16 A10 RRO ALrr AOrr ACCrr RRdj SKA AOo ALo HBh ZKB CRED KONT).
Qed.
End Writer.

Theorem ntb_f32_ok : PENTBAF.ntbf_specA RSEGS AD L ar HI 0xb0c38 4 P.
Proof. apply (writer_ok 0xb0c38 0xb0cc0 48 (-48) 4 f32_runA f32_runM f32_runL); [left; reflexivity| clear; lia| clear; lia| split; [clear; lia| reflexivity]]. Qed.
Theorem ntb_f64_ok : PENTBAF.ntbf_specA RSEGS AD L ar HI 0xb0cf0 8 P.
Proof. apply (writer_ok 0xb0cf0 0xb0db0 64 (-56) 8 f64_runA f64_runM f64_runL); [right; reflexivity| clear; lia| clear; lia| split; [clear; lia| reflexivity]]. Qed.
End WithHeap.
End PEAENTBF.
