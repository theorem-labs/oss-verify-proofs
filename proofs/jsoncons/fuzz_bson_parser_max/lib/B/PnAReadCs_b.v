(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation Zwf.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAReadCsP_b Ba0_code_b19d8_b19dc_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNACS.
Import L5A. Import L5CA. Import L5SAR. Import PNACSK.

Lemma zb_mod64 a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. clear; lia. Qed.
Lemma bax_cat_add ax : PNST.bax_cat (PNST.bax_add_cat ax) = true.
Proof. destruct ax; reflexivity. Qed.
Lemma bvu_rng (x : word) : 0 <= bv_unsigned x < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 x) as B. change (bv_modulus 64) with (2 ^ 64) in B. exact B. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.


(* [comment removed for export] *)
Lemma cs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNACSK.cs_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNACSK.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

Lemma set_cs_src w s x g : PNM.b_src (set_cs w s x g) = PNM.b_src s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_stk w s x g : PNM.b_stk (set_cs w s x g) = PNM.b_stk s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_done w s x g : PNM.b_done (set_cs w s x g) = PNM.b_done s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_bb w s x g : PNM.b_bb (set_cs w s x g) = PNM.b_bb s.
Proof. unfold set_cs. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_cs_str w s x g : PNRA.bcs_str w (set_cs w s x g) = x.
Proof. unfold set_cs, PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma set_stk_str w s l : PNRA.bcs_str w (PNBO.set_stk s l) = PNRA.bcs_str w s.
Proof. unfold PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma with_src_str w s x : PNRA.bcs_str w (PNM.with_srcB s x) = PNRA.bcs_str w s.
Proof. unfold PNRA.bcs_str. destruct (Z.eqb w 0); reflexivity. Qed.
Lemma btop_len s s3 : PNRA.btop_pos s s3 -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat.
Proof. intros (l & c & c' & E1 & E2 & _). rewrite E1, E2, !List.length_app. cbn [length]. apply Nat.le_refl. Qed.
Lemma fdiv_rng F : 6905856 <= F <= 140737488355264 -> 863232 <= F / 8 <= 17592186044408.
Proof.
  intros HF. split; [apply Z.div_le_lower_bound; clear - HF; lia| apply Z.div_le_upper_bound; clear - HF; lia].
Qed.

(* [comment removed for export] *)
Lemma cs_arm_nul K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 pre top :
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> PNM.b_stk s3 = pre ++ [top] ->
  jregs R R3 sp fb w F 1 (PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40) ->
  spill M3 sp F (fb + 464) (fb + 1024) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 ->
  L5.u8_at RSEGS M3 (F + 32) 0 ->
  PM.unread (PNM.b_src s3) sm3 < PM.unread (PNM.b_src s) sm ->
  PM.vs_size (PNRA.bcs_str w s3) + PM.unread (PNM.b_src s3) sm3 + 1 <= PM.vs_size (PNRA.bcs_str w s) + PM.unread (PNM.b_src s) sm ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb2e48 M3 model3) K.
Proof.
  intros CTX G LM INV3 ES JR SPL EC3 TP3 CB UN3 SZ3.
  pose proof CTX as (Hw & _). pose proof (PNACSK.bcs_off_rng w Hw) as HOFF.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM)
    as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 pre top CTX G LM INV3 ES)
    as (TF3 & PT3 & OKt3 & VIN3 & TB13 & TB23 & TB33 & TB43).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. destruct PF3 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  set (e3 := (PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40)) in *.
  unfold tfacts in TF3. destruct TF3 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  destruct JR as (J2 & J3 & J4 & J8 & J9 & J10 & J11 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
  destruct SPL as (SP1 & SP2 & SP3 & SP4).
  pose proof (SV3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SP1) as SP1v.
  pose proof (SV3 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia) SP2) as SP2v.
  pose proof (SV3 (sp - 144) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SP3) as SP3v.
  pose proof (SV3 (sp - 152) (fb + 464) ltac:(clear; lia) ltac:(clear; lia) SP4) as SP4v.
  unfold own in OWN3. destruct OWN3 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  pose proof (U8v3 0 CB) as CBv.
  assert (Q34 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 HOFF; lia).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  LeanFeed.pfeed P (PNACSP.acsKz_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e3 | 43%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _).
  pose proof (fdiv_rng F pf13) as (DF1 & DF2).
  pose proof LM as (_ & RP3 & _). pose proof RP3 as (PA3 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA3.
  pose proof PA3 as (_ & _ & _ & MORE3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB3 & _).
  apply (PNACSK.cs_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3
           fx3 fx9 R3 R9 0xb2e48 (PNM.b_more s3) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV3 M9v); [| clear - pf7; lia| clear - pf7; lia| exact (proj2 (U8op3 _) MORE3)].
    intros j Hj. apply FRZ9; [clear - Hj pf7; lia| clear - Hj pf26; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf27; lia].
  - exact MB3.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact J3.
    + rewrite (KS9 4%nat) by inl. exact J4.
  - right. split; [exact EC3|]. split; [reflexivity|]. unfold PNRA.bprog_cs. split; [exact TP3|]. split; [exact UN3| exact SZ3].
  - exact INV3.
  - exact (btop_len s s3 TP3).
Qed.

(* [comment removed for export] *)
Lemma cs_arm_eof K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 pre top :
  PNRAa.make_ec_spec L ar HI ->
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> PNM.b_stk s3 = pre ++ [top] ->
  jregs R R3 sp fb w F 0 (PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40) ->
  spill M3 sp F (fb + 464) (fb + 1024) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb2e48 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 ES JR SPL EC3 TP3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _). pose proof (PNACSK.bcs_off_rng w Hw) as HOFF.
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM)
    as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 pre top CTX G LM INV3 ES)
    as (TF3 & PT3 & OKt3 & VIN3 & TB13 & TB23 & TB33 & TB43).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  set (e3 := PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40) in *.
  unfold pfacts in PF3. destruct PF3 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF3. destruct TF3 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  destruct JR as (J2 & J3 & J4 & J8 & J9 & J10 & J11 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
  pose proof SPL as (SP1 & SP2 & SP3 & SP4).
  pose proof (SV3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SP1) as SP1v.
  pose proof (SV3 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia) SP2) as SP2v.
  pose proof (SV3 (sp - 144) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SP3) as SP3v.
  pose proof (SV3 (sp - 152) (fb + 464) ltac:(clear; lia) ltac:(clear; lia) SP4) as SP4v.
  assert (Q34 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 HOFF; lia).
  LeanFeed.pfeed P (PNACSP.acsK0_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e3 | 43%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11).
  apply (cs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx4 R3 R4 0xb2e48 0xae848 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNACSK.cs_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 732780 1 e cat MKE CTX G LM4 EC3 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { rewrite (KS4 2%nat) by inl. exact J2. }
  { rewrite (KS4 3%nat) by inl. rewrite J3. exact Rgp. }
  { rewrite (KS4 4%nat) by inl. rewrite J4. exact Rtp. }
  { exact Y10. }
  { exact Y11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 SP1 SP2 SP3 SP4 SP1v SP2v SP3v SP4v U8v3 WRop3 U8op3 SV3 SVr3 OWN3.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5)
    as (PF5 & OWN5 & SV5 & U8v5 & WRop5 & U8op5 & SVr5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. destruct PF5 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  assert (SPL5 : spill M5 sp F (fb + 464) (fb + 1024)).
  { apply (PNACSK.spill_agree M3 M5 sp F (fb + 464) (fb + 1024) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia) SPL). intros a Ha. apply AG5. clear - Ha; lia. }
  destruct SPL5 as (SP1 & SP2 & SP3 & SP4).
  pose proof (SV5 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SP1) as SP1v.
  pose proof (SV5 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia) SP2) as SP2v.
  pose proof (SV5 (sp - 144) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SP3) as SP3v.
  pose proof (SV5 (sp - 152) (fb + 464) ltac:(clear; lia) ltac:(clear; lia) SP4) as SP4v.
  unfold own in OWN5. destruct OWN5 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  pose proof (bvu_rng (getr R (reg 1))) as Q60.
  pose proof (bvu_rng (getr R (reg 8))) as Q61.
  pose proof (bvu_rng (getr R (reg 9))) as Q62.
  pose proof (bvu_rng (getr R (reg 18))) as Q63.
  pose proof (bvu_rng (getr R (reg 19))) as Q64.
  pose proof (bvu_rng (getr R (reg 20))) as Q65.
  pose proof (bvu_rng (getr R (reg 21))) as Q66.
  pose proof (bvu_rng (getr R (reg 22))) as Q67.
  pose proof (bvu_rng (getr R (reg 23))) as Q68.
  pose proof (bvu_rng (getr R (reg 24))) as Q69.
  pose proof (bvu_rng (getr R (reg 25))) as Q70.
  pose proof (bvu_rng (getr R (reg 26))) as Q71.
  pose proof (bvu_rng (getr R (reg 27))) as Q72.
  assert (WR8 : L5.writable RSEGS MV5 (fb + 464 + 8) 1) by (apply (L5.writable_sub RSEGS MV5 (fb + 464) 424); [exact WRop5| clear; lia| clear; lia]).
  assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R3 (reg k)).
  { intros k Hk. rewrite (L5SAR.cs_of_preserved R4 R5 k RP5) by (revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat); vm_compute; reflexivity).
    apply KS4. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (E2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 2%nat) by inl; exact J2).
  assert (E8 : getr R5 (reg 8) = Z_to_bv 64 sp) by (rewrite (RK 8%nat) by inl; exact J8).
  assert (E9 : getr R5 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 9%nat) by inl; exact J9).
  assert (E18 : getr R5 (reg 18) = Z_to_bv 64 40) by (rewrite (RK 18%nat) by inl; exact J18).
  assert (E19 : getr R5 (reg 19) = Z_to_bv 64 1) by (rewrite (RK 19%nat) by inl; exact J19).
  assert (E20 : getr R5 (reg 20) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off w)) by (rewrite (RK 20%nat) by inl; exact J20).
  assert (E21 : getr R5 (reg 21) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (RK 21%nat) by inl; exact J21).
  assert (E22 : getr R5 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (RK 22%nat) by inl; exact J22).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (RK 23%nat) by inl; exact J23).
  assert (E24 : getr R5 (reg 24) = Z_to_bv 64 (fb + 464 + 400)) by (rewrite (RK 24%nat) by inl; exact J24).
  assert (E25 : getr R5 (reg 25) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880)) by (rewrite (RK 25%nat) by inl; exact J25).
  assert (E26 : getr R5 (reg 26) = Z_to_bv 64 F) by (rewrite (RK 26%nat) by inl; exact J26).
  assert (E27 : getr R5 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (RK 27%nat) by inl; exact J27).
  LeanFeed.pfeed P (PNACSP.acsE_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z2 & Z8 & Z9 & Z10 & Z11 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & FL0
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
  pose proof (fdiv_rng F pf13) as (DF1 & DF2).
  apply (PNACSK.cs_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3
           fx5 fx9 R5 R9 732780 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + right. clear - X; lia.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. rewrite (RK 3%nat) by inl. exact J3.
    + rewrite (KS9 4%nat) by inl. rewrite (RK 4%nat) by inl. exact J4.
  - left. exists 1. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact (btop_len s s3 TP3).
Qed.

(* [comment removed for export] *)
Lemma cs_arm_pb K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (n : Z)
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 (cb : Z) pre top :
  PNRAa.str_push_back_spec L ar HI ->
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1,
      cs_linv L ar HI R M model LBX FF LK Aw cr sp fb cat e s str sm ax w F R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
      PM.unread (PNM.b_src s1) sm1 < n ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K) ->
  cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> PNM.b_stk s3 = pre ++ [top] ->
  jregs R R3 sp fb w F 1 (PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40) ->
  spill M3 sp F (fb + 464) (fb + 1024) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 ->
  L5.u8_at RSEGS M3 (F + 32) cb -> 1 <= cb <= 255 ->
  PM.unread (PNM.b_src s3) sm3 < PM.unread (PNM.b_src s) sm -> PM.unread (PNM.b_src s3) sm3 < n ->
  PM.vs_size (PNRA.bcs_str w s3) + PM.unread (PNM.b_src s3) sm3 + 1 <= PM.vs_size (PNRA.bcs_str w s) + PM.unread (PNM.b_src s) sm ->
  PM.vs_size (PNRA.bcs_str w s3) + PM.unread (PNM.b_src s3) sm3 + 1 <= 2 ^ 26 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb2e48 M3 model3) K.
Proof.
  intros PB CTX G IH LM INV3 ES JR SPL EC3 TP3 CB Hcb UN3 UNn SZ3 SZ4.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _). pose proof (PNACSK.bcs_off_rng w Hw) as HOFF.
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM)
    as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 pre top CTX G LM INV3 ES)
    as (TF3 & PT3 & OKt3 & VIN3 & TB13 & TB23 & TB33 & TB43).
  pose proof LM as (_ & RP3 & _). pose proof RP3 as (PA3 & IA3 & _).
  pose proof (PNACSK.unread_nonneg _ _ _ _ _ _ _ PA3 IA3) as UN0.
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  set (e3 := PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40) in *.
  unfold pfacts in PF3. destruct PF3 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF3. destruct TF3 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  destruct JR as (J2 & J3 & J4 & J8 & J9 & J10 & J11 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
  pose proof SPL as (SP1 & SP2 & SP3 & SP4).
  pose proof (SV3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SP1) as SP1v.
  pose proof (SV3 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia) SP2) as SP2v.
  pose proof (SV3 (sp - 144) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SP3) as SP3v.
  pose proof (SV3 (sp - 152) (fb + 464) ltac:(clear; lia) ltac:(clear; lia) SP4) as SP4v.
  pose proof (U8v3 cb CB) as CBv.
  assert (Q34 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 HOFF; lia).
  assert (Q45 : 0 <= cb < 2 ^ 64) by (clear - Hcb; lia).
  LeanFeed.pfeed P (PNACSP.acsKc_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e3 | 43%nat => PNM.bs_pos top | 45%nat => cb | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11).
  apply (cs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx4 R3 R4 0xb2e48 0xd5bc4 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN).
  apply (PNACSK.cs_call_pb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 732764 cb PB CTX G LM4 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { rewrite (KS4 2%nat) by inl. exact J2. }
  { rewrite (KS4 3%nat) by inl. rewrite J3. exact Rgp. }
  { rewrite (KS4 4%nat) by inl. rewrite J4. exact Rtp. }
  { exact Y10. }
  { exact Y11. }
  { clear - Hcb; lia. }
  { clear - SZ4 UN0; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 x' g' cr5 RP5 SZX LM5 AG5 ECK5.
  clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 SP1 SP2 SP3 SP4 SP1v SP2v SP3v SP4v U8v3 WRop3 U8op3 SV3 SVr3 OWN3 CBv.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 (set_cs w s3 x' g') sm3 ax3 cr5 CTX G LM5)
    as (PF5 & OWN5 & SV5 & U8v5 & WRop5 & U8op5 & SVr5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. destruct PF5 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  assert (SPL5 : spill M5 sp F (fb + 464) (fb + 1024)).
  { apply (PNACSK.spill_agree M3 M5 sp F (fb + 464) (fb + 1024) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia) SPL). intros a Ha. apply AG5. clear - Ha; lia. }
  assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k) = getr R3 (reg k)).
  { intros k Hk. rewrite (L5SAR.cs_of_preserved R4 R5 k RP5) by exact Hk.
    apply KS4. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
  assert (E2 : getr R5 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 2%nat) by inl; exact J2).
  assert (E8 : getr R5 (reg 8) = Z_to_bv 64 sp) by (rewrite (RK 8%nat) by inl; exact J8).
  assert (E9 : getr R5 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 9%nat) by inl; exact J9).
  assert (E18 : getr R5 (reg 18) = Z_to_bv 64 40) by (rewrite (RK 18%nat) by inl; exact J18).
  assert (E19 : getr R5 (reg 19) = Z_to_bv 64 1) by (rewrite (RK 19%nat) by inl; exact J19).
  assert (E20 : getr R5 (reg 20) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off w)) by (rewrite (RK 20%nat) by inl; exact J20).
  assert (E21 : getr R5 (reg 21) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (RK 21%nat) by inl; exact J21).
  assert (E22 : getr R5 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (RK 22%nat) by inl; exact J22).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (RK 23%nat) by inl; exact J23).
  assert (E24 : getr R5 (reg 24) = Z_to_bv 64 (fb + 464 + 400)) by (rewrite (RK 24%nat) by inl; exact J24).
  assert (E25 : getr R5 (reg 25) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880)) by (rewrite (RK 25%nat) by inl; exact J25).
  assert (E26 : getr R5 (reg 26) = Z_to_bv 64 F) by (rewrite (RK 26%nat) by inl; exact J26).
  assert (E27 : getr R5 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (RK 27%nat) by inl; exact J27).
  LeanFeed.pfeed P (PNACSP.acsP_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Z1 & Z10 & Z11 & Z12).
  apply (cs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 (set_cs w s3 x' g') sm3 ax3 cr5 fx5 fx6 R5 R6 732764 0xaed4c M6v CTX G LM5 MS6 MG6 FRZ6).
  intros model6 LM6 HID6.
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (IH fx6 R6 M5 model6 LK5 Aw5 (set_cs w s3 x' g') sm3 ax3 cr5); [| rewrite set_cs_src; exact UNn].
  unfold cs_linv. split; [exact LM6|].
  split.
  { unfold lregs.
    split; [exact Z1|].
    split; [rewrite (KS6 2%nat) by inl; exact E2|].
    split; [rewrite (KS6 3%nat) by inl; rewrite (RK 3%nat) by inl; exact J3|].
    split; [rewrite (KS6 4%nat) by inl; rewrite (RK 4%nat) by inl; exact J4|].
    split; [rewrite (KS6 8%nat) by inl; exact E8|].
    split; [rewrite (KS6 9%nat) by inl; exact E9|].
    split; [exact Z10|]. split; [exact Z11|]. split; [exact Z12|].
    split; [rewrite (KS6 18%nat) by inl; exact E18|].
    split; [rewrite (KS6 19%nat) by inl; exact E19|].
    split; [rewrite (KS6 20%nat) by inl; exact E20|].
    split; [rewrite (KS6 21%nat) by inl; exact E21|].
    split; [rewrite (KS6 22%nat) by inl; exact E22|].
    split; [rewrite (KS6 23%nat) by inl; exact E23|].
    split; [rewrite (KS6 24%nat) by inl; exact E24|].
    split; [rewrite (KS6 25%nat) by inl; exact E25|].
    split; [rewrite (KS6 26%nat) by inl; exact E26|].
    rewrite (KS6 27%nat) by inl; exact E27. }
  split; [exact SPL5|].
  split; [unfold PNRA.binv; rewrite set_cs_done, set_cs_stk; exact INV3|].
  split; [exact (ECK5 _ _ EC3)|].
  split; [unfold PNRA.btop_pos; rewrite set_cs_stk; exact TP3|].
  rewrite set_cs_str, set_cs_src.
  split; [clear - SZX SZ3; lia|]. split; [clear - SZX SZ4; lia| exact UN3].
Qed.

(* [comment removed for export] *)
Lemma cs_store K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (n : Z)
      M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 (fx1 : FPState) R1 (d : Z) pre top :
  PNRAa.str_push_back_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1,
      cs_linv L ar HI R M model LBX FF LK Aw cr sp fb cat e s str sm ax w F R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
      PM.unread (PNM.b_src s1) sm1 < n ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K) ->
  cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  PNRA.binv s1 -> PNM.b_stk s1 = pre ++ [top] ->
  jregs R R1 sp fb w F d (PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40) ->
  getr R1 (reg 12) = Z_to_bv 64 (PNM.bs_pos top + d) ->
  spill M1 sp F (fb + 464) (fb + 1024) ->
  PMSPA.ec_at RSEGS M1 (fb + 1024) e cat -> PNRA.btop_pos s s1 ->
  0 <= d <= 1 -> L5.defined M1 (F + 32) d ->
  (d = 1 -> PM.unread (PNM.b_src s1) sm1 < PM.unread (PNM.b_src s) sm /\ PM.unread (PNM.b_src s1) sm1 < n
            /\ PM.vs_size (PNRA.bcs_str w s1) + PM.unread (PNM.b_src s1) sm1 + 1 <= PM.vs_size (PNRA.bcs_str w s) + PM.unread (PNM.b_src s) sm
            /\ PM.vs_size (PNRA.bcs_str w s1) + PM.unread (PNM.b_src s1) sm1 + 1 <= 2 ^ 26) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0xb2e44 M1 model1) K.
Proof.
  intros PB MKE CTX G IH LM INV1 ES JR J12 SPL EC1 TP1 Hd DEF HD1.
  pose proof CTX as (Hw & _). pose proof (PNACSK.bcs_off_rng w Hw) as HOFF.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM)
    as (PF1 & OWN1 & SV1 & U8v1 & WRop1 & U8op1 & SVr1).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 pre top CTX G LM INV1 ES)
    as (TF1 & PT1 & OKt1 & VIN1 & TB11 & TB21 & TB31 & TB41).
  set (MV1 := mrestrict (ahid Aw1 model1) M1) in *.
  set (e1 := PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p46 := (PNM.bs_pos top + d) mod 2 ^ 64).
  unfold pfacts in PF1. destruct PF1 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF1. destruct TF1 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof JR as (J2 & J3 & J4 & J8 & J9 & J10 & J11 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & J25 & J26 & J27).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 HOFF; lia).
  assert (Q44 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Q46 : 0 <= p46 < 2 ^ 64) by (unfold p46; apply Z.mod_pos_bound; clear; lia).
  assert (Q46' : 0 <= p46 <= 18446744073709551615) by (clear - Q46; lia).
  assert (J12' : getr R1 (reg 12) = Z_to_bv 64 p46) by (rewrite J12; unfold p46; symmetry; apply zb_mod64).
  LeanFeed.pfeed P (PNACSP.acsS_conc fx1 R1 MV1 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e1 | 43%nat => PNM.bs_pos top | 44%nat => d | 46%nat => p46 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & CP3).
  apply (PNACSK.cs_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 fx3 R1 R3 0xb2e44 0xb2e48 M3v pre top p46 CTX G LM INV1 ES MS3 MG3 FRZ3 CP3 Q46).
  intros M3 model3 LM3 HID3 VIS3 FR3 MGM3 ECK3.
  set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p46 (PNM.bs_type top) (PNM.bs_idx top)) in *.
  set (s3 := PNBO.set_stk s1 (pre ++ [top'])) in *.
  assert (OK' : PNM.bstate_ok top').
  { destruct OKt1 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    split; [exact X1|]. split; [exact X2|]. split; [exact Q46|]. split; [exact X4| exact X5]. }
  assert (INV3 : PNRA.binv s3) by (apply (PNACSK.binv_set_stk_top s1 pre top top' INV1 ES OK'); reflexivity).
  assert (ES3 : PNM.b_stk s3 = pre ++ [top']) by reflexivity.
  assert (TP3 : PNRA.btop_pos s s3).
  { apply (PNACSK.btop_pos_trans s s1 s3 TP1). apply (PNACSK.btop_pos_set_stk s1 pre top top' ES OK'); reflexivity. }
  assert (AGX : forall a, (a < e1 - 40 \/ e1 <= a) -> 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hr. apply FR3; [exact Hr|]. fold e1. clear - Ha; lia. }
  assert (SPL3 : spill M3 sp F (fb + 464) (fb + 1024)).
  { apply (PNACSK.spill_agree M1 M3 sp F (fb + 464) (fb + 1024) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia) SPL). intros a Ha. apply AGX; [clear - Ha tf9; lia| clear - Ha pf4; lia]. }
  assert (JR3 : jregs R R3 sp fb w F d (PNM.b_sb s3 + 40 * Z.of_nat (length pre) + 40)).
  { change (PNM.b_sb s3) with (PNM.b_sb s1). fold e1. unfold jregs.
    split; [rewrite (KS3 2%nat) by inl; exact J2|].
    split; [rewrite (KS3 3%nat) by inl; exact J3|].
    split; [rewrite (KS3 4%nat) by inl; exact J4|].
    split; [rewrite (KS3 8%nat) by inl; exact J8|].
    split; [rewrite (KS3 9%nat) by inl; exact J9|].
    split; [rewrite (KS3 10%nat) by inl; exact J10|].
    split; [rewrite (KS3 11%nat) by inl; exact J11|].
    split; [rewrite (KS3 18%nat) by inl; exact J18|].
    split; [rewrite (KS3 19%nat) by inl; exact J19|].
    split; [rewrite (KS3 20%nat) by inl; exact J20|].
    split; [rewrite (KS3 21%nat) by inl; exact J21|].
    split; [rewrite (KS3 22%nat) by inl; exact J22|].
    split; [rewrite (KS3 23%nat) by inl; exact J23|].
    split; [rewrite (KS3 24%nat) by inl; exact J24|].
    split; [rewrite (KS3 25%nat) by inl; exact J25|].
    split; [rewrite (KS3 26%nat) by inl; exact J26|].
    rewrite (KS3 27%nat) by inl; exact J27. }
  assert (DC : d = 0 \/ d = 1) by (clear - Hd; lia).
  destruct DC as [D0|D1].
  - subst d.
    exact (cs_arm_eof K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK1 Aw1 s3 sm1 ax1 cr1 fx3 R3 pre top' MKE CTX G LM3 INV3 ES3 JR3 SPL3 (ECK3 _ _ EC1) TP3).
  - subst d. destruct (HD1 eq_refl) as (UNa & UNb & SZa & SZb).
    destruct (PMCG.u8_of_defined RSEGS M1 (F + 32) ltac:(clear - pf13; lia) ltac:(clear - pf13; lia) DEF) as (cb & Hcb & CB).
    assert (CB3 : L5.u8_at RSEGS M3 (F + 32) cb).
    { apply (L5C.u8_at_agree RSEGS M1 M3); [| clear - pf13; lia| clear - pf13; lia| exact CB]. intros j Hj. apply AGX; [clear - Hj tf11; lia| clear - Hj pf13; lia]. }
    destruct (Z.eq_dec cb 0) as [C0|CN].
    + subst cb.
      apply (cs_arm_nul K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK1 Aw1 s3 sm1 ax1 cr1 fx3 R3 pre top' CTX G LM3 INV3 ES3 JR3 SPL3 (ECK3 _ _ EC1) TP3 CB3).
      * exact UNa.
      * unfold s3. rewrite set_stk_str. exact SZa.
    + apply (cs_arm_pb K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 n M3 model3 LK1 Aw1 s3 sm1 ax1 cr1 fx3 R3 cb pre top' PB CTX G IH LM3 INV3 ES3 JR3 SPL3 (ECK3 _ _ EC1) TP3 CB3).
      * clear - Hcb CN; lia.
      * exact UNa.
      * exact UNb.
      * unfold s3. rewrite set_stk_str. exact SZa.
      * unfold s3. rewrite set_stk_str. exact SZb.
Qed.

(* [comment removed for export] *)
Lemma cs_loop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  PNRAa.src_read_spec L ar HI -> PNRAa.str_push_back_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> cs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  forall n, 0 <= n -> forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1,
    cs_linv L ar HI R M model LBX FF LK Aw cr sp fb cat e s str sm ax w F R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
    PM.unread (PNM.b_src s1) sm1 = n ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K.
Proof.
  intros SR PB MKE CTX G n. pattern n. apply (well_founded_ind (Zwf_well_founded 0)). clear n.
  intros n IHn Hn fx1 R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 LI EN.
  assert (IH : (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1,
      cs_linv L ar HI R M model LBX FF LK Aw cr sp fb cat e s str sm ax w F R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
      PM.unread (PNM.b_src s1) sm1 < n ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K)).
  { intros fx2 R2 M2' model2' LK2' Aw2' s2 sm2 ax2 cr2 LI2 LT2.
    pose proof LI2 as ((_ & RPx & _) & _). pose proof RPx as (PAx & IAx & _).
    pose proof (PNACSK.unread_nonneg _ _ _ _ _ _ _ PAx IAx) as UNx.
    exact (IHn (PM.unread (PNM.b_src s2) sm2) ltac:(unfold Zwf; clear - UNx LT2 Hn; lia) UNx fx2 R2 M2' model2' LK2' Aw2' s2 sm2 ax2 cr2 LI2 eq_refl). }
  clear IHn.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _). pose proof (PNACSK.bcs_off_rng w Hw) as HOFF.
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct LI as (LM & LR & SPL & INV1 & EC1 & TP1 & SZ1 & SZ2 & UN1).
  destruct LR as (X1 & X2 & X3 & X4 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
  apply (PNACSK.cs_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 fx1 R1 0xb2e08 SR CTX G LM X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact X2. }
  { rewrite X3. exact Rgp. }
  { rewrite X4. exact Rtp. }
  { exact X10. } { exact X11. } { exact X12. }
  intros fx2 R2 M3 model3 LK3 Aw3 src3 sm3 d RP2 Y10 Hd UNR3 RD1 RD0 DEF3 QC3 LM3 AG3 ECK3.
  set (s3 := PNM.with_srcB s1 src3) in *.
  assert (INV3 : PNRA.binv s3) by exact INV1.
  pose proof TP1 as (pre & c0 & top & ES0 & ES & _).
  assert (ES3 : PNM.b_stk s3 = pre ++ [top]) by exact ES.
  assert (TP3 : PNRA.btop_pos s s3) by exact TP1.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax1 cr1 CTX G LM3)
    as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax1 cr1 pre top CTX G LM3 INV3 ES3)
    as (TF3 & PT3 & OKt3 & VIN3 & TB13 & TB23 & TB33 & TB43).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  change (PNM.b_sb s3) with (PNM.b_sb s1) in *.
  set (e3 := PNM.b_sb s1 + 40 * Z.of_nat (length pre) + 40) in *.
  unfold pfacts in PF3. destruct PF3 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF3. destruct TF3 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  assert (SPL3 : spill M3 sp F (fb + 464) (fb + 1024)).
  { apply (PNACSK.spill_agree M1 M3 sp F (fb + 464) (fb + 1024) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia) SPL). intros a Ha. apply AG3. clear - Ha; lia. }
  pose proof SPL3 as (SP1 & SP2 & SP3 & SP4).
  pose proof (SV3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia) SP1) as SP1v.
  pose proof (SV3 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia) SP2) as SP2v.
  pose proof (SV3 (sp - 144) (fb + 1024) ltac:(clear; lia) ltac:(clear; lia) SP3) as SP3v.
  pose proof (SV3 (sp - 152) (fb + 464) ltac:(clear; lia) ltac:(clear; lia) SP4) as SP4v.
  assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg k) = getr R1 (reg k)).
  { intros k Hk. exact (L5SAR.cs_of_preserved R1 R2 k RP2 Hk). }
  assert (E2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 2%nat) by inl; exact X2).
  assert (E8 : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (RK 8%nat) by inl; exact X8).
  assert (E9 : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 9%nat) by inl; exact X9).
  assert (E18 : getr R2 (reg 18) = Z_to_bv 64 40) by (rewrite (RK 18%nat) by inl; exact X18).
  assert (E19 : getr R2 (reg 19) = Z_to_bv 64 1) by (rewrite (RK 19%nat) by inl; exact X19).
  assert (E20 : getr R2 (reg 20) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off w)) by (rewrite (RK 20%nat) by inl; exact X20).
  assert (E21 : getr R2 (reg 21) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (RK 21%nat) by inl; exact X21).
  assert (E22 : getr R2 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (RK 22%nat) by inl; exact X22).
  assert (E23 : getr R2 (reg 23) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (RK 23%nat) by inl; exact X23).
  assert (E24 : getr R2 (reg 24) = Z_to_bv 64 (fb + 464 + 400)) by (rewrite (RK 24%nat) by inl; exact X24).
  assert (E25 : getr R2 (reg 25) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880)) by (rewrite (RK 25%nat) by inl; exact X25).
  assert (E26 : getr R2 (reg 26) = Z_to_bv 64 F) by (rewrite (RK 26%nat) by inl; exact X26).
  assert (E27 : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (RK 27%nat) by inl; exact X27).
  assert (Q34 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 HOFF; lia).
  assert (Q44 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  LeanFeed.pfeed P (PNACSP.acsL_conc fx2 R2 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e3 | 43%nat => PNM.bs_pos top | 44%nat => d | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z11 & Z12).
  apply (cs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax1 cr1 fx2 fx4 R2 R4 0xb2e08 0xb2e44 M4v CTX G LM3 MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  apply (cs_store K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 n M3 model4 LK3 Aw3 s3 sm3 ax1 cr1 fx4 R4 d pre top PB MKE CTX G IH LM4 INV3 ES3).
  - change (PNM.b_sb s3) with (PNM.b_sb s1). fold e3. unfold jregs.
    split; [rewrite (KS4 2%nat) by inl; exact E2|].
    split; [rewrite (KS4 3%nat) by inl; rewrite (RK 3%nat) by inl; exact X3|].
    split; [rewrite (KS4 4%nat) by inl; rewrite (RK 4%nat) by inl; exact X4|].
    split; [rewrite (KS4 8%nat) by inl; exact E8|].
    split; [rewrite (KS4 9%nat) by inl; exact E9|].
    split; [rewrite (KS4 10%nat) by inl; exact Y10|].
    split; [exact Z11|].
    split; [rewrite (KS4 18%nat) by inl; exact E18|].
    split; [rewrite (KS4 19%nat) by inl; exact E19|].
    split; [rewrite (KS4 20%nat) by inl; exact E20|].
    split; [rewrite (KS4 21%nat) by inl; exact E21|].
    split; [rewrite (KS4 22%nat) by inl; exact E22|].
    split; [rewrite (KS4 23%nat) by inl; exact E23|].
    split; [rewrite (KS4 24%nat) by inl; exact E24|].
    split; [rewrite (KS4 25%nat) by inl; exact E25|].
    split; [rewrite (KS4 26%nat) by inl; exact E26|].
    rewrite (KS4 27%nat) by inl; exact E27.
  - exact Z12.
  - exact SPL3.
  - exact (ECK3 _ _ EC1).
  - exact TP3.
  - exact Hd.
  - exact DEF3.
  - intros D1. unfold s3. rewrite with_src_str. cbn [PNM.with_srcB PNM.b_src]. rewrite UNR3. subst d. subst n.
    split; [clear - UN1; lia|]. split; [clear; lia|]. split; [clear - SZ1; lia| clear - SZ2; lia].
Qed.

(* [comment removed for export] *)
Theorem read_cstring_ok : PNRAa.src_read_spec L ar HI -> PNRAa.str_push_back_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNRAa.read_cstring_spec L ar HI.
Proof.
  intros SR PB MKE. unfold PNRAa.read_cstring_spec, PNRA.read_cstring_spec, PNRA.brun_spec. intros w Hw.
  intros fx R M model K LBX FF LK Aw cr sp r fb cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  assert (CTX : cs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11 & A12 & SZ).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 22528 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 22528 160 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  assert (Hbo : 344 <= PNRA.bcs_off w <= 368) by (unfold PNRA.bcs_off, PNM.OFF_NB, PNM.OFF_TB; destruct Hw as [-> | ->]; cbn; clear; lia).
  LeanFeed.pfeed P (PNACSP.acsA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oec | 35%nat => op + PNRA.bcs_off w | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption | clear - SL160 SHI SPT; lia | clear - O1; lia | clear - O1 Hbo; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T13 & T18 & T20 & T27
                 & C144 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_read_cstring PMA.AN) with 0xb2cd0.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb2cd0 R1 0x5dc2c M1v (fun a => sp - 160 <= a < sp - 160 + 160) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 22528 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 22528 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 22528 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M M1 (fun a => sp - 160 <= a < sp - 160 + 160) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 22528 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 22528 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  assert (OEC1 : L5.u64_at RSEGS M1 (sp - 144) oec) by (apply SV1; [clear; lia| clear; lia| exact C144]).
  clear C144 C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 5 FF LK 0 FRM); [clear; lia| left; reflexivity]).
  change 0x5dc2c with (PMA.SM_PC 0).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PNM.bparser_own s) FF LK cr Aw sp 22528 (sp - 160) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb2d48 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 160) with (sp + (-10) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk0. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 0) with 64 in *. change (64 / 8) with 8 in *. change (64 - 8) with 56 in *.
  pose proof G as G'. destruct G' as [_ _ _ _ _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 0) with 64 in *.
  pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 22528 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 160 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 22528 160 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 (op + PNRA.bcs_off w)) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B18R : getr R2 (reg 18) = Z_to_bv 64 op) by (rewrite (R2c 18%nat) by inl; exact T18).
  assert (B27R : getr R2 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (R2c 27%nat) by inl; exact T27).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64 /\ 0 <= op + PNRA.bcs_off w < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 GFR GFLR Hbo; unfold oec, op in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g & Q0h).
  assert (Q1 : 140735332487328 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Q3 : 6905856 <= F <= 140737488355264) by (clear - GFR; lia).
  assert (Q4 : (sp - 160) + 160 <= F \/ F + 64 <= (sp - 160)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  assert (Q2 : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  LeanFeed.pfeed P (PNACSP.acsB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 34%nat => oec | 35%nat => op + PNRA.bcs_off w | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y18 & Y19 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26
                 & UC & SH3 & SH2 & SH1 & SH0 & SAVP & SH7 & SH6 & SH5 & SH4 & HPC & HDESC & HMAG & SAVF & SAVG & D24 & D33).
  set (W3 := fun a => (sp - 112 <= a < sp - 112 + 8) \/ (F <= a < F + 24) \/ (F + 32 <= a < F + 33) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8) \/ (sp - 136 <= a < sp - 136 + 8) \/ (sp - 152 <= a < sp - 152 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb2d48 R3 0xaed4c M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia
                    | intros X; apply Hn; right; right; left; clear - X; lia| intros X; apply Hn; right; right; right; left; clear - X; lia
                    | intros X; apply Hn; right; right; right; right; left; clear - X; lia| intros X; apply Hn; right; right; right; right; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|[X|[X|[X|[X|X]]]]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
    - destruct Wa as [X|[X|[X|[X|[X|X]]]]]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 22528 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|[X|[X|[X|X]]]]].
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia.
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - apply (NCS0 a); [clear - X; lia| exact Hc]. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|[X|[X|[X|[X|X]]]]]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 22528 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 22528 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 22528 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4; 22; 23; 25; 26]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 22; 23; 25; 26]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 22528 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (VIS3' : PMSPA.visitor_at RSEGS PMA.AD M3 ov).
  { apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 22528 [] M M3 EK03f PMKA.wapp_nil FRB ov); [| intros i _ r0 []| exact VIS].
    apply (PNAPAR.aobj_fbB FF fb ov 8 FOK); unfold ov; clear; lia. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 22528 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 22528 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV4 : avis H2 (F / 8 + 2147450884) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 8); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450884) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450884 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450884) 1 AV4 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450884) 1) by (apply (proj1 UV); exact SH4). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNACSK.pre_after_call L ar LB FF sp 22528 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : cs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold cs_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNACSK.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNACSK.credit_keep_refl|]. split; [exact U8c| reflexivity]. }
  assert (SPL3 : spill M3 sp F op oec).
  { pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (_ & _ & _ & _ & _ & _ & SVr3).
    fold H2 in HID3. rewrite HID3, VIS3 in SVr3. unfold spill.
    split; [apply (SVr3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia)); exact SAVF|].
    split; [apply (SVr3 (sp - 136) F ltac:(clear; lia) ltac:(clear; lia)); exact SAVG|].
    split; [| apply (SVr3 (sp - 152) op ltac:(clear; lia) ltac:(clear; lia)); exact SAVP].
    apply (L5C.u64_at_agree RSEGS M1 M3); [| clear - SL160 SPT; lia| clear - SHI SPT; lia| exact OEC1].
    intros j Hj. rewrite FR3; [apply AGF; clear - Hj; lia| clear - Hj SL160 SHI SPT; lia| intros [X|[X|[X|[X|[X|X]]]]]; clear - X Hj GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  apply (PNACSK.cs_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 R3 0xb2e08 SR CTX G LM3 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { rewrite (KS3 2%nat) by inl. exact B2R. }
  { rewrite R3gp. exact Rgp. }
  { rewrite R3tp. exact Rtp. }
  { exact Y10. } { exact Y11. } { exact Y12. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 d RP4 Y10d Hd UNR4 RD1 RD0 DEF4 QC4 LM4 AG4 ECK4.
  set (s4 := PNM.with_srcB s src4) in *.
  assert (INV4 : PNRA.binv s4) by exact INV.
  pose proof (PNACSK.btop_pos_refl s INV) as TP0.
  pose proof TP0 as (pre & top & c0 & ES & _).
  assert (ES4 : PNM.b_stk s4 = pre ++ [top]) by exact ES.
  assert (TP4 : PNRA.btop_pos s s4) by exact TP0.
  pose proof (PNACSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax cr CTX G LM4)
    as (PF4 & OWN4 & SV4 & U8v4 & WRop4 & U8op4 & SVr4).
  pose proof (PNACSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax cr pre top CTX G LM4 INV4 ES4)
    as (TF4 & PT4 & OKt4 & VIN4 & TB14 & TB24 & TB34 & TB44).
  set (MV4 := mrestrict (ahid Aw4 model4) M4) in *.
  change (PNM.b_sb s4) with (PNM.b_sb s) in *.
  set (e4 := PNM.b_sb s + 40 * Z.of_nat (length pre) + 40) in *.
  unfold pfacts in PF4. destruct PF4 as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF4. destruct TF4 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  assert (RK : forall k, In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg k) = getr R3 (reg k)).
  { intros k Hk. exact (L5SAR.cs_of_preserved R3 R4 k RP4 Hk). }
  assert (E2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R).
  assert (E8 : getr R4 (reg 8) = Z_to_bv 64 sp) by (rewrite (RK 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R).
  assert (E9 : getr R4 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (RK 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R).
  assert (E18 : getr R4 (reg 18) = Z_to_bv 64 40) by (rewrite (RK 18%nat) by inl; exact Y18).
  assert (E19 : getr R4 (reg 19) = Z_to_bv 64 1) by (rewrite (RK 19%nat) by inl; exact Y19).
  assert (E20 : getr R4 (reg 20) = Z_to_bv 64 (fb + 464 + PNRA.bcs_off w)) by (rewrite (RK 20%nat) by inl; rewrite (KS3 20%nat) by inl; exact B20R).
  assert (E21 : getr R4 (reg 21) = Z_to_bv 64 (F / 8 + 2147450880)) by (rewrite (RK 21%nat) by inl; exact Y21).
  assert (E22 : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (RK 22%nat) by inl; exact Y22).
  assert (E23 : getr R4 (reg 23) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (RK 23%nat) by inl; exact Y23).
  assert (E24 : getr R4 (reg 24) = Z_to_bv 64 (fb + 464 + 400)) by (rewrite (RK 24%nat) by inl; exact Y24).
  assert (E25 : getr R4 (reg 25) = Z_to_bv 64 ((fb + 464 + 400) / 8 + 2147450880)) by (rewrite (RK 25%nat) by inl; exact Y25).
  assert (E26 : getr R4 (reg 26) = Z_to_bv 64 F) by (rewrite (RK 26%nat) by inl; exact Y26).
  assert (E27 : getr R4 (reg 27) = Z_to_bv 64 2147450880) by (rewrite (RK 27%nat) by inl; rewrite (KS3 27%nat) by inl; exact B27R).
  assert (Q34 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q35 : 0 <= fb + 464 + PNRA.bcs_off w < 2 ^ 64) by (clear - pf7 Hbo; lia).
  assert (Q44 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  LeanFeed.pfeed P (PNACSP.acsR_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 1024 | 35%nat => fb + 464 + PNRA.bcs_off w | 42%nat => e4 | 43%nat => PNM.bs_pos top | 44%nat => d | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNACSP.aligned; assumption]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z11 & Z12).
  apply (PNACSK.cs_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax cr fx4 fx5 R4 R5 0xb2e08 0xb2e44 M5v
           (fun _ => False) CTX G LM4 MS5 MG5 (fun a Ha _ => FRZ5 a Ha)).
  { intros a []. }
  intros M5 model5 LM5 HID5 VIS5 FR5 MGM5 ECK5.
  assert (SPL5 : spill M5 sp F (fb + 464) (fb + 1024)).
  { apply (PNACSK.spill_agree M3 M5 sp F (fb + 464) (fb + 1024) ltac:(clear - pf4; lia) ltac:(clear - pf4; lia) SPL3). intros a Ha.
    rewrite FR5; [apply AG4; clear - Ha; lia| clear - Ha pf4; lia| intros []]. }
  assert (IH : forall (fx1 : FPState) R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1,
      cs_linv L ar HI R M model LBX FF LK Aw cr sp fb cat e s str sm ax w F R1 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
      PM.unread (PNM.b_src s1) sm1 < PM.unread (PNM.b_src s) sm ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 (pa_src_read PMA.AD) M1 model1) K).
  { intros fxa Ra Ma modela LKa Awa sa sma axa cra LI _.
    pose proof LI as ((_ & RPx & _) & _). pose proof RPx as (PAx & IAx & _).
    pose proof (PNACSK.unread_nonneg _ _ _ _ _ _ _ PAx IAx) as UNx.
    exact (cs_loop K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 SR PB MKE CTX G (PM.unread (PNM.b_src sa) sma) UNx fxa Ra Ma modela LKa Awa sa sma axa cra LI eq_refl). }
  apply (cs_store K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (PM.unread (PNM.b_src s) sm) M5 model5 LK4 Aw4 s4 sm4 ax cr fx5 R5 d pre top PB MKE CTX G IH LM5 INV4 ES4).
  - change (PNM.b_sb s4) with (PNM.b_sb s). fold e4. unfold jregs.
    split; [rewrite (KS5 2%nat) by inl; exact E2|].
    split; [rewrite (KS5 3%nat) by inl; rewrite (RK 3%nat) by inl; exact R3gp|].
    split; [rewrite (KS5 4%nat) by inl; rewrite (RK 4%nat) by inl; exact R3tp|].
    split; [rewrite (KS5 8%nat) by inl; exact E8|].
    split; [rewrite (KS5 9%nat) by inl; exact E9|].
    split; [rewrite (KS5 10%nat) by inl; exact Y10d|].
    split; [exact Z11|].
    split; [rewrite (KS5 18%nat) by inl; exact E18|].
    split; [rewrite (KS5 19%nat) by inl; exact E19|].
    split; [rewrite (KS5 20%nat) by inl; exact E20|].
    split; [rewrite (KS5 21%nat) by inl; exact E21|].
    split; [rewrite (KS5 22%nat) by inl; exact E22|].
    split; [rewrite (KS5 23%nat) by inl; exact E23|].
    split; [rewrite (KS5 24%nat) by inl; exact E24|].
    split; [rewrite (KS5 25%nat) by inl; exact E25|].
    split; [rewrite (KS5 26%nat) by inl; exact E26|].
    rewrite (KS5 27%nat) by inl; exact E27.
  - exact Z12.
  - exact SPL5.
  - apply ECK5. apply ECK4. exact EC3.
  - exact TP4.
  - exact Hd.
  - apply (L5.defined_grows M4 M5 _ _ MGM5). exact DEF4.
  - intros D1. unfold s4. rewrite with_src_str. cbn [PNM.with_srcB PNM.b_src]. rewrite UNR4. subst d.
    split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia| clear - SZ; lia].
Qed.

End WithHeap.
End PNACS.
