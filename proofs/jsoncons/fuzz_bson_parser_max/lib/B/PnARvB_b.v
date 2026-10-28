(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIface
     AsanAcct AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvBP_b PnARvB2P_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnARvBv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PnARvK_b PnARvKB_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVB.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK. Import PNARVKB.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma u32_of_defined (M : word -> option byte) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 -> exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 4%nat a Ha ltac:(cbn; Lia.lia) ltac:(intros i Hi; apply D; cbn in Hi; Lia.lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [Lia.lia|]. unfold L5.u32_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| Lia.lia].
Qed.

(* [comment removed for export] *)
Lemma rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

Lemma sh_apart e F : e mod 8 = 0 -> F / 8 * 8 = F -> ((e - 40) + 40 <= F \/ F + 512 <= (e - 40)) ->
  ((((e - 24) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= (((e - 24) / 8) + 2147450880)).
Proof.
  intros He HF [X|X].
  - left. assert ((e - 24) / 8 < F / 8) by (apply Z.div_lt_upper_bound; [Lia.lia| rewrite Z.mul_comm, HF; Lia.lia]). Lia.lia.
  - right. assert (F / 8 + 64 <= (e - 24) / 8) by (apply Z.div_le_lower_bound; [Lia.lia| Lia.lia]). Lia.lia.
Qed.


(* [comment removed for export] *)
Lemma cell_agree (M M' : mem) a v : 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.u64_at RSEGS M' a v.
Proof.
  intros H0 H1 C1 AG. eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; clear - Hj; lia | exact H0 | exact H1].
Qed.

(* [comment removed for export] *)
Lemma bin_err1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb1628 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb1628 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDBREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDBREGS. kin. }
  pose proof (midb_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY1c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb1628 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - left. exists 1. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma bin_err2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb1744 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 6 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb1744 6 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDBREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDBREGS. kin. }
  pose proof (midb_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY2c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb1744 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - left. exists 6. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma bin_err3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb176c -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb176c 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDBREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDBREGS. kin. }
  pose proof (midb_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY3c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb176c 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - left. exists 1. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma bin_err4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb1798 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb1798 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDBREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDBREGS. kin. }
  pose proof (midb_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY4c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb1798 0 M9v CTX G LM5 MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
  - left; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - left. exists 1. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma bin_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R3 sp fb F ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNRA.bb_room s3 sm3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0a5c M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 EC3 TP3 ROOM3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (U10 & WR8 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY5c_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb0a5c 1 M9v CTX G LM MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia| intros X; apply N3; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO1.
  - right; reflexivity.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact J2.
  - rewrite (KS9 8%nat) by inl. exact J8.
  - rewrite (KS9 19%nat) by inl. exact J19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact J3.
    + rewrite (KS9 4%nat) by inl. exact J4.
  - right. split; [exact EC3|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact TP3.
  - exact INV3.
  - exact (btop_len s s3 TP3).
  - intros _ _. exact ROOM3.
Qed.

(* [comment removed for export] *)
Lemma bin_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 (ptr len : Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R3 sp fb F ->
  getr R3 (reg 10) = Z_to_bv 64 ptr -> getr R3 (reg 11) = Z_to_bv 64 (F + 32) -> getr R3 (reg 24) = Z_to_bv 64 len ->
  0 <= ptr < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> L5.u64_at RSEGS M3 (sp - 144) (F + 336) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNRA.bb_room s3 sm3 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0a00 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X10 X11 X24 Hptr Hlen SUB3 EC3 TP3 ROOM3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J25 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _ & SV3 & _).
  pose proof (PNARVKB.sfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (SF1 & SF2 & SF3 & SF4 & SF5 & SF6).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 136 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 128 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VZ128 & _).
  change ((1251456 + 136) / 8 + 2147450880) with 2147607329 in VFX. change ((1251456 + 128) / 8 + 2147450880) with 2147607328 in VZ128.
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (SUBv : L5.u64_at RSEGS MV3 (sp - 144) (F + 336)) by (apply SV3; [clear; lia| clear; lia| exact SUB3]).
  assert (DEFP : L5.defined MV3 (F + 336) 1) by (apply (L5.defined_sub MV3 F 512); [assumption| clear; lia| clear; lia]).
  assert (QF : 0 <= F + 336 /\ F + 336 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= F <= _ |- _ => clear - H; lia end).
  destruct (PMCG.u8_of_defined RSEGS MV3 (F + 336) (proj1 QF) (proj2 QF) DEFP) as (v43 & Hv43 & PAY).
  assert (Hv43' : 0 <= v43 <= 255) by (clear - Hv43; lia).
  assert (Hv43'' : 0 <= v43 < 2 ^ 64) by (clear - Hv43; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY5b_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 43%nat => v43 | 45%nat => ptr | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  apply (PNARVKB.rv_piece_scr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb0a00 0xb0a5c M9v
           (fun a => F + 32 <= a < F + 32 + 16 \/ F / 8 + 2147450880 + 4 <= a < F / 8 + 2147450880 + 4 + 2 \/ sp - 176 <= a < sp - 176 + 16) CTX G LM MS9 MG9).
  { intros a Ha N. apply FRZ9; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a [X|[X|X]]; [right; left; clear - X; lia| right; right; left; clear - X; lia| right; right; right; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  apply (bin_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx9 R9 CTX G LM4 INV3).
  - apply (midb_keep R R3 R9 sp fb F MID3). unfold MIDBREGS. kks KS9.
  - apply ECK4. exact EC3.
  - exact TP3.
  - exact ROOM3.
Qed.

(* [comment removed for export] *)
Lemma bin_pos3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (ptr len : Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midb R R5 sp fb F ->
  getr R5 (reg 10) = Z_to_bv 64 ptr -> getr R5 (reg 24) = Z_to_bv 64 len -> 0 <= ptr < 2 ^ 64 -> 0 <= len <= 2147483647 ->
  ecsp M5 sp fb -> L5.u64_at RSEGS M5 (sp - 144) (F + 336) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> PNRA.bb_room s5 sm5 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb09b0 M5 model5) K.
Proof.
  intros CTX G LM5 INV5 MID5 X10 X24 Hptr Hlen ECS5 SUB5 EC5 TP5 ROOM5.
  pose proof TP5 as (pre & c0 & top & _ & ES5 & _).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _ & SV5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (PNM.bs_pos top + len) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (ECSv : L5.u64_at RSEGS MV5 (sp - 136) (fb + 464 + 16)) by (apply SV5; [clear; lia| clear; lia| exact ECS5]).
  assert (Q48 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY5a_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 38%nat => e5 | 39%nat => PNM.bs_pos top | 45%nat => ptr | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & Y11 & Y12 & Y13 & CP6).
  apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb09b0 0xb0a00 M6v pre top p5
           CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
  intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
  set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
  set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
  assert (OK' : PNM.bstate_ok top').
  { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
    split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
  assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
  assert (TP7 : PNRA.btop_pos s s7).
  { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
  assert (FRS7 : forall i, sp - 160 <= i < sp - 104 -> M7 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i)).
  { intros i Hi. apply FR7; [match goal with H : 140735332487392 <= sp <= _ |- _ => clear - Hi H; lia end|]. intros X. fold e5 in X. clear - X Hi tf9. lia. }
  assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
  apply (bin_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 ptr len CTX G LM7 INV7).
  - apply (midb_keep R R5 R6 sp fb F MID5). unfold MIDBREGS. kks KS6.
  - rewrite (KS6 10%nat) by inl. exact X10.
  - exact Y11.
  - rewrite (KS6 24%nat) by inl. exact X24.
  - exact Hptr.
  - exact Q48.
  - apply (cell_agree M5 M7 (sp - 144) (F + 336)); [clear - QSP; lia| clear - QSP; lia| exact SUB5|]. intros i Hi. apply FRS7. clear - Hi; lia.
  - apply ECK7. exact EC5.
  - exact TP7.
  - exact ROOM5.
Qed.

(* [comment removed for export] *)
Lemma bin_fork4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (ptr n len : Z) :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midb R R5 sp fb F ->
  getr R5 (reg 10) = Z_to_bv 64 ptr -> getr R5 (reg 11) = Z_to_bv 64 n -> getr R5 (reg 24) = Z_to_bv 64 len ->
  0 <= ptr < 2 ^ 64 -> 0 <= n <= len -> 0 <= len <= 2147483647 ->
  ecsp M5 sp fb -> L5.u64_at RSEGS M5 (sp - 144) (F + 336) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> (n = len -> PNRA.bb_room s5 sm5) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb09ac M5 model5) K.
Proof.
  intros MKE CTX G LM5 INV5 MID5 X10 X11 X24 Hptr Hn Hlen ECS5 SUB5 EC5 TP5 ROOM5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _ & SV5 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (ECSv : L5.u64_at RSEGS MV5 (sp - 136) (fb + 464 + 16)) by (apply SV5; [clear; lia| clear; lia| exact ECS5]).
  assert (Q46 : 0 <= n < 2 ^ 64) by (clear - Hn Hlen; lia).
  assert (Q48 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (R46 : 0 <= n <= 2147483647) by (clear - Hn Hlen; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY4b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 45%nat => ptr | 46%nat => n | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [(MS6 & KS6 & CND)|(MS6 & KS6 & Y1 & Y10 & Y11 & CND)]).
  - (* [comment removed for export] *)
    assert (Enl : n = len).
    { destruct (Z.eq_dec n len) as [Y|Y]; [exact Y| exfalso].
      assert (E1 : (n - len) mod 2 ^ 64 = n - len + 2 ^ 64) by (symmetry; apply (Z.mod_unique_pos _ _ (-1)); clear - Hn Hlen Y; Lia.lia).
      rewrite E1 in CND. clear - CND Hn Hlen. Lia.lia. }
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb09ac 0xb09b0 M6v CTX G LM5 MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (bin_pos3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 ptr len CTX G LM6 INV5).
    + apply (midb_keep R R5 R6 sp fb F MID5). unfold MIDBREGS. kks KS6.
    + rewrite (KS6 10%nat) by inl. exact X10.
    + rewrite (KS6 24%nat) by inl. exact X24.
    + exact Hptr.
    + exact Hlen.
    + exact ECS5.
    + exact SUB5.
    + exact EC5.
    + exact TP5.
    + exact (ROOM5 Enl).
  - (* [comment removed for export] *)
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb09ac 0xae848 M6v CTX G LM5 MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (bin_err4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 MKE CTX G LM6 INV5).
    + apply (midb_keep R R5 R6 sp fb F MID5). unfold MIDBREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + exact EC5.
    + exact (btop_len s s5 TP5).
Qed.

(* [comment removed for export] *)
Lemma bin_rsv K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (len : Z) :
  PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midb R R5 sp fb F ->
  getr R5 (reg 24) = Z_to_bv 64 len -> 0 <= len <= 2147483647 ->
  ecsp M5 sp fb -> L5.u64_at RSEGS M5 (sp - 144) (F + 336) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb099c M5 model5) K.
Proof.
  intros RSV MKE CTX G LM5 INV5 MID5 X24 Hlen ECS5 SUB5 EC5 TP5 BB5.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & RARGS & _ & _ & INV & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct RARGS as (_ & _ & _ & _ & ROOM0).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _ & SV5 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (ECSv : L5.u64_at RSEGS MV5 (sp - 136) (fb + 464 + 16)) by (apply SV5; [clear; lia| clear; lia| exact ECS5]).
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (Q48 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY4a_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fxa R5 Ra 0xb099c 0xb3bfc Mav CTX G LM5 MSa MGa FRZa).
  intros modela LMa HIDa.
  assert (MIDa : midb R Ra sp fb F) by (apply (midb_keep R R5 Ra sp fb F MID5); unfold MIDBREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  assert (LE5 : PM.unread (PNM.b_src s5) sm5 <= PM.unread (PNM.b_src s) sm).
  { destruct LM5 as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE). exact LE. }
  change 0xb3bfc with (PNL.pn_read_span_v PMA.AN).
  apply (PNARVKB.rv_call_rsv L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 modela LK5 Aw5 s5 sm5 ax5 cr5 fxa Ra 0xb09ac len RSV CTX G LMa A1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact A10. }
  { exact A11. }
  { exact A12. }
  { exact Q48. }
  { clear - LE5 UNR. lia. }
  { rewrite BB5. unfold PNRA.bb_room in ROOM0. exact (PGV8.v8_room_mono _ _ _ LE5 ROOM0). }
  intros fx6 R6 M6 model6 LK6 Aw6 src6 bb6 bg6 sm6 cr6 ptr n RP6 Y10 Y11 Hn1 Hn2 CONS6 LOC6 DEF6 ACC6 ROOM6 LE6 LM6 AG6 ECK6.
  set (s6 := PNM.with_src_bb s5 src6 bb6 bg6) in *.
  assert (INV6 : PNRA.binv s6) by exact INV5.
  assert (TP6 : PNRA.btop_pos s s6) by exact TP5.
  assert (RK : forall k, In k MIDBREGS -> getr R6 (reg k) = getr Ra (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved Ra R6 k RP6). revert k Hk. unfold MIDBREGS. kin. }
  assert (E10 : getr R6 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R6 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  apply (bin_fork4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax5 cr6 fx6 R6 (bv_unsigned (getr R6 (reg 10))) n len MKE CTX G LM6 INV6).
  - exact (midb_keep R Ra R6 sp fb F MIDa RK).
  - exact E10.
  - exact Y11.
  - rewrite (L5SAR.cs_of_preserved Ra R6 24%nat RP6) by inl. rewrite (KSa 24%nat) by inl. exact X24.
  - exact (bvu_rng (getr R6 (reg 10))).
  - exact Hn1.
  - exact Hlen.
  - apply (cell_agree M5 M6 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS5|]. intros i Hi. apply AG6. clear - Hi; lia.
  - apply (cell_agree M5 M6 (sp - 144) (F + 336)); [clear - QSP; lia| clear - QSP; lia| exact SUB5|]. intros i Hi. apply AG6. clear - Hi; lia.
  - apply ECK6. exact EC5.
  - exact TP6.
  - intros Enl. unfold PNRA.bb_room, s6. cbn [PNM.with_src_bb PNM.b_bb PNM.b_src]. exact (ROOM6 Enl).
Qed.

(* [comment removed for export] *)
Lemma bin_fork3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (d len : Z) :
  PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midb R R5 sp fb F ->
  getr R5 (reg 10) = Z_to_bv 64 d -> 0 <= d <= 1 -> getr R5 (reg 24) = Z_to_bv 64 len -> 0 <= len <= 2147483647 ->
  ecsp M5 sp fb -> L5.u64_at RSEGS M5 (sp - 144) (F + 336) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb0948 M5 model5) K.
Proof.
  intros RSV MKE CTX G LM5 INV5 MID5 X10 Hd X24 Hlen ECS5 SUB5 EC5 TP5 BB5.
  pose proof TP5 as (pre & c0 & top & _ & ES5 & _).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _ & SV5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (d + PNM.bs_pos top) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (ECSv : L5.u64_at RSEGS MV5 (sp - 136) (fb + 464 + 16)) by (apply SV5; [clear; lia| clear; lia| exact ECS5]).
  assert (Q37 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (Q48 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY3b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => d | 38%nat => e5 | 39%nat => PNM.bs_pos top | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb0948 0xb099c M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    assert (FRS7 : forall i, sp - 160 <= i < sp - 104 -> M7 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i)).
    { intros i Hi. apply FR7; [match goal with H : 140735332487392 <= sp <= _ |- _ => clear - Hi H; lia end|]. intros X. fold e5 in X. clear - X Hi tf9. lia. }
    assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
    apply (bin_rsv K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 len RSV MKE CTX G LM7 INV7).
    + apply (midb_keep R R5 R6 sp fb F MID5). unfold MIDBREGS. kks KS6.
    + rewrite (KS6 24%nat) by inl. exact X24.
    + exact Hlen.
    + apply (cell_agree M5 M7 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS5|]. intros i Hi. apply FRS7. clear - Hi; lia.
    + apply (cell_agree M5 M7 (sp - 144) (F + 336)); [clear - QSP; lia| clear - QSP; lia| exact SUB5|]. intros i Hi. apply FRS7. clear - Hi; lia.
    + apply ECK7. exact EC5.
    + exact TP7.
    + exact BB5.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb0948 0xae848 M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    apply (bin_err3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 MKE CTX G LM7 INV7).
    + apply (midb_keep R R5 R6 sp fb F MID5). unfold MIDBREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + apply ECK7. exact EC5.
    + exact (btop_len s s7 TP7).
Qed.

(* [comment removed for export] *)
Lemma bin_rd2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 (len : Z) :
  PNRAa.src_read_spec L ar HI -> PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R3 sp fb F ->
  getr R3 (reg 24) = Z_to_bv 64 len -> 0 <= len <= 2147483647 ->
  ecsp M3 sp fb ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb092c M3 model3) K.
Proof.
  intros SR RSV MKE CTX G LM3 INV3 MID3 X24 Hlen ECS3 EC3 TP3 BB3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM3) as (PF3 & _ & SV3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (ECSv : L5.u64_at RSEGS MV3 (sp - 136) (fb + 464 + 16)) by (apply SV3; [clear; lia| clear; lia| exact ECS3]).
  pose proof MID3 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (Q48 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY3a_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 48%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12 & SUBW & SHZ).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fxa R3 Ra 0xb092c 0xaed4c Mav
           (fun a => sp - 144 <= a < sp - 144 + 8 \/ F / 8 + 2147450880 + 42 <= a < F / 8 + 2147450880 + 42 + 1) CTX G LM3 MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [X|X]; [left; clear - X; lia| right; right; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM4) as (_ & _ & _ & _ & _ & _ & SVr4).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM4) as (_ & _ & _ & _ & VSH4 & _).
  assert (SUB4 : L5.u64_at RSEGS M4 (sp - 144) (F + 336)).
  { apply SVr4; [clear; lia| clear; lia|]. rewrite HID4, VIS4. exact SUBW. }
  assert (ECS4 : ecsp M4 sp fb).
  { apply (cell_agree M3 M4 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS3|]. intros i Hi. apply FR4; [clear - Hi QSP; lia|].
    intros [X|X]; [clear - X Hi; lia| clear - X Hi DF2 QSP GSLO GSHI GSPT; match goal with H : 140735332487392 <= sp <= _ |- _ => idtac | _ => idtac end; lia]. }
  assert (SHR : 0 <= F / 8 + 2147450922 /\ F / 8 + 2147450922 + 1 <= 2 ^ 64) by (clear - DF1 DF2; lia).
  assert (SH4 : L5.u8_at RSEGS M4 (F / 8 + 2147450922) 1).
  { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M4 (F / 8 + 2147450922) 1 (L5A.avis_sub _ (F / 8 + 2147450880) 64 (F / 8 + 2147450922) 1 VSH4 ltac:(clear; lia) ltac:(clear; lia)) (proj1 SHR) (proj2 SHR))).
    rewrite HID4, VIS4. exact SHZ. }
  assert (ACC : aacc M4 (F + 336) 1).
  { assert (HK : (1 = 8 /\ 1 = 0) \/ (1 <= 1 <= 7 /\ 1 = 1)) by (right; split; [clear; lia| reflexivity]).
    assert (HO8 : 336 mod 8 = 0) by reflexivity. assert (HO0 : 0 <= 336) by (clear; lia). assert (HF0 : 0 <= F) by (clear - GF1; lia).
    apply (aacc_local M4 F 336 1 1 (proj1 GF8) HO8 HO0 HF0 HK).
    change (336 / 8) with 42. replace (F / 8 + 42 + 2147450880) with (F / 8 + 2147450922) by (clear; lia).
    assert (SHR1 : F / 8 + 2147450922 < 65536 \/ 6905856 <= F / 8 + 2147450922) by (right; clear - DF1; lia).
    assert (SHR2 : 0 <= F / 8 + 2147450922 < 2 ^ 64) by (clear - SHR; lia).
    exact (L5ADHR.byte_of_u8 M4 (F / 8 + 2147450922) 1 SH4 SHR1 SHR2). }
  assert (MIDa : midb R Ra sp fb F) by (apply (midb_keep R R3 Ra sp fb F MID3); unfold MIDBREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (PNARVK.rv_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 fxa Ra 0xb0948 336 1 SR CTX G LM4
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC A1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact A10. }
  { exact A11. }
  { exact A12. }
  intros fx5 R5 M5 model5 LK5 Aw5 src5 sm5 d RP5 Y10d Hd UNR5 RD1 RD0 DEF5 QC5 LM5 AG5 ECK5.
  set (s5 := PNM.with_srcB s3 src5) in *.
  assert (INV5 : PNRA.binv s5) by exact INV3.
  assert (TP5 : PNRA.btop_pos s s5) by exact TP3.
  assert (RK : forall k, In k MIDBREGS -> getr R5 (reg k) = getr Ra (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDBREGS. kin. }
  apply (bin_fork3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax3 cr3 fx5 R5 d len RSV MKE CTX G LM5 INV5).
  - exact (midb_keep R Ra R5 sp fb F MIDa RK).
  - exact Y10d.
  - exact Hd.
  - rewrite (L5SAR.cs_of_preserved Ra R5 24%nat RP5) by inl. rewrite (KSa 24%nat) by inl. exact X24.
  - exact Hlen.
  - apply (cell_agree M4 M5 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS4|]. intros i Hi. apply AG5. clear - Hi; lia.
  - apply (cell_agree M4 M5 (sp - 144) (F + 336)); [clear - QSP; lia| clear - QSP; lia| exact SUB4|]. intros i Hi. apply AG5. clear - Hi; lia.
  - apply ECK5. apply ECK4. exact EC3.
  - exact TP5.
  - exact BB3.
Qed.

(* [comment removed for export] *)
Lemma bin_len K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  PNRAa.src_read_spec L ar HI -> PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midb R R3 sp fb F ->
  getr R3 (reg 24) = Z_to_bv 64 (F + 320) ->
  ecsp M3 sp fb ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0924 M3 model3) K.
Proof.
  intros SR RSV MKE CTX G LM3 INV3 MID3 X24 ECS3 EC3 TP3 BB3.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM3) as (PF3 & _ & SV3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  pose proof MID3 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27).
  assert (ECSv : L5.u64_at RSEGS MV3 (sp - 136) (fb + 464 + 16)) by (apply SV3; [clear; lia| clear; lia| exact ECS3]).
  assert (DEFP : L5.defined MV3 (F + 320) 4) by (apply (L5.defined_sub MV3 F 512); [assumption| clear; lia| clear; lia]).
  assert (QF : 0 <= F + 320 /\ F + 320 + 4 <= 2 ^ 64) by (match goal with H : 6905856 <= F <= _ |- _ => clear - H; lia end).
  destruct (u32_of_defined MV3 (F + 320) (proj1 QF) (proj2 QF) DEFP) as (v42 & Hv42 & PAY).
  assert (Hv42' : 0 <= v42 <= 4294967295) by (clear - Hv42; lia).
  assert (Hv42'' : 0 <= v42 < 2 ^ 64) by (clear - Hv42; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVB2P.awvY2_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 42%nat => v42 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVB2P.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [(MS6 & KS6 & Y24 & CND)|(MS6 & KS6 & Y1 & Y10 & Y11 & Y24 & CND)]).
  - (* [comment removed for export] *)
    destruct (PNARVBV.lw_nonneg _ 42%nat v42 CND ltac:(reflexivity) Hv42') as (LT & EV). rewrite EV in Y24.
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx6 R3 R6 0xb0924 0xb092c M6v CTX G LM3 MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (bin_rd2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model6 LK3 Aw3 s3 sm3 ax3 cr3 fx6 R6 v42 SR RSV MKE CTX G LM6 INV3).
    + apply (midb_keep R R3 R6 sp fb F MID3). unfold MIDBREGS. kks KS6.
    + exact Y24.
    + clear - Hv42 LT. lia.
    + exact ECS3.
    + exact EC3.
    + exact TP3.
    + exact BB3.
  - (* [comment removed for export] *)
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx6 R3 R6 0xb0924 0xae848 M6v CTX G LM3 MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (bin_err2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model6 LK3 Aw3 s3 sm3 ax3 cr3 fx6 R6 MKE CTX G LM6 INV3).
    + apply (midb_keep R R3 R6 sp fb F MID3). unfold MIDBREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + exact EC3.
    + exact (btop_len s s3 TP3).
Qed.

(* [comment removed for export] *)
Lemma bin_fork1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (d : Z) :
  PNRAa.src_read_spec L ar HI -> PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> mid R R5 sp fb F ->
  getr R5 (reg 10) = Z_to_bv 64 d -> 0 <= d <= 4 -> getr R5 (reg 24) = Z_to_bv 64 (F + 320) ->
  ecsp M5 sp fb ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb08c4 M5 model5) K.
Proof.
  intros SR RSV MKE CTX G LM5 INV5 MID5 X10 Hd X24 ECS5 EC5 TP5 BB5.
  pose proof TP5 as (pre & c0 & top & _ & ES5 & _).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _ & SV5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (d + PNM.bs_pos top) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (ECSv : L5.u64_at RSEGS MV5 (sp - 136) (fb + 464 + 16)) by (apply SV5; [clear; lia| clear; lia| exact ECS5]).
  assert (Q37 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY1b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => d | 38%nat => e5 | 39%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y11 & Y12 & Y13 & Y23 & Y26 & CND & CP6).
    assert (MID6 : midb R R6 sp fb F).
    { unfold midb. rewrite (KS6 2%nat), (KS6 3%nat), (KS6 4%nat), (KS6 8%nat), (KS6 9%nat), (KS6 18%nat), (KS6 19%nat), (KS6 20%nat), (KS6 21%nat), (KS6 22%nat), (KS6 26%nat), (KS6 27%nat) by inl.
      repeat split; assumption. }
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb08c4 0xb0924 M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    assert (FRS7 : forall i, sp - 160 <= i < sp - 104 -> M7 (Z_to_bv 64 i) = M5 (Z_to_bv 64 i)).
    { intros i Hi. apply FR7; [clear - Hi QSP; lia|]. intros X. fold e5 in X. clear - X Hi tf9. lia. }
    apply (bin_len K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 SR RSV MKE CTX G LM7 INV7 MID6).
    + rewrite (KS6 24%nat) by inl. exact X24.
    + apply (cell_agree M5 M7 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS5|]. intros i Hi. apply FRS7. clear - Hi; lia.
    + apply ECK7. exact EC5.
    + exact TP7.
    + exact BB5.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y13 & Y23 & Y26 & CND & CP6).
    assert (MID6 : midb R R6 sp fb F).
    { unfold midb. rewrite (KS6 2%nat), (KS6 3%nat), (KS6 4%nat), (KS6 8%nat), (KS6 9%nat), (KS6 18%nat), (KS6 19%nat), (KS6 20%nat), (KS6 21%nat), (KS6 22%nat), (KS6 26%nat), (KS6 27%nat) by inl.
      repeat split; assumption. }
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb08c4 0xae848 M6v pre top p5
             CTX G LM5 INV5 ES5 MS6 MG6 FRZ6 CP6 QP5).
    intros M7 model7 LM7 HID7 VIS7 FR7 MGM7 ECK7.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p5 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s7 := PNBO.set_stk s5 (pre ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt5 as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact QP5|]. split; [exact X4| exact X5]. }
    assert (INV7 : PNRA.binv s7) by (apply (PNBKA.binv_set_stk_top s5 pre top top' INV5 ES5 OK'); reflexivity).
    assert (TP7 : PNRA.btop_pos s s7).
    { apply (PNBKA.btop_pos_trans s s5 s7 TP5). apply (PNBKA.btop_pos_set_stk s5 pre top top' ES5 OK'); reflexivity. }
    apply (bin_err1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 MKE CTX G LM7 INV7 MID6).
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + apply ECK7. exact EC5.
    + exact (btop_len s s7 TP7).
Qed.

(* [comment removed for export] *)
Lemma arm_bin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.src_read_spec L ar HI -> PNRAa.read_span_v_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb08a4 M3 model3) K.
Proof.
  intros SR RSV MKE CTX G LM3 MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & INV & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM3) as (PF3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  assert (QSP : 0 <= sp - 160 /\ sp <= 2 ^ 64) by (match goal with H : 140735332487392 <= sp <= _ |- _ => clear - H; lia end).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVBP.awvY1a_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVBP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12 & A24 & A25 & SHZ & ECW).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxa R3 Ra 0xb08a4 0xaed4c Mav
           (fun a => sp - 136 <= a < sp - 136 + 8 \/ F / 8 + 2147450880 + 40 <= a < F / 8 + 2147450880 + 40 + 1) CTX G LM3 MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a [X|X]; [left; clear - X; lia| right; right; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr CTX G LM4) as (_ & _ & _ & _ & _ & _ & SVr4).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr CTX G LM4) as (_ & _ & _ & _ & VSH4 & _).
  assert (ECS4 : ecsp M4 sp fb).
  { unfold ecsp. apply SVr4; [clear; lia| clear; lia|]. rewrite HID4, VIS4. exact ECW. }
  assert (SHR : 0 <= F / 8 + 2147450920 /\ F / 8 + 2147450920 + 1 <= 2 ^ 64) by (clear - DF1 DF2; lia).
  assert (SH4 : L5.u8_at RSEGS M4 (F / 8 + 2147450920) 4).
  { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M4 (F / 8 + 2147450920) 4 (L5A.avis_sub _ (F / 8 + 2147450880) 64 (F / 8 + 2147450920) 1 VSH4 ltac:(clear; lia) ltac:(clear; lia)) (proj1 SHR) (proj2 SHR))).
    rewrite HID4, VIS4. exact SHZ. }
  assert (ACC : aacc M4 (F + 320) 4).
  { assert (HK : (4 = 8 /\ 4 = 0) \/ (1 <= 4 <= 7 /\ 4 = 4)) by (right; split; [clear; lia| reflexivity]).
    assert (HO8 : 320 mod 8 = 0) by reflexivity. assert (HO0 : 0 <= 320) by (clear; lia). assert (HF0 : 0 <= F) by (clear - GF1; lia).
    apply (aacc_local M4 F 320 4 4 (proj1 GF8) HO8 HO0 HF0 HK).
    change (320 / 8) with 40. replace (F / 8 + 40 + 2147450880) with (F / 8 + 2147450920) by (clear; lia).
    assert (SHR1 : F / 8 + 2147450920 < 65536 \/ 6905856 <= F / 8 + 2147450920) by (right; clear - DF1; lia).
    assert (SHR2 : 0 <= F / 8 + 2147450920 < 2 ^ 64) by (clear - SHR; lia).
    exact (L5ADHR.byte_of_u8 M4 (F / 8 + 2147450920) 4 SH4 SHR1 SHR2). }
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R R3 Ra sp fb F MID3); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (PNARVK.rv_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xb08c4 320 4 SR CTX G LM4
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC A1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact A10. }
  { exact A11. }
  { exact A12. }
  intros fx5 R5 M5 model5 LK5 Aw5 src5 sm5 d RP5 Y10d Hd UNR5 RD1 RD0 DEF5 QC5 LM5 AG5 ECK5.
  set (s5 := PNM.with_srcB s src5) in *.
  assert (INV5 : PNRA.binv s5) by exact INV.
  pose proof (PNBKA.btop_pos_refl s INV) as TP0.
  assert (TP5 : PNRA.btop_pos s s5) by exact TP0.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr Ra (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  apply (bin_fork1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 R5 d SR RSV MKE CTX G LM5 INV5).
  - exact (mid_keep R Ra R5 sp fb F MIDa RK).
  - exact Y10d.
  - exact Hd.
  - rewrite (L5SAR.cs_of_preserved Ra R5 24%nat RP5) by inl. exact A24.
  - apply (cell_agree M4 M5 (sp - 136) (fb + 464 + 16)); [clear - QSP; lia| clear - QSP; lia| exact ECS4|]. intros i Hi. apply AG5. clear - Hi; lia.
  - apply ECK5. apply ECK4. exact EC3.
  - exact TP5.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disp5 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 5 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb08a4 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (5 - 1)) with (Z_to_bv 64 4) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ5_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 5 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb08a4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

End WithHeap.
End PNARVB.
