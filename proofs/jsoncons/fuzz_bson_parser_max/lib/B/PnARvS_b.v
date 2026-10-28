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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvSP_b PnARvK_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVS.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

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


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str2_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  mid R R5 sp fb F -> getr R5 (reg 23) = Z_to_bv 64 (F + 96) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.btop_pos s s5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb03ac M5 model5) K.
Proof.
  intros CTX G LM MID5 X23 RES INV5 LEN5 BB5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (_ & _ & _ & _ & _ & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2e_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MOR : PNM.b_more s5 = 0 \/ PNM.b_more s5 = 1).
  { destruct LM as (_ & (PA5 & _) & _). destruct PA5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (QOP : 0 <= fb + 464 + 8 /\ fb + 464 + 8 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  assert (SHop : forall i, fb + 464 + 8 <= i < fb + 464 + 8 + 1 -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 64)).
  { intros i Hi X. match goal with H : (2147446784 + 17592186048512 <= fb + 464 \/ fb + 464 + 416 <= 2147446784) |- _ => destruct H as [Y|Y] end.
    - assert (F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; [clear; Lia.lia| match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end]). clear - Hi X Y H. Lia.lia.
    - assert (0 <= F / 8) by (apply Z.div_pos; [match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end| clear; Lia.lia]). clear - Hi X Y H. Lia.lia. }
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx9 R5 R9 0xb03ac (PNM.b_more s5) M9v CTX G LM MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV5 M9v); [| exact (proj1 QOP)| exact (proj2 QOP)| exact MO5].
    intros i Hi. apply FRZ9; [clear - Hi QOP; lia| | exact (SHop i Hi)]. intros X.
    match goal with H : (fb + 464 + 416 <= F \/ F + 512 <= fb + 464) |- _ => clear - H X Hi; lia end.
  - exact MOR.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - destruct RES as [(v & Hv & ECv & MO0 & CAT)|(EC5 & TP5)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO0| exact CAT].
    + right. split; [exact EC5|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact TP5.
  - exact INV5.
  - exact LEN5.
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB5. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma str2_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb1588 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 3 -> getr R4 (reg 23) = Z_to_bv 64 (F + 96) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 X23 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb1588 3 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (L5SAR.cs_of_preserved R4 R5 23%nat RP5) by inl; exact X23).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2d_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb1588 0 M9v CTX G LM5 MS9 MG9).
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
  - left. exists 3. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma str2_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R3 sp fb F -> getr R3 (reg 23) = Z_to_bv 64 (F + 96) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0314 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X23 EC3 TP3 BB3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (U10 & WR8 & _).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 120 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 120) / 8 + 2147450880) with 2147607327 in VFX.
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2v_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb0314 1 M9v CTX G LM MS9 MG9).
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
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB3. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma str2_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx7 : FPState) R7 (ptr n : Z) :
  PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mid R R7 sp fb F -> getr R7 (reg 23) = Z_to_bv 64 (F + 96) ->
  getr R7 (reg 1) = Z_to_bv 64 0xb0308 -> getr R7 (reg 10) = Z_to_bv 64 ptr -> getr R7 (reg 11) = Z_to_bv 64 n ->
  0 <= n < 2 ^ 26 -> L5.defined M6 ptr n -> aacc M6 ptr n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s6) ptr n \/ (fb + 464 + 368 + 1 <= ptr /\ ptr + n <= fb + 464 + 368 + 24)) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 0xb2f54 M6 model6) K.
Proof.
  intros VAL MKE CTX G LM INV6 MID7 X23 X1 X10 X11 Hn DEF ACC SPAN EC6 TP6 BB6.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID7 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  destruct (PNARVK.span_facts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ptr n CTX G LM Hn SPAN) as (P0 & P1 & P2 & PV & PS).
  change 0xb2f54 with (pa_validate PMA.AD).
  apply (PNARVK.rv_call_val L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xb0308 ptr n VAL CTX G LM X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { exact Hn. } { exact P0. } { exact P1. } { exact P2. } { exact DEF. } { exact ACC. } { exact PV. } { exact PS. }
  intros fx8 R8 M8 model8 RP8 LM8 AG8 ECK8.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (PF8 & _).
  set (MV8 := mrestrict (ahid Aw6 model8) M8) in *.
  unfold pfacts in PF8. conj_open PF8.
  assert (RK : forall k, In k MIDREGS -> getr R8 (reg k) = getr R7 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R7 R8 k RP8). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R7 R8 sp fb F MID7 RK) as MID8.
  pose proof MID8 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R8 (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23%nat RP8) by inl; exact X23).
  assert (E11 : getr R8 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bvu_rng (getr R8 (reg 11))) as Q47.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2c_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 47%nat => bv_unsigned (getr R8 (reg 11)) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & [(MS9 & KS9)|(MS9 & KS9 & Y1 & Y10 & Y11)]).
  - apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 fx9 R8 R9 0xb0308 0xb0314 M9v CTX G LM8 MS9 MG9 FRZ9).
    intros model9 LM9 HID9.
    apply (str2_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK6 Aw6 s6 sm6 ax6 cr6 fx9 R9 CTX G LM9 INV6).
    + apply (mid_keep R R8 R9 sp fb F MID8). unfold MIDREGS. kks KS9.
    + rewrite (KS9 23%nat) by inl. exact E23.
    + apply ECK8. exact EC6.
    + exact TP6.
    + exact BB6.
  - apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 fx9 R8 R9 0xb0308 0xae848 M9v CTX G LM8 MS9 MG9 FRZ9).
    intros model9 LM9 HID9.
    apply (str2_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK6 Aw6 s6 sm6 ax6 cr6 fx9 R9 MKE CTX G LM9 INV6).
    + apply (mid_keep R R8 R9 sp fb F MID8). unfold MIDREGS. kks KS9.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite (KS9 23%nat) by inl. exact E23.
    + apply ECK8. exact EC6.
    + exact (btop_len s s6 TP6).
Qed.

(* [comment removed for export] *)
Lemma str2_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (v44 c44 : Z) :
  PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> mid R R5 sp fb F -> getr R5 (reg 23) = Z_to_bv 64 (F + 96) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) v44 c44 -> 0 <= v44 <= 64 ->
  ( (1 <= v44 /\ c44 = pa_errcat_obj PMA.AD /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (v44 = e /\ c44 = cat /\ PNRA.btop_pos s s5
        /\ exists ptr n, getr R5 (reg 10) = Z_to_bv 64 ptr /\ getr R5 (reg 11) = Z_to_bv 64 n /\ 0 <= n < 2 ^ 26 /\ L5.defined M5 ptr n /\ aacc M5 ptr n
             /\ ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s5) ptr n \/ (fb + 464 + 368 + 1 <= ptr /\ ptr + n <= fb + 464 + 368 + 24))) ) ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb02dc M5 model5) K.
Proof.
  intros VAL MKE CTX G LM INV5 MID5 X23 ECX Hv OUT LEN5 BB5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 v44 c44 CTX G LM ECX) as EF5.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5. conj_open EF5.
  assert (E10 : getr R5 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R5 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : getr R5 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R5 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bvu_rng (getr R5 (reg 10))) as Q45. pose proof (bvu_rng (getr R5 (reg 11))) as Q46.
  assert (Q44 : 0 <= v44 < 2 ^ 64) by (clear - Hv; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 44%nat => v44
      | 45%nat => bv_unsigned (getr R5 (reg 10)) | 46%nat => bv_unsigned (getr R5 (reg 11)) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y1 & CND & _).
    assert (V0 : v44 = 0).
    { rewrite Z.sub_0_r in CND. rewrite Z.mod_small in CND by (clear - Hv; lia). clear - CND Hv. lia. }
    destruct OUT as [(X & _)|(Ee & Ec & TP5 & ptr & n & A0 & A1 & Hn & DEF & ACC & SPAN)]; [exfalso; clear - X V0; lia|].
    apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb02dc 0xb2f54 M6v (fun a => F + 96 <= a < F + 96 + 16) CTX G LM MS6 MG6).
    { intros a Ha N. apply FRZ6; [exact Ha| intros X; apply N; clear - X; lia]. }
    { intros a X. right; left. clear - X; lia. }
    intros M7 model7 LM7 HID7 VIS7 FR7 MG7 ECK7.
    assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; [match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end| clear; Lia.lia]).
    assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; [clear; Lia.lia| match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end]).
    destruct (PNARVK.span_facts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ptr n CTX G LM Hn SPAN) as (P0 & P1 & P2 & _).
    apply (str2_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 ptr n VAL MKE CTX G LM7 INV5).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + exact Y1.
    + rewrite (KS6 10%nat) by inl. exact A0.
    + rewrite (KS6 11%nat) by inl. exact A1.
    + exact Hn.
    + exact (L5.defined_grows M5 M7 _ _ MG7 DEF).
    + apply (PMFA.aacc_agree M5 M7 ptr n); [| exact ACC]. intros x Hx. apply FR7.
      * unfold S, SB. assert (0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; clear - Hx P0; Lia.lia| apply Z.div_le_upper_bound; clear - Hx P2; Lia.lia]). clear - H. lia.
      * intros X. unfold S, SB in X. assert (0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; clear - Hx P0; Lia.lia| apply Z.div_le_upper_bound; clear - Hx P2; Lia.lia]).
        match goal with H0 : (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) |- _ => clear - H0 X H; lia end.
    + exact SPAN.
    + apply ECK7. rewrite <- Ee, <- Ec. exact ECX.
    + exact TP5.
    + exact BB5.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y10 & CND & _).
    apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb02dc 0xb03ac M6v (fun a => F + 96 <= a < F + 96 + 16) CTX G LM MS6 MG6).
    { intros a Ha N. apply FRZ6; [exact Ha| intros X; apply N; clear - X; lia]. }
    { intros a X. right; left. clear - X; lia. }
    intros M7 model7 LM7 HID7 VIS7 FR7 MG7 ECK7.
    apply (str2_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G LM7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + destruct OUT as [(X & Ec & MO0 & CAT)|(Ee & Ec & TP5 & _)].
      * left. exists v44. split; [clear - X Hv; lia|]. split; [rewrite <- Ec; apply ECK7; exact ECX|]. split; [exact MO0| exact CAT].
      * right. split; [rewrite <- Ee, <- Ec; apply ECK7; exact ECX| exact TP5].
    + exact INV5.
    + exact LEN5.
    + exact BB5.
Qed.

(* [comment removed for export] *)
Lemma arm_str2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.read_string_spec L ar HI -> PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb02c4 M3 model3) K.
Proof.
  intros RSTR VAL MKE CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & INV & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS2a_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A23 & _).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxa R3 Ra 0xb02c4 0xb343c Mav (fun a => F / 8 + 2147450880 + 12 <= a < F / 8 + 2147450880 + 12 + 2) CTX G LM MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; right. clear - X; lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R R3 Ra sp fb F MID3); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xb343c with (PNL.pn_read_string PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xb02dc e cat (PNL.pn_read_string PMA.AN) 7 (PNRA.bargs_rs PMA.AD) (PNRA.bprog_rs PMA.AD fb)
           (RSTR fb) ltac:(right; reflexivity) CTX G LM4 INV (ECK4 _ _ EC3) HE UNR).
  { unfold PNRA.bargs_rs, PNRA.o_p, PNRA.o_ec, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11. split; [exact A10| exact A11]. }
  { exact A1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BB5 AG5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr Ra (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R Ra R5 sp fb F MIDa RK) as MID5.
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (L5SAR.cs_of_preserved Ra R5 23%nat RP5) by inl; exact A23).
  destruct RES5 as [(v & Hv & ECv & MO0 & CAT & LENv & INVv)|(EC5 & INV5 & PRG)].
  - apply (str2_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 R5 v (pa_errcat_obj PMA.AD) VAL MKE CTX G LM5 INVv MID5 E23 ECv ltac:(clear - Hv; lia)).
    + left. split; [clear - Hv; lia|]. split; [reflexivity|]. split; [exact MO0| exact CAT].
    + exact LENv.
    + exact BB5.
  - unfold PNRA.bprog_rs in PRG. destruct PRG as (TP5 & UN5 & ptr & n & A0' & A1' & Hn & DEF & ACC & SPAN).
    rewrite L5K.rl10 in A0'. rewrite L5K.rl11 in A1'.
    apply (str2_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 R5 e cat VAL MKE CTX G LM5 INV5 MID5 E23 EC5 HE).
    + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact TP5|]. exists ptr, n.
      split; [exact A0'|]. split; [exact A1'|]. split; [exact Hn|]. split; [exact DEF|]. split; [exact ACC|].
      unfold PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB in SPAN. cbn [pa_off_p PMA.AD PnLayoutA_b.ADDR_A] in SPAN. exact SPAN.
    + exact (btop_len s s5 TP5).
    + exact BB5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma str13_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  mid R R5 sp fb F -> getr R5 (reg 23) = Z_to_bv 64 (F + 128) ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.btop_pos s s5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb0880 M5 model5) K.
Proof.
  intros CTX G LM MID5 X23 RES INV5 LEN5 BB5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (_ & _ & _ & _ & _ & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13e_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MOR : PNM.b_more s5 = 0 \/ PNM.b_more s5 = 1).
  { destruct LM as (_ & (PA5 & _) & _). destruct PA5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (QOP : 0 <= fb + 464 + 8 /\ fb + 464 + 8 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  assert (SHop : forall i, fb + 464 + 8 <= i < fb + 464 + 8 + 1 -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 64)).
  { intros i Hi X. match goal with H : (2147446784 + 17592186048512 <= fb + 464 \/ fb + 464 + 416 <= 2147446784) |- _ => destruct H as [Y|Y] end.
    - assert (F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; [clear; Lia.lia| match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end]). clear - Hi X Y H. Lia.lia.
    - assert (0 <= F / 8) by (apply Z.div_pos; [match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end| clear; Lia.lia]). clear - Hi X Y H. Lia.lia. }
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx9 R5 R9 0xb0880 (PNM.b_more s5) M9v CTX G LM MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV5 M9v); [| exact (proj1 QOP)| exact (proj2 QOP)| exact MO5].
    intros i Hi. apply FRZ9; [clear - Hi QOP; lia| | exact (SHop i Hi)]. intros X.
    match goal with H : (fb + 464 + 416 <= F \/ F + 512 <= fb + 464) |- _ => clear - H X Hi; lia end.
  - exact MOR.
  - exact Z1.
  - exact Z10.
  - exact Z11.
  - rewrite (KS9 2%nat) by inl. exact E2.
  - rewrite (KS9 8%nat) by inl. exact E8.
  - rewrite (KS9 19%nat) by inl. exact E19.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - destruct RES as [(v & Hv & ECv & MO0 & CAT)|(EC5 & TP5)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO0| exact CAT].
    + right. split; [exact EC5|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact TP5.
  - exact INV5.
  - exact LEN5.
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB5. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma str13_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb171c -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 3 -> getr R4 (reg 23) = Z_to_bv 64 (F + 128) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 X23 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb171c 3 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 128)) by (rewrite (L5SAR.cs_of_preserved R4 R5 23%nat RP5) by inl; exact X23).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13d_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb171c 0 M9v CTX G LM5 MS9 MG9).
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
  - left. exists 3. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV3.
  - exact LEN3.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma str13_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R3 sp fb F -> getr R3 (reg 23) = Z_to_bv 64 (F + 128) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb07ec M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X23 EC3 TP3 BB3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (U10 & WR8 & _).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 120 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 120) / 8 + 2147450880) with 2147607327 in VFX.
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13v_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb07ec 1 M9v CTX G LM MS9 MG9).
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
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB3. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma str13_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx7 : FPState) R7 (ptr n : Z) :
  PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> mid R R7 sp fb F -> getr R7 (reg 23) = Z_to_bv 64 (F + 128) ->
  getr R7 (reg 1) = Z_to_bv 64 0xb07e4 -> getr R7 (reg 10) = Z_to_bv 64 ptr -> getr R7 (reg 11) = Z_to_bv 64 n ->
  0 <= n < 2 ^ 26 -> L5.defined M6 ptr n -> aacc M6 ptr n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s6) ptr n \/ (fb + 464 + 368 + 1 <= ptr /\ ptr + n <= fb + 464 + 368 + 24)) ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 0xb2f54 M6 model6) K.
Proof.
  intros VAL MKE CTX G LM INV6 MID7 X23 X1 X10 X11 Hn DEF ACC SPAN EC6 TP6 BB6.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID7 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  destruct (PNARVK.span_facts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ptr n CTX G LM Hn SPAN) as (P0 & P1 & P2 & PV & PS).
  change 0xb2f54 with (pa_validate PMA.AD).
  apply (PNARVK.rv_call_val L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xb07e4 ptr n VAL CTX G LM X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { exact Hn. } { exact P0. } { exact P1. } { exact P2. } { exact DEF. } { exact ACC. } { exact PV. } { exact PS. }
  intros fx8 R8 M8 model8 RP8 LM8 AG8 ECK8.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (PF8 & _).
  set (MV8 := mrestrict (ahid Aw6 model8) M8) in *.
  unfold pfacts in PF8. conj_open PF8.
  assert (RK : forall k, In k MIDREGS -> getr R8 (reg k) = getr R7 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R7 R8 k RP8). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R7 R8 sp fb F MID7 RK) as MID8.
  pose proof MID8 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R8 (reg 23) = Z_to_bv 64 (F + 128)) by (rewrite (L5SAR.cs_of_preserved R7 R8 23%nat RP8) by inl; exact X23).
  assert (E11 : getr R8 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R8 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bvu_rng (getr R8 (reg 11))) as Q47.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13c_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 47%nat => bv_unsigned (getr R8 (reg 11)) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & [(MS9 & KS9)|(MS9 & KS9 & Y1 & Y10 & Y11)]).
  - apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 fx9 R8 R9 0xb07e4 0xb07ec M9v CTX G LM8 MS9 MG9 FRZ9).
    intros model9 LM9 HID9.
    apply (str13_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK6 Aw6 s6 sm6 ax6 cr6 fx9 R9 CTX G LM9 INV6).
    + apply (mid_keep R R8 R9 sp fb F MID8). unfold MIDREGS. kks KS9.
    + rewrite (KS9 23%nat) by inl. exact E23.
    + apply ECK8. exact EC6.
    + exact TP6.
    + exact BB6.
  - apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 fx9 R8 R9 0xb07e4 0xae848 M9v CTX G LM8 MS9 MG9 FRZ9).
    intros model9 LM9 HID9.
    apply (str13_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model9 LK6 Aw6 s6 sm6 ax6 cr6 fx9 R9 MKE CTX G LM9 INV6).
    + apply (mid_keep R R8 R9 sp fb F MID8). unfold MIDREGS. kks KS9.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite (KS9 23%nat) by inl. exact E23.
    + apply ECK8. exact EC6.
    + exact (btop_len s s6 TP6).
Qed.

(* [comment removed for export] *)
Lemma str13_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (v44 c44 : Z) :
  PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> mid R R5 sp fb F -> getr R5 (reg 23) = Z_to_bv 64 (F + 128) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) v44 c44 -> 0 <= v44 <= 64 ->
  ( (1 <= v44 /\ c44 = pa_errcat_obj PMA.AD /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (v44 = e /\ c44 = cat /\ PNRA.btop_pos s s5
        /\ exists ptr n, getr R5 (reg 10) = Z_to_bv 64 ptr /\ getr R5 (reg 11) = Z_to_bv 64 n /\ 0 <= n < 2 ^ 26 /\ L5.defined M5 ptr n /\ aacc M5 ptr n
             /\ ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PNM.bparser_own s5) ptr n \/ (fb + 464 + 368 + 1 <= ptr /\ ptr + n <= fb + 464 + 368 + 24))) ) ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb07b8 M5 model5) K.
Proof.
  intros VAL MKE CTX G LM INV5 MID5 X23 ECX Hv OUT LEN5 BB5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 v44 c44 CTX G LM ECX) as EF5.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5. conj_open EF5.
  assert (E10 : getr R5 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R5 (reg 10)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : getr R5 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R5 (reg 11)))) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bvu_rng (getr R5 (reg 10))) as Q45. pose proof (bvu_rng (getr R5 (reg 11))) as Q46.
  assert (Q44 : 0 <= v44 < 2 ^ 64) by (clear - Hv; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 44%nat => v44
      | 45%nat => bv_unsigned (getr R5 (reg 10)) | 46%nat => bv_unsigned (getr R5 (reg 11)) | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y1 & CND & _).
    assert (V0 : v44 = 0).
    { rewrite Z.sub_0_r in CND. rewrite Z.mod_small in CND by (clear - Hv; lia). clear - CND Hv. lia. }
    destruct OUT as [(X & _)|(Ee & Ec & TP5 & ptr & n & A0 & A1 & Hn & DEF & ACC & SPAN)]; [exfalso; clear - X V0; lia|].
    apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb07b8 0xb2f54 M6v (fun a => F + 128 <= a < F + 128 + 16) CTX G LM MS6 MG6).
    { intros a Ha N. apply FRZ6; [exact Ha| intros X; apply N; clear - X; lia]. }
    { intros a X. right; left. clear - X; lia. }
    intros M7 model7 LM7 HID7 VIS7 FR7 MG7 ECK7.
    assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; [match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end| clear; Lia.lia]).
    assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; [clear; Lia.lia| match goal with H : 6905856 <= F <= _ |- _ => clear - H; Lia.lia end]).
    destruct (PNARVK.span_facts L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ptr n CTX G LM Hn SPAN) as (P0 & P1 & P2 & _).
    apply (str13_val K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 ptr n VAL MKE CTX G LM7 INV5).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + exact Y1.
    + rewrite (KS6 10%nat) by inl. exact A0.
    + rewrite (KS6 11%nat) by inl. exact A1.
    + exact Hn.
    + exact (L5.defined_grows M5 M7 _ _ MG7 DEF).
    + apply (PMFA.aacc_agree M5 M7 ptr n); [| exact ACC]. intros x Hx. apply FR7.
      * unfold S, SB. assert (0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; clear - Hx P0; Lia.lia| apply Z.div_le_upper_bound; clear - Hx P2; Lia.lia]). clear - H. lia.
      * intros X. unfold S, SB in X. assert (0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; clear - Hx P0; Lia.lia| apply Z.div_le_upper_bound; clear - Hx P2; Lia.lia]).
        match goal with H0 : (2147446784 + 17592186048512 <= F \/ F + 512 <= 2147446784) |- _ => clear - H0 X H; lia end.
    + exact SPAN.
    + apply ECK7. rewrite <- Ee, <- Ec. exact ECX.
    + exact TP5.
    + exact BB5.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y10 & CND & _).
    apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb07b8 0xb0880 M6v (fun a => F + 128 <= a < F + 128 + 16) CTX G LM MS6 MG6).
    { intros a Ha N. apply FRZ6; [exact Ha| intros X; apply N; clear - X; lia]. }
    { intros a X. right; left. clear - X; lia. }
    intros M7 model7 LM7 HID7 VIS7 FR7 MG7 ECK7.
    apply (str13_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G LM7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + destruct OUT as [(X & Ec & MO0 & CAT)|(Ee & Ec & TP5 & _)].
      * left. exists v44. split; [clear - X Hv; lia|]. split; [rewrite <- Ec; apply ECK7; exact ECX|]. split; [exact MO0| exact CAT].
      * right. split; [rewrite <- Ee, <- Ec; apply ECK7; exact ECX| exact TP5].
    + exact INV5.
    + exact LEN5.
    + exact BB5.
Qed.

(* [comment removed for export] *)
Lemma arm_str13 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.read_string_spec L ar HI -> PMA.validate_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb07a0 M3 model3) K.
Proof.
  intros RSTR VAL MKE CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & INV & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVSP.awvS13a_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVSP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A23 & _).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxa R3 Ra 0xb07a0 0xb343c Mav (fun a => F / 8 + 2147450880 + 16 <= a < F / 8 + 2147450880 + 16 + 2) CTX G LM MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; right. clear - X; lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R R3 Ra sp fb F MID3); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xb343c with (PNL.pn_read_string PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xb07b8 e cat (PNL.pn_read_string PMA.AN) 7 (PNRA.bargs_rs PMA.AD) (PNRA.bprog_rs PMA.AD fb)
           (RSTR fb) ltac:(right; reflexivity) CTX G LM4 INV (ECK4 _ _ EC3) HE UNR).
  { unfold PNRA.bargs_rs, PNRA.o_p, PNRA.o_ec, PMSP.o_p, PMSP.o_ec. cbn [pa_off_p pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11. split; [exact A10| exact A11]. }
  { exact A1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BB5 AG5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr Ra (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R Ra R5 sp fb F MIDa RK) as MID5.
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 128)) by (rewrite (L5SAR.cs_of_preserved Ra R5 23%nat RP5) by inl; exact A23).
  destruct RES5 as [(v & Hv & ECv & MO0 & CAT & LENv & INVv)|(EC5 & INV5 & PRG)].
  - apply (str13_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 R5 v (pa_errcat_obj PMA.AD) VAL MKE CTX G LM5 INVv MID5 E23 ECv ltac:(clear - Hv; lia)).
    + left. split; [clear - Hv; lia|]. split; [reflexivity|]. split; [exact MO0| exact CAT].
    + exact LENv.
    + exact BB5.
  - unfold PNRA.bprog_rs in PRG. destruct PRG as (TP5 & UN5 & ptr & n & A0' & A1' & Hn & DEF & ACC & SPAN).
    rewrite L5K.rl10 in A0'. rewrite L5K.rl11 in A1'.
    apply (str13_back K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 R5 e cat VAL MKE CTX G LM5 INV5 MID5 E23 EC5 HE).
    + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact TP5|]. exists ptr, n.
      split; [exact A0'|]. split; [exact A1'|]. split; [exact Hn|]. split; [exact DEF|]. split; [exact ACC|].
      unfold PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB in SPAN. cbn [pa_off_p PMA.AD PnLayoutA_b.ADDR_A] in SPAN. exact SPAN.
    + exact (btop_len s s5 TP5).
    + exact BB5.
Qed.

(* [comment removed for export] *)
Lemma disp2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 2 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 2 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb02c4 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (2 - 1)) with (Z_to_bv 64 1) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 2 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ2_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 2 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb02c4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp14 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 14 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 14 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb02c4 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (14 - 1)) with (Z_to_bv 64 13) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 14 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ14_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 14 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb02c4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp127 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 127 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 127 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb02c4 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (127 - 1)) with (Z_to_bv 64 126) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 127 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ127_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 127 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb02c4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp255 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 255 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 255 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb02c4 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (255 - 1)) with (Z_to_bv 64 254) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 255 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ255_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 255 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb02c4 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp13 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 13 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 13 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb07a0 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (13 - 1)) with (Z_to_bv 64 12) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 13 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ13_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 13 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb07a0 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

End WithHeap.
End PNARVS.
