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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvXP_b PnARvK_b PnARvKX_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVX.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARVK. Import PNARVKX.

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
Definition midx (R Rc : bvmap 5 word) (sp fb F : Z) : Prop :=
  mid R Rc sp fb F /\ getr Rc (reg 23) = Z_to_bv 64 (fb + 464 + 368) /\ getr Rc (reg 24) = Z_to_bv 64 ((fb + 464 + 368) / 8 + 2147450880).
Definition MIDXREGS : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26; 27]%nat.
Lemma midx_keep R Rc R1 sp fb F : midx R Rc sp fb F -> (forall k, In k MIDXREGS -> getr R1 (reg k) = getr Rc (reg k)) -> midx R R1 sp fb F.
Proof.
  intros (MD & X23 & X24) KS. unfold midx. split; [apply (mid_keep R Rc R1 sp fb F MD); intros k Hk; apply KS; revert k Hk; unfold MIDREGS, MIDXREGS; kin|].
  rewrite !KS by (cbn; tauto). split; assumption.
Qed.
(* [comment removed for export] *)
Definition x25ec (Rc : bvmap 5 word) (fb : Z) : Prop := getr Rc (reg 25) = Z_to_bv 64 ((fb + 1024) / 8 + 2147450880).

(* [comment removed for export] *)
Lemma rx_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  mid R R5 sp fb F ->
  ( (exists v, 1 <= v <= 64 /\ PMSPA.ec_at RSEGS M5 (fb + 1024) v (pa_errcat_obj PMA.AD) /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (PMSPA.ec_at RSEGS M5 (fb + 1024) e cat /\ PNRA.btop_pos s s5) ) ->
  PNRA.binv s5 -> (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb1424 M5 model5) K.
Proof.
  intros CTX G LM MID5 RES INV5 LEN5 BB5.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (_ & _ & _ & _ & _ & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvXR_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MOR : PNM.b_more s5 = 0 \/ PNM.b_more s5 = 1).
  { destruct LM as (_ & (PA5 & _) & _). destruct PA5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (QOP : 0 <= fb + 464 + 8 /\ fb + 464 + 8 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx9 R5 R9 0xb1424 (PNM.b_more s5) M9v CTX G LM MS9 MG9).
  - intros a Ha N1 N2 N3. apply FRZ9; [exact Ha| intros X; apply N1; clear - X; lia].
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV5 M9v); [| exact (proj1 QOP)| exact (proj2 QOP)| exact MO5].
    intros i Hi. apply FRZ9; [clear - Hi QOP; lia|]. intros X.
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
Lemma rx_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midx R R3 sp fb F -> x25ec R3 fb ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb13d8 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X25 EC3 TP3 BB3.
  pose proof MID3 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24). unfold x25ec in X25.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (U10 & WR8 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvX6_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb13d8 1 M9v CTX G LM MS9 MG9).
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
Lemma rx_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midx R R3 sp fb F -> x25ec R3 fb ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb1054 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X25 EC3 TP3 BB3.
  pose proof MID3 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24). pose proof X25 as J25. unfold x25ec in J25.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 120 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 120) / 8 + 2147450880) with 2147607327 in VFX.
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (Z368 & Z369 & Z376 & Z384 & TW2 & TW8 & _ & SHAPE).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (FIN : forall (fx9 : FPState) R9 M9v,
            msteps RSEGS (st fx3 R3 0xb1054 MV3) (st fx9 R9 0xb13d8 M9v) -> mem_grows MV3 M9v ->
            (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (F / 8 + 2147450880 + 20 <= i < F / 8 + 2147450880 + 20 + 2) -> ~ (F + 160 <= i < F + 160 + 16) -> M9v (Z_to_bv 64 i) = MV3 (Z_to_bv 64 i)) ->
            (forall k, In k (25%nat :: MIDXREGS) -> getr R9 (reg k) = getr R3 (reg k)) ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb1054 M3 model3) K).
  { intros fx9 R9 M9v MS9 MG9 FRZ9 KS9.
    apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb1054 0xb13d8 M9v
             (fun a => F / 8 + 2147450880 + 20 <= a < F / 8 + 2147450880 + 20 + 2 \/ F + 160 <= a < F + 160 + 16) CTX G LM MS9 MG9).
    { intros a Ha N. apply FRZ9; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a [X|X]; [right; right; clear - X; lia| right; left; clear - X; lia]. }
    intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
    apply (rx_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx9 R9 CTX G LM4 INV3).
    - apply (midx_keep R R3 R9 sp fb F MID3). intros k Hk. apply KS9. right. exact Hk.
    - unfold x25ec. rewrite (KS9 25%nat) by (left; reflexivity). exact J25.
    - apply ECK4. exact EC3.
    - exact TP3.
    - exact BB3. }
  destruct (PNM.b_tb s3) as [n|c n p].
  - (* [comment removed for export] *)
    destruct SHAPE as (Hn & U8 & Rn & TB0).
    assert (Q56 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    LeanFeed.pfeed P (PNARVXP.awvX5S_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => 2 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _).
    apply (FIN fx9 R9 M9v MS9 MG9).
    + intros i Hi N1 N2. apply FRZ9; [exact Hi| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia].
    + intros k Hk. apply KS9. revert k Hk. unfold MIDXREGS. kin.
  - (* [comment removed for export] *)
    destruct SHAPE as (U8 & Rb & TB1 & UD & UN & Hn & Hc & Hp & P8 & _).
    assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - Rb; lia).
    assert (Q57 : 0 <= p < 2 ^ 64) by (clear - Hp; lia).
    assert (Q58 : 0 <= n < 2 ^ 64) by (clear - Hn Hc; lia).
    LeanFeed.pfeed P (PNARVXP.awvX5L_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _).
    apply (FIN fx9 R9 M9v MS9 MG9).
    + intros i Hi N1 N2. apply FRZ9; [exact Hi| intros X; apply N1; clear - X; lia| intros X; apply N2; clear - X; lia].
    + intros k Hk. apply KS9. revert k Hk. unfold MIDXREGS. kin.
Qed.

(* [comment removed for export] *)
Lemma rx_fork2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (v44 c44 : Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midx R R5 sp fb F -> x25ec R5 fb ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) v44 c44 -> 0 <= v44 <= 64 ->
  ( (1 <= v44 /\ c44 = pa_errcat_obj PMA.AD /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (v44 = e /\ c44 = cat /\ PNRA.btop_pos s s5) ) ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb1044 M5 model5) K.
Proof.
  intros CTX G LM INV5 MID5 X25 ECX Hv OUT LEN5 BB5.
  pose proof MID5 as ((E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27) & E23 & E24). pose proof X25 as E25. unfold x25ec in E25.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 v44 c44 CTX G LM ECX) as EF5.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5. conj_open EF5.
  assert (Q44 : 0 <= v44 < 2 ^ 64) by (clear - Hv; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvX4_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 44%nat => v44 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [(MS6 & KS6 & Y10 & CND)|(MS6 & KS6 & Y10 & CND)]).
  - (* [comment removed for export] *)
    assert (V0 : v44 = 0).
    { rewrite Z.sub_0_r in CND. rewrite Z.mod_small in CND by (clear - Hv; lia). clear - CND Hv. lia. }
    destruct OUT as [(X & _)|(Ee & Ec & TP5)]; [exfalso; clear - X V0; lia|].
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb1044 0xb1054 M6v CTX G LM MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (rx_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G LM6 INV5).
    + apply (midx_keep R R5 R6 sp fb F MID5). unfold MIDXREGS. kks KS6.
    + unfold x25ec. rewrite (KS6 25%nat) by inl. exact E25.
    + rewrite <- Ee, <- Ec. exact ECX.
    + exact TP5.
    + exact BB5.
  - (* [comment removed for export] *)
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb1044 0xb1424 M6v CTX G LM MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (rx_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G LM6).
    + apply (mid_keep R R5 R6 sp fb F (proj1 MID5)). unfold MIDREGS. kks KS6.
    + destruct OUT as [(X & Ec & MO0 & CAT)|(Ee & Ec & TP5)].
      * left. exists v44. split; [clear - X Hv; lia|]. split; [rewrite <- Ec; exact ECX|]. split; [exact MO0| exact CAT].
      * right. split; [rewrite <- Ee, <- Ec; exact ECX| exact TP5].
    + exact INV5.
    + exact LEN5.
    + exact BB5.
Qed.

(* [comment removed for export] *)
Lemma rx_round2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  PNRAa.str_push_back_spec L ar HI -> PNRAa.read_cstring_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> midx R R6 sp fb F -> x25ec R6 fb ->
  getr R6 (reg 1) = Z_to_bv 64 0xb1034 -> getr R6 (reg 10) = Z_to_bv 64 (fb + 464 + 368) -> getr R6 (reg 11) = Z_to_bv 64 47 ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  PM.unread (PNM.b_src s6) sm6 < 2 ^ 26 -> PM.vs_size (PNM.b_tb s6) + PM.unread (PNM.b_src s6) sm6 + 1 <= 2 ^ 26 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (PNL.pn_str_push_back PMA.AN) M6 model6) K.
Proof.
  intros PB RCS CTX G LM6 INV6 MID6 X25 X1 X10 X11 EC6 TP6 BB6 UN6 SZ6.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID6 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24).
  assert (UN0 : 0 <= PM.unread (PNM.b_src s6) sm6).
  { destruct LM6 as (_ & (PA & IA & _) & _). exact (PNBKA.unread_nonneg _ _ _ _ _ _ _ PA IA). }
  apply (PNARVKX.rv_call_pbw L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xb1034 47 1 PB (or_intror eq_refl) CTX G LM6 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  { unfold PNRA.bcs_str. cbn [Z.eqb]. clear - SZ6 UN0. lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 x7 g7 cr7 RP7 SZ7 LM7 AG7 ECK7.
  unfold PNRA.bcs_str in SZ7. cbn [Z.eqb] in SZ7.
  set (s7 := set_cs 1 s6 x7 g7) in *.
  assert (INV7 : PNRA.binv s7) by exact INV6.
  assert (TP7 : PNRA.btop_pos s s7) by exact TP6.
  assert (EC7 : PMSPA.ec_at RSEGS M7 (fb + 1024) e cat) by (apply ECK7; exact EC6).
  assert (RK7 : forall k, In k (25%nat :: MIDXREGS) -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R6 R7 k RP7). revert k Hk. unfold MIDXREGS. kin. }
  assert (MID7 : midx R R7 sp fb F) by (apply (midx_keep R R6 R7 sp fb F MID6); intros k Hk; apply RK7; right; exact Hk).
  pose proof MID7 as ((E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27) & E23 & E24).
  assert (E25 : getr R7 (reg 25) = Z_to_bv 64 ((fb + 1024) / 8 + 2147450880)) by (rewrite (RK7 25%nat) by (left; reflexivity); exact X25).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 CTX G LM7) as (PF7 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 e cat CTX G LM7 EC7) as EF7.
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF7. conj_open PF7. conj_open EF7.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvX3_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & A1 & A10 & A11 & A12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 fx7 fx8 R7 R8 0xb1034 0xb2cd0 M8v CTX G LM7 MS8 MG8 FRZ8).
  intros model8 LM8 HID8.
  assert (RK8 : forall k, In k (25%nat :: MIDXREGS) -> getr R8 (reg k) = getr R7 (reg k)) by (intros k Hk; apply KS8; revert k Hk; unfold MIDXREGS; kin).
  assert (MID8 : midx R R8 sp fb F) by (apply (midx_keep R R7 R8 sp fb F MID7); intros k Hk; apply RK8; right; exact Hk).
  pose proof MID8 as ((B2 & B3 & B4 & _) & _).
  pose proof RCS as RCS'. unfold PNRAa.read_cstring_spec, PNRA.read_cstring_spec in RCS'.
  change 0xb2cd0 with (PNL.pn_read_cstring PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model8 LK7 Aw7 s7 sm6 ax6 cr7 fx8 R8 0xb1044 e cat (PNL.pn_read_cstring PMA.AN) 5 (PNRA.bargs_cs PMA.AD 1) (PNRA.bprog_cs 1)
           (proj1 (PNRA.brun_spec_iff RSEGS PMA.AD PMA.AN PMA.AAD L ar HI false _ _ _ _) (RCS' 1 (or_intror eq_refl)) fb) ltac:(left; reflexivity) CTX G LM8 INV7 EC7 HE).
  { unfold s7. rewrite PNBKA.set_cs_src. exact UN6. }
  { unfold PNRA.bargs_cs, PNRA.o_p, PNRA.o_ec, PMSP.o_p, PMSP.o_ec, PNRA.bcs_off, PNRA.bcs_str, PNM.OFF_TB. cbn [Z.eqb pa_off_p pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact A10|]. split; [exact A11|]. split; [exact A12|].
    pose proof (PNBKA.set_cs_str 1 s6 x7 g7) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS. fold s7 in XS. rewrite XS. unfold s7. rewrite PNBKA.set_cs_src. clear - SZ7 SZ6. lia. }
  { exact A1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx9 R9 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 RP9 LM9 STEP9 AXL9 RES9 BB9 AG9.
  assert (RK9 : forall k, In k (25%nat :: MIDXREGS) -> getr R9 (reg k) = getr R8 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R8 R9 k RP9). revert k Hk. unfold MIDXREGS. kin. }
  assert (MID9 : midx R R9 sp fb F) by (apply (midx_keep R R8 R9 sp fb F MID8); intros k Hk; apply RK9; right; exact Hk).
  assert (BB9' : PNM.b_bb s9 = PNM.b_bb s) by (rewrite BB9; unfold s7; rewrite PNBKA.set_cs_bb; exact BB6).
  pose proof (PNBKA.set_cs_str 1 s6 x7 g7) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS. fold s7 in XS.
  assert (SRC7 : PNM.b_src s7 = PNM.b_src s6) by (unfold s7; apply PNBKA.set_cs_src).
  destruct RES9 as [(v & Hv & ECv & MO0 & CAT & LENv & INVv)|(EC9 & INV9 & PRG)].
  - apply (rx_fork2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 fx9 R9 v (pa_errcat_obj PMA.AD) CTX G LM9 INVv MID9 ltac:(unfold x25ec; rewrite (RK9 25%nat) by (left; reflexivity); rewrite (RK8 25%nat) by (left; reflexivity); exact E25) ECv ltac:(clear - Hv; lia)).
    + left. split; [clear - Hv; lia|]. split; [reflexivity|]. split; [exact MO0| exact CAT].
    + apply (Nat.le_trans _ (length (PNM.b_stk s7))); [exact (btop_len s s7 TP7)| exact LENv].
    + exact BB9'.
  - unfold PNRA.bprog_cs, PNRA.bcs_str in PRG. cbn [Z.eqb] in PRG. destruct PRG as (TP9 & UN9 & SZ9). rewrite XS, SRC7 in SZ9. rewrite SRC7 in UN9.
    apply (rx_fork2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 fx9 R9 e cat CTX G LM9 INV9 MID9 ltac:(unfold x25ec; rewrite (RK9 25%nat) by (left; reflexivity); rewrite (RK8 25%nat) by (left; reflexivity); exact E25) EC9 HE).
    + right. split; [reflexivity|]. split; [reflexivity|]. exact (PNBKA.btop_pos_trans s s7 s9 TP7 TP9).
    + exact (btop_len s s9 (PNBKA.btop_pos_trans s s7 s9 TP7 TP9)).
    + exact BB9'.
Qed.

(* [comment removed for export] *)
Lemma rx_fork1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (v44 c44 : Z) :
  PNRAa.str_push_back_spec L ar HI -> PNRAa.read_cstring_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> midx R R5 sp fb F ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) v44 c44 -> 0 <= v44 <= 64 ->
  ( (1 <= v44 /\ c44 = pa_errcat_obj PMA.AD /\ PNM.b_more s5 = 0 /\ PNST.bax_cat ax5 = true)
    \/ (v44 = e /\ c44 = cat /\ PNRA.btop_pos s s5
        /\ PM.unread (PNM.b_src s5) sm5 < 2 ^ 26 /\ PM.vs_size (PNM.b_tb s5) + PM.unread (PNM.b_src s5) sm5 + 1 <= 2 ^ 26) ) ->
  (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb1010 M5 model5) K.
Proof.
  intros PB RCS CTX G LM INV5 MID5 ECX Hv OUT LEN5 BB5.
  pose proof MID5 as ((E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27) & E23 & E24).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM) as (PF5 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 v44 c44 CTX G LM ECX) as EF5.
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5. conj_open EF5.
  assert (Q44 : 0 <= v44 < 2 ^ 64) by (clear - Hv; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvX2_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 44%nat => v44 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [(MS6 & KS6 & Y1 & Y10 & Y11 & Y25 & CND)|(MS6 & KS6 & Y10 & Y25 & CND)]).
  - (* [comment removed for export] *)
    assert (V0 : v44 = 0).
    { rewrite Z.sub_0_r in CND. rewrite Z.mod_small in CND by (clear - Hv; lia). clear - CND Hv. lia. }
    destruct OUT as [(X & _)|(Ee & Ec & TP5 & UN5 & SZ5)]; [exfalso; clear - X V0; lia|].
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb1010 0xd5bc4 M6v CTX G LM MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN).
    apply (rx_round2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 PB RCS CTX G LM6 INV5).
    + apply (midx_keep R R5 R6 sp fb F MID5). unfold MIDXREGS. kks KS6.
    + exact Y25.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite <- Ee, <- Ec. exact ECX.
    + exact TP5.
    + exact BB5.
    + exact UN5.
    + exact SZ5.
  - (* [comment removed for export] *)
    apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb1010 0xb1424 M6v CTX G LM MS6 MG6 FRZ6).
    intros model6 LM6 HID6.
    apply (rx_ejoin K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model6 LK5 Aw5 s5 sm5 ax5 cr5 fx6 R6 CTX G LM6).
    + apply (mid_keep R R5 R6 sp fb F (proj1 MID5)). unfold MIDREGS. kks KS6.
    + destruct OUT as [(X & Ec & MO0 & CAT)|(Ee & Ec & TP5 & _)].
      * left. exists v44. split; [clear - X Hv; lia|]. split; [rewrite <- Ec; exact ECX|]. split; [exact MO0| exact CAT].
      * right. split; [rewrite <- Ee, <- Ec; exact ECX| exact TP5].
    + exact INV5.
    + exact LEN5.
    + exact BB5.
Qed.

(* [comment removed for export] *)
Lemma rx_round1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 :
  PNRAa.str_push_back_spec L ar HI -> PNRAa.read_cstring_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  PNRA.binv s6 -> midx R R6 sp fb F -> 
  getr R6 (reg 1) = Z_to_bv 64 0xb1000 -> getr R6 (reg 10) = Z_to_bv 64 (fb + 464 + 368) -> getr R6 (reg 11) = Z_to_bv 64 47 ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PNM.b_bb s6 = PNM.b_bb s ->
  PM.unread (PNM.b_src s6) sm6 < 2 ^ 26 -> PM.vs_size (PNM.b_tb s6) + PM.unread (PNM.b_src s6) sm6 + 1 <= 2 ^ 26 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (PNL.pn_str_push_back PMA.AN) M6 model6) K.
Proof.
  intros PB RCS CTX G LM6 INV6 MID6 X1 X10 X11 EC6 TP6 BB6 UN6 SZ6.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID6 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24).
  assert (UN0 : 0 <= PM.unread (PNM.b_src s6) sm6).
  { destruct LM6 as (_ & (PA & IA & _) & _). exact (PNBKA.unread_nonneg _ _ _ _ _ _ _ PA IA). }
  apply (PNARVKX.rv_call_pbw L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 0xb1000 47 1 PB (or_intror eq_refl) CTX G LM6 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  { unfold PNRA.bcs_str. cbn [Z.eqb]. clear - SZ6 UN0. lia. }
  intros fx7 R7 M7 model7 LK7 Aw7 x7 g7 cr7 RP7 SZ7 LM7 AG7 ECK7.
  unfold PNRA.bcs_str in SZ7. cbn [Z.eqb] in SZ7.
  set (s7 := set_cs 1 s6 x7 g7) in *.
  assert (INV7 : PNRA.binv s7) by exact INV6.
  assert (TP7 : PNRA.btop_pos s s7) by exact TP6.
  assert (EC7 : PMSPA.ec_at RSEGS M7 (fb + 1024) e cat) by (apply ECK7; exact EC6).
  assert (RK7 : forall k, In k (25%nat :: MIDXREGS) -> getr R7 (reg k) = getr R6 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R6 R7 k RP7). revert k Hk. unfold MIDXREGS. kin. }
  assert (MID7 : midx R R7 sp fb F) by (apply (midx_keep R R6 R7 sp fb F MID6); intros k Hk; apply RK7; right; exact Hk).
  pose proof MID7 as ((E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27) & E23 & E24).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 CTX G LM7) as (PF7 & _).
  pose proof (PNARVK.efacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 e cat CTX G LM7 EC7) as EF7.
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF7. conj_open PF7. conj_open EF7.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVXP.awvX1_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
  destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & A1 & A10 & A11 & A12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model7 LK7 Aw7 s7 sm6 ax6 cr7 fx7 fx8 R7 R8 0xb1000 0xb2cd0 M8v CTX G LM7 MS8 MG8 FRZ8).
  intros model8 LM8 HID8.
  assert (RK8 : forall k, In k (25%nat :: MIDXREGS) -> getr R8 (reg k) = getr R7 (reg k)) by (intros k Hk; apply KS8; revert k Hk; unfold MIDXREGS; kin).
  assert (MID8 : midx R R8 sp fb F) by (apply (midx_keep R R7 R8 sp fb F MID7); intros k Hk; apply RK8; right; exact Hk).
  pose proof MID8 as ((B2 & B3 & B4 & _) & _).
  pose proof RCS as RCS'. unfold PNRAa.read_cstring_spec, PNRA.read_cstring_spec in RCS'.
  change 0xb2cd0 with (PNL.pn_read_cstring PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M7 model8 LK7 Aw7 s7 sm6 ax6 cr7 fx8 R8 0xb1010 e cat (PNL.pn_read_cstring PMA.AN) 5 (PNRA.bargs_cs PMA.AD 1) (PNRA.bprog_cs 1)
           (proj1 (PNRA.brun_spec_iff RSEGS PMA.AD PMA.AN PMA.AAD L ar HI false _ _ _ _) (RCS' 1 (or_intror eq_refl)) fb) ltac:(left; reflexivity) CTX G LM8 INV7 EC7 HE).
  { unfold s7. rewrite PNBKA.set_cs_src. exact UN6. }
  { unfold PNRA.bargs_cs, PNRA.o_p, PNRA.o_ec, PMSP.o_p, PMSP.o_ec, PNRA.bcs_off, PNRA.bcs_str, PNM.OFF_TB. cbn [Z.eqb pa_off_p pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact A10|]. split; [exact A11|]. split; [exact A12|].
    pose proof (PNBKA.set_cs_str 1 s6 x7 g7) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS. fold s7 in XS. rewrite XS. unfold s7. rewrite PNBKA.set_cs_src. clear - SZ7 SZ6. lia. }
  { exact A1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx9 R9 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 RP9 LM9 STEP9 AXL9 RES9 BB9 AG9.
  assert (RK9 : forall k, In k (25%nat :: MIDXREGS) -> getr R9 (reg k) = getr R8 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R8 R9 k RP9). revert k Hk. unfold MIDXREGS. kin. }
  assert (MID9 : midx R R9 sp fb F) by (apply (midx_keep R R8 R9 sp fb F MID8); intros k Hk; apply RK9; right; exact Hk).
  assert (BB9' : PNM.b_bb s9 = PNM.b_bb s) by (rewrite BB9; unfold s7; rewrite PNBKA.set_cs_bb; exact BB6).
  pose proof (PNBKA.set_cs_str 1 s6 x7 g7) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS. fold s7 in XS.
  assert (SRC7 : PNM.b_src s7 = PNM.b_src s6) by (unfold s7; apply PNBKA.set_cs_src).
  destruct RES9 as [(v & Hv & ECv & MO0 & CAT & LENv & INVv)|(EC9 & INV9 & PRG)].
  - apply (rx_fork1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 fx9 R9 v (pa_errcat_obj PMA.AD) PB RCS CTX G LM9 INVv MID9 ECv ltac:(clear - Hv; lia)).
    + left. split; [clear - Hv; lia|]. split; [reflexivity|]. split; [exact MO0| exact CAT].
    + apply (Nat.le_trans _ (length (PNM.b_stk s7))); [exact (btop_len s s7 TP7)| exact LENv].
    + exact BB9'.
  - unfold PNRA.bprog_cs, PNRA.bcs_str in PRG. cbn [Z.eqb] in PRG. destruct PRG as (TP9 & UN9 & SZ9). rewrite XS, SRC7 in SZ9. rewrite SRC7 in UN9.
    apply (rx_fork1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M9 model9 LK9 Aw9 s9 sm9 ax9 cr9 fx9 R9 e cat PB RCS CTX G LM9 INV9 MID9 EC9 HE).
    + right. split; [reflexivity|]. split; [reflexivity|]. split; [exact (PNBKA.btop_pos_trans s s7 s9 TP7 TP9)|]. split; [clear - UN9 UN6; lia| clear - SZ9 SZ7 SZ6; lia].
    + exact (btop_len s s9 (PNBKA.btop_pos_trans s s7 s9 TP7 TP9)).
    + exact BB9'.
Qed.

(* [comment removed for export] *)
Lemma arm_rx K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.str_push_back_spec L ar HI -> PNRAa.read_cstring_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0610 M3 model3) K.
Proof.
  intros PB RCS CTX G LM3 MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INV & _ & HE & UNR & _).
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM3) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM3) as (_ & _ & OVIS3 & _).
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM3) as (Z368 & Z369 & Z376 & Z384 & TW2 & TW8 & VSTR & SHAPE).
  assert (GTB : PM.tb_ok (PNM.b_tb s) (PNM.b_tg s)).
  { destruct LM3 as (_ & (_ & _ & _ & _ & _ & _ & _ & GR) & _). exact (proj1 (proj2 GR)). }
  assert (UN0 : 0 <= PM.unread (PNM.b_src s) sm).
  { destruct LM3 as (_ & (PA & IA & _) & _). exact (PNBKA.unread_nonneg _ _ _ _ _ _ _ PA IA). }
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (ONSH : 2147446784 + 17592186048512 <= fb + 464 \/ fb + 464 + 416 <= 2147446784) by assumption.
  assert (OR : 6905856 <= fb + 464 <= 140737488354912) by assumption.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (NEXT : forall (fx4 : FPState) R4 M5 model5 x',
            rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK3 Aw3 (set_cs 1 s x' (PNM.b_tg s)) sm ax cr ->
            (forall v c, PMSPA.ec_at RSEGS M3 (fb + 1024) v c -> PMSPA.ec_at RSEGS M5 (fb + 1024) v c) ->
            (forall k, In k MIDREGS -> getr R4 (reg k) = getr R3 (reg k)) ->
            getr R4 (reg 1) = Z_to_bv 64 0xb1000 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 464 + 368) -> getr R4 (reg 11) = Z_to_bv 64 47 ->
            getr R4 (reg 23) = Z_to_bv 64 (fb + 464 + 368) -> getr R4 (reg 24) = Z_to_bv 64 ((fb + 464 + 368) / 8 + 2147450880) ->
            PM.vs_size x' = 0 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (PNL.pn_str_push_back PMA.AN) M5 model5) K).
  { intros fx4 R4 M5 model5 x' LM5 ECK5 KS4 Z1 Z10 Z11 Z23 Z24 SZ0.
    pose proof (PNBKA.set_cs_str 1 s x' (PNM.b_tg s)) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS.
    apply (rx_round1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK3 Aw3 (set_cs 1 s x' (PNM.b_tg s)) sm ax cr fx4 R4 PB RCS CTX G LM5).
    - exact INV.
    - split; [exact (mid_keep R R3 R4 sp fb F MID3 KS4)|]. split; [exact Z23| exact Z24].
    - exact Z1.
    - exact Z10.
    - exact Z11.
    - apply ECK5. exact EC3.
    - exact (PNBKA.btop_pos_refl s INV).
    - apply PNBKA.set_cs_bb.
    - rewrite PNBKA.set_cs_src. exact UNR.
    - rewrite XS, SZ0, PNBKA.set_cs_src. clear - UNR. lia. }
  assert (SHK : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 + 2147450880 < 2 ^ 64 /\ 2147446784 <= x / 8 + 2147450880 < 2147446784 + 17592186048512).
  { intros x Hx. pose proof (Z.div_pos x 8 ltac:(clear - Hx; Lia.lia) ltac:(clear; Lia.lia)) as D0.
    pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; Lia.lia) ltac:(clear - Hx; Lia.lia)) as D1. clear - D0 D1. Lia.lia. }
  revert VSTR SHAPE GTB. destruct (PNM.b_tb s) as [n|c n p] eqn:ETB; intros VSTR SHAPE GTB.
  - (* [comment removed for export] *)
    destruct SHAPE as (Hn & U8 & Rn & TB0). destruct VSTR as (Dtb & Atb & _).
    assert (Q56 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    LeanFeed.pfeed P (PNARVXP.awvX0S_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => 2 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z23 & Z24 & NB0 & NB1).
    change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN) in MS4 |- *.
    apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx4 R3 R4 0xb0610 (PNL.pn_str_push_back PMA.AN) M4v
             (fun a => fb + 464 + 368 <= a < fb + 464 + 368 + 2) (PM.VShort 0) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; exact X]. }
    { intros a X. left. clear - X; lia. }
    { rewrite ETB. reflexivity. }
    { exact GTB. }
    { rewrite ETB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at. split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dtb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 368) 24); [| exact Atb].
        intros x Hx. unfold S, SB. destruct (SHK x ltac:(clear - Hx OR; lia)) as (K1 & K2). apply FR5; [exact K1|]. intros X. clear - X K2 ONSH. lia.
      - split; [clear; lia|]. change (2 * 0) with 0.
        apply (proj1 (L5A.u8_at_vis _ M5 (fb + 464 + 368) 0 (OVIS3 (fb + 464 + 368) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
        rewrite VIS5. exact NB0. }
    intros M5 model5 LM5 HID5 VIS5 FR5 MG5 ECK5.
    apply (NEXT fx4 R4 M5 model5 (PM.VShort 0) LM5 ECK5); [unfold MIDREGS; kks KS4| exact Z1| exact Z10| exact Z11| exact Z23| exact Z24| reflexivity].
  - (* [comment removed for export] *)
    destruct SHAPE as (U8 & Rb & TB1 & UD & UN & Hn & Hc & Hp & P8 & PNS & PZ & PW & PSP & POP & PIM & PIN). destruct VSTR as (Dtb & Atb & (W0 & W8 & W16 & _ & _ & Hev & DBp & CBp)).
    assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - Rb; lia).
    assert (Q57 : 0 <= p < 2 ^ 64) by (clear - Hp; lia).
    assert (Q58 : 0 <= n < 2 ^ 64) by (clear - Hn Hc; lia).
    assert (PCE : p + c <= 2 ^ 47).
    { destruct LM3 as ((HH3 & _) & _). pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH3 (p, c) (in_or_app _ _ _ (or_introl PIN))) as (_ & Q1). exact Q1. }
    LeanFeed.pfeed P (PNARVXP.awvX0L_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVXP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z23 & Z24 & SZ0 & D0).
    change 0xd5bc4 with (PNL.pn_str_push_back PMA.AN) in MS4 |- *.
    apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx4 R3 R4 0xb0610 (PNL.pn_str_push_back PMA.AN) M4v
             (fun a => p <= a < p + 1 \/ fb + 464 + 376 <= a < fb + 464 + 376 + 8) (PM.VLong c 0 p) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; left; clear - X; lia| intros X; apply N; right; exact X]. }
    { intros a [X|X]; [right; left; exists p, c; split; [rewrite ETB; left; reflexivity| clear - X Hc; lia]| left; clear - X; lia]. }
    { rewrite ETB. reflexivity. }
    { exact GTB. }
    { rewrite ETB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at.
      assert (SHK5 : forall x, 0 <= x < 2 ^ 47 -> M5 (Z_to_bv 64 (x / 8 + 2147450880)) = M3 (Z_to_bv 64 (x / 8 + 2147450880))).
      { intros x Hx. destruct (SHK x Hx) as (K1 & K2). apply FR5; [exact K1|]. intros [X|X]; [clear - X K2 PNS; lia| clear - X K2 ONSH; lia]. }
      split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dtb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 368) 24); [| exact Atb]. intros x Hx. unfold S, SB. apply SHK5. clear - Hx OR; lia.
      - split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 368) (c + 1)); [| clear - OR; lia| clear - OR; lia| exact W0].
                 intros j Hj. apply FR5; [clear - Hj OR; lia|]. intros [X|X]; [clear - X Hj POP; lia| clear - X Hj; lia]. }
        split. { replace (fb + 464 + 368 + 8) with (fb + 464 + 376) by (clear; lia).
                 apply (proj1 (L5A.u64_at_vis _ M5 (fb + 464 + 376) 0 (OVIS3 (fb + 464 + 376) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
                 rewrite VIS5. exact SZ0. }
        split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 368 + 16) p); [| clear - OR; lia| clear - OR; lia| exact W16].
                 intros j Hj. apply FR5; [clear - Hj OR; lia|]. intros [X|X]; [clear - X Hj POP; lia| clear - X Hj; lia]. }
        split; [clear - Hc; lia|]. split; [exact Hc|]. split; [exact Hev|].
        split; [exact (L5.defined_grows M3 M5 _ _ MG5 DBp)|].
        apply (PMFA.accA_agree M3 M5 p c); [| exact CBp]. intros x Hx. unfold S, SB. apply SHK5. clear - Hx Hp PCE; lia. }
    intros M5 model5 LM5 HID5 VIS5 FR5 MG5 ECK5.
    apply (NEXT fx4 R4 M5 model5 (PM.VLong c 0 p) LM5 ECK5); [unfold MIDREGS; kks KS4| exact Z1| exact Z10| exact Z11| exact Z23| exact Z24| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma disp11 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 11 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0610 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (11 - 1)) with (Z_to_bv 64 10) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ11_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 11 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0610 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

End WithHeap.
End PNARVX.
