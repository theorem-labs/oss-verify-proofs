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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvDP_b PnARvK_b PnARvKX_b PnARvKT_b PnARvKD_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVD.
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

Lemma sh_apart e F : e mod 8 = 0 -> F / 8 * 8 = F -> ((e - 40) + 40 <= F \/ F + 512 <= (e - 40)) ->
  ((((e - 24) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= (((e - 24) / 8) + 2147450880)).
Proof.
  intros He HF [X|X].
  - left. assert ((e - 24) / 8 < F / 8) by (apply Z.div_lt_upper_bound; [Lia.lia| rewrite Z.mul_comm, HF; Lia.lia]). Lia.lia.
  - right. assert (F / 8 + 64 <= (e - 24) / 8) by (apply Z.div_le_lower_bound; [Lia.lia| Lia.lia]). Lia.lia.
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
Lemma d_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb15d8 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 -> getr R4 (reg 23) = Z_to_bv 64 (F + 352) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 X23 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb15d8 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5) as (U10 & WR8 & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 352)) by (rewrite (L5SAR.cs_of_preserved R4 R5 23%nat RP5) by inl; exact X23).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVDP.awvD1c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 fx5 fx9 R5 R9 0xb15d8 0 M9v CTX G LM5 MS9 MG9).
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
Lemma d_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midx R R3 sp fb F ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb1300 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 EC3 TP3 BB3.
  pose proof MID3 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (U10 & WR8 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVDP.awvD5_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb1300 1 M9v CTX G LM MS9 MG9).
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
Lemma d_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 (ptr c p : Z) :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midx R R3 sp fb F -> PNM.b_tb s3 = PM.VLong c 42 p ->
  getr R3 (reg 10) = Z_to_bv 64 ptr -> 0 <= ptr < 2 ^ 64 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb1274 M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 ETB X10 Hptr EC3 TP3 BB3.
  pose proof MID3 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 120 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 120) / 8 + 2147450880) with 2147607327 in VFX.
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (Z368 & Z369 & Z376 & Z384 & TW2 & TW8 & _ & SHAPE).
  rewrite ETB in SHAPE. destruct SHAPE as (U8 & Rb & TB1 & UD & UN & Hn & Hc & Hp & P8 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - Rb; lia).
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - Hp; lia).
  assert (Q58 : 0 <= 42 < 2 ^ 64) by (clear; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVDP.awvD4L_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 45%nat => ptr | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => 42 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & _).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx9 R3 R9 0xb1274 0xb1300 M9v
           (fun a => F / 8 + 2147450880 + 48 <= a < F / 8 + 2147450880 + 48 + 2 \/ F + 384 <= a < F + 384 + 16) CTX G LM MS9 MG9).
  { intros a Ha N. apply FRZ9; [exact Ha| intros X; apply N; left; clear - X; lia| intros X; apply N; right; clear - X; lia]. }
  { intros a [X|X]; [right; right; clear - X; lia| right; left; clear - X; lia]. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  apply (d_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M4 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx9 R9 CTX G LM4 INV3).
  - apply (midx_keep R R3 R9 sp fb F MID3). unfold MIDXREGS. kks KS9.
  - apply ECK4. exact EC3.
  - exact TP3.
  - exact BB3.
Qed.

(* [comment removed for export] *)
Lemma d_dec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  PNARVKD.dec128_specS L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> midx R R3 sp fb F -> PM.vs_size (PNM.b_tb s3) = 42 ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb11f8 M3 model3) K.
Proof.
  intros DEC CTX G LM INV3 MID3 SZ3 EC3 TP3 BB3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID3 as ((J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27) & J23 & J24).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (PF3 & _).
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM) as (Z368 & Z369 & Z376 & Z384 & TW2 & TW8 & _ & SHAPE).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  revert SHAPE SZ3. destruct (PNM.b_tb s3) as [n|c n p] eqn:ETB; intros SHAPE SZ3; cbn [PM.vs_size] in SZ3.
  { exfalso. destruct SHAPE as (Hn & _). clear - Hn SZ3. lia. }
  subst n. destruct SHAPE as (U8 & Rb & TB1 & UD & UN & Hn & Hc & Hp & P8 & _).
  assert (Q56 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (clear - Rb; lia).
  assert (Q57 : 0 <= p < 2 ^ 64) by (clear - Hp; lia).
  assert (Q58 : 0 <= 42 < 2 ^ 64) by (clear; lia).
  assert (R58 : 0 <= 42 <= 134217728) by (clear; lia).
  LeanFeed.pfeed P (PNARVDP.awvD3L_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => 42 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & A1 & A10 & A11 & A12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx4 R3 R4 0xb11f8 0xb3e24 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  assert (MID4 : midx R R4 sp fb F) by (apply (midx_keep R R3 R4 sp fb F MID3); unfold MIDXREGS; kks KS4).
  pose proof MID4 as ((B2 & B3 & B4 & _) & _).
  change 0xb3e24 with (PNL.pn_dec128 PMA.AN).
  apply (PNARVKD.rv_call_dec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model4 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb1274 c p DEC CTX G LM4 ETB A1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact A10. }
  { exact A11. }
  { exact A12. }
  intros fx6 R6 M6 model6 LK6 Aw6 ptr RP6 Y10 Hptr LM6 AG6 ECK6.
  assert (RK : forall k, In k MIDXREGS -> getr R6 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R6 k RP6). revert k Hk. unfold MIDXREGS. kin. }
  apply (d_vis K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 s3 sm3 (PNST.bax_add_dec ax3) cr3 fx6 R6 ptr c p CTX G LM6 INV3).
  - exact (midx_keep R R4 R6 sp fb F MID4 RK).
  - exact ETB.
  - exact Y10.
  - clear - Hptr Hp. lia.
  - apply ECK6. exact EC3.
  - exact TP3.
  - exact BB3.
Qed.

(* [comment removed for export] *)
Lemma d_rsz K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  PMA.str_resize_spec L ar HI -> PNARVKD.dec128_specS L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R3 sp fb F -> getr R3 (reg 23) = Z_to_bv 64 (F + 352) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb05a0 M3 model3) K.
Proof.
  intros RSZ DEC CTX G LM3 INV3 MID3 X23 EC3 TP3 BB3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM3) as (PF3 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM3) as (_ & _ & OVIS3 & _).
  pose proof (PNARVKX.tbfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM3) as (Z368 & Z369 & Z376 & Z384 & TW2 & TW8 & VSTR & SHAPE).
  assert (GTB : PM.tb_ok (PNM.b_tb s3) (PNM.b_tg s3)).
  { destruct LM3 as (_ & (_ & _ & _ & _ & _ & _ & _ & GR) & _). exact (proj1 (proj2 GR)). }
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (ONSH : 2147446784 + 17592186048512 <= fb + 464 \/ fb + 464 + 416 <= 2147446784) by assumption.
  assert (OR : 6905856 <= fb + 464 <= 140737488354912) by assumption.
  assert (SPR : 140735332487392 <= sp <= 140737488355328) by assumption.
  assert (FDEF : L5.defined MV3 F 512) by assumption.
  assert (QF : 0 <= F + 352 /\ F + 360 + 8 <= 2 ^ 64) by (match goal with H : 6905856 <= F <= _ |- _ => clear - H; lia end).
  destruct (PMCG.u64_of_defined RSEGS MV3 (F + 352) ltac:(clear - QF; lia) ltac:(clear - QF; lia) ltac:(apply (L5.defined_sub MV3 F 512); [exact FDEF| clear; lia| clear; lia])) as (v53 & Q53 & PAY53).
  destruct (PMCG.u64_of_defined RSEGS MV3 (F + 360) ltac:(clear - QF; lia) ltac:(clear - QF; lia) ltac:(apply (L5.defined_sub MV3 F 512); [exact FDEF| clear; lia| clear; lia])) as (v54 & Q54 & PAY54).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  assert (NEXT : forall (fx4 : FPState) R4 M5 model5 x',
            rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK3 Aw3 (set_cs 1 s3 x' (PNM.b_tg s3)) sm3 ax3 cr3 ->
            (forall v c, PMSPA.ec_at RSEGS M3 (fb + 1024) v c -> PMSPA.ec_at RSEGS M5 (fb + 1024) v c) ->
            (forall k, In k MIDREGS -> getr R4 (reg k) = getr R3 (reg k)) ->
            getr R4 (reg 1) = Z_to_bv 64 0xb11f8 -> getr R4 (reg 10) = Z_to_bv 64 (fb + 464 + 368) -> getr R4 (reg 11) = Z_to_bv 64 42 ->
            getr R4 (reg 23) = Z_to_bv 64 (fb + 464 + 368) -> getr R4 (reg 24) = Z_to_bv 64 ((fb + 464 + 368) / 8 + 2147450880) ->
            PM.vs_size x' = 0 ->
            srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 (pa_str_resize PMA.AD) M5 model5) K).
  { intros fx4 R4 M5 model5 x' LM5 ECK5 KS4 Z1 Z10 Z11 Z23 Z24 SZ0.
    pose proof (PNBKA.set_cs_str 1 s3 x' (PNM.b_tg s3)) as XS. unfold PNRA.bcs_str in XS. cbn [Z.eqb] in XS.
    set (s5 := set_cs 1 s3 x' (PNM.b_tg s3)) in *.
    assert (MID4 : midx R R4 sp fb F) by (split; [exact (mid_keep R R3 R4 sp fb F MID3 KS4)|]; split; [exact Z23| exact Z24]).
    pose proof MID4 as ((B2 & B3 & B4 & _) & _).
    apply (PNARVKT.rv_call_resize L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK3 Aw3 s5 sm3 ax3 cr3 fx4 R4 0xb11f8 42 1 RSZ (or_intror eq_refl) CTX G LM5 Z1).
    { unfold L5.ra_ok; clear; lia. }
    { exact B2. }
    { rewrite B3. exact Rgp. }
    { rewrite B4. exact Rtp. }
    { exact Z10. }
    { exact Z11. }
    { unfold PNRA.bcs_str. cbn [Z.eqb]. rewrite XS, SZ0. unfold PM.CHUNK. clear; lia. }
    { unfold PM.CHUNK. clear; lia. }
    intros fx6 R6 M6 model6 LK6 Aw6 x6 g6 cr6 RP6 SZ6 LM6 AG6 ECK6.
    assert (RK : forall k, In k MIDXREGS -> getr R6 (reg k) = getr R4 (reg k)).
    { intros k Hk. apply (L5SAR.cs_of_preserved R4 R6 k RP6). revert k Hk. unfold MIDXREGS. kin. }
    pose proof (PNBKA.set_cs_str 1 s5 x6 g6) as XS6. unfold PNRA.bcs_str in XS6. cbn [Z.eqb] in XS6.
    apply (d_dec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M6 model6 LK6 Aw6 (set_cs 1 s5 x6 g6) sm3 ax3 cr6 fx6 R6 DEC CTX G LM6).
    - exact INV3.
    - exact (midx_keep R R4 R6 sp fb F MID4 RK).
    - rewrite XS6. exact SZ6.
    - apply ECK6. apply ECK5. exact EC3.
    - exact TP3.
    - rewrite PNBKA.set_cs_bb. unfold s5. rewrite PNBKA.set_cs_bb. exact BB3. }
  assert (SHK : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 + 2147450880 < 2 ^ 64 /\ 2147446784 <= x / 8 + 2147450880 < 2147446784 + 17592186048512).
  { intros x Hx. pose proof (Z.div_pos x 8 ltac:(clear - Hx; Lia.lia) ltac:(clear; Lia.lia)) as D0.
    pose proof (Z.div_lt_upper_bound x 8 17592186044416 ltac:(clear; Lia.lia) ltac:(clear - Hx; Lia.lia)) as D1. clear - D0 D1. Lia.lia. }
  revert VSTR SHAPE GTB. destruct (PNM.b_tb s3) as [n|c n p] eqn:ETB; intros VSTR SHAPE GTB.
  - (* [comment removed for export] *)
    destruct SHAPE as (Hn & U8 & Rn & TB0). destruct VSTR as (Dtb & Atb & _).
    assert (Q56 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
    LeanFeed.pfeed P (PNARVDP.awvD2S_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 53%nat => v53 | 54%nat => v54 | 56%nat => 2 * n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z12 & Z23 & Z24 & NB0 & NB1 & _).
    change 0xd628c with (pa_str_resize PMA.AD) in MS4 |- *.
    apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx4 R3 R4 0xb05a0 (pa_str_resize PMA.AD) M4v
             (fun a => sp - 120 <= a < sp - 120 + 16 \/ fb + 464 + 368 <= a < fb + 464 + 368 + 2) (PM.VShort 0) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a [X|X]; [right; right; clear - X; lia| left; clear - X; lia]. }
    { rewrite ETB. reflexivity. }
    { exact GTB. }
    { rewrite ETB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at. split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dtb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 368) 24); [| exact Atb].
        intros x Hx. unfold S, SB. destruct (SHK x ltac:(clear - Hx OR; lia)) as (K1 & K2). apply FR5; [exact K1|]. intros [X|X]; [clear - X K2 SPR; lia| clear - X K2 ONSH; lia].
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
    LeanFeed.pfeed P (PNARVDP.awvD2L_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 53%nat => v53 | 54%nat => v54 | 56%nat => (c + 1) mod 256 | 57%nat => p | 58%nat => n | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
    destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Z1 & Z10 & Z11 & Z12 & Z23 & Z24 & SZ0 & D0 & _).
    change 0xd628c with (pa_str_resize PMA.AD) in MS4 |- *.
    apply (PNARVKX.rv_piece_tb L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx3 fx4 R3 R4 0xb05a0 (pa_str_resize PMA.AD) M4v
             (fun a => sp - 120 <= a < sp - 120 + 16 \/ p <= a < p + 1 \/ fb + 464 + 376 <= a < fb + 464 + 376 + 8) (PM.VLong c 0 p) CTX G LM3 MS4 MG4).
    { intros a Ha N. apply FRZ4; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; clear - X; lia| intros X; apply N; right; right; exact X]. }
    { intros a [X|[X|X]]; [right; right; clear - X; lia| right; left; exists p, c; split; [rewrite ETB; left; reflexivity| clear - X Hc; lia]| left; clear - X; lia]. }
    { rewrite ETB. reflexivity. }
    { exact GTB. }
    { rewrite ETB. reflexivity. }
    { intros M5 FR5 MG5 VIS5. unfold PM.vstr_at.
      assert (SHK5 : forall x, 0 <= x < 2 ^ 47 -> M5 (Z_to_bv 64 (x / 8 + 2147450880)) = M3 (Z_to_bv 64 (x / 8 + 2147450880))).
      { intros x Hx. destruct (SHK x Hx) as (K1 & K2). apply FR5; [exact K1|]. intros [X|[X|X]]; [clear - X K2 SPR; lia| clear - X K2 PNS; lia| clear - X K2 ONSH; lia]. }
      split; [exact (L5.defined_grows M3 M5 _ _ MG5 Dtb)|]. split.
      - apply (PMFA.accA_agree M3 M5 (fb + 464 + 368) 24); [| exact Atb]. intros x Hx. unfold S, SB. apply SHK5. clear - Hx OR; lia.
      - split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 368) (c + 1)); [| clear - OR; lia| clear - OR; lia| exact W0].
                 intros j Hj. apply FR5; [clear - Hj OR; lia|]. intros [X|[X|X]]; [match goal with H : ((sp - 160) + 160 <= fb + 464 \/ _) |- _ => clear - X Hj H; lia end| clear - X Hj POP; lia| clear - X Hj; lia]. }
        split. { replace (fb + 464 + 368 + 8) with (fb + 464 + 376) by (clear; lia).
                 apply (proj1 (L5A.u64_at_vis _ M5 (fb + 464 + 376) 0 (OVIS3 (fb + 464 + 376) 8 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - OR; lia) ltac:(clear - OR; lia))).
                 rewrite VIS5. exact SZ0. }
        split. { apply (L5C.u64_at_agree RSEGS M3 M5 (fb + 464 + 368 + 16) p); [| clear - OR; lia| clear - OR; lia| exact W16].
                 intros j Hj. apply FR5; [clear - Hj OR; lia|]. intros [X|[X|X]]; [match goal with H : ((sp - 160) + 160 <= fb + 464 \/ _) |- _ => clear - X Hj H; lia end| clear - X Hj POP; lia| clear - X Hj; lia]. }
        split; [clear - Hc; lia|]. split; [exact Hc|]. split; [exact Hev|].
        split; [exact (L5.defined_grows M3 M5 _ _ MG5 DBp)|].
        apply (PMFA.accA_agree M3 M5 p c); [| exact CBp]. intros x Hx. unfold S, SB. apply SHK5. clear - Hx Hp PCE; lia. }
    intros M5 model5 LM5 HID5 VIS5 FR5 MG5 ECK5.
    apply (NEXT fx4 R4 M5 model5 (PM.VLong c 0 p) LM5 ECK5); [unfold MIDREGS; kks KS4| exact Z1| exact Z10| exact Z11| exact Z23| exact Z24| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma d_fork K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 (fx5 : FPState) R5 (d : Z) :
  PMA.str_resize_spec L ar HI -> PNARVKD.dec128_specS L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 ->
  PNRA.binv s5 -> mid R R5 sp fb F ->
  getr R5 (reg 10) = Z_to_bv 64 d -> 0 <= d <= 16 -> getr R5 (reg 23) = Z_to_bv 64 (F + 352) ->
  PMSPA.ec_at RSEGS M5 (fb + 1024) e cat -> PNRA.btop_pos s s5 -> PNM.b_bb s5 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx5 R5 0xb0530 M5 model5) K.
Proof.
  intros RSZ DEC MKE CTX G LM5 INV5 MID5 X10 Hd X23 EC5 TP5 BB5.
  pose proof TP5 as (pre & c0 & top & _ & ES5 & _).
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (d + PNM.bs_pos top) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (Q37 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVDP.awvD1b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => d | 38%nat => e5 | 39%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb0530 0xb05a0 M6v pre top p5
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
    apply (d_rsz K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 RSZ DEC CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + apply ECK7. exact EC5.
    + exact TP7.
    + exact BB5.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx6 R5 R6 0xb0530 0xae848 M6v pre top p5
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
    apply (d_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax5 cr5 fx6 R6 MKE CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite (KS6 23%nat) by inl. exact X23.
    + apply ECK7. exact EC5.
    + exact (btop_len s s7 TP7).
Qed.

(* [comment removed for export] *)
Lemma arm_dec K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.src_read_spec L ar HI -> PMA.str_resize_spec L ar HI -> PNARVKD.dec128_specS L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0514 M3 model3) K.
Proof.
  intros SR RSZ DEC MKE CTX G LM3 MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & INV & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM3) as (PF3 & _).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVDP.awvD1a_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVDP.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12 & A23 & SHZ1 & SHZ0).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxa R3 Ra 0xb0514 0xaed4c Mav
           (fun a => F / 8 + 2147450880 + 44 <= a < F / 8 + 2147450880 + 44 + 2) CTX G LM3 MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; exact X]. }
  { intros a X. right; right. clear - X; lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr CTX G LM4) as (_ & _ & _ & _ & VSH4 & _).
  assert (SHB : forall k, (k = 44 \/ k = 45) -> L5.u8_at RSEGS Mav (F / 8 + 2147450880 + k) 0 -> aacc M4 (F + 8 * k) 8).
  { intros k Hk SHZ.
    assert (SHR : 0 <= F / 8 + 2147450880 + k /\ F / 8 + 2147450880 + k + 1 <= 2 ^ 64) by (clear - DF1 DF2 Hk; lia).
    assert (SH4 : L5.u8_at RSEGS M4 (F / 8 + 2147450880 + k) 0).
    { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M4 (F / 8 + 2147450880 + k) 0 (L5A.avis_sub _ (F / 8 + 2147450880) 64 (F / 8 + 2147450880 + k) 1 VSH4 ltac:(clear - Hk; lia) ltac:(clear - Hk; lia)) (proj1 SHR) (proj2 SHR))).
      rewrite HID4, VIS4. exact SHZ. }
    assert (HK : (8 = 8 /\ 0 = 0) \/ (1 <= 8 <= 7 /\ 0 = 8)) by (left; split; reflexivity).
    assert (HO8 : (8 * k) mod 8 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult). assert (HO0 : 0 <= 8 * k) by (clear - Hk; lia). assert (HF0 : 0 <= F) by (clear - GF1; lia).
    apply (aacc_local M4 F (8 * k) 8 0 (proj1 GF8) HO8 HO0 HF0 HK).
    replace (8 * k / 8) with k by (rewrite Z.mul_comm, Z.div_mul; [reflexivity| clear; lia]). replace (F / 8 + k + 2147450880) with (F / 8 + 2147450880 + k) by (clear; lia).
    assert (SHR1 : F / 8 + 2147450880 + k < 65536 \/ 6905856 <= F / 8 + 2147450880 + k) by (right; clear - DF1 Hk; lia).
    assert (SHR2 : 0 <= F / 8 + 2147450880 + k < 2 ^ 64) by (clear - SHR; lia).
    exact (L5ADHR.byte_of_u8 M4 (F / 8 + 2147450880 + k) 0 SH4 SHR1 SHR2). }
  assert (ACC : aacc M4 (F + 352) 16).
  { pose proof (SHB 44 ltac:(left; reflexivity) ltac:(replace (F / 8 + 2147450880 + 44) with (F / 8 + 2147450924) by (clear; lia); exact SHZ0)) as A44.
    pose proof (SHB 45 ltac:(right; reflexivity) ltac:(replace (F / 8 + 2147450880 + 45) with (F / 8 + 2147450925) by (clear; lia); exact SHZ1)) as A45.
    change (8 * 44) with 352 in A44. change (8 * 45) with 360 in A45.
    intros x Hx. destruct (Z_lt_le_dec x (F + 360)) as [X|X]; [apply A44; clear - Hx X; lia| apply A45; clear - Hx X; lia]. }
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R R3 Ra sp fb F MID3); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (PNARVK.rv_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xb0530 352 16 SR CTX G LM4
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
  apply (d_fork K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 R5 d RSZ DEC MKE CTX G LM5 INV5).
  - exact (mid_keep R Ra R5 sp fb F MIDa RK).
  - exact Y10d.
  - exact Hd.
  - rewrite (L5SAR.cs_of_preserved Ra R5 23%nat RP5) by inl. exact A23.
  - apply ECK5. apply ECK4. exact EC3.
  - exact TP5.
  - reflexivity.
Qed.

(* [comment removed for export] *)
Lemma disp19 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 19 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0514 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (19 - 1)) with (Z_to_bv 64 18) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ19_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 19 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0514 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

End WithHeap.
End PNARVD.
