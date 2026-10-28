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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvNP_b PnARvK_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVN.
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
Lemma arm_unk K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb03bc M3 model3) K.
Proof.
  intros MKE CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & INV & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVNP.awvU_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx4 R3 R4 0xb03bc 0xae848 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  pose proof (mid_keep R R3 R4 sp fb F MID3 ltac:(unfold MIDREGS; kks KS4)) as MID4.
  pose proof MID4 as (B2 & B3 & B4 & _).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model4 LK3 Aw3 s sm ax cr fx4 R4 0xb03c8 14 e cat MKE CTX G LM4 EC3 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  { exact Y10. }
  { exact Y11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm (PNST.bax_add_cat ax) cr CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm (PNST.bax_add_cat ax) cr CTX G LM5) as (U10b & WR8b & _).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  LeanFeed.pfeed P (PNARVNP.awvUc_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO0 : L5.u8_at RSEGS M9v (fb + 464 + 8) 0) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s sm (PNST.bax_add_cat ax) cr fx5 fx9 R5 R9 0xb03c8 0 M9v CTX G LM5 MS9 MG9).
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
  - left. exists 14. split; [clear; lia|]. split; [exact EC5|]. split; [reflexivity| apply bax_cat_add].
  - exact INV.
  - apply Nat.le_refl.
  - intros _ X. exfalso. clear - X. lia.
Qed.

(* [comment removed for export] *)
Lemma disp12 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 12 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 12 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb03bc M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (12 - 1)) with (Z_to_bv 64 11) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 12 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ12_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 12 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb03bc Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp15 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 15 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 15 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb03bc M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (15 - 1)) with (Z_to_bv 64 14) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 15 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ15_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 15 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb03bc Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp0 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 0 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 0 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb03bc M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  assert (D13' : getr R3 (reg 13) = Z_to_bv 64 18446744073709551615) by (rewrite D13; apply bv_eq; vm_compute; reflexivity).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 0 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ0_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 0 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb03bc Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma dispr1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  20 <= t <= 126 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb t F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb03bc M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G HR LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  assert (QT : 0 <= t < 2 ^ 64) by (clear - HR; lia).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJr1_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => t | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb03bc Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma dispr2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  128 <= t <= 254 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb t F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb03bc M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G HR LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  assert (QT : 0 <= t < 2 ^ 64) by (clear - HR; lia).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJr2_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 35%nat => t | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax t F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb03bc Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma disp6 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 6 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0b8c M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (6 - 1)) with (Z_to_bv 64 5) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ6_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0b8c Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma arm_null6 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0b8c M3 model3) K.
Proof.
  intros CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INV & _).
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr 104 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 104) / 8 + 2147450880) with 2147607325 in VFX. fold MV3 in VFX. conj_open VFX.
  LeanFeed.pfeed P (PNARVNP.awvN6_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 6 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx9 R3 R9 0xb0b8c 1 M9v CTX G LM MS9 MG9).
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
  - right. split; [exact EC3|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact (PNBKA.btop_pos_refl s INV).
  - exact INV.
  - apply Nat.le_refl.
  - intros R0 _. exact R0.
Qed.

(* [comment removed for export] *)
Lemma disp10 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 10 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0d2c M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (10 - 1)) with (Z_to_bv 64 9) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ10_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0d2c Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma arm_null10 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0d2c M3 model3) K.
Proof.
  intros CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & INV & _).
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr 104 CTX G LM ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 104) / 8 + 2147450880) with 2147607325 in VFX. fold MV3 in VFX. conj_open VFX.
  LeanFeed.pfeed P (PNARVNP.awvN10_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 10 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx9 R3 R9 0xb0d2c 1 M9v CTX G LM MS9 MG9).
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
  - right. split; [exact EC3|]. unfold PNRA.bprog_value, PNRA.bpush_rel. left. exact (PNBKA.btop_pos_refl s INV).
  - exact INV.
  - apply Nat.le_refl.
  - intros R0 _. exact R0.
Qed.

(* [comment removed for export] *)
Lemma disp3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 3 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0664 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (3 - 1)) with (Z_to_bv 64 2) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ3_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0664 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma arm_cont3 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.begin_document_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0664 M3 model3) K.
Proof.
  intros BSP CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & ARGS & _ & _ & INV & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (_ & _ & _ & _ & ROOM).
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVNP.awvC3_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11 & Y12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx4 R3 R4 0xb0664 0xae924 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  pose proof (mid_keep R R3 R4 sp fb F MID3 ltac:(unfold MIDREGS; kks KS4)) as MID4.
  pose proof MID4 as (B2 & B3 & B4 & _).
  change 0xae924 with (PNL.pn_begin_document PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M3 model4 LK3 Aw3 s sm ax cr fx4 R4 722548 e cat (PNL.pn_begin_document PMA.AN) 7 (PNRA.bargs3 PMA.AD) PNRA.bprog_value
           (proj1 (PNRA.brun_spec_iff RSEGS PMA.AD PMA.AN PMA.AAD L ar HI false (PNL.pn_begin_document PMA.AN) 7 (PNRA.bargs3 PMA.AD) PNRA.bprog_value) BSP fb) ltac:(right; reflexivity) CTX G LM4 INV EC3 HE UNR).
  { unfold PNRA.bargs3, PNRA.o_p, PNRA.o_v, PNRA.o_ec, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10|]. split; [exact Y11| exact Y12]. }
  { exact Y1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BB5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (_ & _ & _ & _ & _ & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  LeanFeed.pfeed P (PNARVNP.awvC3r_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MOR : PNM.b_more s5 = 0 \/ PNM.b_more s5 = 1).
  { destruct LM5 as (_ & (PA5 & _) & _). destruct PA5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (QOP : 0 <= fb + 464 + 8 /\ fb + 464 + 8 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  assert (INV5 : PNRA.binv s5) by (destruct RES5 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X).
  assert (LEN5 : (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat).
  { destruct RES5 as [(v & _ & _ & _ & _ & X & _)|(_ & _ & X)]; [exact X|]. unfold PNRA.bprog_value, PNRA.bpush_rel in X.
    destruct X as [X|(c & X & _)]; [exact (btop_len s s5 X)| rewrite X, length_app; cbn [length]; clear; Lia.lia]. }
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 3 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx9 R5 R9 722548 (PNM.b_more s5) M9v CTX G LM5 MS9 MG9).
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
  - destruct RES5 as [(v & Hv & ECv & MO0 & CAT & _)|(EC5 & _ & PRG)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO0| exact CAT].
    + right. split; [exact EC5| exact PRG].
  - exact INV5.
  - exact LEN5.
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB5. destruct STEP5 as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

(* [comment removed for export] *)
Lemma disp4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax  F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 4 F ->
  (forall (fxj : FPState) Rj modelj, rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 modelj LK3 Aw3 s sm ax cr -> mid R Rj sp fb F ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fxj Rj 0xb0890 M3 modelj) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros CTX G LM DR KJ.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (4 - 1)) with (Z_to_bv 64 3) in D13.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ4_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0890 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  apply (KJ fxj Rj modelj LMj). exact (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)).
Qed.

(* [comment removed for export] *)
Lemma arm_cont4 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.begin_array_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  mid R R3 sp fb F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0890 M3 model3) K.
Proof.
  intros BSP CTX G LM MID3 EC3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _ & _ & _ & _ & ARGS & _ & _ & INV & _ & HE & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct ARGS as (_ & _ & _ & _ & ROOM).
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM) as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVNP.awvC4_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx4 & R4 & M4v & MG4 & _ & FRZ4 & MS4 & KS4 & Y1 & Y10 & Y11 & Y12).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fx4 R3 R4 0xb0890 0xb37a8 M4v CTX G LM MS4 MG4 FRZ4).
  intros model4 LM4 HID4.
  pose proof (mid_keep R R3 R4 sp fb F MID3 ltac:(unfold MIDREGS; kks KS4)) as MID4.
  pose proof MID4 as (B2 & B3 & B4 & _).
  change 0xb37a8 with (PNL.pn_begin_array PMA.AN).
  apply (PNARVK.rv_call_brun L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M3 model4 LK3 Aw3 s sm ax cr fx4 R4 723104 e cat (PNL.pn_begin_array PMA.AN) 7 (PNRA.bargs3 PMA.AD) PNRA.bprog_value
           (proj1 (PNRA.brun_spec_iff RSEGS PMA.AD PMA.AN PMA.AAD L ar HI false (PNL.pn_begin_array PMA.AN) 7 (PNRA.bargs3 PMA.AD) PNRA.bprog_value) BSP fb) ltac:(right; reflexivity) CTX G LM4 INV EC3 HE UNR).
  { unfold PNRA.bargs3, PNRA.o_p, PNRA.o_v, PNRA.o_ec, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec PMA.AD PnLayoutA_b.ADDR_A].
    rewrite L5K.rl10, L5K.rl11, L5K.rl12. split; [exact Y10|]. split; [exact Y11| exact Y12]. }
  { exact Y1. }
  { unfold L5.ra_ok; clear; lia. }
  { exact B2. }
  { rewrite B3. exact Rgp. }
  { rewrite B4. exact Rtp. }
  intros fx5 R5 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 RP5 LM5 STEP5 AXL5 RES5 BB5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (PF5 & _).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 CTX G LM5) as (_ & _ & _ & _ & _ & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  LeanFeed.pfeed P (PNARVNP.awvC4r_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVNP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & ZR).
  assert (Z1 : getr R9 (reg 1) = Z_to_bv 64 726080) by (conj_open ZR; assumption).
  assert (Z10 : getr R9 (reg 10) = Z_to_bv 64 ((F / 8) + 2147450880)) by (conj_open ZR; assumption).
  assert (Z11 : getr R9 (reg 11) = Z_to_bv 64 64) by (conj_open ZR; assumption).
  assert (MOR : PNM.b_more s5 = 0 \/ PNM.b_more s5 = 1).
  { destruct LM5 as (_ & (PA5 & _) & _). destruct PA5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). exact X. }
  assert (QOP : 0 <= fb + 464 + 8 /\ fb + 464 + 8 + 1 <= 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  assert (INV5 : PNRA.binv s5) by (destruct RES5 as [(v & _ & _ & _ & _ & _ & X)|(_ & X & _)]; exact X).
  assert (LEN5 : (length (PNM.b_stk s) <= length (PNM.b_stk s5))%nat).
  { destruct RES5 as [(v & _ & _ & _ & _ & X & _)|(_ & _ & X)]; [exact X|]. unfold PNRA.bprog_value, PNRA.bpush_rel in X.
    destruct X as [X|(c & X & _)]; [exact (btop_len s s5 X)| rewrite X, length_app; cbn [length]; clear; Lia.lia]. }
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 4 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax5 cr5 fx5 fx9 R5 R9 723104 (PNM.b_more s5) M9v CTX G LM5 MS9 MG9).
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
  - destruct RES5 as [(v & Hv & ECv & MO0 & CAT & _)|(EC5 & _ & PRG)].
    + left. exists v. split; [exact Hv|]. split; [exact ECv|]. split; [exact MO0| exact CAT].
    + right. split; [exact EC5| exact PRG].
  - exact INV5.
  - exact LEN5.
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB5. destruct STEP5 as (_ & _ & _ & _ & LE). exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

End WithHeap.
End PNARVN.
