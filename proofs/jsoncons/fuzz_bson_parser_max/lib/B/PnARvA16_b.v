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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnARvTP_b PnARvA16P_b PnARvK_b PnARvKV_b PnARvE_b PnARvF_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARVA16.
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

(* [comment removed for export] *)
Lemma arm_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx4 : FPState) R4 :
  PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R4 sp fb F ->
  getr R4 (reg 1) = Z_to_bv 64 0xb16cc -> getr R4 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R4 (reg 11) = Z_to_bv 64 1 -> getr R4 (reg 23) = Z_to_bv 64 (F + 208) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> (length (PNM.b_stk s) <= length (PNM.b_stk s3))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx4 R4 0xae848 M3 model3) K.
Proof.
  intros MKE CTX G LM INV3 MID4 X1 X10 X11 X23 EC3 LEN3.
  pose proof CTX as (Hw & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof MID4 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  change 0xae848 with (pa_make_ec PMA.AD).
  apply (PNARVK.rv_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 fx4 R4 0xb16cc 1 e cat MKE CTX G LM EC3 X1).
  { unfold L5.ra_ok; clear; lia. }
  { exact J2. }
  { rewrite J3. exact Rgp. }
  { rewrite J4. exact Rtp. }
  { exact X10. }
  { exact X11. }
  { clear; lia. }
  intros fx5 R5 M5 model5 LK5 Aw5 RP5 EC5 LM5 AG5.
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5)
    as (PF5 & OWN5 & SV5 & U8v5 & WRop5 & U8op5 & SVr5).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3 CTX G LM5)
    as (U10 & WR8 & OVIS5 & VF5 & VSH5 & MO5).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  unfold pfacts in PF5. conj_open PF5.
  assert (RK : forall k, In k MIDREGS -> getr R5 (reg k) = getr R4 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof (mid_keep R R4 R5 sp fb F MID4 RK) as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 208)) by (rewrite (L5SAR.cs_of_preserved R4 R5 23%nat RP5) by inl; exact X23).
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (clear - pf5; lia).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVA16P.awv16c_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVA16P.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & HMAG & SH8 & MO0 & D8).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M5 model5 LK5 Aw5 s3 sm3 (PNST.bax_add_cat ax3) cr3
           fx5 fx9 R5 R9 0xb16cc 0 M9v CTX G LM5 MS9 MG9).
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
Lemma arm_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2
      M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 (fx3 : FPState) R3 :
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 ->
  PNRA.binv s3 -> mid R R3 sp fb F -> getr R3 (reg 23) = Z_to_bv 64 (F + 208) ->
  PMSPA.ec_at RSEGS M3 (fb + 1024) e cat -> PNRA.btop_pos s s3 -> PNM.b_bb s3 = PNM.b_bb s ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb0e1c M3 model3) K.
Proof.
  intros CTX G LM INV3 MID3 X23 EC3 TP3 BB3.
  pose proof MID3 as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM)
    as (PF3 & OWN3 & SV3 & U8v3 & WRop3 & U8op3 & SVr3).
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 CTX G LM)
    as (U10 & WR8 & OVIS3 & VF3 & VSH3 & MO3).
  pose proof (PNARVKV.vfacts_of L ar C HI LY HIok IL ICok ILY K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3 40 CTX G LM
                ltac:(reflexivity) ltac:(clear; lia)) as VFX.
  change ((1251456 + 40) / 8 + 2147450880) with 2147607317 in VFX.
  set (MV3 := mrestrict (ahid Aw3 model3) M3) in *.
  unfold pfacts in PF3. conj_open PF3. conj_open VFX.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (clear - pf5; lia).
  destruct QV as (QV1 & QV2).
  assert (DEFP : L5.defined MV3 (F + 208) 4) by (apply (L5.defined_sub MV3 F 512); [assumption| clear; lia| clear; lia]).
  assert (QF : 0 <= F + 208 /\ F + 208 + 4 <= 2 ^ 64) by (match goal with H : 6905856 <= F <= _ |- _ => clear - H; lia end).
  destruct (u32_of_defined MV3 (F + 208) (proj1 QF) (proj2 QF) DEFP) as (v40 & Hv40 & PAY).
  assert (Hv40' : 0 <= v40 <= 4294967295) by (clear - Hv40; lia).
  assert (Hv40'' : 0 <= v40 < 2 ^ 64) by (clear - Hv40; lia).
  LeanFeed.pfeed P (PNARVA16P.awv16v_conc fx3 R3 MV3 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 40%nat => v40 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVA16P.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Z1 & Z10 & Z11 & ZR).
  assert (MO1 : L5.u8_at RSEGS M9v (fb + 464 + 8) 1) by (conj_open ZR; assumption).
  apply (PNARVF.rv_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK3 Aw3 s3 sm3 ax3 cr3
           fx3 fx9 R3 R9 0xb0e1c 1 M9v CTX G LM MS9 MG9).
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
  - intros R0 _. unfold PNRA.bb_room in *. rewrite BB3. destruct LM as (_ & _ & STEP & _). destruct STEP as (_ & _ & _ & _ & LE).
    exact (PGV8.v8_room_mono _ _ _ LE R0).
Qed.

Lemma sh_apart e F : e mod 8 = 0 -> F / 8 * 8 = F -> ((e - 40) + 40 <= F \/ F + 512 <= (e - 40)) ->
  ((((e - 24) / 8) + 2147450880) + 1 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 64 <= (((e - 24) / 8) + 2147450880)).
Proof.
  intros He HF [X|X].
  - left. assert ((e - 24) / 8 < F / 8) by (apply Z.div_lt_upper_bound; [Lia.lia| rewrite Z.mul_comm, HF; Lia.lia]). Lia.lia.
  - right. assert (F / 8 + 64 <= (e - 24) / 8) by (apply Z.div_le_lower_bound; [Lia.lia| Lia.lia]). Lia.lia.
Qed.

(* [comment removed for export] *)
Lemma arm K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax F fl LK2 M2 model2 (fx3 : FPState) R3 M3 model3 LK3 Aw3 :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rv_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 -> rv_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rv_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK3 Aw3 s sm ax cr ->
  PNARVE.dregs R R3 sp fb 16 F -> PMSPA.ec_at RSEGS M3 (fb + 1024) e cat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx3 R3 0xb016c M3 model3) K.
Proof.
  intros SR MKE CTX G LM DR EC3.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  destruct DR as (D2 & D3 & D4 & D8 & D9 & D10 & D13 & D18 & D19 & D20 & D21 & D22 & D23 & D26 & D27).
  assert (MID3 : mid R R3 sp fb F) by (unfold mid; repeat split; assumption).
  change (Z_to_bv 64 (16 - 1)) with (Z_to_bv 64 15) in D13.
  pose proof G as G'. unfold rv_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 3) with 512 in *. change (512 / 8) with 64 in *.
  pose proof GFR as (GF1 & GF2 & GF3 & _).
  assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044352) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  (* [comment removed for export] *)
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr CTX G LM)
    as (PF3 & _).
  unfold pfacts in PF3. conj_open PF3.
  assert (QV : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (clear - pf5; lia).
  destruct QV as (QV1 & QV2).
  LeanFeed.pfeed P (PNARVTP.awvJ16_conc fx3 R3 (mrestrict (ahid Aw3 model3) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | _ => 0 end)) ltac:(first [assumption | unfold PNARVTP.aligned; assumption]).
  destruct P as (fxj & Rj & Mjv & MGj & _ & FRZj & MSj & KSj & _).
  apply (rv_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M3 model3 LK3 Aw3 s sm ax cr fx3 fxj R3 Rj 0xb016c 0xb0da8 Mjv CTX G LM MSj MGj FRZj).
  intros modelj LMj HIDj.
  pose proof (mid_keep R R3 Rj sp fb F MID3 ltac:(unfold MIDREGS; kks KSj)) as MIDj.
  (* [comment removed for export] *)
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M3 modelj LK3 Aw3 s sm ax cr CTX G LMj)
    as (PFj & _).
  unfold pfacts in PFj. conj_open PFj.
  pose proof MIDj as (J2 & J3 & J4 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J26 & J27).
  LeanFeed.pfeed P (PNARVA16P.awv16a_conc fxj Rj (mrestrict (ahid Aw3 modelj) M3) (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVA16P.aligned; assumption]).
  destruct P as (fxa & Ra & Mav & MGa & _ & FRZa & MSa & KSa & A1 & A10 & A11 & A12 & A23 & SHZ).
  apply (PNARVK.rv_piece_loc L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M3 modelj LK3 Aw3 s sm ax cr
           fxj fxa Rj Ra 0xb0da8 0xaed4c Mav (fun a => F / 8 + 2147450880 + 26 <= a < F / 8 + 2147450880 + 26 + 1) CTX G LMj MSa MGa).
  { intros a Ha N. apply FRZa; [exact Ha| intros X; apply N; clear - X; lia]. }
  { intros a X. right; right. clear - X; lia. }
  intros M4 model4 LM4 HID4 VIS4 FR4 MG4 ECK4.
  pose proof (PNARVK.ofacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr CTX G LM4)
    as (_ & _ & _ & _ & VSH4 & _).
  assert (SHR : 0 <= F / 8 + 2147450906 /\ F / 8 + 2147450906 + 1 <= 2 ^ 64) by (clear - DF1 DF2; lia).
  assert (SH4 : L5.u8_at RSEGS M4 (F / 8 + 2147450906) 4).
  { apply (proj1 (L5A.u8_at_vis (ahid Aw3 model4) M4 (F / 8 + 2147450906) 4 (L5A.avis_sub _ (F / 8 + 2147450880) 64 (F / 8 + 2147450906) 1 VSH4 ltac:(clear; lia) ltac:(clear; lia)) (proj1 SHR) (proj2 SHR))).
    rewrite HID4, VIS4. exact SHZ. }
  assert (ACC : aacc M4 (F + 208) 4).
  { assert (HK : (4 = 8 /\ 4 = 0) \/ (1 <= 4 <= 7 /\ 4 = 4)) by (first [left; split; reflexivity | right; split; [clear; lia| reflexivity]]).
    assert (HO8 : 208 mod 8 = 0) by reflexivity. assert (HO0 : 0 <= 208) by (clear; lia). assert (HF0 : 0 <= F) by (clear - GF1; lia).
    apply (aacc_local M4 F 208 4 4 (proj1 GF8) HO8 HO0 HF0 HK).
    change (208 / 8) with 26. replace (F / 8 + 26 + 2147450880) with (F / 8 + 2147450906) by (clear; lia).
    assert (SHR1 : F / 8 + 2147450906 < 65536 \/ 6905856 <= F / 8 + 2147450906) by (right; clear - DF1; lia).
    assert (SHR2 : 0 <= F / 8 + 2147450906 < 2 ^ 64) by (clear - SHR; lia).
    exact (L5ADHR.byte_of_u8 M4 (F / 8 + 2147450906) 4 SH4 SHR1 SHR2). }
  assert (MIDa : mid R Ra sp fb F) by (apply (mid_keep R Rj Ra sp fb F MIDj); unfold MIDREGS; kks KSa).
  pose proof MIDa as (B2 & B3 & B4 & _).
  change 0xaed4c with (pa_src_read PMA.AD).
  apply (PNARVK.rv_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M4 model4 LK3 Aw3 s sm ax cr fxa Ra 0xb0dc4 208 4 SR CTX G LM4
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
  pose proof TP0 as (pre & top & c0 & ES & _).
  assert (ES5 : PNM.b_stk s5 = pre ++ [top]) by exact ES.
  assert (TP5 : PNRA.btop_pos s s5) by exact TP0.
  assert (EC5 : PMSPA.ec_at RSEGS M5 (fb + 1024) e cat) by (apply ECK5; apply ECK4; exact EC3).
  pose proof (PNARVK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr CTX G LM5)
    as (PF5 & _).
  pose proof (PNARVK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr pre top CTX G LM5 INV5 ES5)
    as (TF5 & PT5 & OKt5 & VIN5 & TB15 & TB25 & TB35 & TB45).
  set (MV5 := mrestrict (ahid Aw5 model5) M5) in *.
  set (e5 := PNM.b_sb s5 + 40 * Z.of_nat (length pre) + 40) in *.
  set (p5 := (d + PNM.bs_pos top) mod 2 ^ 64).
  unfold pfacts in PF5. conj_open PF5.
  unfold tfacts in TF5. destruct TF5 as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof (sh_apart e5 F tf4 (proj1 GF8) tf11) as SHAP.
  assert (MID5 : mid R R5 sp fb F).
  { apply (mid_keep R Ra R5 sp fb F MIDa). intros k Hk. apply (L5SAR.cs_of_preserved Ra R5 k RP5). revert k Hk. unfold MIDREGS. kin. }
  pose proof MID5 as (E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E26 & E27).
  assert (E23 : getr R5 (reg 23) = Z_to_bv 64 (F + 208)) by (rewrite (L5SAR.cs_of_preserved Ra R5 23%nat RP5) by inl; exact A23).
  assert (E10 : getr R5 (reg 10) = Z_to_bv 64 d) by exact Y10d.
  assert (Q37 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
  assert (QP5 : 0 <= p5 < 2 ^ 64) by (unfold p5; apply Z.mod_pos_bound; clear; lia).
  assert (QVb : 0 <= fb + 432 < 2 ^ 64 /\ 0 <= fb + 1024 < 2 ^ 64) by (match goal with H : 6905856 <= fb + 464 <= _ |- _ => clear - H; lia end).
  destruct QVb as (QVb1 & QVb2).
  LeanFeed.pfeed P (PNARVA16P.awv16b_conc fx5 R5 MV5 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 34%nat => fb + 432 | 36%nat => fb + 1024 | 37%nat => d | 38%nat => e5 | 39%nat => PNM.bs_pos top | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARVA16P.aligned; assumption]).
  destruct P as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & [X0|X1]).
  - (* [comment removed for export] *)
    destruct X0 as (MS6 & KS6 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 fx6 R5 R6 0xb0dc4 0xb0e1c M6v pre top p5
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
    apply (arm_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax cr fx6 R6 CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + rewrite (KS6 23%nat) by inl. exact E23.
    + apply ECK7. exact EC5.
    + exact TP7.
    + reflexivity.
  - (* [comment removed for export] *)
    destruct X1 as (MS6 & KS6 & Y1 & Y10 & Y11 & Y12 & Y13 & CND & CP6).
    apply (PNARVK.rv_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M5 model5 LK5 Aw5 s5 sm5 ax cr fx5 fx6 R5 R6 0xb0dc4 0xae848 M6v pre top p5
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
    apply (arm_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax 16 F fl LK2 M2 model2 M7 model7 LK5 Aw5 s7 sm5 ax cr fx6 R6 MKE CTX G LM7 INV7).
    + apply (mid_keep R R5 R6 sp fb F MID5). unfold MIDREGS. kks KS6.
    + exact Y1.
    + exact Y10.
    + exact Y11.
    + rewrite (KS6 23%nat) by inl. exact E23.
    + apply ECK7. exact EC5.
    + exact (btop_len s s7 TP7).
Qed.

End WithHeap.
End PNARVA16.
