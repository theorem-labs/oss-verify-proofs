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
     AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanSoundSums SegRun BigLinkBase BigLinkGlue L5Defs L5Kn L5KnA L5Core L5CoreKit L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5CoreSpecsA_b L5StepAR_b L5CoreBR_b L5ADetailHR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParSpecs PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnAReadStrP_b Ba0_code_b2010_b2014_b PnAReadStrK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNARST.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNARSK.

(* [comment removed for export] *)
Definition rregs (R R4 : bvmap 5 word) (sp fb F : Z) : Prop :=
  getr R4 (reg 2) = Z_to_bv 64 (sp - 160) /\ getr R4 (reg 3) = getr R (reg 3) /\ getr R4 (reg 4) = getr R (reg 4)
  /\ getr R4 (reg 8) = Z_to_bv 64 sp /\ getr R4 (reg 9) = Z_to_bv 64 (sp - 160)
  /\ getr R4 (reg 19) = Z_to_bv 64 (fb + 464) /\ getr R4 (reg 24) = Z_to_bv 64 F /\ getr R4 (reg 25) = Z_to_bv 64 (F / 8 + 2147450880)
  /\ getr R4 (reg 26) = Z_to_bv 64 F.
Lemma rregs_keep R R4 R5 sp fb F :
  rregs R R4 sp fb F -> (forall k, In k [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat -> getr R5 (reg k) = getr R4 (reg k)) -> rregs R R5 sp fb F.
Proof.
  intros (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26) RK. unfold rregs.
  rewrite (RK 2%nat) by inl. rewrite (RK 3%nat) by inl. rewrite (RK 4%nat) by inl. rewrite (RK 8%nat) by inl. rewrite (RK 9%nat) by inl.
  rewrite (RK 19%nat) by inl. rewrite (RK 24%nat) by inl. rewrite (RK 25%nat) by inl. rewrite (RK 26%nat) by inl.
  repeat split; assumption.
Qed.
Lemma rregs_pres R R4 R5 sp fb F : rregs R R4 sp fb F -> regs_preserved R4 R5 -> rregs R R5 sp fb F.
Proof. intros ER RP. apply (rregs_keep R R4 R5 sp fb F ER). intros k Hk. apply (L5SAR.cs_of_preserved R4 R5 k RP). revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition span_loc (own : list (Z * Z)) (fb ptr n : Z) : Prop :=
  (ptr = 0 /\ n = 0) \/ PGS.in_blk own ptr n \/ (fb + 464 + 368 + 1 <= ptr /\ ptr + n <= fb + 464 + 368 + 24).
Lemma span_keep (M M' : mem) ptr n :
  mem_grows M M' -> (forall x, ptr <= x < ptr + n -> M' (Z_to_bv 64 (S x)) = M (Z_to_bv 64 (S x))) ->
  L5.defined M ptr n -> PMSPA.accA M ptr n -> L5.defined M' ptr n /\ PMSPA.accA M' ptr n.
Proof.
  intros MG SH D A. split; [exact (L5.defined_grows M M' _ _ MG D)|]. apply (PMFA.accA_agree M M' ptr n); [| exact A]. intros x Hx. exact (SH x Hx).
Qed.
Lemma u32_of_defined (M : mem) a : 0 <= a -> a + 4 <= 2 ^ 64 -> L5.defined M a 4 -> exists w, 0 <= w < 2 ^ 32 /\ L5.u32_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 4%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u32_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
      (fx1 fx2 : FPState) R1 R2 (pc1 pc2 : Z) (M2v : mem) :
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w -> rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  msteps RSEGS (st fx1 R1 pc1 (mrestrict (ahid Aw1 model1) M1)) (st fx2 R2 pc2 M2v) ->
  mem_grows (mrestrict (ahid Aw1 model1) M1) M2v ->
  (forall a, 0 <= a < 2 ^ 64 -> M2v (Z_to_bv 64 a) = mrestrict (ahid Aw1 model1) M1 (Z_to_bv 64 a)) ->
  (forall model3,
      rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model3 LK1 Aw1 s1 sm1 ax1 cr1 ->
      ahid Aw1 model3 = ahid Aw1 model1 ->
      srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 pc2 M1 model3) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K.
Proof.
  intros CTX G LM MS MG FRZ KR.
  apply (PNARSK.rs_piece_fr L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1
           fx1 fx2 R1 R2 pc1 pc2 M2v (fun _ => False) CTX G LM MS MG).
  - intros a Ha _. exact (FRZ a Ha).
  - intros a [].
  - intros M3 model3 LM3 HID3 VIS3 FR3 MG3 ECK3.
    assert (EM31 : M3 = M1) by (apply PNBKA.mem_eq_of_agree; exact FR3). subst M3.
    exact (KR model3 LM3 HID3).
Qed.

(* [comment removed for export] *)
Lemma fvis_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 :
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  avis (ahid Aw1 model1) F 64 /\ avis (ahid Aw1 model1) (F / 8 + SB) 8.
Proof.
  intros CTX G LM. destruct LM as (BI & _).
  destruct (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R) F fl 0 LK2 M2 model2 cr (PNM.bparser_own s) G
              _ (PNM.bparser_own s1) M1 model1 LK1 cr1 Aw1 BI) as (_ & _ & _ & (_ & _ & X & _ & Y)).
  change (ff_bytes 0) with 64 in X, Y. change (64 / 8) with 8 in Y. split; [exact X| exact Y].
Qed.
Lemma span_app K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ptr n :
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  span_loc (PNM.bparser_own s1) fb ptr n -> 0 <= n ->
  forall x, ptr <= x < ptr + n -> 0 <= x < 2 ^ 47 /\ ~ (F <= x < F + 64).
Proof.
  intros CTX G LM LOC Hn x Hx.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _ & _ & _ & _ & _ & pf13 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & pf26 & _).
  destruct LM as (BI & _). pose proof BI as (HH1 & _).
  destruct LOC as [(Ep & En)|[(B & m & Hin & X1 & X2)|(X1 & X2)]].
  - exfalso. clear - Hx En. lia.
  - assert (HqL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hin).
    pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH1) as (WB1 & _).
    destruct (WB1 _ HqL) as (_ & _ & _ & _ & _ & BFA & _). cbn [fst snd] in BFA.
    pose proof (BFA (F, 0, sp - 160 + 32) (in_or_app ((F, 0, sp - 160 + 32) :: FF) LK1 _ (or_introl (or_introl eq_refl)))) as Z1. cbn [ff_addr ff_class fst snd] in Z1. change (ff_bytes 0) with 64 in Z1.
    split; [clear - Hx X1 X2 B0 B1; lia| clear - Hx X1 X2 Z1; lia].
  - split; [clear - Hx X1 X2 pf7; lia| clear - Hx X1 X2 pf26; lia].
Qed.

(* [comment removed for export] *)
Lemma rs_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ra v ev ec :
  PNRAa.make_ec_spec L ar HI ->
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  rregs R R6 sp fb F -> spill M6 sp F ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) ev ec ->
  getr R6 (reg 1) = Z_to_bv 64 ra -> (ra = 0xb36c8 \/ ra = 0xb36f8 \/ ra = 0xb3728 \/ ra = 0xb375c) ->
  getr R6 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  PNRA.binv s6 -> (length (PNM.b_stk s) <= length (PNM.b_stk s6))%nat ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 (pa_make_ec PMA.AD) M6 model6) K.
Proof.
  intros MKE CTX G LM ER SPL EC6 X1 Hra X10 X11 Hv INV6 LEN6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof ER as (E2 & E3 & E4 & _).
  apply (PNARSK.rs_call_mkec L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 R6 ra v ev ec MKE CTX G LM EC6).
  { exact X1. } { unfold L5.ra_ok; destruct Hra as [->|[->|[->| ->]]]; clear; lia. } { exact E2. } { rewrite E3. exact Rgp. } { rewrite E4. exact Rtp. } { exact X10. } { exact X11. } { exact Hv. }
  intros fx7 R7 M7 model7 LK7 Aw7 RP7 EC7 LM7 AG7.
  pose proof (rregs_pres R R6 R7 sp fb F ER RP7) as ER7.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6 CTX G LM7)
    as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
  set (MV7 := mrestrict (ahid Aw7 model7) M7) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  assert (SPL7 : spill M7 sp F) by (apply (PNARSK.spill_agree M6 M7 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG7; clear - Ha; lia]).
  destruct SPL7 as (SPF7 & SPS7).
  pose proof (SV7 (sp - 136) 2147450880 ltac:(clear; lia) ltac:(clear; lia) SPS7) as SPSv.
  assert (WRmo : L5.writable RSEGS MV7 (fb + 464 + 8) 1) by (apply (L5.writable_sub RSEGS MV7 (fb + 464) 424); [exact WRop7| clear; lia| clear; lia]).
  destruct ER7 as (E2' & E3' & E4' & E8 & E9 & E19 & E24 & E25 & E26).
  unfold own in OWN7. destruct OWN7 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
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
  assert (FIN : forall (fx9 : FPState) R9 M9v,
             msteps RSEGS (st fx7 R7 ra MV7) (st fx9 R9 0xb36b8 M9v) -> mem_grows MV7 M9v ->
             (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (fb + 464 + 8 <= i < fb + 464 + 8 + 1) -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 8)
                            -> ~ (fl + 0 <= i < fl + 0 + 1) -> M9v (Z_to_bv 64 i) = MV7 (Z_to_bv 64 i)) ->
             (forall k, In k [3; 4]%nat -> getr R9 (reg k) = getr R7 (reg k)) ->
             getr R9 (reg 2) = Z_to_bv 64 sp ->
             (forall k, In k [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R9 (reg k) = Z_to_bv 64 (bv_unsigned (getr R (reg k)))) ->
             L5.u8_at RSEGS M9v fl 0 -> L5.u8_at RSEGS M9v (fb + 464 + 8) 0 ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx7 R7 ra M7 model7) K).
  { intros fx9 R9 M9v MS9 MG9 FRZ9 K34 Y2 YK FL0 MO0.
    apply (PNARSK.rs_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M7 model7 LK7 Aw7 s6 sm6 _ cr6
             fx7 fx9 R7 R9 ra 0 M9v CTX G LM7 MS9 MG9).
    - intros a Ha N. apply FRZ9; [exact Ha| | | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
      + right. clear - X; lia.
      + left; left; left. clear - X; lia.
      + left; left; right. clear - X; lia.
      + left; right. clear - X; lia.
    - exact FL0.
    - replace (fb + 472) with (fb + 464 + 8) by (clear; lia). exact MO0.
    - left; reflexivity.
    - exact Y2.
    - exact YK.
    - intros k Hk. rewrite (K34 k Hk). cbn [In] in Hk. destruct Hk as [<-|[<-|[]]]; [exact E3'| exact E4'].
    - left. exists v. split; [exact Hv|]. split; [exact EC7|]. split; [reflexivity| apply bax_cat_add].
    - exact INV6.
    - exact LEN6. }
  pose (VM := fun j : nat => match j with 2%nat => sp | 33%nat => fb + 464 | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end).
  destruct Hra as [->|[->|[->| ->]]].
  - (let T := type of (PNARSP.arsE1_conc fx7 R7 MV7 VM) in let T := eval unfold VM in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNARSP.arsE1_conc fx7 R7 MV7 VM) T ltac:(try (unfold VM); cbn beta iota) ltac:(first [assumption | unfold PNARSP.aligned; assumption])).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO0].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - (let T := type of (PNARSP.arsE5_conc fx7 R7 MV7 VM) in let T := eval unfold VM in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNARSP.arsE5_conc fx7 R7 MV7 VM) T ltac:(try (unfold VM); cbn beta iota) ltac:(first [assumption | unfold PNARSP.aligned; assumption])).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO0].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - (let T := type of (PNARSP.arsEs_conc fx7 R7 MV7 VM) in let T := eval unfold VM in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNARSP.arsEs_conc fx7 R7 MV7 VM) T ltac:(try (unfold VM); cbn beta iota) ltac:(first [assumption | unfold PNARSP.aligned; assumption])).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO0].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - (let T := type of (PNARSP.arsEc_conc fx7 R7 MV7 VM) in let T := eval unfold VM in T in let T := eval cbn beta iota in T in LeanFeed.pfeed_at P (PNARSP.arsEc_conc fx7 R7 MV7 VM) T ltac:(try (unfold VM); cbn beta iota) ltac:(first [assumption | unfold PNARSP.aligned; assumption])).
    destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y12 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MO0 & _).
    apply (FIN fx9 R9 M9v MS9 MG9 FRZ9); [| exact Y2| | exact FL0| exact MO0].
    + intros k Hk. apply KS9. revert k Hk. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity.
    + intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
Qed.

(* [comment removed for export] *)
Lemma rs_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ptr n :
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  rregs R R6 sp fb F ->
  getr R6 (reg 12) = Z_to_bv 64 ptr -> getr R6 (reg 21) = Z_to_bv 64 n -> 0 <= ptr < 2 ^ 64 ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 + 5 <= PM.unread (PNM.b_src s) sm -> PNRA.binv s6 ->
  0 <= n < 2 ^ 26 -> L5.defined M6 ptr n -> PMSPA.accA M6 ptr n -> span_loc (PNM.bparser_own s6) fb ptr n ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xb3604 M6 model6) K.
Proof.
  intros CTX G LM ER X12 X21 Hptr EC6 TP6 UN6 INV6 Hn DEF6 ACC6 LOC6.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  destruct ER as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
  unfold own in OWN6. destruct OWN6 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13).
  assert (Q48 : 0 <= n < 2 ^ 64) by (clear - Hn; lia).
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
  LeanFeed.pfeed P (PNARSP.arsV_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 41%nat => ptr | 48%nat => n | 50%nat => F | 51%nat => fl | 60%nat => bv_unsigned (getr R (reg 1)) | 61%nat => bv_unsigned (getr R (reg 8)) | 62%nat => bv_unsigned (getr R (reg 9)) | 63%nat => bv_unsigned (getr R (reg 18)) | 64%nat => bv_unsigned (getr R (reg 19)) | 65%nat => bv_unsigned (getr R (reg 20)) | 66%nat => bv_unsigned (getr R (reg 21)) | 67%nat => bv_unsigned (getr R (reg 22)) | 68%nat => bv_unsigned (getr R (reg 23)) | 69%nat => bv_unsigned (getr R (reg 24)) | 70%nat => bv_unsigned (getr R (reg 25)) | 71%nat => bv_unsigned (getr R (reg 26)) | 72%nat => bv_unsigned (getr R (reg 27)) | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FRZ9 & MS9 & KS9 & Y1 & Y2 & Y8 & Y9 & Y10 & Y11 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & FL0 & _).
  pose proof (fdiv_rng F pf13) as (DF1 & DF2).
  pose proof LM as (_ & RP6 & _). pose proof RP6 as (PA6 & _). change (PNRA.o_p PMA.AD fb) with (fb + 464) in PA6.
  pose proof PA6 as (_ & _ & _ & MORE6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MB6 & _).
  apply (PNARSK.rs_fin L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6
           fx6 fx9 R6 R9 0xb3604 (PNM.b_more s6) M9v CTX G LM MS9 MG9).
  - intros a Ha N. apply FRZ9; [exact Ha| | |]; intros X; apply N; unfold PMAUK.WretX, PMAUK.Wret; change (ff_bytes 0 / 8) with 8; unfold SB.
    + left; left; left. clear - X; lia.
    + left; left; right. clear - X; lia.
    + left; right. clear - X; lia.
  - exact FL0.
  - replace (fb + 472) with (fb + 464 + 8) by (clear; lia).
    apply (L5C.u8_at_agree RSEGS MV6 M9v); [| clear - pf7; lia| clear - pf7; lia| exact (proj2 (U8op6 _) MORE6)].
    intros j Hj. apply FRZ9; [clear - Hj pf7; lia| clear - Hj pf26; lia| clear - Hj pf9 DF1 DF2; lia| clear - Hj pf27; lia].
  - exact MB6.
  - exact Y2.
  - intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [assumption|]). destruct Hk.
  - intros k Hk. cbn [In] in Hk. destruct Hk as [<-|[<-|[]]].
    + rewrite (KS9 3%nat) by inl. exact E3.
    + rewrite (KS9 4%nat) by inl. exact E4.
  - right. split; [exact EC6|]. split; [reflexivity|]. unfold PNRA.bprog_rs. split; [exact TP6|]. split; [exact UN6|].
    exists ptr, n. rewrite L5K.rl10, L5K.rl11. split; [exact Y10|]. split; [exact Y11|]. split; [exact Hn|]. split; [exact DEF6|]. split; [exact ACC6|].
    unfold PNRA.o_tb, PNRA.o_p, PMSP.o_p, PNM.OFF_TB. cbn [pa_off_p PMA.AD PnLayoutA_b.ADDR_A]. exact LOC6.
  - exact INV6.
  - destruct TP6 as (l & c & c' & Q1 & Q2 & _). rewrite Q1, Q2, !List.length_app. cbn [length]. apply Nat.le_refl.
Qed.

(* [comment removed for export] *)
Lemma rs_after_rd2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 d2 ptr n len :
  PNRAa.make_ec_spec L ar HI ->
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  rregs R R6 sp fb F -> spill M6 sp F ->
  getr R6 (reg 10) = Z_to_bv 64 d2 -> getr R6 (reg 18) = Z_to_bv 64 ptr -> getr R6 (reg 20) = Z_to_bv 64 1 -> getr R6 (reg 21) = Z_to_bv 64 n ->
  getr R6 (reg 22) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 27) = Z_to_bv 64 len ->
  0 <= d2 <= 1 -> 1 <= len <= 2147483647 -> 0 <= ptr < 2 ^ 64 ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 + 4 + d2 <= PM.unread (PNM.b_src s) sm -> PNRA.binv s6 ->
  0 <= n < 2 ^ 26 -> L5.defined M6 ptr n -> PMSPA.accA M6 ptr n -> span_loc (PNM.bparser_own s6) fb ptr n ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xb35a4 M6 model6) K.
Proof.
  intros MKE CTX G LM ER SPL X10 X18 X20 X21 X22 X27 Hd2 Hlen Hptr EC6 TP6 UN6 INV6 Hn DEF6 ACC6 LOC6.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & OWN6 & SV6 & U8v6 & WRop6 & U8op6 & SVr6).
  pose proof TP6 as (pre0 & top0 & top & ES0 & ES & _).
  pose proof (PNARSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 pre0 top CTX G LM INV6 ES)
    as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  set (e1 := PNM.b_sb s6 + 40 * Z.of_nat (length pre0) + 40) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  unfold tfacts in TF. destruct TF as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
  pose proof SPL as (SPF & SPS).
  pose proof (SV6 (sp - 136) 2147450880 ltac:(clear; lia) ltac:(clear; lia) SPS) as SPSv.
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q46 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
  assert (DC : d2 = 0 \/ d2 = 1) by (clear - Hd2; lia).
  destruct DC as [-> | ->].
  - (* [comment removed for export] *)
    LeanFeed.pfeed P (PNARSP.arsT0_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11).
    apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb35a4 0xae848 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity. }
    change 0xae848 with (pa_make_ec PMA.AD).
    apply (rs_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xb375c 1 e cat MKE CTX G LM7
             (rregs_keep R R6 R7 sp fb F ER RK) SPL EC6 Y1 ltac:(right; right; right; reflexivity) Y10 Y11 ltac:(clear; lia) INV6 (btop_len s s6 TP6)).
  - (* [comment removed for export] *)
    assert (Q41 : 0 <= ptr < 2 ^ 64) by exact Hptr.
    LeanFeed.pfeed P (PNARSP.arsU_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 41%nat => ptr | 42%nat => e1 | 43%nat => PNM.bs_pos top | 46%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y10 & Y11 & Y12 & Y27).
    apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb35a4 0xb3600 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 19; 21; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 21; 24; 25; 26]%nat). vm_compute. reflexivity. }
    assert (ER7 : rregs R R7 sp fb F) by (apply (rregs_keep R R6 R7 sp fb F ER); intros k Hk; apply RK; revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat); vm_compute; reflexivity).
    clear OWN6 SV6 U8v6 WRop6 U8op6 SVr6 pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32
          tf1 tf2 tf3 tf4 tf5 tf6 tf7 tf8 tf9 tf10 tf11 tf12 tf13 tf14 PT OKt VIN TB1 TB2 TB3 TB4 SPSv E2 E3 E4 E8 E9 E19 E24 E25 E26.
    pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM7)
      as (PF & OWN7 & SV7 & U8v7 & WRop7 & U8op7 & SVr7).
    pose proof (PNARSK.tfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 pre0 top CTX G LM7 INV6 ES)
      as (TF & PT & OKt & VIN & TB1 & TB2 & TB3 & TB4).
    fold e1 in TF, TB2.
    set (MV7 := mrestrict (ahid Aw6 model7) M6) in *.
    unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
    unfold tfacts in TF. destruct TF as (tf1 & tf2 & tf3 & tf4 & tf5 & tf6 & tf7 & tf8 & tf9 & tf10 & tf11 & tf12 & tf13 & tf14).
    pose proof ER7 as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
    set (p49 := (PNM.bs_pos top + len + 4) mod 2 ^ 64).
    assert (Q49 : 0 <= p49 < 2 ^ 64) by (unfold p49; apply Z.mod_pos_bound; clear; lia).
    assert (Q49' : 0 <= p49 <= 18446744073709551615) by (clear - Q49; lia).
    assert (Y11' : getr R7 (reg 11) = Z_to_bv 64 p49) by (rewrite Y11; unfold p49; symmetry; apply zb_mod64).
    LeanFeed.pfeed P (PNARSP.arsW_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 42%nat => e1 | 43%nat => PNM.bs_pos top | 49%nat => p49 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
    destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & CP8).
    apply (PNARSK.rs_piece_top L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 fx8 R7 R8 0xb3600 0xb3604 M8v pre0 top p49 CTX G LM7 INV6 ES MS8 MG8 FRZ8 CP8 Q49).
    intros M8 model8 LM8 HID8 VIS8 FR8 MGM8 ECK8.
    set (top' := PNM.BS (PNM.bs_mode top) (PNM.bs_len top) p49 (PNM.bs_type top) (PNM.bs_idx top)) in *.
    set (s8 := PNBO.set_stk s6 (pre0 ++ [top'])) in *.
    assert (OK' : PNM.bstate_ok top').
    { destruct OKt as (X1 & X2 & X3 & X4 & X5). unfold PNM.bstate_ok, top'. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact X1|]. split; [exact X2|]. split; [exact Q49|]. split; [exact X4| exact X5]. }
    assert (INV8 : PNRA.binv s8) by (apply (PNBKA.binv_set_stk_top s6 pre0 top top' INV6 ES OK'); reflexivity).
    assert (TP8 : PNRA.btop_pos s s8).
    { apply (PNBKA.btop_pos_trans s s6 s8 TP6). apply (PNBKA.btop_pos_set_stk s6 pre0 top top' ES OK'); reflexivity. }
    assert (RK8 : forall k, In k [2; 3; 4; 8; 9; 12; 19; 21; 24; 25; 26]%nat -> getr R8 (reg k) = getr R7 (reg k)).
    { intros k Hk. apply KS8. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 12; 19; 21; 24; 25; 26]%nat). vm_compute. reflexivity. }
    assert (ER8 : rregs R R8 sp fb F) by (apply (rregs_keep R R7 R8 sp fb F ER7); intros k Hk; apply RK8; revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat); vm_compute; reflexivity).
    pose proof (span_app K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 ptr n CTX G LM7 LOC6 ltac:(clear - Hn; lia)) as SPA.
    destruct (span_keep M6 M8 ptr n MGM8) as (DEF8 & ACC8); [| exact DEF6| exact ACC6|].
    { intros x Hx. destruct (SPA x Hx) as (Xr & _). pose proof (PMKA.S_in_shadow x Xr) as S1. unfold BIGSHADOW_LO, BIGSHADOW_HI in S1.
      apply FR8; [clear - S1; lia|]. fold e1. clear - S1 tf7. lia. }
    apply (rs_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s8 sm6 ax6 cr6 fx8 R8 ptr n CTX G LM8 ER8).
    + rewrite (RK8 12%nat) by inl. exact Y12.
    + rewrite (RK8 21%nat) by inl. rewrite (RK 21%nat) by inl. exact X21.
    + exact Hptr.
    + exact (ECK8 _ _ EC6).
    + exact TP8.
    + change (PNM.b_src s8) with (PNM.b_src s6). clear - UN6. lia.
    + exact INV8.
    + exact Hn.
    + exact DEF8.
    + exact ACC8.
    + exact LOC6.
Qed.

(* [comment removed for export] *)
Lemma aacc_sh (M : mem) F off k :
  F / 8 * 8 = F -> 6905856 <= F <= 140737488355264 -> off mod 8 = 0 -> 0 <= off <= 56 -> 1 <= k <= 7 ->
  L5.u8_at RSEGS M (F / 8 + 2147450880 + off / 8) k -> aacc M (F + off) k.
Proof.
  intros F8 HF O8 Ho Hk U.
  pose proof (Z.div_pos F 8 ltac:(clear - HF; lia) ltac:(clear; lia)) as D0.
  pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(clear; lia) ltac:(clear - HF; lia)) as D1.
  pose proof (Z.div_pos off 8 ltac:(clear - Ho; lia) ltac:(clear; lia)) as D2.
  pose proof (Z.div_le_upper_bound off 8 7 ltac:(clear; lia) ltac:(clear - Ho; lia)) as D3.
  apply (aacc_local M F off k k F8 O8 ltac:(clear - Ho; lia) ltac:(clear - HF; lia) ltac:(right; split; [exact Hk| reflexivity])).
  unfold byte_at. replace (F / 8 + off / 8 + 2147450880) with (F / 8 + 2147450880 + off / 8) by (clear; lia).
  apply (L5ADHR.byte_of_u8 M (F / 8 + 2147450880 + off / 8) k U); [right; clear - D0 D2; lia| clear - D0 D1 D2 D3; lia].
Qed.

(* [comment removed for export] *)
Lemma rs_after_span K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 ptr n2 len :
  PNRAa.src_read_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  rregs R R6 sp fb F -> spill M6 sp F ->
  getr R6 (reg 10) = Z_to_bv 64 ptr -> getr R6 (reg 11) = Z_to_bv 64 n2 -> getr R6 (reg 20) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 21) = Z_to_bv 64 (len - 1) ->
  getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 16) -> getr R6 (reg 27) = Z_to_bv 64 len ->
  1 <= len <= 2147483647 -> 0 <= n2 <= len - 1 -> 0 <= ptr < 2 ^ 64 ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 + 4 <= PM.unread (PNM.b_src s) sm -> PNRA.binv s6 ->
  n2 < 2 ^ 26 -> L5.defined M6 ptr n2 -> PMSPA.accA M6 ptr n2 -> span_loc (PNM.bparser_own s6) fb ptr n2 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xb3580 M6 model6) K.
Proof.
  intros SR MKE CTX G LM ER SPL X10 X11 X20 X21 X23 X27 Hlen Hn2 Hptr EC6 TP6 UN6 INV6 Hn26 DEF6 ACC6 LOC6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & _).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (Q47 : 0 <= n2 < 2 ^ 64) by (clear - Hn2 Hlen; lia).
  assert (Q47' : 0 <= n2 <= 2147483647) by (clear - Hn2 Hlen; lia).
  assert (Q48 : 0 <= len - 1 < 2 ^ 64) by (clear - Hlen; lia).
  assert (Q48' : 0 <= len - 1 <= 2147483647) by (clear - Hlen; lia).
  LeanFeed.pfeed P (PNARSP.arsS_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 47%nat => n2 | 48%nat => len - 1 | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
  destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & [(MS7 & KS7 & Y1 & Y10 & Y11 & PATH)|(MS7 & KS7 & PATH)]).
  - (* [comment removed for export] *)
    apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb3580 0xae848 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity. }
    change 0xae848 with (pa_make_ec PMA.AD).
    apply (rs_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xb3728 1 e cat MKE CTX G LM7
             (rregs_keep R R6 R7 sp fb F ER RK) SPL EC6 Y1 ltac:(right; right; left; reflexivity) Y10 Y11 ltac:(clear; lia) INV6 (btop_len s s6 TP6)).
  - (* [comment removed for export] *)
    assert (En : n2 = len - 1).
    { pose proof (Z.mod_pos_bound (n2 - (len - 1)) (2 ^ 64) ltac:(clear; lia)) as MB.
      assert (E0 : (n2 - (len - 1)) mod 2 ^ 64 = 0) by (clear - PATH MB; lia).
      apply Z.mod_divide in E0; [| clear; lia]. destruct E0 as (k & Ek). clear - Ek Hn2 Hlen. lia. }
    subst n2. clear PATH.
    apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb3580 0xb3584 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    assert (RK : forall k, In k [2; 3; 4; 8; 9; 10; 19; 20; 21; 23; 24; 25; 26; 27]%nat -> getr R7 (reg k) = getr R6 (reg k)).
    { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 10; 19; 20; 21; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    assert (ER7 : rregs R R7 sp fb F) by (apply (rregs_keep R R6 R7 sp fb F ER); intros k Hk; apply RK; revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat); vm_compute; reflexivity).
    clear pf1 pf2 pf3 pf4 pf5 pf6 pf7 pf8 pf9 pf10 pf11 pf12 pf13 pf14 pf15 pf16 pf17 pf18 pf19 pf20 pf21 pf22 pf23 pf24 pf25 pf26 pf27 pf28 pf29 pf30 pf31 pf32 E2 E3 E4 E8 E9 E19 E24 E25 E26.
    pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM7)
      as (PF & _).
    set (MV7 := mrestrict (ahid Aw6 model7) M6) in *.
    unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
    pose proof ER7 as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
    assert (Z10 : getr R7 (reg 10) = Z_to_bv 64 ptr) by (rewrite (RK 10%nat) by inl; exact X10).
    assert (Z20 : getr R7 (reg 20) = Z_to_bv 64 (fb + 1024)) by (rewrite (RK 20%nat) by inl; exact X20).
    assert (Z23 : getr R7 (reg 23) = Z_to_bv 64 (fb + 464 + 16)) by (rewrite (RK 23%nat) by inl; exact X23).
    assert (Q41 : 0 <= ptr < 2 ^ 64) by exact Hptr.
    LeanFeed.pfeed P (PNARSP.arsQ_conc fx7 R7 MV7 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 41%nat => ptr | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
    destruct P as (fx8 & R8 & M8v & MG8 & _ & FRZ8 & MS8 & KS8 & Y1 & Y10 & Y11 & Y12 & Y18 & Y20 & Y22 & SH6).
    apply (PNARSK.rs_piece_sh L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 fx8 R7 R8 0xb3584 0xaed4c M8v
             (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) CTX G LM7 MS8 MG8).
    { intros a Ha N. apply FRZ8; [exact Ha| exact N]. }
    { intros a X. clear - X. lia. }
    intros M8 model8 LM8 HID8 VIS8 FR8 MGM8 ECK8.
    destruct (fvis_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM8) as (FV8 & SV8).
    pose proof (fdiv_rng F pf13) as (DF1 & DF2).
    assert (SH8 : L5.u8_at RSEGS M8 (F / 8 + 2147450880 + 48 / 8) 1).
    { change (48 / 8) with 6.
      apply (proj1 (L5A.u8_at_vis (ahid Aw6 model8) M8 (F / 8 + 2147450880 + 6) 1 ltac:(apply (L5A.avis_sub _ (F / 8 + SB) 8); [exact SV8| unfold SB; clear; lia| unfold SB; clear; lia]) ltac:(clear - DF1; lia) ltac:(clear - DF2; lia))).
      rewrite HID8, VIS8. replace (F / 8 + 2147450880 + 6) with (F / 8 + 2147450886) by (clear; lia). exact SH6. }
    pose proof G as G'. unfold rs_frame in G'. destruct G' as [_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ GF8 _ _ _ _ _ _ _].
    change (ff_bytes 0) with 64 in GF8.
    pose proof (aacc_sh M8 F 48 1 (proj1 GF8) pf13 ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia) SH8) as ACC48.
    assert (RK8 : forall k, In k [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%nat -> getr R8 (reg k) = getr R7 (reg k)).
    { intros k Hk. apply KS8. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    assert (ER8 : rregs R R8 sp fb F) by (apply (rregs_keep R R7 R8 sp fb F ER7); intros k Hk; apply RK8; revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat); vm_compute; reflexivity).
    pose proof ER8 as (G2 & G3 & G4 & _).
    assert (SPL8 : spill M8 sp F).
    { apply (PNARSK.spill_agree M6 M8 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL|]. intros a Ha. apply FR8; [clear - Ha pf4; lia|]. clear - Ha pf4 DF1 DF2. lia. }
    pose proof (span_app K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 ptr (len - 1) CTX G LM7 LOC6 ltac:(clear - Hlen; lia)) as SPA.
    destruct (span_keep M6 M8 ptr (len - 1) MGM8) as (DEF8 & ACC8); [| exact DEF6| exact ACC6|].
    { intros x Hx. destruct (SPA x Hx) as (Xr & XF). pose proof (PMKA.S_in_shadow x Xr) as S1. unfold BIGSHADOW_LO, BIGSHADOW_HI in S1.
      apply FR8; [clear - S1; lia|]. unfold S, SB.
      pose proof (Z.div_mod x 8 ltac:(clear; lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(clear; lia)) as Mx.
      destruct GF8 as (GF8a & _). clear - XF Dx Mx GF8a. lia. }
    change 0xaed4c with (pa_src_read PMA.AD).
    apply (PNARSK.rs_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK6 Aw6 s6 sm6 ax6 cr6 fx8 R8 0xb35a4 48 1 SR CTX G LM8
             ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC48 Y1).
    { unfold L5.ra_ok; clear; lia. } { exact G2. } { rewrite G3. exact Rgp. } { rewrite G4. exact Rtp. } { exact Y10. } { exact Y11. } { exact Y12. }
    intros fx9 R9 M9 model9 LK9 Aw9 src9 sm9 d RP9 Y10d Hd UNR9 RD1 RD0 DEF9 QC9 LM9 AG9 ECK9 DKB9.
    set (s9 := PNM.with_srcB s6 src9) in *.
    assert (RC9 : forall k, In k [18; 20; 21; 22; 27]%nat -> getr R9 (reg k) = getr R8 (reg k)).
    { intros k Hk. apply (L5SAR.cs_of_preserved R8 R9 k RP9). revert k Hk. apply (L5K.incl_b [18; 20; 21; 22; 27]%nat). vm_compute. reflexivity. }
    assert (SP9 : L5.defined M9 ptr (len - 1) /\ PMSPA.accA M9 ptr (len - 1)).
    { destruct LOC6 as [(Ep & En)|[(B & m & Hin & X1 & X2)|(X1 & X2)]].
      - split; [intros i Hi; exfalso; clear - Hi En; lia| intros x Hx; exfalso; clear - Hx En; lia].
      - split.
        + intros i Hi. apply (proj1 (DKB9 B m (ptr + i) (or_introl Hin) ltac:(clear - Hi X1 X2; lia))). apply DEF8. exact Hi.
        + apply (PMFA.accA_agree M8 M9 ptr (len - 1)); [| exact ACC8]. intros x Hx. exact (proj2 (DKB9 B m x (or_introl Hin) ltac:(clear - Hx X1 X2; lia))).
      - split.
        + intros i Hi. apply (proj1 (DKB9 (fb + 464) 416 (ptr + i) (or_intror (conj eq_refl eq_refl)) ltac:(clear - Hi X1 X2; lia))). apply DEF8. exact Hi.
        + apply (PMFA.accA_agree M8 M9 ptr (len - 1)); [| exact ACC8]. intros x Hx. exact (proj2 (DKB9 (fb + 464) 416 x (or_intror (conj eq_refl eq_refl)) ltac:(clear - Hx X1 X2; lia))). }
    destruct SP9 as (DEF9' & ACC9').
    apply (rs_after_rd2 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M9 model9 LK9 Aw9 s9 sm9 ax6 cr6 fx9 R9 d ptr (len - 1) len MKE CTX G LM9
             (rregs_pres R R8 R9 sp fb F ER8 RP9)).
    + apply (PNARSK.spill_agree M8 M9 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL8| intros a Ha; apply AG9; clear - Ha; lia].
    + exact Y10d.
    + rewrite (RC9 18%nat) by inl. exact Y18.
    + rewrite (RC9 20%nat) by inl. exact Y20.
    + rewrite (RC9 21%nat) by inl. rewrite (RK8 21%nat) by inl. rewrite (RK 21%nat) by inl. exact X21.
    + rewrite (RC9 22%nat) by inl. exact Y22.
    + rewrite (RC9 27%nat) by inl. rewrite (RK8 27%nat) by inl. rewrite (RK 27%nat) by inl. exact X27.
    + exact Hd.
    + exact Hlen.
    + exact Hptr.
    + exact (ECK9 _ _ (ECK8 _ _ EC6)).
    + exact TP6.
    + unfold s9. cbn [PNM.with_srcB PNM.b_src]. rewrite UNR9. clear - UN6. lia.
    + exact INV6.
    + clear - Hlen Hn26. lia.
    + exact DEF9'.
    + exact ACC9'.
    + unfold s9. rewrite (PNBKA.own_with_srcB s6 src9 QC9). exact LOC6.
Qed.

Lemma span_ptr_rng K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ptr n :
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 ->
  span_loc (PNM.bparser_own s1) fb ptr n -> 0 <= n -> 0 <= ptr < 2 ^ 64.
Proof.
  intros CTX G LM LOC Hn.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm1 ax1 cr1 CTX G LM) as (PF & _).
  unfold pfacts in PF. destruct PF as (_ & _ & _ & _ & _ & _ & pf7 & _).
  destruct LM as (BI & _). pose proof BI as (HH1 & _).
  destruct LOC as [(Ep & En)|[(B & m & Hin & X1 & X2)|(X1 & X2)]].
  - subst ptr. clear; lia.
  - assert (HqL : In (B, m) (PNM.bparser_own s1 ++ LBX)) by (apply in_or_app; left; exact Hin).
    pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH1 _ HqL) as (B0 & B1). cbn [fst snd] in B0, B1.
    clear - Hn X1 X2 B0 B1. lia.
  - clear - Hn X1 X2 pf7. lia.
Qed.

(* [comment removed for export] *)
Lemma rs_after_rd1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 (fx6 : FPState) R6 d :
  PNRAa.src_read_spec L ar HI -> PNRAa.read_span_spec L ar HI -> PNRAa.make_ec_spec L ar HI ->
  rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w ->
  rs_frame L ar HI R M model LBX FF LK Aw cr sp s F fl LK2 M2 model2 ->
  rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 ->
  rregs R R6 sp fb F -> spill M6 sp F ->
  getr R6 (reg 10) = Z_to_bv 64 d -> getr R6 (reg 20) = Z_to_bv 64 (fb + 1024) -> getr R6 (reg 21) = Z_to_bv 64 (F + 32) -> getr R6 (reg 22) = Z_to_bv 64 4 ->
  getr R6 (reg 23) = Z_to_bv 64 (fb + 464 + 16) ->
  0 <= d <= 4 -> L5.defined M6 (F + 32) d ->
  PMSPA.ec_at RSEGS M6 (fb + 1024) e cat -> PNRA.btop_pos s s6 -> PM.unread (PNM.b_src s6) sm6 + d <= PM.unread (PNM.b_src s) sm -> PNRA.binv s6 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xb3560 M6 model6) K.
Proof.
  intros SR SPN MKE CTX G LM ER SPL X10 X20 X21 X22 X23 Hd DEF EC6 TP6 UN6 INV6.
  pose proof CTX as (_ & _ & _ & _ & ENT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UNR & _).
  destruct ENT as (_ & _ & _ & Rgp & Rtp & _). rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM)
    as (PF & _).
  destruct (fvis_of K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 CTX G LM) as (FV6 & SV6).
  set (MV6 := mrestrict (ahid Aw6 model6) M6) in *.
  unfold pfacts in PF. destruct PF as (pf1 & pf2 & pf3 & pf4 & pf5 & pf6 & pf7 & pf8 & pf9 & pf10 & pf11 & pf12 & pf13 & pf14 & pf15 & pf16 & pf17 & pf18 & pf19 & pf20 & pf21 & pf22 & pf23 & pf24 & pf25 & pf26 & pf27 & pf28 & pf29 & pf30 & pf31 & pf32).
  pose proof ER as (E2 & E3 & E4 & E8 & E9 & E19 & E24 & E25 & E26).
  assert (Q36 : 0 <= fb + 1024 < 2 ^ 64) by (clear - pf7; lia).
  assert (RKx : forall (R7 : bvmap 5 word), (forall k, In k [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)) -> rregs R R7 sp fb F).
  { intros R7 RK. exact (rregs_keep R R6 R7 sp fb F ER RK). }
  assert (ERRARM : forall (fx7 : FPState) R7 M7v ra v,
             msteps RSEGS (st fx6 R6 0xb3560 MV6) (st fx7 R7 0xae848 M7v) -> mem_grows MV6 M7v ->
             (forall i : Z, 0 <= i < 2 ^ 64 -> M7v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i)) ->
             (forall k, In k [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)) ->
             getr R7 (reg 1) = Z_to_bv 64 ra -> (ra = 0xb36c8 \/ ra = 0xb36f8 \/ ra = 0xb3728 \/ ra = 0xb375c) ->
             getr R7 (reg 10) = Z_to_bv 64 (fb + 1024) -> getr R7 (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
             srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx6 R6 0xb3560 M6 model6) K).
  { intros fx7 R7 M7v ra v MS7 MG7 FRZ7 RK Y1 Hra Y10 Y11 Hv.
    apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb3560 0xae848 M7v CTX G LM MS7 MG7 FRZ7).
    intros model7 LM7 HID7.
    change 0xae848 with (pa_make_ec PMA.AD).
    exact (rs_err K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 ra v e cat MKE CTX G LM7
             (RKx R7 RK) SPL EC6 Y1 Hra Y10 Y11 Hv INV6 (btop_len s s6 TP6)). }
  destruct (Z_lt_le_dec d 4) as [D3|D4].
  - (* [comment removed for export] *)
    assert (Q40 : 0 <= d < 2 ^ 64) by (clear - Hd; lia).
    assert (Q40' : 0 <= d <= 3) by (clear - Hd D3; lia).
    LeanFeed.pfeed P (PNARSP.arsRe_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 40%nat => d | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
    destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11).
    apply (ERRARM fx7 R7 M7v 0xb36c8 1 MS7 MG7 FRZ7); [| exact Y1| left; reflexivity| exact Y10| exact Y11| clear; lia].
    intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity.
  - assert (Ed : d = 4) by (clear - Hd D4; lia). subst d.
    destruct (u32_of_defined M6 (F + 32) ltac:(clear - pf13; lia) ltac:(clear - pf13; lia) DEF) as (len & Hlen & ULEN).
    assert (ULv : L5.u32_at RSEGS MV6 (F + 32) len).
    { apply (proj2 (L5A.u32_at_vis (ahid Aw6 model6) M6 (F + 32) len ltac:(apply (L5A.avis_sub _ F 64); [exact FV6| clear; lia| clear; lia]) ltac:(clear - pf13; lia) ltac:(clear - pf13; lia))). exact ULEN. }
    assert (Q46 : 0 <= len < 2 ^ 64) by (clear - Hlen; lia).
    destruct (Z.eq_dec len 0) as [L0|LN0].
    + (* [comment removed for export] *)
      assert (Q46' : 0 <= len <= 0) by (clear - L0; lia).
      LeanFeed.pfeed P (PNARSP.arsRz_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 46%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
      destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & _).
      apply (ERRARM fx7 R7 M7v 0xb36f8 5 MS7 MG7 FRZ7); [| exact Y1| right; left; reflexivity| exact Y10| exact Y11| clear; lia].
      intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity.
    + destruct (Z_lt_le_dec 2147483647 len) as [LNEG|LPOS].
      * (* [comment removed for export] *)
        assert (Q46' : 2147483648 <= len <= 4294967295) by (clear - Hlen LNEG; lia).
        LeanFeed.pfeed P (PNARSP.arsRn_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 46%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
        destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11).
        apply (ERRARM fx7 R7 M7v 0xb36f8 5 MS7 MG7 FRZ7); [| exact Y1| right; left; reflexivity| exact Y10| exact Y11| clear; lia].
        intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat). vm_compute. reflexivity.
      * (* [comment removed for export] *)
        assert (Q46' : 1 <= len <= 2147483647) by (clear - Hlen LN0 LPOS; lia).
        LeanFeed.pfeed P (PNARSP.arsRp_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 33%nat => fb + 464 | 36%nat => fb + 1024 | 46%nat => len | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
        destruct P as (fx7 & R7 & M7v & MG7 & _ & FRZ7 & MS7 & KS7 & Y1 & Y10 & Y11 & Y12 & Y21 & Y27).
        apply (rs_piece_reg K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model6 LK6 Aw6 s6 sm6 ax6 cr6 fx6 fx7 R6 R7 0xb3560 0xb4dc0 M7v CTX G LM MS7 MG7 FRZ7).
        intros model7 LM7 HID7.
        assert (RK : forall k, In k [2; 3; 4; 8; 9; 19; 20; 23; 24; 25; 26]%nat -> getr R7 (reg k) = getr R6 (reg k)).
        { intros k Hk. apply KS7. revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 23; 24; 25; 26]%nat). vm_compute. reflexivity. }
        assert (ER7 : rregs R R7 sp fb F) by (apply RKx; intros k Hk; apply RK; revert k Hk; apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 24; 25; 26]%nat); vm_compute; reflexivity).
        pose proof ER7 as (G2 & G3 & G4 & _).
        change 0xb4dc0 with (pa_read_span PMA.AD).
        apply (PNARSK.rs_call_span L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M6 model7 LK6 Aw6 s6 sm6 ax6 cr6 fx7 R7 0xb3580 (len - 1) SPN CTX G LM7 Y1).
        { unfold L5.ra_ok; clear; lia. } { exact G2. } { rewrite G3. exact Rgp. } { rewrite G4. exact Rtp. } { exact Y10. } { exact Y11. } { exact Y12. }
        { clear - Q46'. lia. } { clear - UN6 UNR Hd. lia. }
        intros fx8 R8 M8 model8 LK8 Aw8 src8 tb8 tg8 sm8 cr8 ptr n RP8 Z10 Z11 Hn Hn26 LOC8 DEF8 ACC8 UN8 LM8 AG8 ECK8.
        set (s8 := PNM.with_src_tb s6 src8 tb8 tg8) in *.
        assert (RC8 : forall k, In k [20; 21; 23; 27]%nat -> getr R8 (reg k) = getr R7 (reg k)).
        { intros k Hk. apply (L5SAR.cs_of_preserved R7 R8 k RP8). revert k Hk. apply (L5K.incl_b [20; 21; 23; 27]%nat). vm_compute. reflexivity. }
        assert (LOC8' : span_loc (PNM.bparser_own s8) fb ptr n) by exact LOC8.
        pose proof (span_ptr_rng K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax6 cr8 ptr n CTX G LM8 LOC8' ltac:(clear - Hn; lia)) as Hptr.
        apply (rs_after_span K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M8 model8 LK8 Aw8 s8 sm8 ax6 cr8 fx8 R8 ptr n len SR MKE CTX G LM8
                 (rregs_pres R R7 R8 sp fb F ER7 RP8)).
        -- apply (PNARSK.spill_agree M6 M8 sp F); [clear - pf4; lia| clear - pf4; lia| exact SPL| intros a Ha; apply AG8; clear - Ha; lia].
        -- exact Z10.
        -- exact Z11.
        -- rewrite (RC8 20%nat) by inl. rewrite (RK 20%nat) by inl. exact X20.
        -- rewrite (RC8 21%nat) by inl. exact Y21.
        -- rewrite (RC8 23%nat) by inl. rewrite (RK 23%nat) by inl. exact X23.
        -- rewrite (RC8 27%nat) by inl. exact Y27.
        -- exact Q46'.
        -- exact Hn.
        -- exact Hptr.
        -- exact (ECK8 _ _ EC6).
        -- exact TP6.
        -- unfold s8. cbn [PNM.with_src_tb PNM.b_src]. clear - UN8 UN6. lia.
        -- exact INV6.
        -- exact Hn26.
        -- exact DEF8.
        -- exact ACC8.
        -- exact LOC8'.
Qed.

(* [comment removed for export] *)
Theorem read_string_ok : PNRAa.src_read_spec L ar HI -> PNRAa.read_span_spec L ar HI -> PNRAa.make_ec_spec L ar HI -> PNRAa.read_string_spec L ar HI.
Proof.
  intros SR SPN MKE. unfold PNRAa.read_string_spec, PNRA.read_string_spec, PNRA.brun_spec_fb. intros fb.
  set (w := 0). assert (Hw : w = 0 \/ w = 1) by (left; reflexivity).
  intros fx R M model K LBX FF LK Aw cr sp r cat e s str sm ax HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC HE UNR CRED KONT.
  assert (CTX : rs_ctx L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w).
  { exact (conj Hw (conj HH (conj AM (conj K0 (conj ENT (conj FRM (conj FRS (conj FOK (conj SP32 (conj ARGS (conj RPRE (conj INCS (conj INV (conj EC (conj HE (conj UNR (conj CRED KONT))))))))))))))))). }
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 7) with 26624 in *. change (26624 / 8) with 3328 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  destruct ARGS as (A10 & A11).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof RPRE as (PA & IA & VIS & VREF & OACC & BASE & ERR & GROW).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL, F1, F2.
  change (PNRA.o_p PMA.AD fb) with (fb + 464) in *. change (PNRA.o_ec PMA.AD fb) with (fb + 1024) in *.
  change (PNRA.o_v PMA.AD fb) with (fb + 432) in *. change (PNRA.o_is PMA.AD fb) with (fb + 96) in *.
  pose proof (PNAPAR.op_visB L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA OACC) as ((O1 & O8 & ONSH) & Zop & OWR & OCE & OVIS & AOP).
  pose proof (PMASK.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm sp 26624 HH) as ISV.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 26624 160 HH ASTK ltac:(lia)) as (SL160 & SH160 & SWR).
  set (op := fb + 464) in *. set (ov := fb + 432) in *. set (oec := fb + 1024) in *. set (ois := fb + 96) in *.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VISs & _).
  LeanFeed.pfeed P (PNARSP.arsA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => op | 36%nat => oec | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption | clear - SL160 SHI SPT; lia | clear - O1; lia | unfold oec, op in *; clear - O1; lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T19 & T20 & T23
                 & C104 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C160).
  unfold PMSP.cfg. change (PNL.pn_read_string PMA.AN) with 0xb343c.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb343c R1 0x5dc2c M1v (fun a => sp - 160 <= a < sp - 160 + 160) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; clear - X Wa SL160 FSAPP FSCEIL; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL160 SHI SPT; lia| intros X; clear - X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  set (LB := PNM.bparser_own s ++ LBX) in *.
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (NCS0 : forall a, sp - 160 <= a < sp -> ~ aclient L ar LB FF sp 26624 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 26624 a HH SPT Hc) as [Y|Y].
    - clear - Xa Y; lia.
    - clear - Xa Y SL160; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 26624 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M M1 (fun a => sp - 160 <= a < sp - 160 + 160) FR1). intros a Ha Hc _ X. apply (NCS0 a); [clear - X; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 26624 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 26624 M M1 INCX DK01f) as DK01.
  (* [comment removed for export] *)
  assert (SV1 : forall a v, sp - 160 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (proj1 (L5A.u64_at_vis H M1 a v (VISs a 8 ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL160 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X. }
  assert (OWN1 : own sp R M1).
  { unfold own. repeat split; (apply SV1; [clear; lia| clear; lia| assumption]). }
  clear C104 C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 SV1.
  (* [comment removed for export] *)
  assert (FRk0 : ff_room 0 FF LK) by (apply (PMAUAR.ff_room_ofB PNRA.FCB 7 FF LK 0 FRM); [clear; lia| left; reflexivity]).
  change 0x5dc2c with (PMA.SM_PC 0).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 0 LBX (PNM.bparser_own s) FF LK cr Aw sp 26624 (sp - 160) (sp - 104) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb34b0 ltac:(left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
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
  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 26624 M M1 M2 DK01f DK12f) as DK02f.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (HH2 : ri_inv HI LB ((F, 0, sp - 160 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 0, sp - 160 + 32) :: FF) in *.
  assert (FOK' : PNRA.frame_okB FF' fb). { split; [exists rs; right; exact Hfb| exact Fal]. }
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 26624 160 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  (* [comment removed for export] *)
  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 160)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B23R : getr R2 (reg 23) = Z_to_bv 64 2147450880) by (rewrite (R2c 23%nat) by inl; exact T23).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 56) fl) by (replace (F + 56) with (F + 64 - 8) by (clear; lia); exact FLC).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL160 SHI SPT O1 GFR GFLR; unfold oec, op in *; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g).
  assert (Q1 : 140735332487328 <= sp <= 140737488355328) by (clear - SL160 SHI SPT; lia).
  assert (Qop : 6905856 <= op <= 140737488354912) by (clear - O1; lia).
  assert (Q3 : 6905856 <= F <= 140737488355264) by (clear - GFR; lia).
  assert (Q4 : (sp - 160) + 160 <= F \/ F + 64 <= (sp - 160)) by (clear - GFCEIL SL160; lia).
  assert (Q5 : (sp - 160) + 160 <= fl \/ fl + 1 <= (sp - 160)) by (clear - GFLR SL160; lia).
  assert (Q7 : 4096 <= fl <= 140737488355327) by (clear - GFLR; lia).
  LeanFeed.pfeed P (PNARSP.arsB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => op | 36%nat => oec | 50%nat => F | 51%nat => fl | _ => 0 end)) ltac:(first [assumption | unfold PNARSP.aligned; assumption]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26
                 & SH3 & SH2 & SH1 & SH0 & SH7 & SH6 & SH5 & SH4 & SAVS & HPC & HDESC & HMAG & SAVF & D24).
  set (W3 := fun a => (sp - 112 <= a < sp - 112 + 8) \/ (sp - 136 <= a < sp - 136 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 8)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb34b0 R3 0xaed4c M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X; apply Hn; left; clear - X; lia| intros X; apply Hn; right; left; clear - X; lia
                    | intros X; apply Hn; right; right; left; clear - X; lia| intros X; apply Hn; right; right; right; clear - X; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X|[X|[X|X]]].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      + unfold aclientw, aclient_g. right; left. split; [clear - X SL160 SHI SPT; lia| intros Y; clear - Y; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity| change (ff_bytes 0) with 64; clear - X; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 0 (sp - 160 + 32)); [left; reflexivity|]. change (ff_bytes 0) with 64.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X; lia.
    - destruct Wa as [X|[X|[X|X]]]; clear - X GFR SL160 SPT FSAPP FSCEIL; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 26624 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 26624 [] M2 M3 W3 FR3). intros a Ha Hc _ X. destruct X as [X|[X|[X|X]]].
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - apply (NCS0 a); [clear - X; lia| exact Hc].
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y & _). clear - X Y; lia.
    - destruct (APART a 1 sp 26624 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y & _). unfold SB in Y. clear - X Y; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 26624 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL160 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL160 SHI SPT; lia| intros [X|[X|[X|X]]]; clear - X Ha GFCEIL GFR SL160 SPT; unfold SB in *; lia]. }
  assert (WAPPR : PMKA.wapp (PNRA.W_brun PMA.AD PMA.AN fb)).
  { unfold PNRA.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNRA.o_src, PNRA.o_is, PNRA.o_bb, PNRA.o_nb, PNRA.o_tb, PNRA.o_stk, PNRA.o_ec, PNRA.o_p, PMSP.o_p, PMSP.o_is, PMSP.o_ec.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PMA.AD ADDR_A PMA.AN NADDR_A PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj].
    unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
    pose proof FSAPP as (FA0 & FA1 & FA2). unfold BIGSHADOW_LO, BIGSHADOW_HI in FA1.
    repeat apply PMKA.wapp_cons; [..| apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia. }
  set (WR := PNRA.W_brun PMA.AD PMA.AN fb) in *.
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 26624 (sp - 160) (own sp R) F 0 WR (PNM.bparser_own s) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 26624 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 26624 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 26624 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [apply (L5SAR.dk_trans L ar LBX FF sp 26624 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3|].
    split; [exact OWN3|].
    change (ff_bytes 0 / 8) with 8. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 8 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (R1c : forall j, In j [3; 4]%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj. apply KS1. revert j Hj. apply (L5K.incl_b [3; 4]%nat). vm_compute. reflexivity. }
  (* [comment removed for export] *)
  assert (AOPp : PMSPA.aobjA FF op PNM.PSIZE) by (apply (PNAPAR.aobj_fbB FF fb op PNM.PSIZE FOK); unfold op, PNM.PSIZE; clear; lia).
  assert (PA3 : PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD) M3 op ois s).
  { apply (PNAPAR.bparser_keepA L ar C HI HIok LB FF LK cr Aw (vml_of model) [] sp 26624 M M3 op ois s HH EK03f PMKA.wapp_nil AOPp);
      [unfold LB; apply incl_appl; apply incl_refl| intros i _ r0 []| intros B m _ i _ r0 []| exact PA]. }
  assert (IA3 : PM.iss_at RSEGS PMA.AD PMSPA.accA M3 ois str sm).
  { apply (PMKA.iss_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB BRB ois str sm); [| | intros i _ r0 []| intros c n p _ i _ r0 []| exact IA].
    - apply (PNAPAR.aobj_fbB FF fb ois 272 FOK); unfold ois; clear; lia.
    - unfold LB. apply incl_appr. exact INCS. }
  assert (VIS3' : PMSPA.visitor_at RSEGS PMA.AD M3 ov).
  { apply (PMKA.visitor_keepA RSEGS PMA.AD L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB ov); [| intros i _ r0 []| exact VIS].
    apply (PNAPAR.aobj_fbB FF fb ov 8 FOK); unfold ov; clear; lia. }
  assert (EC3 : PMSPA.ec_at RSEGS M3 oec e cat).
  { apply (PMKA.ec_keepA RSEGS L ar LB FF sp 26624 [] M M3 EK03f PMKA.wapp_nil FRB oec e cat); [| intros i _ r0 []| exact EC].
    apply (PNAPAR.aobj_fbB FF fb oec 16 FOK); unfold oec; clear; lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3) by (apply (PMASK.base_keep L ar C LY LB FF sp 26624 [] M M3 EK03f); [intros a _ r0 []| exact BASE]).
  assert (ERR3 : PNSTA.berr_okA RSEGS PMA.AD PMA.AAD PMA.AN M3 ax).
  { apply (PNSTA.berr_okA_frame RSEGS PMA.AD PMA.AAD PMA.AN PMA.addrs_wf_B M M3); [| exact ERR].
    intros a Ha D. apply EK03f. split; [exact Ha|]. split; [| intros r0 []]. unfold aclient, aclient_g. right; right; left.
    pose proof (depA_img a D). rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia| exact (PMA.ly_static L C LY a D)]. }
  assert (AV4 : avis H2 (F / 8 + 2147450884) 1) by (apply (L5A.avis_sub H2 (F / 8 + SB) 8); [exact VSH| unfold SB; clear; lia| unfold SB; clear; lia]).
  assert (R4a : 0 <= F / 8 + 2147450884) by (clear - Q3; lia).
  assert (R4b : F / 8 + 2147450884 + 1 <= 2 ^ 64) by (clear - Q3; pose proof (Z.div_le_upper_bound F 8 17592186044408 ltac:(lia) ltac:(lia)); lia).
  pose proof (L5A.u8_at_vis H2 M3 (F / 8 + 2147450884) 4 AV4 R4a R4b) as UV. rewrite VIS3 in UV.
  assert (U8c : L5.u8_at RSEGS M3 (F / 8 + 2147450884) 4) by (apply (proj1 UV); exact SH4). clear UV.
  (* [comment removed for export] *)
  assert (PRE3 : PNRA.brun_pre RSEGS PMA.AD PMA.AN PMA.AAD M3 fb s str sm ax).
  { refine (PNBKA.pre_after_call L ar LB FF sp 26624 [] M M3 fb s s str sm sm ax ax FRB EK03f PMKA.wapp_nil FOK _ RPRE PA3 IA3 GROW BASE3 ERR3). intros i _ rr []. }
  assert (LM3 : rs_mem L ar HI R M model LBX FF LK Aw cr sp fb s str sm ax F M3 model3 LK2 Aw s sm ax cr).
  { unfold rs_mem. split; [exact BI3|]. split; [exact PRE3|]. split; [apply PNBKA.src_step_refl|]. split; [apply PNST.bax_le_refl|].
    split; [apply PNBKA.credit_keep_refl|]. split; [exact U8c| reflexivity]. }
  assert (SPL3 : spill M3 sp F).
  { pose proof (PNARSK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr CTX G LM3) as (_ & _ & _ & _ & _ & _ & SVr3).
    fold H2 in HID3. split.
    - apply (SVr3 (sp - 112) F ltac:(clear; lia) ltac:(clear; lia)). rewrite HID3. rewrite VIS3. exact SAVF.
    - apply (SVr3 (sp - 136) 2147450880 ltac:(clear; lia) ltac:(clear; lia)). rewrite HID3. rewrite VIS3. exact SAVS. }
  assert (ACC32 : aacc M3 (F + 32) 4).
  { apply (aacc_sh M3 F 32 4 (proj1 GF8) Q3 ltac:(reflexivity) ltac:(clear; lia) ltac:(clear; lia)). change (32 / 8) with 4. replace (F / 8 + 2147450880 + 4) with (F / 8 + 2147450884) by (clear; lia). exact U8c. }
  unfold op, ov, oec, ois in *. clear op ov oec ois.
  assert (R3gp : getr R3 (reg 3) = getr R (reg 3)) by (rewrite (KS3 3%nat) by inl; rewrite (R2c 3%nat) by inl; apply R1c; inl).
  assert (R3tp : getr R3 (reg 4) = getr R (reg 4)) by (rewrite (KS3 4%nat) by inl; rewrite (R2c 4%nat) by inl; apply R1c; inl).
  apply (PNARSK.rs_call_read L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M3 model3 LK2 Aw s sm ax cr fx3 R3 0xb3560 32 4 SR CTX G LM3
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) ACC32 Y1).
  { unfold L5.ra_ok; clear; lia. }
  { rewrite (KS3 2%nat) by inl. exact B2R. }
  { rewrite R3gp. exact Rgp. }
  { rewrite R3tp. exact Rtp. }
  { exact Y10. } { exact Y11. } { exact Y12. }
  intros fx4 R4 M4 model4 LK4 Aw4 src4 sm4 d RP4 Y10d Hd UNR4 RD1 RD0 DEF4 QC4 LM4 AG4 ECK4 DKB4.
  set (s4 := PNM.with_srcB s src4) in *.
  assert (RC4 : forall k, In k [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R4 (reg k) = getr R3 (reg k)).
  { intros k Hk. apply (L5SAR.cs_of_preserved R3 R4 k RP4). revert k Hk. apply (L5K.incl_b [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26]%nat). vm_compute. reflexivity. }
  apply (rs_after_rd1 K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M4 model4 LK4 Aw4 s4 sm4 ax cr fx4 R4 d SR SPN MKE CTX G LM4).
  - unfold rregs.
    split; [rewrite (RC4 2%nat) by inl; rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (RC4 3%nat) by inl; exact R3gp|]. split; [rewrite (RC4 4%nat) by inl; exact R3tp|].
    split; [rewrite (RC4 8%nat) by inl; rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (RC4 9%nat) by inl; rewrite (KS3 9%nat) by inl; exact B9R|].
    split; [rewrite (RC4 19%nat) by inl; rewrite (KS3 19%nat) by inl; exact B19R|]. split; [rewrite (RC4 24%nat) by inl; exact Y24|].
    split; [rewrite (RC4 25%nat) by inl; exact Y25|]. rewrite (RC4 26%nat) by inl; exact Y26.
  - apply (PNARSK.spill_agree M3 M4 sp F); [clear - SL160 SPT; lia| clear - SHI SPT; lia| exact SPL3| intros a Ha; apply AG4; clear - Ha; lia].
  - exact Y10d.
  - rewrite (RC4 20%nat) by inl. rewrite (KS3 20%nat) by inl. exact B20R.
  - rewrite (RC4 21%nat) by inl. exact Y21.
  - rewrite (RC4 22%nat) by inl. exact Y22.
  - rewrite (RC4 23%nat) by inl. exact Y23.
  - exact Hd.
  - exact DEF4.
  - exact (ECK4 _ _ EC3).
  - exact (PNBKA.btop_pos_refl s INV).
  - unfold s4. cbn [PNM.with_srcB PNM.b_src]. rewrite UNR4. clear. lia.
  - exact INV.
Qed.
End WithHeap.
End PNARST.
