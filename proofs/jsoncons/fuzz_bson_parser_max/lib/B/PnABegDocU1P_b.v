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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout PnModel PnModelFacts PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b PnASrcKit_b PnASrcRead1_b PmAUarK_b PmAUar_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnBrObj. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnAParKit_b PnAReset1_b PnOwnerOkA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrKitA_b PnSpecsAX_b PnSpecsAXR_b PnAEmbCF_b PnABegDocP_b Ba0_code_ad9e4_ad9e8_b PnABegDocK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require BatByteCell_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnABegDoc_b PnAEmbKit_b PnAHarnessKit_b PnAReset1_b.

Module PNABDU1P.
Import L5A. Import L5CA. Import L5SAR. Import PNBKA. Import PNABDK. Import PNABD.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma wa_u64_of_defined (M : mem) a : 0 <= a -> a + 8 <= 2 ^ 64 -> L5.defined M a 8 -> exists w, 0 <= w < 2 ^ 64 /\ L5.u64_at RSEGS M a w.
Proof.
  intros Ha Hn D. destruct (PMCG.rdn_some RSEGS M 8%nat a Ha ltac:(cbn; lia) ltac:(intros i Hi; apply D; cbn in Hi; lia)) as (bs & E & Hl).
  exists (bytes_le_to_Z bs). pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. cbn in Hb.
  split; [lia|]. unfold L5.u64_at. rewrite E. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl| lia].
Qed.

Lemma wa_u32_agree (M M' : mem) a v : L5C.agree_on M M' a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros AG H0 H1 U. unfold L5.u32_at in *. rewrite (L5C.rdn_agree RSEGS M M' 4%nat a); [exact U| lia| cbn; lia|].
  intros i Hi. cbn in Hi. apply AG. lia.
Qed.

Lemma u1_ahpres_up (LBx : list (Z * Z)) (FFx : list fframe) (sp scr d : Z) (Wx : list L5.range) (Ma Mb : mem) :
  L5CA.ahpres L ar LBx FFx sp scr Wx Ma Mb -> 0 <= d -> 0 <= scr -> 0 <= sp -> ahl_ceil ar <= sp -> sp + d <= 2 ^ 47 -> L5.defined Ma sp d ->
  L5CA.ahpres L ar LBx FFx (sp + d) (scr + d) Wx Ma Mb.
Proof.
  intros (AK & DF & DK) Hd Hs Hp Hc Ht DA.
  assert (CL : forall a, HeapIfaceA.aclient L ar LBx FFx (sp + d) (scr + d) a -> HeapIfaceA.aclient L ar LBx FFx sp scr a).
  { intros a X. unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g in X |- *.
    destruct X as [X|[(X1 & X2)|X]]; [left; exact X| right; left; split; [exact X1| intros (Y1 & Y2); apply X2; split; lia]| right; right; exact X]. }
  split; [| split].
  - intros a (A0 & A1 & A2). apply AK. split; [exact A0|]. split; [exact (CL a A1)| exact A2].
  - intros i Hi. replace (sp + d - (scr + d) + i) with (sp - scr + i) by lia.
    destruct (Z_lt_ge_dec i scr) as [Hl|Hg]; [apply DF; lia|].
    replace (sp - scr + i) with (sp + (i - scr)) by lia.
    apply (DK (sp + (i - scr))); [lia| | apply DA; lia].
    unfold HeapIfaceA.aclient, HeapIfaceA.aclient_g. right; left. split; [lia| intros (Y1 & Y2); lia].
  - intros a Ha Hc'. apply DK; [exact Ha| exact (CL a Hc')].
Qed.
Lemma u1_ahpres_g (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (Aw : list (Z * Z)) (V : _) (M1 M3 M7 : mem) (b k e x wa wl sp wlo : Z) :
  ri_inv HI (PNM.bvec_own b k ++ LB) FF LK cr Aw M3 V ->
  L5CA.ahpres L ar LB FF (sp - 224) (PMSPA.pm_scr 0) [] M1 M3 ->
  L5.defined M1 (sp - 224) 64 -> 0 <= ahl_ceil ar -> ahl_ceil ar <= wlo -> sp - 224 - PMSPA.pm_scr 0 <= wlo -> wlo <= sp - 224 ->
  0x7fff80000000 <= ar_sptop ar <= 2 ^ 47 -> sp <= 2 ^ 47 ->
  b <= e -> e + 40 <= b + 40 * 2 ^ k -> wa <= x -> x + 8 <= wa + wl -> mem_grows M3 M7 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e <= a < e + 40 \/ x <= a < x + 8 \/ wlo <= a < sp - 160) -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)) ->
  L5CA.ahpres L ar LB FF (sp - 160) (64 + PMSPA.pm_scr 0) [(wa, wl)] M1 M7.
Proof.
  intros HH3 AH D1 C0 CW W1 W2 SPT SPH BE EE WX XW MG WR.
  assert (AH' : L5CA.ahpres L ar LB FF (sp - 224 + 64) (PMSPA.pm_scr 0 + 64) [] M1 M3).
  { apply u1_ahpres_up; [exact AH | lia | unfold PMSPA.pm_scr; lia | lia | lia | lia | exact D1]. }
  replace (sp - 224 + 64) with (sp - 160) in AH' by lia.
  replace (PMSPA.pm_scr 0 + 64) with (64 + PMSPA.pm_scr 0) in AH' by lia.
  destruct AH' as (AK & DF & DK).
  split; [|split].
  - intros a (A0 & A1 & A2).
    assert (A1' : HeapIfaceA.aclient L ar (PNM.bvec_own b k ++ LB) FF (sp - 160) (64 + PMSPA.pm_scr 0) a).
    { unfold HeapIfaceA.aclient in *. eapply L5SAR.aclient_appb. exact A1. }
    rewrite WR.
    + apply AK. split; [exact A0|]. split; [exact A1| intros r Hr; destruct Hr].
    + exact A0.
    + intros [Xe|[Xx|Xw]].
      * apply (PMARS1.own_not_aclient L ar C HI HIok (PNM.bvec_own b k) LB FF LK cr Aw M3 V b (40 * 2 ^ k) a (sp - 160) (64 + PMSPA.pm_scr 0) HH3);
          [unfold PNM.bvec_own, PNM.BSZ; left; reflexivity | lia | exact A1].
      * apply (A2 (wa, wl) (or_introl eq_refl)). unfold L5.in_rng; cbn [fst snd]; lia.
      * assert (CS : (ahl_ceil ar <= a /\ ~ (sp - 160 - (64 + PMSPA.pm_scr 0) <= a < sp - 160)) \/ a < ahl_ceil ar).
        { eapply (L5SAR.aclient_cases L ar C HI LYa HIok); [exact HH3 | exact SPT | exact A1']. }
        destruct CS as [(Y1 & Y2)|Y]; [apply Y2; lia | lia].
  - intros i Hi. apply MG. apply DF. exact Hi.
  - intros a Ha Hc HM. apply MG. exact (DK a Ha Hc HM).
Qed.

Lemma bd_u1_push_ok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 :
  bd_u1_push_T L ar HI K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2.
Proof.
  unfold bd_u1_push_T.
  intros s6 sm6 ax6 cr6 M1 model1 LK1 Aw1 M3 model3 LK3 Aw3 M7 model7 CTX G LM INV6 DEP CAP V0 V8 V16 ELT DEF3 ACC3 ANN3 ACCO BASE3 HP3 MRT3 INCL INCA AM3 RI3 RI7 AM7 MRT7 MG7 FR7 E0 E16 E24 E32 END7.
  set (s1 := PNBO.set_more s6 1) in *.
  change (PNM.b_sb s1) with (PNM.b_sb s6) in *. change (PNM.b_sk s1) with (PNM.b_sk s6) in *. change (PNM.b_stk s1) with (PNM.b_stk s6) in *.
  assert (INV1 : PNRA.binv s1) by exact INV6.
  pose proof (vecfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm6 ax6 cr6 CTX G LM INV1)
    as (_ & _ & _ & VRB & _ & _ & VK).
  change (PNM.b_sb s1) with (PNM.b_sb s6) in VRB. change (PNM.b_sk s1) with (PNM.b_sk s6) in VK.
  set (b := PNM.b_sb s6) in *. set (k := PNM.b_sk s6) in *. set (stk := PNM.b_stk s6) in *.
  set (n := Z.of_nat (length stk)) in *.
  pose proof CTX as (Hw & HH & AM & K0 & ENT & FRM & FRS & FOK & SP32 & ARGS & RPRE & INCS & INV & EC0 & HE & UNR & CRED & KONT).
  destruct ENT as (Rra & RAok0 & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof FOK as ((rs & Hfb) & Fal).
  pose proof LM as (BI & RP1 & STEP1 & AXL1 & CK1 & SHC1 & EBB1).
  pose proof (PNABDK.pfacts_of L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm6 ax6 cr6 CTX G LM)
    as (PF & _). unfold pfacts in PF.
  destruct PF as (_ & _ & _ & PFSP & _ & _ & PFOP & _ & PFOS & _).
  assert (BIN : In (b, PNM.BSZ * 2 ^ k) (PNM.bvec_own b k ++ rest_own s1 ++ LBX)) by (left; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ _ _ _ _ M3 _ b (PNM.BSZ * 2 ^ k) RI3 BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5 & Bq6 & Bq7 & Bq8).
  unfold PNM.BSZ in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ RI3) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  unfold app_mem in FSAPP.
  assert (HfbF : In (fb, 5, rs) ((F, 0, sp - 160 + 32) :: FF)) by (right; exact Hfb).
  pose proof (Bq8 _ HfbF) as VFB. cbn [ff_addr ff_class fst snd] in VFB. change (ff_bytes 5) with 2048 in VFB.
  pose proof (WF _ HfbF) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 5) with 2048 in F2.
  destruct VK as (VK & _).
  pose proof BI as (HH1 & AM1 & MRT1 & INCA1 & INCL1 & ASTK1 & EK1 & DK1 & OWN1 & DSH1).
  pose proof ASTK1 as (_ & SLO1 & _ & _ & SDEF1 & _).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)) as P2K0.
  assert (P2K : 2 ^ k <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
  assert (NK : n + 1 <= 2 ^ k) by lia.
  assert (N0 : 0 <= n) by (unfold n; lia).
  assert (HS7 : 4096 <= PMSPA.pm_scr 7) by (unfold PMSPA.pm_scr; lia).
  assert (HS0 : 16 <= PMSPA.pm_scr 0) by (unfold PMSPA.pm_scr; lia).
  set (c := PNM.BS 2 0 4 0 0) in *.
  (* the written ranges, as one predicate *)
  set (WR := fun a => b + 40 * n <= a < b + 40 * n + 40 \/ fb + 464 + 400 <= a < fb + 464 + 400 + 8 \/ sp - 240 <= a < sp - 160) in *.
  assert (AGR : forall x m, 0 <= x -> x + m <= 2 ^ 64 -> (forall a, x <= a < x + m -> ~ WR a) -> L5C.agree_on M3 M7 x m).
  { intros x m Hx Hm NW j Hj. apply FR7; [lia|]. apply NW. lia. }
  (* the vector block lies below the stack and apart from the parser object's frame *)
  assert (VSTK : b + 40 * 2 ^ k <= sp - 240) by lia.
  assert (FSTK : fb + 2048 <= sp - 240) by lia.
  assert (NWV : forall a, b <= a < b + 40 * n -> ~ WR a).
  { intros a Ha [X|[X|X]]; [lia| destruct VFB; lia| lia]. }
  assert (NWO : forall a, fb + 464 + 392 <= a < fb + 464 + 400 \/ fb + 464 + 408 <= a < fb + 464 + 416 -> ~ WR a).
  { intros a Ha [X|[X|X]]; [destruct VFB; lia| lia| lia]. }
  (* the new element's length cell exists at M7 *)
  assert (DEF7 : L5.defined M7 b (40 * 2 ^ k)) by (intros i Hi; apply MG7; apply DEF3; exact Hi).
  destruct (wa_u64_of_defined M7 (b + 40 * n + 8) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (b + 40 * n + 8 + i) with (b + (40 * n + 8 + i)) by lia; apply DEF7; lia))
    as (lenv & Hlenv & ULEN).
  exists lenv. split; [exact Hlenv|].
  set (stk' := stk ++ [PNM.BS 2 lenv 4 0 0]).
  assert (LEN' : Z.of_nat (length stk') = n + 1) by (unfold stk', n; rewrite length_app; cbn [length]; lia).
  (* bvec_at at M7 *)
  assert (VEC7 : PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M7 (fb + 464 + 392) b k stk').
  { unfold PNM.bvec_at. unfold PNM.BSZ. rewrite LEN'.
    split; [apply (L5C.u64_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWO; lia]| lia| lia| exact V0]|].
    split; [replace (fb + 464 + 392 + 8) with (fb + 464 + 400) by lia; replace (b + 40 * (n + 1)) with (b + 40 * n + 40) by lia; exact END7|].
    split; [apply (L5C.u64_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWO; lia]| lia| lia| exact V16]|].
    split; [lia|]. split; [lia|]. split; [exact Bq4|]. split; [exact DEF7|].
    assert (AGS : forall a m, 0 <= a -> a + m <= b + 40 * 2 ^ k -> b <= a -> PMFA.agsh M3 M7 a m).
    { intros a m H0 H1 H2 x Hx.
      assert (D8 : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
      apply FR7; [unfold S, SB; lia|]. unfold S, SB. intros [X|[X|X]]; [destruct Bq6; lia| destruct PFOS; lia| lia]. }
    split; [apply (PMFA.accA_agree M3 M7 b (40 * (n + 1))); [apply AGS; lia| exact ACC3]|].
    split; [apply (PMFA.annA_agree M3 M7 b (40 * (n + 1)) (40 * 2 ^ k)); [lia| lia| replace (40 * 2 ^ k) with ((5 * 2 ^ k) * 8) by lia; apply Z_mod_mult| apply AGS; lia| exact ANN3]|].
    intros i Hi. unfold stk' in Hi |- *. rewrite length_app in Hi. cbn [length] in Hi.
    destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hg].
    - rewrite app_nth1 by exact Hl. pose proof (ELT i Hl) as (B0 & B8 & B16 & B24 & B32).
      assert (Hi40 : 40 * Z.of_nat i + 40 <= 40 * n) by (unfold n; lia).
      split; [apply (wa_u32_agree M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWV; lia]| lia| lia| exact B0]|].
      split; [apply (L5C.u64_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWV; lia]| lia| lia| exact B8]|].
      split; [apply (L5C.u64_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWV; lia]| lia| lia| exact B16]|].
      split; [apply (L5C.u8_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWV; lia]| lia| lia| exact B24]|].
      apply (L5C.u64_at_agree RSEGS M3 M7); [apply AGR; [lia|lia|intros a Ha; apply NWV; lia]| lia| lia| exact B32].
    - assert (Ei : i = length stk) by lia. subst i. rewrite nth_middle.
      replace (Z.of_nat (length stk)) with n by reflexivity.
      unfold PNM.bstate_at. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [exact E0|]. split; [exact ULEN|]. split; [exact E16|]. split; [exact E24| exact E32]. }
  (* base cells are image addresses, none written *)
  assert (BASE7 : PMSTA.base_okA RSEGS PMA.AD M7).
  { apply (PNHAK.base_keep M3 M7); [| exact BASE3].
    intros a Ha Hb. apply FR7; [exact Ha|]. unfold PNHAK.bcell in Hb.
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG.
    intros [X|[X|X]]; [destruct Bq5; lia| destruct FSIMG; lia| lia]. }
  (* ahpres from M1 to M7 *)
  assert (HP7 : L5CA.ahpres L ar (rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) (sp - 160) (64 + PMSPA.pm_scr 0) [(fb + 464 + 392, 24)] M1 M7).
  { apply (u1_ahpres_g (rest_own s1 ++ LBX) ((F, 0, sp - 160 + 32) :: FF) LK3 cr6 Aw3 (vml_of model3) M1 M3 M7 b k (b + 40 * n) (fb + 464 + 400) (fb + 464 + 392) 24 sp (sp - 240) RI3 HP3);
      [eapply L5.defined_sub; [exact SDEF1| lia| lia]| lia| lia| lia| lia| exact SPT| lia| lia| lia| lia| lia| exact MG7| exact FR7]. }
  destruct (bd_push_post L ar C HI LY HIok K R M model LBX FF LK Aw cr sp r fb cat e s str sm ax w F fl LK2 M2 model2 M1 model1 LK1 Aw1 s1 sm6 ax6 cr6 M7 model7 LK3 Aw3 cr6 b k stk' (64 + PMSPA.pm_scr 0)
              ltac:(unfold PMSPA.pm_scr; lia) CTX G LM VEC7 BASE7 HP7 (L5LZ.model_rt_trans _ _ _ MRT3 MRT7) INCL INCA AM7 RI7 CK1) as (BM7 & FR17 & EC17).
  split; [exact BM7|]. split; [exact FR17| exact EC17].
Qed.

End WithHeap.
End PNABDU1P.
