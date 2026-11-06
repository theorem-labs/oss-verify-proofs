(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmParStep PeBSrcKitJ PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCSrcXsgetnB PeBFillP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b9b7c_b9b80.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PECFILLTBB.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Ltac vis64 OAV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis32 OAV := lazymatch goal with |- L5.u32_at ?sg (mrestrict ?H ?M0) ?a ?v =>
  apply (proj2 (L5A.u32_at_vis H M0 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Lemma vstr_at_tbw (M M' : word -> option byte) o s : 0 <= o -> o + 24 <= 2 ^ 64 -> PMFA.agA M M' o 24 ->
  (forall c n p, s = PM.VLong c n p -> PMFA.agsh M M' p c /\ L5.defined M' p c) ->
  PM.vstr_at RSEGS PMSPA.accA M o s -> PM.vstr_at RSEGS PMSPA.accA M' o s.
Proof.
  intros Ho Ho' [AG SH] AGB (D & C & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|].
  split; [apply (PMFA.accA_agree M M' o 24); [intros x Hx; apply SH; lia| exact C]|].
  destruct s as [n|c n p].
  - destruct H as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia|exact B0].
  - destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (AGB c n p eq_refl) as [SHp DBp].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia|exact W0]|].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia|exact W8]|].
    split; [apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia|lia|lia|exact W16]|].
    split; [exact Hn|]. split; [exact Hc|]. split; [exact He|]. split; [exact DBp|]. apply (PMFA.accA_agree M M' p c SHp CB).
Qed.

Lemma parser_tbw_keepA (M M' : word -> option byte) op ois s :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 -> PMFA.agA M M' op 384 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agsh M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  L5.defined M' op 384 -> L5.defined M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> PMFA.agA M M' (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> PMFA.agsh M M' p c /\ L5.defined M' p c) ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M' op ois s.
Proof.
  intros PA Ho Ho' [AG SH] Hq Hq' SHQ DOP DCQ Hb Hb' AGB AGT.
  pose proof PA as (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
  destruct SRC as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & G1 & G2 & G3 & G4 & DC & CC & C240).
  assert (U64 : forall a v, op <= a -> a + 8 <= op + 384 -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U32 : forall a v, op <= a -> a + 4 <= op + 384 -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  assert (U8 : forall a v, op <= a -> a + 1 <= op + 384 -> L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v).
  { intros a v Ha Hb0 X. apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact X]. }
  unfold PM.parser_at, PM.src_fields_at.
  split; [apply U64; [lia|lia|exact H0]|]. split; [exact DOP|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply U8; [lia|lia|exact H8]|]. split; [apply U8; [lia|lia|exact H9]|]. split; [apply U32; [lia|lia|exact H12]|].
  split; [apply U8; [lia|lia|exact H16]|]. split; [apply U32; [lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PeCLayoutB.CADDR_B M M' (op + 32)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact NI]|].
  split.
  { split; [apply U64; [lia|lia|exact F1]|]. split; [apply U64; [lia|lia|exact F2]|].
    split; [intros i Hi; replace (op + 24 + 256 + i) with (op + (280 + i)) by lia; apply DOP; lia|].
    split; [apply U64; [lia|lia|exact F4]|]. split; [apply U64; [lia|lia|exact F5]|]. split; [apply U64; [lia|lia|exact F6]|]. split; [apply U64; [lia|lia|exact F7]|].
    split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
    split; [exact DCQ|].
    split; [apply (PMFA.accA_agree M M' _ _ SHQ CC)|].
    apply (PMFA.accA_agree M M' (op + 24 + 240) 56); [intros x Hx; apply SH; lia| exact C240]. }
  split; [apply U32; [lia|lia|exact H320]|]. split; [apply U64; [lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (vstr_at_tbw M M' (op + 336)); [lia|lia| split; [intros i Hi; apply AG; lia| intros x Hx; apply SH; lia]| exact AGT| exact TB]|].
  split; [apply (PMFA.vec_at_agreeA RSEGS M M' (op + 360)); [lia|lia|lia|lia| intros i Hi; apply AG; lia| exact AGB| exact VEC]|].
  split; [exact B1|]. split; [exact B2|]. exact B3.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Definition ctbfill_res (pl : list Z) (R R' : bvmap 5 word) (M' : word -> option byte) (src src' : PM.srcst) (sm sm' : PM.strm) : Prop :=
  src' = src /\ exists p c, getr R 11%bv = Z_to_bv 64 p /\ getr R' 10%bv = Z_to_bv 64 c /\ 0 <= c <= PM.CHUNK /\ PM.sm_g sm' = PM.sm_g sm + c
    /\ (c < PM.CHUNK -> PM.sm_g sm' = PM.sm_eg sm /\ PM.sm_st sm' = 2) /\ (PM.sm_st sm = 2 -> c = 0)
    /\ L5.defined M' p c /\ L5.bytes_at RSEGS M' p (UbjRef.slice pl (blen pl - (PM.sm_eg sm - PM.sm_g sm)) c)
    /\ (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm').
Definition cfill_tb_spec : Prop := @PECSPA.csrc_spec SCFG_P RSEGS PeCLayoutB.CADDR_B L ar HI (pa_fill_buffer PeCLayoutB.CADDR_B) 3 16 PMSPA.tbfill_args PMSPA.tbfill_W ctbfill_res.

Theorem cfill_tb_ok : cfill_tb_spec.
Proof.
  pose proof (PECXGB.cxsgetn_ok L ar C IL HI LY HIok ICok ILY) as XS. unfold cfill_tb_spec, PECSPA.csrc_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb pl s str sm Wextra HH AM K0 ENT FRM FRS FOK ALN A10 FARGS WX PA IA BASE ACCP INCS POK CONT KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  unfold PMSPA.tbfill_args in FARGS. destruct FARGS as (p & A11 & A12 & ct & nt & qt & ETB & Dq1 & Dq2). unfold PMSPA.tbfill_W in WX. destruct WX as (p' & A11' & Hp' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12. unfold PM.CHUNK in A12, Dq2.
  change (PMSPA.pm_scr 3) with 18432 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (LB := PM.parser_own s ++ LBX) in *.
  pose proof (PMBSKJ.src_vis L ar C HI LY HIok LB FF LK cr Aw M model fb (PMSPA.o_is PeCLayoutB.CADDR_B fb) s sp 18432 HH FOK PA ASTK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof (PMBSKJ.iss_vis L ar C HI LY HIok LB FF LK cr Aw M model fb str sm sp 18432 HH FOK IA ASTK)
    as ((I1 & I8 & IBIG) & IZ & IW & ICE & IAV & AOI & IOS).
  set (os := PMSPA.o_src PeCLayoutB.CADDR_B fb) in *. set (ois := PMSPA.o_is PeCLayoutB.CADDR_B fb) in *.
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 18432 48 HH ASTK ltac:(lia)) as (SL48 & SH48 & V3).
  pose proof (PMBSKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x13b520 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMBSKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x13b488 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem]. destruct sm as [g eg st].
  cbn [PM.p_src PM.p_tb PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st PM.p_more PM.p_done PM.p_depth PM.p_tg PM.p_b PM.p_k PM.p_stk] in *. subst tb.
  pose proof PA as (_ & PDEF & _ & _ & _ & _ & _ & _ & _ & PSRC & _).
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.p_src PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  fold os ois in S240, S248.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & E1 & E2).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.parser_own, PM.src_own; cbn; left; reflexivity).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.

  pose proof CONT as (CSZ & CBS & _ & _ & CST2). cbn [PM.sm_st PM.sm_g PM.sm_eg] in CST2.
  change (PMSP.o_is PeCLayoutB.CADDR_B fb) with ois in CBS.
  assert (TIN : In (qt, ct) LB) by (unfold LB, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own; cbn; right; right; left; reflexivity).
  destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, T4, TAPP. unfold app_mem in TAPP.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PTB & _). cbn [PM.p_tb] in PTB.
  destruct PTB as (_ & _ & _ & _ & _ & _ & _ & _ & DBt & CBt).
  assert (Ep : p' = p).
  { rewrite A11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by lia. lia. }
  subst p'. clear A11'.
  pose proof (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct ois 272 HH TIN AOI) as TAO.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (BOWN : incl (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) (PM.VLong ct nt qt) tg vb vk stk)) LB) by (unfold LB; apply incl_appl, incl_refl).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (HO : bv_unsigned (getr R (reg 10)) = os) by (rewrite A10; apply L5.unsigned_lit; lia).
  destruct IST as [ST0|ST2].
  2:{
    subst st.
    pose proof (PMBFBP.afbE_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => p | 36%nat => os | 37%nat => ois | _ => 0 end)) as P.
    cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
        | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
        | |- PMBFBP.aligned _ _ => unfold PMBFBP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & PP). pdestr PP.
    unfold PMSPA.cfg. cbn [pa_fill_buffer PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B].
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb9944 R1 0xb9bcc M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1).
    { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
    { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (EK01 : L5SAR.ek L ar LB FF sp 18432 [] M M1).
    { apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 18432 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
      intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
    assert (ASTK1 : L5CA.astk ar M1 sp 18432) by (apply (L5SAR.astk_grows ar M M1 sp 18432 ASTK MGM1)).
    assert (Rr : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    apply (PMBSKJ.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K LB FF LK cr Aw 0xb9bcc r W_b9b7c HH1 AM1 F_b9b7c eq_refl D_b9b7c Rr ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (AOP : PMSPA.aobjA FF (PMSPA.o_p PeCLayoutB.CADDR_B fb) 384).
    { apply (PMBSKJ.aobj_fb FF fb); [exact FOK| |]; unfold PMSPA.o_p; cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]; lia. }
    apply (KONT fx1 R1 M1 model2 LK Aw (PM.SRC qc de rem) (PM.STRM g eg 2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk]; [ first [ rewrite (KS1 _) by inl; reflexivity ] |]). destruct Hk.
    + apply (PMKB.parser_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 18432 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOP); [exact BOWN| intros i _ r0 []| | | |exact PA].
      * intros i _ r0 []. * intros i _ r0 []. * intros c0 n0 p0 _ i _ r0 [].
    + apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 18432 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    + unfold ctbfill_res. split; [reflexivity|]. exists p, 0. cbn [PM.sm_g PM.sm_st PM.sm_eg].
      split; [rewrite L5SAR.r11; exact A11|]. split; [rewrite L5K.rl10; match goal with H : getr R1 (reg 10) = _ |- _ => exact H end|].
      split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros _; split; [apply CST2; reflexivity| reflexivity]|]. split; [intros _; reflexivity|].
      split; [intros i Hi; exfalso; clear - Hi; lia|]. split; [unfold UbjRef.slice; cbn [Z.to_nat firstn]; apply PECSD.bytes_at_nil| intros _; apply CST2; reflexivity].
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M1).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01). intros a _ r0 [].
      * pose proof ASTK1 as (_ & _ & _ & _ & DS1 & _). exact DS1.
      * apply L5SAR.dk_grows. exact MGM1.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2. }
  subst st.

  pose proof (PMBFBP.afbA_conc fx R MV (fun j => match j with 2%nat => sp | 34%nat => p | 36%nat => os | 37%nat => ois | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | exact Rsp | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ (ois + _) _ => unfold MV; vis64 IAV
      | |- L5.u64_at _ _ ois _ => unfold MV; apply (proj2 (L5A.u64_at_vis _ M ois _ ltac:(apply IAV; lia) ltac:(lia) ltac:(lia))); assumption
      | |- L5.u32_at _ _ (ois + _) _ => unfold MV; vis32 IAV
      | |- PMBFBP.aligned _ _ => unfold PMBFBP.aligned; lia
      | |- _ => lia end]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T13 & T14 & T19 & T20 & C48 & C40 & C32 & C24 & C16 & C8).
  unfold PMSPA.cfg. cbn [pa_fill_buffer PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B].
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb9944 R1 0xe0b2c M1v (fun a => sp - 48 <= a < sp - 48 + 48) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (EK01 : L5SAR.ek L ar LB FF sp 18432 [] M M1).
  { apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 18432 [] (sp - 48) (sp - 48 + 48) HH SPT); [lia|lia|lia|].
    intros a Ha Hn. apply FR1; [exact Ha| exact Hn]. }
  assert (ASTK1 : L5CA.astk ar M1 sp 18432) by (apply (L5SAR.astk_grows ar M M1 sp 18432 ASTK MGM1)).
  pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (BASE1 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M1) by (apply (PMBSKJ.base_keep L ar C LY LB FF sp 18432 [] M M1 EK01); [intros a _ r0 []| exact BASE]).
  assert (IA1 : PM.iss_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA M1 ois str (PM.STRM g eg 0)).
  { apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 18432 [] M M1 EK01 PMKB.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (TS1 : forall k v, 8 <= k <= 48 -> L5.u64_at RSEGS M1v (sp - k) v -> L5.u64_at RSEGS M1 (sp - k) v).
  { intros k v Hk X. rewrite <- VIS1, <- HID1 in X.
    apply (proj1 (L5A.u64_at_vis _ M1 (sp - k) v (VIS1s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (STK1 : shadow_zero M1 (sp - 48 - 16384) (16384 / 8)).
  { change (16384 / 8) with 2048. change (18432 / 8) with 2304 in STKSH.
    assert (M8a : (sp - 18432) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 18432) with (sp + (-1152) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 48 - 16384) mod 8 = 0) by (apply PMKB.mod16_8'; replace (sp - 48 - 16384) with (sp + (-1027) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    apply (PMKB.shadow_zero_sub M1 (sp - 18432) 2304); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKB.stksh_keepA L ar LB FF sp 18432 [] M M1 EK01 PMKB.wapp_nil (sp - 18432) 2304); [lia|lia|lia| exact M8a| lia| exact STKSH]. }

  assert (APART : p + 16384 <= g \/ eg <= p).
  { pose proof (PMBSKJ.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c0 & n0 & p0 & -> & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in *.
    - destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct ois 272 HH TIN AOI) as [Z1|Z1]; lia.
    - assert (PIN : In (p0, c0) LBX) by (apply INCS; left; reflexivity).
      assert (NEQ : qt <> p0).
      { apply (PMBSKJ.fst_neq_appA (PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) (PM.VLong ct nt qt) tg vb vk stk)) LBX qt ct p0 c0); [| | exact PIN].
        - exact (PMBSKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
        - unfold PM.parser_own, PM.vs_own; cbn; right; right; left; reflexivity. }
      destruct (PMBSKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct p0 c0 HH TIN (SOWN _ (or_introl eq_refl)) NEQ) as [Z1|Z1]; lia. }

  assert (ACH1 : PMSPA.accA M1 p 16384).
  { pose proof (BRB _ TIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
    apply (PMFA.accA_agree M M1 p 16384); [| intros x Hx; apply CBt; lia].
    intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR1; [unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia| unfold HeapIfaceA.S, HeapIfaceA.SB in *; lia]. }

  unfold PECXGB.cxsgetn_spec in XS. cbn [pa_xsgetn PeCLayoutB.CADDR_B] in XS.
  apply (XS fx1 R1 M1 model1 K LB FF LK Aw cr (sp - 48) 760384 ois p str (PM.STRM g eg 0) HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact T1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split; [|exact STK1].
    apply (L5SAR.astk_sub ar M1 M1 sp 18432 48 16384 ASTK1 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact T10. }
  { rewrite L5SAR.r11. rewrite (KS1 11%nat) by inl. exact A11. }
  { rewrite L5SAR.r12. rewrite (KS1 12%nat) by inl. exact A12. }
  { exact AOI. }
  { exact I8. }
  { exact IA1. }
  { exact BASE1. }
  { exact SOWN. }
  { exists qt, ct. split; [exact TIN| unfold PM.CHUNK; split; lia]. }
  { unfold PM.CHUNK. exact ACH1. }
  { cbn [PM.sm_g PM.sm_eg]. unfold PM.CHUNK. exact APART. }
  intros fx2 R2 M2 model2 LK2 Aw2 c RP2 A10c Hc IA2 D2 COPYB HP2 MRT2 INC2 INCA2 AM2 HH2.
  rewrite L5K.rl10 in A10c. change (PMSPA.pm_scr 2) with 16384 in HP2. cbn [PM.sm_g PM.sm_eg PM.sm_st] in IA2. unfold PM.CHUNK in Hc. cbn [PM.sm_g PM.sm_eg PM.sm_st] in Hc.
  pose proof (PMBSKJ.iss_size_ltA M ois str _ IA) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  assert (Hcm := Hc). assert (C0 : 0 <= c <= 16384) by (rewrite Hc; destruct (Z.min_spec 16384 (eg - g)) as [[X1 X2]|[X1 X2]]; rewrite X2; split; lia).
  set (WX := [(ois + 40, 8); (p, 16384)]) in *.
  assert (EK12 : L5SAR.ek L ar LB FF sp 18432 WX M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 18432 (sp - 48) 16384 _ _ M1 M2 HP2); [lia|lia|]. intros a _ O. exact O. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 18432 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 18432 (sp - 48) 16384 _ M1 M2 HP2); lia).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TOP2 & _).
  assert (ASTK2 : L5CA.astk ar M2 sp 18432).
  { apply (PMKB.astk_after_ahpres L ar LB FF M1 M2 sp 18432 (sp - 48) 16384 _ ASTK1 HP2); lia. }
  pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof FOK as ((rs & Hfb) & F1024).
  pose proof (PMBSKJ.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qc 16384 HH QIN) as QIMG.
  pose proof (PMBSKJ.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ qt ct HH TIN) as TIMG.
  destruct (WB _ QIN) as ((_ & _ & _ & _ & _ & QAPP) & _). cbn [fst snd] in QAPP. unfold app_mem in QAPP.
  assert (OUTW : forall a, 65536 <= a < 6930432 -> L5.outside WX a).
  { intros a Ha r0 Hr. unfold WX in Hr. unfold L5.in_rng. unfold ois, PMSPA.o_is in *. cbn [pa_off_is PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  assert (BASE2 : PMSTA.base_okA RSEGS PeCLayoutB.CADDR_B M2) by (apply (PMBSKJ.base_keep L ar C LY LB FF sp 18432 _ M1 M2 EK12 OUTW BASE1)).
  assert (KF2 : forall a, sp - 48 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. destruct HP2 as (E & _). apply E. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar LB FF (sp - 48) 16384 a); [lia| lia].
    - intros r0 Hr. unfold WX in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold PM.CHUNK; lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2s & _).
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  assert (TS2 : forall k v, 8 <= k <= 48 -> L5.u64_at RSEGS M1 (sp - k) v -> L5.u64_at RSEGS MV2 (sp - k) v).
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis _ M2 (sp - k) v (VIS2s (sp - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply KF2; lia| lia| lia| exact X]. }
  assert (EK02 : L5SAR.ek L ar LB FF sp 18432 WX M M2).
  { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []| exact EK12]. }
  assert (DK02 : L5SAR.dk L ar LB FF sp 18432 M M2) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]).
  assert (WSX : PMKB.wapp WX).
  { unfold WX.
    apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|].
    apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]| apply PMKB.wapp_nil]. }
  assert (AOP : PMSPA.aobjA FF (PMSPA.o_p PeCLayoutB.CADDR_B fb) 384).
  { apply (PMBSKJ.aobj_fb FF fb); [exact FOK| |]; unfold PMSPA.o_p; cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]; lia. }
  assert (OP8 : (PMSPA.o_p PeCLayoutB.CADDR_B fb) mod 8 = 0).
  { unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite F1024, Z.add_0_r in Dm.
    rewrite Dm. replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by lia. apply Z_mod_mult. }
  assert (VIN : In (vb, 32 * 2 ^ vk) LB) by (apply BOWN; unfold PM.parser_own, PM.src_own, PM.vec_own; cbn; right; left; reflexivity).
  assert (OUTP : forall i, PMSPA.o_p PeCLayoutB.CADDR_B fb <= i < PMSPA.o_p PeCLayoutB.CADDR_B fb + 384 -> L5.outside WX i).
  { intros i Hi r0 Hr. unfold WX in Hr. unfold L5.in_rng. unfold ois, PMSPA.o_is, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
    destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct _ 384 HH TIN AOP) as [Z1|Z1];
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; unfold PMSPA.o_p in Z1; cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in Z1; lia. }
  assert (OUTB : forall q m, In (q, m) LB -> q <> qt -> forall i, q <= i < q + m -> L5.outside WX i).
  { intros q m Hq NE i Hi r0 Hr. unfold WX in Hr. unfold L5.in_rng.
    destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q m _ 272 HH Hq AOI) as [Z1|Z1];
    destruct (PMBSKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q m qt ct HH Hq TIN NE) as [Z2|Z2];
    destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  assert (ND : NoDup (map fst LB)) by exact (PMBSKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (VNE : vb <> qt).
  { intros E. subst vb. unfold LB, PM.parser_own, PM.src_own, PM.vec_own, PM.vs_own in ND. cbn in ND. inversion ND as [|x l NI ND1]. inversion ND1 as [|y l' NI' _].
    apply NI'. apply PMBSKJ.elem_of_InA. left. reflexivity. }
  assert (PA2 : PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M2 (PMSPA.o_p PeCLayoutB.CADDR_B fb) ois (PM.PST mo dn dp (PM.SRC qc de rem) (PM.VLong ct nt qt) tg vb vk stk)).
  { apply (parser_tbw_keepA M M2 _ _ _ PA); cbn [PM.p_src PM.sr_qc PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
    - unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
    - unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
    - apply (PMKB.agA_obj L ar LB FF sp 18432 _ M M2 EK02 WSX FRB _ 384 AOP OUTP).
    - lia. - lia.
    - apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M2 qc 16384 EK02 WSX QIN); lia.
    - apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M2 _ 384 DK02); [intros i Hi; apply (L5SAR.obj_client L ar LB FF sp 18432 _ 384 i (PMKB.aobj_of_aobjA FF _ 384 AOP OP8) Hi)| | |exact PDEF].
      + unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      + unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
    - apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M2 qc 16384 DK02); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qc 16384 i QIN Hi)| lia| lia| exact DCH].
    - destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
    - destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
    - apply (PMKB.agA_blk L ar LB FF sp 18432 _ M M2 EK02 WSX BRB vb _ VIN). apply (OUTB _ _ VIN VNE).
    - intros c1 n1 q1 E. injection E as <- <- <-.
      destruct (BRB _ TIN) as (X1 & X2). cbn [fst snd] in *.
      split; [apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M2 qt ct EK02 WSX TIN); lia|].
      apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M2 qt ct DK02); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qt ct i TIN Hi)| lia| lia| exact DBt]. }
  pose proof (PMBSKJ.src_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb ois _ sp 18432 HH2 FOK PA2 ASTK2)
    as ((P1 & P8 & PBIG) & PZ & PW & PCE & PAV & _ & _).
  pose proof (PMBSKJ.iss_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 fb str _ sp 18432 HH2 FOK IA2 ASTK2)
    as ((J1 & J8 & JBIG) & JZ & JW & JCE & JAV & _ & _).
  fold os ois in P1, P8, PBIG, PZ, PW, PCE, PAV, J1, J8, JBIG, JZ, JW, JCE, JAV.
  pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PSRC2 & _).
  destruct PSRC2 as (S240b & S248b & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _). cbn [PM.p_src] in S240b, S248b. fold os ois in S240b, S248b.
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 HH2 BASE2) as (W0 & W1' & W2').
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok LB FF LK2 cr Aw2 M2 model2 sp 18432 48 HH2 ASTK2 ltac:(lia)) as (_ & _ & W3').
  pose proof (PMBSKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x13b520 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as WT1.
  pose proof (PMBSKJ.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK2 cr Aw2 M2 model2 0x13b488 1 HH2 ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as WT2.
  cbn in WT1, WT2. fold MV2 in W0, W1', W2', W3', WT1, WT2.
  pose proof IA2 as (K0i & _ & _ & K16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB2 & _ & _).
  destruct IOSB2 as (K0' & K32 & K36 & K40 & _ & _ & _ & _ & _).
  cbn [pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
  replace (ois + 120 + 32) with (ois + 152) in K32 by lia. replace (ois + 120 + 36) with (ois + 156) in K36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in K40 by lia.
  set (WALL := [(ois + 40, 8); (p, 16384); (ois + 152, 4)]).
  assert (OUTP3 : forall i, PMSPA.o_p PeCLayoutB.CADDR_B fb <= i < PMSPA.o_p PeCLayoutB.CADDR_B fb + 384 -> L5.outside WALL i).
  { intros i Hi r0 Hr. unfold WALL in Hr. unfold L5.in_rng. unfold ois, PMSPA.o_is, PMSPA.o_p in *. cbn [pa_off_is pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in *.
    destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qt ct _ 384 HH TIN AOP) as [Z1|Z1];
    destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; unfold PMSPA.o_p in Z1; cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in Z1; lia. }
  assert (OUTB3 : forall q m, In (q, m) LB -> q <> qt -> forall i, q <= i < q + m -> L5.outside WALL i).
  { intros q m Hq NE i Hi r0 Hr. unfold WALL in Hr. unfold L5.in_rng.
    destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q m _ 272 HH Hq AOI) as [Z1|Z1];
    destruct (PMBSKJ.blk_apart L ar C HI HIok LB FF LK cr Aw M _ q m qt ct HH Hq TIN NE) as [Z2|Z2];
    destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia. }
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20. change (bv_modulus 64) with (2 ^ 64) in *.
  set (VS := fun j => match j with 2%nat => sp | 35%nat => c | 36%nat => os | 37%nat => ois | 40%nat => bv_unsigned (getr R (reg 1))
                                | 41%nat => bv_unsigned (getr R (reg 8)) | 42%nat => bv_unsigned (getr R (reg 9)) | 43%nat => bv_unsigned (getr R (reg 18))
                                | 44%nat => bv_unsigned (getr R (reg 19)) | 45%nat => bv_unsigned (getr R (reg 20)) | _ => 0 end).
  assert (RG2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact T2).
  assert (RG8 : getr R2 (reg 8) = Z_to_bv 64 (os + 240)) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact T8).
  assert (RG9 : getr R2 (reg 9) = Z_to_bv 64 16384) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact T9).
  assert (RG19 : getr R2 (reg 19) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 19 RP2) by inl; exact T19).
  assert (RG20 : getr R2 (reg 20) = Z_to_bv 64 ((os + 240) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R1 R2 20 RP2) by inl; exact T20).
  destruct (Z.eq_dec c 16384) as [CEQ|CNE].
  {
    assert (HcmX : 16384 = Z.min 16384 (eg - g)) by (rewrite <- Hc; symmetry; exact CEQ). clear Hc Hcm. subst c.

    pose proof (PMBFBP.afbB1_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
        | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
        | |- PMBFBP.aligned _ _ => unfold PMBFBP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb9a40 R3 0xb9bcc M3v (fun a => sp - 48 <= a < sp - 48 + 48) K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| exact N]. }
    { intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 18432 [] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 18432 [] M2 M3 (fun a => sp - 48 <= a < sp - 48 + 48) FR3). intros a Ha CL O X. destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 18432 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia]. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMBSKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb9bcc r W_b9b7c HH3 AM3 F_b9b7c eq_refl D_b9b7c Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    assert (EK03 : L5SAR.ek L ar LB FF sp 18432 WALL M M3).
    { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M2 M3).
      - apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []|].
        apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M1 M2 EK12). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]| exact X].
      - apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M2 M3 EK23). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr| exact X]. }
    assert (DK03 : L5SAR.dk L ar LB FF sp 18432 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
    assert (WSALL : PMKB.wapp WALL).
    { unfold WALL. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|]. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]|]. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKB.wapp_nil]. }

    set (data := PM.vs_data (ois + 80) str) in E1, E2, CBS.
    set (sl := UbjRef.slice pl (g - data) 16384).
    pose proof (PECF.slice_length_le pl (g - data) 16384 ltac:(clear; lia)) as SL. fold sl in SL.
    assert (GW : (ois + 81 <= g /\ eg <= ois + 104 /\ ois + 272 <= ahl_ceil ar /\ 0 <= ois) \/ (4096 <= g /\ eg <= ahl_ceil ar)).
    { destruct (PMBSKJ.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c0 & n0 & p0 & Hs & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in Y1, Y2.
      - left. destruct AOI as (f0 & Hf0 & F01 & F02). destruct (WF f0 Hf0) as (Yw1 & Yw2 & _).
        unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Yw1, Yw2. clear - Y1 Y2 F01 F02 Yw1 Yw2 FSAPP FSCEIL. lia.
      - right. assert (PIN : In (p0, c0) LB) by (apply SOWN; rewrite Hs; left; reflexivity).
        destruct (WB _ PIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. clear - Y1 Y2 B0 B4. lia. }
    assert (BYg : L5.bytes_at RSEGS M g sl).
    { apply (PECSD.payload_at_gptr RSEGS M pl data g 16384 CBS); clear - E1 E2 CSZ HcmX; Lia.lia. }
    assert (BYg1 : L5.bytes_at RSEGS M1 g sl).
    { apply (L5C.bytes_at_agree RSEGS M M1 g sl); [| clear - GW SLO; lia | clear - GW SL HcmX E1 E2 SLO SHI SPT; Lia.lia | exact BYg].
      intros i Hi. apply FR1; [clear - Hi GW SL HcmX E1 E2 SLO SHI SPT; Lia.lia| intros X; clear - X Hi GW SL HcmX E1 E2 SLO; Lia.lia]. }
    pose proof (COPYB sl SL BYg1) as BY2.
    assert (BY3 : L5.bytes_at RSEGS M3 p sl).
    { apply (L5C.bytes_at_agree RSEGS M2 M3 p sl); [| clear - T0 Dq1; lia | clear - T4 Dq2 SL SLO SHI SPT ; lia | exact BY2].
      intros i Hi. apply FR3; [clear - Hi SL T0 T4 Dq1 Dq2 SLO SHI SPT ; lia|].
      clear - TAO Hi SL T0 T4 Dq1 Dq2 SLO SHI SPT ; intros X; lia. }
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc de rem) (PM.STRM (g + 16384) eg 0)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (parser_tbw_keepA M M3 _ _ _ PA); cbn [PM.p_src PM.sr_qc PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
      * unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * apply (PMKB.agA_obj L ar LB FF sp 18432 _ M M3 EK03 WSALL FRB _ 384 AOP). intros i Hi. apply OUTP3; exact Hi.
      * lia. * lia.
      * apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M3 qc 16384 EK03 WSALL QIN); lia.
      * apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 _ 384 DK03); [intros i Hi; apply (L5SAR.obj_client L ar LB FF sp 18432 _ 384 i (PMKB.aobj_of_aobjA FF _ 384 AOP OP8) Hi)| | |exact PDEF].
        -- unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
        -- unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 qc 16384 DK03); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qc 16384 i QIN Hi)| lia| lia| exact DCH].
      * destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      * destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      * apply (PMKB.agA_blk L ar LB FF sp 18432 _ M M3 EK03 WSALL BRB vb _ VIN). apply (OUTB3 _ _ VIN VNE).
      * intros c1 n1 q1 E. injection E as <- <- <-.
        destruct (BRB _ TIN) as (X1 & X2). cbn [fst snd] in *.
        split; [apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M3 qt ct EK03 WSALL TIN); lia|].
        apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 qt ct DK03); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qt ct i TIN Hi)| lia| lia| exact DBt].
    + apply (PMKB.iss_keepA RSEGS PeCLayoutB.CADDR_B L ar LB FF sp 18432 [] M2 M3 EK23 PMKB.wapp_nil FRB BRB _ _ _ AOI); [exact SOWN| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA2].
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    + unfold ctbfill_res. split; [reflexivity|]. exists p, 16384. cbn [PM.sm_g PM.sm_st PM.sm_eg].
      split; [rewrite L5SAR.r11; exact A11|]. split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|].
      split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros X; exfalso; clear - X; unfold PM.CHUNK in X; lia|]. split; [intros X; discriminate X|].
      split; [apply (L5C.defined_agree M2 M3 p 16384); [intros i Hi; rewrite FR3; [reflexivity| lia|]; intros X; lia| exact D2]|].
      split; [replace (blen pl - (eg - g)) with (g - data) by (clear - E1 CSZ; lia); exact BY3| intros X; discriminate X].
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M3).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ WALL M M3 EK03). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr as [<-|[<-|[<-|[]]]]; unfold PMSPA.W_src, PMSPA.W_srcf; cbn [app PM.sr_qc]; [right; left; reflexivity| right; right; right; right; left; reflexivity| right; right; left; reflexivity]| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3); [apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]|].
        apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
  assert (CLT : c < 16384) by lia.
  {
    pose proof (PMBFBP.afbB2_conc fx2 R2 MV2 VS) as P. unfold VS in P. cbn beta iota in P.
    L5SAR.feed P ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (sp - _) _ => apply TS2; [lia| apply TS1; [lia| assumption]]
        | |- L5.u64_at _ _ (os + _) _ => unfold MV2; vis64 PAV
        | |- L5.u64_at _ _ (ois + _) _ => unfold MV2; vis64 JAV
        | |- L5.u64_at _ _ ois _ => unfold MV2; apply (proj2 (L5A.u64_at_vis _ M2 ois _ ltac:(apply JAV; lia) ltac:(lia) ltac:(lia))); assumption
        | |- L5.u32_at _ _ (ois + _) _ => unfold MV2; vis32 JAV
        | |- PMBFBP.aligned _ _ => unfold PMBFBP.aligned; lia
        | |- _ => lia end]).
    destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & PP). pdestr PP.
    apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xb9a40 R3 0xb9bcc M3v (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (ois + 152 <= a < ois + 152 + 4)) K HH2 AM2 MS3 MG3).
    { intros a Ha N. apply FRZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
    { intros a Ha Wa. split; [|intros X; lia]. destruct Wa as [Wa|Wa]; [unfold aclientw, aclient_g; right; left; split; [lia| intros X; lia]|]. unfold aclientw, aclient_g. do 3 right. left. destruct AOI as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. split; [lia| intros X; lia]. }
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
    assert (EK23 : L5SAR.ek L ar LB FF sp 18432 [(ois + 152, 4)] M2 M3).
    { apply (L5SAR.ek_piece L ar LB FF sp 18432 [(ois + 152, 4)] M2 M3 (fun a => (sp - 48 <= a < sp - 48 + 48) \/ (ois + 152 <= a < ois + 152 + 4)) FR3). intros a Ha CL O X. destruct X as [X|X]; [destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 _ sp 18432 a HH2 SPT CL) as [(Y1 & Y2)|Y]; [apply Y2; lia| lia]|]. apply (O (ois + 152, 4)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    assert (Rr : getr R3 (reg 1) = Z_to_bv 64 r) by (match goal with H : getr R3 (reg 1) = _ |- _ => rewrite H end; rewrite Z_to_bv_bv_unsigned; exact Rra).
    apply (PMBSKJ.ret_exit L ar C HI LY HIok fx3 R3 M3 model3 K LB FF LK2 cr Aw2 0xb9bcc r W_b9b7c HH3 AM3 F_b9b7c eq_refl D_b9b7c Rr ltac:(lia) Hr2).
    intros model4 MRT4 AM4 HH4.
    assert (EK03 : L5SAR.ek L ar LB FF sp 18432 WALL M M3).
    { apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M2 M3).
      - apply (L5SAR.ek_trans L ar LB FF sp 18432 _ M M1 M2); [apply (L5SAR.ek_W L ar LB FF sp 18432 _ [] M M1 EK01); intros a _ r0 []|].
        apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M1 M2 EK12). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr as [<-|[<-|[]]]; [left; reflexivity| right; left; reflexivity]| exact X].
      - apply (L5SAR.ek_W L ar LB FF sp 18432 _ _ M2 M3 EK23). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr as [<-|[]]; right; right; left; reflexivity| exact X]. }
    assert (DK03 : L5SAR.dk L ar LB FF sp 18432 M M3) by (apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3 DK02); apply L5SAR.dk_grows; exact MGM3).
    assert (WSALL : PMKB.wapp WALL).
    { unfold WALL. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]|]. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; destruct TAPP as (_ & [X|X] & _); [left; lia| right; lia]|]. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKB.wapp_nil]. }

    set (data := PM.vs_data (ois + 80) str) in E1, E2, CBS.
    set (sl := UbjRef.slice pl (g - data) c).
    pose proof (PECF.slice_length_le pl (g - data) c ltac:(clear - C0; lia)) as SL. fold sl in SL.
    assert (GW : (ois + 81 <= g /\ eg <= ois + 104 /\ ois + 272 <= ahl_ceil ar /\ 0 <= ois) \/ (4096 <= g /\ eg <= ahl_ceil ar)).
    { destruct (PMBSKJ.iss_unread_whereA M ois str _ IA) as [(Y1 & Y2)|(c0 & n0 & p0 & Hs & Y1 & Y2)]; cbn [PM.sm_g PM.sm_eg] in Y1, Y2.
      - left. destruct AOI as (f0 & Hf0 & F01 & F02). destruct (WF f0 Hf0) as (Yw1 & Yw2 & _).
        unfold app_mem, FS_BYTES in FSAPP, FSCEIL, Yw1, Yw2. clear - Y1 Y2 F01 F02 Yw1 Yw2 FSAPP FSCEIL. lia.
      - right. assert (PIN : In (p0, c0) LB) by (apply SOWN; rewrite Hs; left; reflexivity).
        destruct (WB _ PIN) as ((B0 & _ & _ & _ & B4 & _) & _). cbn [fst snd] in B0, B4. clear - Y1 Y2 B0 B4. lia. }
    assert (BYg : L5.bytes_at RSEGS M g sl).
    { apply (PECSD.payload_at_gptr RSEGS M pl data g c CBS); clear - E1 E2 CSZ Hcm CLT C0; Lia.lia. }
    assert (BYg1 : L5.bytes_at RSEGS M1 g sl).
    { apply (L5C.bytes_at_agree RSEGS M M1 g sl); [| clear - GW SLO; lia | clear - GW SL Hcm CLT C0 E1 E2 SLO SHI SPT; Lia.lia | exact BYg].
      intros i Hi. apply FR1; [clear - Hi GW SL Hcm CLT C0 E1 E2 SLO SHI SPT; Lia.lia| intros X; clear - X Hi GW SL Hcm CLT C0 E1 E2 SLO; Lia.lia]. }
    pose proof (COPYB sl SL BYg1) as BY2.
    assert (BY3 : L5.bytes_at RSEGS M3 p sl).
    { apply (L5C.bytes_at_agree RSEGS M2 M3 p sl); [| clear - T0 Dq1; lia | clear - T4 Dq2 SL SLO SHI SPT C0; lia | exact BY2].
      intros i Hi. apply FR3; [clear - Hi SL T0 T4 Dq1 Dq2 SLO SHI SPT C0; lia|].
      clear - TAO Hi SL T0 T4 Dq1 Dq2 SLO SHI SPT C0; intros X; lia. }
    apply (KONT fx3 R3 M3 model4 LK2 Aw2 (PM.SRC qc de rem) (PM.STRM (g + c) eg 2)).
    + apply L5SAR.preserved_by_index. intros k Hk. unfold L5SAR.cs_all in Hk.
      repeat (destruct Hk as [<-|Hk];
        [ first [ match goal with H : getr R3 (reg ?x) = Z_to_bv 64 (bv_unsigned (getr R (reg ?x))) |- getr R3 (reg ?x) = _ => rewrite H, Z_to_bv_bv_unsigned; reflexivity end
                | match goal with H : getr R3 (reg 2) = Z_to_bv 64 sp |- getr R3 (reg 2) = _ => rewrite H; exact (eq_sym Rsp) end
                | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; rewrite (KS1 _) by inl; reflexivity ] |]).
      destruct Hk.
    + apply (parser_tbw_keepA M M3 _ _ _ PA); cbn [PM.p_src PM.sr_qc PM.p_b PM.p_k PM.p_tb]; unfold PM.CHUNK.
      * unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * apply (PMKB.agA_obj L ar LB FF sp 18432 _ M M3 EK03 WSALL FRB _ 384 AOP). intros i Hi. apply OUTP3; exact Hi.
      * lia. * lia.
      * apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M3 qc 16384 EK03 WSALL QIN); lia.
      * apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 _ 384 DK03); [intros i Hi; apply (L5SAR.obj_client L ar LB FF sp 18432 _ 384 i (PMKB.aobj_of_aobjA FF _ 384 AOP OP8) Hi)| | |exact PDEF].
        -- unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
        -- unfold PMSPA.o_p. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B]. unfold os, PMSPA.o_src, PMSPA.o_p in O1. cbn [pa_off_p PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B] in O1. lia.
      * apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 qc 16384 DK03); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qc 16384 i QIN Hi)| lia| lia| exact DCH].
      * destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      * destruct (BRB _ VIN) as (X1 & X2). cbn [fst snd] in *. lia.
      * apply (PMKB.agA_blk L ar LB FF sp 18432 _ M M3 EK03 WSALL BRB vb _ VIN). apply (OUTB3 _ _ VIN VNE).
      * intros c1 n1 q1 E. injection E as <- <- <-.
        destruct (BRB _ TIN) as (X1 & X2). cbn [fst snd] in *.
        split; [apply (PMBSKJ.agsh_blk L ar LB FF sp 18432 _ M M3 qt ct EK03 WSALL TIN); lia|].
        apply (PMBSKJ.defined_dk L ar LB FF sp 18432 M M3 qt ct DK03); [intros i Hi; apply (L5SAR.block_client L ar LB FF sp 18432 qt ct i TIN Hi)| lia| lia| exact DBt].
    + assert (TJ3 : forall a v, ois <= a -> a + 4 <= ois + 272 -> L5.u32_at RSEGS M3v a v -> L5.u32_at RSEGS M3 a v).
      { intros a v Ha Hb X. rewrite <- VIS3 in X. apply (proj1 (L5A.u32_at_vis _ M3 a v ltac:(rewrite HID3 || idtac; apply JAV; lia) ltac:(lia) ltac:(lia))). exact X. }
      assert (WS23 : PMKB.wapp [(ois + 152, 4)]).
      { apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct IBIG as [X|X]; [right; lia| left; lia]| apply PMKB.wapp_nil]. }
      apply (PMBSKJ.iss_st_updA M2 M3 ois str (g + c) eg 0 2 IA2); [lia| lia| | | | exact MGM3| | | right; reflexivity].
      -- apply (PMKB.agA_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB ois 152 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
      -- apply (PMKB.agA_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB (ois + 156) 116 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
      -- apply (PMKB.agsh_obj L ar LB FF sp 18432 _ M2 M3 EK23 WS23 FRB (ois + 152) 4 ltac:(destruct AOI as (f & Hf & X1 & X2); exists f; split; [exact Hf| lia])).
      -- intros c0 n0 p0 E. subst str.
         assert (SIN : In (p0, c0) LB) by (apply SOWN; cbn; left; reflexivity).
         apply (PMKB.agA_blk L ar LB FF sp 18432 _ M2 M3 EK23 WS23 BRB p0 c0 SIN).
         intros i Hi r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
         destruct (PMBSKJ.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ p0 c0 _ 272 HH SIN AOI) as [Z1|Z1]; lia.
      -- apply TJ3; [lia|lia| assumption].
    + unfold PMSPA.src_step, PM.unread. cbn. lia.
    + unfold ctbfill_res. split; [reflexivity|]. exists p, c. cbn [PM.sm_g PM.sm_st PM.sm_eg].
      split; [rewrite L5SAR.r11; exact A11|]. split; [rewrite L5K.rl10; match goal with H : getr R3 (reg 10) = _ |- _ => exact H | _ => rewrite (KS3 10%nat) by inl; exact A10c end|].
      split; [unfold PM.CHUNK; lia|]. split; [lia|]. split; [intros _; split; [clear - Hcm CLT; unfold PM.CHUNK in *; Lia.lia| reflexivity]|]. split; [intros X; discriminate X|].
      split; [apply (L5C.defined_agree M2 M3 p c); [intros i Hi; rewrite FR3; [reflexivity| lia|]; intros [X|X]; [clear - X Hi Dq2 T4 SLO C0; lia| clear - X Hi Dq1 Dq2 TAO C0; lia]| exact D2]|].
      split; [replace (blen pl - (eg - g)) with (g - data) by (clear - E1 CSZ; lia); exact BY3| intros _; clear - Hcm CLT; unfold PM.CHUNK in *; Lia.lia].
    + apply (L5SAR.ahpres_of L ar LB FF sp 18432 _ M M3).
      * apply (L5SAR.ek_W L ar LB FF sp 18432 _ WALL M M3 EK03). intros a O r0 Hr X. apply (O r0); [unfold WALL; destruct Hr as [<-|[<-|[<-|[]]]]; unfold PMSPA.W_src, PMSPA.W_srcf; cbn [app PM.sr_qc]; [right; left; reflexivity| right; right; right; right; left; reflexivity| right; right; left; reflexivity]| exact X].
      * pose proof (L5SAR.astk_grows ar M2 M3 sp 18432 ASTK2 MGM3) as (_ & _ & _ & _ & DS3 & _). exact DS3.
      * apply (L5SAR.dk_trans L ar LB FF sp 18432 M M2 M3); [apply (L5SAR.dk_trans L ar LB FF sp 18432 M M1 M2); [apply L5SAR.dk_grows; exact MGM1| exact DK12]|].
        apply L5SAR.dk_grows. exact MGM3.
    + eapply L5LZ.model_rt_trans; [exact MRT1|]. eapply L5LZ.model_rt_trans; [exact MRT2|]. eapply L5LZ.model_rt_trans; [exact MRT3| exact MRT4].
    + exact INC2.
    + exact INCA2.
    + exact AM4.
    + exact HH4. }
Qed.

End WithHeap.
End PECFILLTBB.
