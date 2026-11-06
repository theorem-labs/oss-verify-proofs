(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PmStep PeStepA PeStepA2 PmCertKitG PeAIss1 PeAEmbKitJ PeASrcKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCEPushSpecsA PeAEPushP1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b0f7c_b0f80.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.asan Require Import L5CoreBS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PEAEPF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma stack_zeros12 M sp : shadow_zero M (sp - 12288) 1536 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (1024 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 12288) / 8 + 2147450880 + (1024 + i)) by Lia.lia. exact X.
Qed.
Lemma zsh1 M p : byte_at M (S p) 0 -> L5KA.zeros_at M (p / 8 + 2147450880) 1.
Proof. intros X i Hi. replace i with 0 by Lia.lia. rewrite Z.add_0_r. unfold byte_at, S, SB in X. exact X. Qed.
Lemma shadow_low b c j : 0 <= b -> b + c <= 2 ^ 47 -> 0 <= j < c / 8 -> 2147450880 <= S b + j < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma vis_u8 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 1 -> 0 <= a -> a < 2 ^ 63 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u8_at_vis H M1 a v AV ltac:(Lia.lia) ltac:(Lia.lia)) X). Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma S_range x : 0 <= x < 2 ^ 47 -> 2147450880 <= S x < 2147450880 + 2 ^ 44.
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma S_add8 a j : S a + j = S (a + 8 * j).
Proof. unfold S. Lia.lia. Qed.
Lemma d24 x : (24 * x) / 8 = 3 * x.
Proof. Lia.lia. Qed.
Lemma d24b x : (24 * x + 24) / 8 = 3 * x + 3.
Proof. Lia.lia. Qed.
Lemma ecap_rng k : 0 < k <= 12 -> 1 <= PEC.ecap k <= 2048.
Proof.
  intros Hk. unfold PEC.ecap. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; Lia.lia).
  split; [pose proof (Z.pow_pos_nonneg 2 (k - 1) ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma zeros_of_bytes (M : word -> option byte) a n : (forall i, 0 <= i < n -> exists v, v = 0 mod 256 /\ byte_at M (a + i) v) -> L5KA.zeros_at M a n.
Proof. intros BY i Hi. destruct (BY i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv, Ev. reflexivity. Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Lemma ek_of_keep LB FF LK cr Aw M V sp (W : list L5.range) (M1 M2 : word -> option byte) :
  ri_inv HI LB FF LK cr Aw M V ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF sp 12288 a -> L5.outside W a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) ->
  L5SAR.ek L ar LB FF sp 12288 W M1 M2.
Proof. intros HH KE a (Ha & Hc & Ho). apply KE; [exact Ha| exact Hc| exact Ho]. Qed.

Theorem fast : forall (fx : FPState) R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd,
    ri_inv HI (PEC.enc_own (PEC.ENC b k stk d) ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 (ov + 24) -> PMSPA.aobjA FF ov 56 -> ov mod 8 = 0 ->
    PECA.enc_atA RSEGS EE L ar M ov fb (PEC.ENC b k stk d) -> Z.of_nat (length stk) < PEC.ecap k -> Z.of_nat (length stk) <= UbjRef.MAX_DEPTH ->
    PMSTA.base_okA RSEGS AD M ->
    getr R (reg 11) = Z_to_bv 64 pk -> pk mod 4 = 0 -> byte_at M (S pk) 0 -> PMAEK.argp (ar_sptop ar) FF sp (ov + 32) pk 4 -> (pk + 4 <= ov \/ ov + 56 <= pk) ->
    L5.u32_at RSEGS M pk kd -> 0 <= kd <= 3 ->
    (forall (fx' : FPState) R' M' model' LK' Aw', regs_preserved R R' -> PECA.enc_atA RSEGS EE L ar M' ov fb (PEC.ENC b k (stk ++ [EI kd 0 0]) d) ->
        PMSTA.base_okA RSEGS AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(ov + 24, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PEC.enc_own (PEC.ENC b k (stk ++ [EI kd 0 0]) d) ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb0de0 M model) K.
Proof.
  intros fx R M model K LBX FF LK Aw cr ov fb b k stk d sp r pk kd HH AM K0 ENT A10 AOV O8 EA LEN LEN1K BASE A11 P14 SP1 AG1 APK U1 RKD KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH. change UbjRef.MAX_DEPTH with 1024 in LEN1K.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  pose proof EA as (EV0 & EV8 & EV16 & EV24 & EV32 & EV40 & EV48 & EDEF & EACC & EK & ELEN & EDEP & EKB & EBLK & EITEMS).
  cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth] in EV24, EV32, EV40, EV48, EK, ELEN, EDEP, EKB, EBLK, EITEMS, LEN.
  change PEC.ESZ with 24 in EV32, EV40, ELEN, EBLK, EITEMS.
  assert (Kp : 0 < k).
  { destruct (Z.eq_dec k 0) as [Ek|Nk]; [| clear - EK Nk; Lia.lia]. exfalso. rewrite Ek in LEN. unfold PEC.ecap in LEN. cbn in LEN. clear - LEN. Lia.lia. }
  pose proof (ecap_rng k ltac:(clear - Kp EK; Lia.lia)) as HC.
  destruct (EBLK Kp) as (B8 & BDEF & BRNG & BACC & BANN).
  set (cap := PEC.ecap k) in *. set (len := Z.of_nat (length stk)) in *.
  set (LB := PEC.enc_own (PEC.ENC b k stk d) ++ LBX) in *.
  assert (ELB : LB = (b, 24 * cap) :: LBX).
  { subst LB cap. unfold PEC.enc_own. cbn [PEC.en_k PEC.en_b PEC.ESZ]. replace (k =? 0) with false by (symmetry; apply Z.eqb_neq; clear - Kp; Lia.lia). reflexivity. }
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, 24 * cap) LB) by (rewrite ELB; left; reflexivity).
  destruct (PMAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (24 * cap) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF ov 56 AOV O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model ov 56 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  destruct (PMAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 (ov + 32) pk 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
  pose proof (Pa5 b (24 * cap) BIN) as PaB.

  assert (VBLK : ov + 56 <= b \/ b + 24 * cap <= ov).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof BASE as (IC & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC.
  assert (X0 : L5.img_clear MV 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC).
  assert (X1 : L5.u64_at RSEGS MV 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X4 : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (stack_zeros12 M sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (X5 : L5KA.zeros_at MV (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model ov 56 HH AOV O8 ltac:(lia) ltac:(reflexivity) EACC). }
  assert (X6 : L5.u64_at RSEGS MV (ov + 24) b) by (apply (proj2 (L5A.u64_at_vis H M (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV24).
  assert (X7 : L5.u64_at RSEGS MV (ov + 32) (b + 24 * len)) by (apply (proj2 (L5A.u64_at_vis H M (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV32).
  assert (X8 : L5.u64_at RSEGS MV (ov + 40) (b + 24 * cap)) by (apply (proj2 (L5A.u64_at_vis H M (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact EV40).

  pose proof (PEAEPP1.aepF1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 36%nat => b | 37%nat => 24 * len | 38%nat => kd | 41%nat => b + 24 * cap | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAEPP1.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR8 & fR9 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR18 & fR19 & fR20 & fR21
                 & T112 & T104 & T56 & T48 & T40 & T32 & T24 & T16 & T8).
  set (W1 := fun a => sp - 112 <= a < sp - 112 + 112).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb0de0 R1 0x7c400 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 112 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).
  assert (EK1 : L5SAR.ek L ar LB FF sp 12288 [] M M1).
  { apply (ek_of_keep LB FF LK cr Aw M _ sp [] M M1 HH). intros a Ha Hc _.
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; (apply FR1; [exact Ha| unfold W1; lia]). }

  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD PeLayoutA.AADDR_A PeCLayoutA.CAADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (24 * cap) (24 * len) (24 * len + 24)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12. exact fR12. }
  { rewrite L5K.rl13, fR13. f_equal. lia. }
  { exact BIN. }
  { exact Bq4. }
  { lia. }
  { lia. }
  { apply (PMAEK.ann_agree M M1 b (24 * len) (24 * cap)); [| lia| lia| exact BANN| clear - HC; Lia.lia].
    intros j Hj. pose proof (shadow_low b (24 * cap) j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 112 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  pose proof AM2 as (Mh2 & _).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2416 <= a < sp) -> ~ in_shadow_of b (24 * cap) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 112) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PMAEK.in_shadow_range b (24 * cap) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (EK2 : L5SAR.ek L ar LB FF sp 12288 [(S b, 3 * cap)] M M2).
  { apply (ek_of_keep LB FF LK cr Aw M _ sp _ M M2 HH). intros a Ha Hc Ho.
    assert (NS : ~ in_shadow_of b (24 * cap) a).
    { intros X. apply (Ho (S b, 3 * cap)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. unfold in_shadow_of, S in X. unfold S. clear - X B8 HC.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT Hc) as [Z1|Z1]; (apply T20; [exact Ha| apply (L5SAR.aclient_narrow L ar LB FF sp 12288); [exact Hc| lia]| lia| exact NS]). }
  assert (BASE2 : PMSTA.base_okA RSEGS AD M2).
  { apply (PMASK.base_keep L ar C LY LB FF sp 12288 [(S b, 3 * cap)] M M2 EK2); [| exact BASE].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. pose proof (S_range b ltac:(lia)) as SR. lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 ov 56 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  pose proof BASE2 as (IC2 & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC2.
  assert (Y0 : L5.img_clear MV2 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC2).
  assert (Y1 : L5.u64_at RSEGS MV2 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1317368 2147450880 (VIMG2 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1317376 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1317376 1 (VIMG2 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
  { intros j Hj. pose proof (S_add8 (sp - 12288) j) as E.
    pose proof (S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia|].
    apply (PMAEK.sh_apart b (24 * cap) (sp - 12288 + 8 * j)); lia. }
  assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (stack_zeros12 M2 sp STKSH2 A16). exact Hi.
    assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }

  assert (ACCV2 : PMSPA.accA M2 ov 56).
  { apply (PMFA.accA_agree M M2 ov 56); [| exact EACC]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia|].
    - exact (PMAEK.frame_sh_client L ar FF ov 56 x LB 0 0 AOV Hx).
    - apply (PMAEK.sh_apart b (24 * cap) x); lia. }
  assert (Y5 : L5KA.zeros_at MV2 (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 ov 56 HH2 AOV O8 ltac:(lia) ltac:(reflexivity) ACCV2). }
  assert (TV : forall a, ov <= a < ov + 56 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 ov 56 a AOB); lia| lia|].
    intros X. pose proof (PMAEK.in_shadow_range b (24 * cap) a ltac:(lia) ltac:(lia) X). lia. }
  assert (Y6 : L5.writable RSEGS MV2 (ov + 24) 24).
  { apply (proj2 (L5A.writable_vis H2 M2 (ov + 24) 24 ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 ov 56); [exact ODEF2| lia| lia]. lia. lia. }
  assert (Y7 : L5.u64_at RSEGS MV2 (ov + 24) b).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV24]. }
  assert (Y8 : L5.u64_at RSEGS MV2 (ov + 32) (b + 24 * len)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV32]. }
  assert (Y9 : L5.u64_at RSEGS MV2 (ov + 40) (b + 24 * cap)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact EV40]. }

  destruct (PMAEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 (ov + 32) pk 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
  assert (TP : forall x, pk <= x < pk + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros x Hx. apply T20; [lia| replace x with (pk + (x - pk)) by lia; apply Pa6; lia| lia|].
    intros X. pose proof (PMAEK.in_shadow_range b (24 * cap) x ltac:(lia) ltac:(lia) X). lia. }
  assert (TPS : byte_at M2 (S pk) 0).
  { pose proof (S_range pk ltac:(lia)) as SRp. unfold byte_at in *. rewrite T20; [exact SP1| lia| | lia|].
    - exact (PMAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 (ov + 32) pk 4 HH ASTK ltac:(lia) AG1 ltac:(lia) LB 0 0).
    - apply (PMAEK.sh_apart b (24 * cap) pk); lia. }
  assert (Y10 : L5.u32_at RSEGS MV2 pk kd).
  { apply (proj2 (L5A.u32_at_vis H2 M2 pk kd AV1 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply TP; lia| lia| lia| exact U1]. }
  assert (Y12 : L5KA.zeros_at MV2 (pk / 8 + 2147450880) 1).
  { apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact TPS|].
    pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }

  assert (TS : forall a v0, sp - 112 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PMAEK.in_shadow_range b (24 * cap) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  pose proof (TS (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Z24.
  pose proof (TS (sp - 32) _ ltac:(lia) ltac:(lia) T32) as Z32.
  pose proof (TS (sp - 40) _ ltac:(lia) ltac:(lia) T40) as Z40.
  pose proof (TS (sp - 48) _ ltac:(lia) ltac:(lia) T48) as Z48.
  pose proof (TS (sp - 56) _ ltac:(lia) ltac:(lia) T56) as Z56.
  pose proof (TS (sp - 104) _ ltac:(lia) ltac:(lia) T104) as Z104.
  pose proof (TS (sp - 112) _ ltac:(lia) ltac:(lia) T112) as Z112.

  assert (BDEF2 : L5.defined M2 b (24 * cap)).
  { intros i Hi. rewrite KEEP2; [apply (L5.defined_grows M M1 _ _ MGM1 BDEF i Hi)| lia| |].
    - unfold aclient, aclient_g. left. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PMAEK.in_shadow_range b (24 * cap) (b + i) ltac:(lia) ltac:(lia) X). lia. }
  assert (Y14 : L5KA.zeros_at MV2 ((b + 24 * len) / 8 + 2147450880) 3).
  { rewrite (PMAEK.sh_idx b (24 * len)) by lia. rewrite d24. destruct ANN2 as (ZA & _). rewrite d24b in ZA. intros i Hi.
    assert (AV : L5A.avis H2 (S b + 3 * len + i) 1).
    { apply (VBSH2 b (24 * cap) _ 1 BIN). intros j Hj. replace (S b + 3 * len + i + j) with (S b + (3 * len + i + j)) by lia.
      apply PMAEK.sh_in; [lia| lia| lia|]. rewrite d24. lia. }
    unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
    - replace (S b + 3 * len + i) with (S b + (3 * len + i)) by lia. apply ZA. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15 : L5.writable RSEGS MV2 (b + 24 * len) 24).
  { apply (proj2 (L5A.writable_vis H2 M2 (b + 24 * len) 24 (VBLK2 b (24 * cap) (b + 24 * len) 24 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 b (24 * cap)); [exact BDEF2| lia| lia]| lia| lia]. }
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS2 by inl; exact fR2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 (ov + 32)) by (rewrite CS2 by inl; exact fR8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (ov + 24)) by (rewrite CS2 by inl; exact fR9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 pk) by (rewrite CS2 by inl; exact fR18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (b + 24 * len)) by (rewrite CS2 by inl; exact fR19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 ((ov + 32) / 8 + 2147450880)) by (rewrite CS2 by inl; exact fR20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact fR21).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21.

  pose proof (PEAEPP1.aepF2_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 36%nat => b | 37%nat => 24 * len | 38%nat => kd | 41%nat => b + 24 * cap
      | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18))
      | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAEPP1.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR10 & gR11 & gR12 & G0).
  set (W3 := fun a => b + 24 * len + 0 <= a < b + 24 * len + 0 + 24).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xaeb4c R3 0x78ab4 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W3 in Wa. split; [|lia]. unfold aclientw, aclient_g. left. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  pose proof AM3 as (Mh3 & MI3).
  assert (ASTK3 : L5CA.astk ar M3 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw2 M2 M2 M3 _ sp 12288 sp 0 HH2 ASTK2 (fun x X => X)).
    - intros a Ha Hs Hns. apply FR3; [exact Ha| unfold W3; lia].
    - intros a Ha. lia.
    - lia. - lia. - lia. }
  assert (EK3 : L5SAR.ek L ar LB FF sp 12288 [(b + 24 * len, 24)] M2 M3).
  { apply (ek_of_keep LB FF LK cr Aw2 M2 _ sp _ M2 M3 HH2). intros a Ha Hc Ho. apply FR3; [exact Ha|].
    intros X. apply (Ho (b + 24 * len, 24)); [left; reflexivity|]. unfold L5.in_rng, W3 in *. cbn [fst snd]. lia. }
  assert (BASE3 : PMSTA.base_okA RSEGS AD M3).
  { apply (PMASK.base_keep L ar C LY LB FF sp 12288 [(b + 24 * len, 24)] M2 M3 EK3); [| exact BASE2].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (BDEF3 : L5.defined M3 b (24 * cap)) by (apply (L5.defined_grows M2 M3 _ _ MGM3); exact BDEF2).

  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MST. unfold amemset_spec, amem_pre, amem_post in MST.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MST.
  assert (U96 : bv_unsigned (getr R3 2%bv) = sp - 96) by (rewrite L5K.rl2, gR2; apply L5.unsigned_lit; lia).
  destruct ANN2 as (ZA2 & PA2).
  assert (ZA3 : forall j, 0 <= j < 3 * len + 3 -> M3 (Z_to_bv 64 (S b + j)) = Some (Z_to_bv 8 0)).
  { intros j Hj. pose proof (shadow_low b (24 * cap) j ltac:(lia) ltac:(lia) ltac:(lia)) as SL. rewrite FR3; [| lia| unfold W3; lia].
    rewrite d24b in ZA2. apply ZA2. exact Hj. }
  apply (MST fx3 R3 M3 model3 LB FF LK cr Aw2 (b + 24 * len + 8) 0 16 K); clear MST.
  { split; [exact HH3|]. split; [exact Mh3|]. split; [exact MI3|].
    split; [rewrite L5K.rl10, gR10; f_equal; lia|]. split; [rewrite L5K.rl12; exact gR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    split; [rewrite L5K.rl1, gR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite U96. apply (L5SAR.astack_ok_of_astk L ar C LYa M3 M3 sp 12288 96 2560 ASTK3 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 96) with (sp + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split. { apply (L5CB.aacc_of_zero M3 b (3 * len + 3) (b + 24 * len + 8) 16 ZA3); lia. }
    split. { intros i Hi. rewrite U96. unfold aclientw, aclient_g. left. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; lia]. }
    split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS M3 (b + 24 * len + 8) 16); [apply (L5.defined_sub M3 b (24 * cap)); [exact BDEF3| lia| lia]| lia| lia| lia| lia]. }
    split; [exact K0|]. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. destruct Bq6 as [YW|YW]; lia. }
  { rewrite L5K.rl11. exact gR11. }
  intros R4 M4 model4 mR10 RP4 BYTES PRES4 SDEF4 RT4 MI4 HH4. rewrite U96 in PRES4, SDEF4. rewrite L5K.rl1, gR1.
  assert (Mh4 : m_halted model4 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT4); exact Mh3).
  assert (AM4 : L5CA.amodel_ok Aw2 model4) by (split; [exact Mh4| exact MI4]).
  assert (CS4 : forall k0, In k0 L5SAR.cs_all -> getr R4 (reg k0) = getr R3 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R3 R4 k0 RP4 Hk)).
  assert (ASTK4 : L5CA.astk ar M4 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw2 M3 M3 M4 _ sp _ (sp - 96) 2560 HH3 ASTK3 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES4. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF4.
    - lia. - lia. - lia. }
  assert (T42 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2656 <= a < sp) -> ~ (b + 24 * len <= a < b + 24 * len + 24) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]| lia]. apply FR3; [exact Ha| unfold W3; lia]. }
  assert (EK4 : L5SAR.ek L ar LB FF sp 12288 [(b + 24 * len, 24)] M3 M4).
  { apply (ek_of_keep LB FF LK cr Aw2 M3 _ sp _ M3 M4 HH3). intros a Ha Hc Ho. apply PRES4; [exact Ha| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 96) 2560 a Hc); intros x Hx; lia|].
    intros X. apply (Ho (b + 24 * len, 24)); [left; reflexivity|]. unfold L5.in_rng. cbn [fst snd]. lia. }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { apply (PMASK.base_keep L ar C LY LB FF sp 12288 [(b + 24 * len, 24)] M3 M4 EK4); [| exact BASE3].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }

  assert (ZW : L5KA.zeros_at M4 (b + 24 * len + 8) 16) by (apply zeros_of_bytes; exact BYTES).
  pose proof (L5SAR.u64_of_zeros_at M4 (b + 24 * len + 8) ltac:(intros i Hi; apply ZW; lia) ltac:(lia) ltac:(lia)) as ZW8.
  pose proof (L5SAR.u64_of_zeros_at M4 (b + 24 * len + 16) ltac:(intros i Hi; replace (b + 24 * len + 16 + i) with (b + 24 * len + 8 + (8 + i)) by lia; apply ZW; lia) ltac:(lia) ltac:(lia)) as ZW16.
  assert (BDEF4 : L5.defined M4 b (24 * cap)).
  { intros i Hi. destruct (L5SAR.rng_dec (b + i) (b + 24 * len + 8) (b + 24 * len + 24)) as [Di|Di].
    - replace (b + i) with (b + 24 * len + 8 + (b + i - (b + 24 * len + 8))) by lia. rewrite ZW by lia. discriminate.
    - rewrite PRES4; [apply BDEF3; exact Hi| lia| unfold aclient, aclient_g; left; exists (b, 24 * cap); split; [exact BIN| cbn [fst snd]; lia]| lia]. }

  assert (G0' : L5.u32_at RSEGS M4 (b + 24 * len) kd).
  { apply (PMF.u32_at_agree RSEGS M3 M4); [| lia| lia|].
    - intros i Hi. apply PRES4; [lia| unfold aclient, aclient_g; left; exists (b, 24 * cap); split; [exact BIN| cbn [fst snd]; lia]| lia].
    - apply (PMAIS1.vis_u32 _ _ _ _ _ VIS3); [apply (VBLK2 b (24 * cap) _ 4 BIN); lia| lia| lia| exact G0]. }

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  set (H4 := ahid Aw2 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M4 model4 ov 56 sp 12288 HH4 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & OVIS4 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as ST4. rewrite (L5A.aly_segs L C LYa) in ST4.
  pose proof (L5A.statics_facts L C M4 LYa ST4) as (GOT4 & CSB4 & CUAR4 & _).
  pose proof BASE4 as (IC4 & _). cbn [pa_rw_lo PeCLayoutA.CADDR_A] in IC4.
  assert (V0 : L5.img_clear MV4 65536 1286144) by (apply L5A.img_clear_mrestrict; exact IC4).
  assert (V1 : L5.u64_at RSEGS MV4 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H4 M4 1317368 2147450880 (VIMG4 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB4).
  assert (V2 : L5.u32_at RSEGS MV4 1317376 1) by (apply (proj2 (L5A.u32_at_vis H4 M4 1317376 1 (VIMG4 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR4).
  assert (V3 : L5.writable RSEGS MV4 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H4 M4 (sp - 4096) 4096 (VIS4 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M4 sp 12288); [exact ASTK4| lia| lia| lia]. }
  assert (STKSH4 : shadow_zero M4 (sp - 12288) 1536).
  { intros j Hj. pose proof (S_add8 (sp - 12288) j) as E. pose proof (S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T42; [| lia| apply (PMAEK.stack_sh_client L ar FF); lia| lia| lia]. rewrite <- E. apply STKSH2. exact Hj. }
  assert (V4 : L5KA.zeros_at MV4 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4). apply (stack_zeros12 M4 sp STKSH4 A16). exact Hi.
    assert (AV : L5A.avis H4 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH4 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (TV4 : forall a, ov <= a < ov + 56 -> M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite T42; [apply TV; exact Ha| lia| apply (L5SAR.obj_client L ar LB FF 0 0 ov 56 a AOB); lia| lia| lia]. }
  assert (ACCV4 : PMSPA.accA M4 ov 56).
  { apply (PMFA.accA_agree M2 M4 ov 56); [| exact ACCV2]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply T42; [lia| | lia| lia].
    exact (PMAEK.frame_sh_client L ar FF ov 56 x LB 0 0 AOV Hx). }
  assert (V5 : L5KA.zeros_at MV4 (ov / 8 + 2147450880) 7).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M4 model4 ov 56 HH4 AOV O8 ltac:(lia) ltac:(reflexivity) ACCV4). }
  assert (V6 : L5.writable RSEGS MV4 (ov + 24) 24).
  { apply (proj2 (L5A.writable_vis H4 M4 (ov + 24) 24 ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M4 ov 56); [exact ODEF4| lia| lia]. lia. lia. }
  assert (V7 : L5.u64_at RSEGS MV4 (ov + 24) b).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (ov + 24) b ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact EV24]. }
  assert (V8 : L5.u64_at RSEGS MV4 (ov + 32) (b + 24 * len)).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (ov + 32) _ ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact EV32]. }
  assert (V9 : L5.u64_at RSEGS MV4 (ov + 40) (b + 24 * cap)).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (ov + 40) _ ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact EV40]. }
  assert (TS4 : forall a v0, sp - 96 <= a -> a + 8 <= sp -> L5.u64_at RSEGS MV2 a v0 -> L5.u64_at RSEGS MV4 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H4 M4 a v0 (VIS4 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; rewrite PRES4; [apply FR3; [lia| unfold W3; lia]| lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
    exact (proj1 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) X). }
  pose proof (TS4 (sp - 8) _ ltac:(lia) ltac:(lia) Z8) as Q8.
  pose proof (TS4 (sp - 16) _ ltac:(lia) ltac:(lia) Z16) as Q16.
  pose proof (TS4 (sp - 24) _ ltac:(lia) ltac:(lia) Z24) as Q24.
  pose proof (TS4 (sp - 32) _ ltac:(lia) ltac:(lia) Z32) as Q32.
  pose proof (TS4 (sp - 40) _ ltac:(lia) ltac:(lia) Z40) as Q40.
  pose proof (TS4 (sp - 48) _ ltac:(lia) ltac:(lia) Z48) as Q48.
  pose proof (TS4 (sp - 56) _ ltac:(lia) ltac:(lia) Z56) as Q56.
  assert (J2' : getr R4 (reg 2) = Z_to_bv 64 (sp - 96)) by (rewrite CS4 by inl; exact gR2).
  assert (J8' : getr R4 (reg 8) = Z_to_bv 64 (ov + 32)) by (rewrite CS4 by inl; rewrite (KS3 8%nat) by inl; exact J8).
  assert (J9' : getr R4 (reg 9) = Z_to_bv 64 (ov + 24)) by (rewrite CS4 by inl; rewrite (KS3 9%nat) by inl; exact J9).
  assert (J18' : getr R4 (reg 18) = Z_to_bv 64 pk) by (rewrite CS4 by inl; rewrite (KS3 18%nat) by inl; exact J18).
  assert (J19' : getr R4 (reg 19) = Z_to_bv 64 (b + 24 * len)) by (rewrite CS4 by inl; rewrite (KS3 19%nat) by inl; exact J19).
  assert (J20' : getr R4 (reg 20) = Z_to_bv 64 ((ov + 32) / 8 + 2147450880)) by (rewrite CS4 by inl; rewrite (KS3 20%nat) by inl; exact J20).
  assert (J21' : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS4 by inl; rewrite (KS3 21%nat) by inl; exact J21).

  pose proof (PEAEPP1.aepF3_conc fx3 R4 MV4 (fun j => match j with 2%nat => sp | 33%nat => ov | 34%nat => pk | 36%nat => b | 37%nat => 24 * len | 38%nat => kd | 41%nat => b + 24 * cap
      | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18))
      | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEAEPP1.aligned; lia | lia]).
  destruct P as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & hR1 & hR2 & hR8 & hR9 & hR10 & hR18 & hR19 & hR20 & hR21 & G32).
  assert (R5ra : getr R5 (reg 1) = Z_to_bv 64 r) by (rewrite hR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx5 R5 M5v 0xb0fcc W_b0f7c r F_b0f7c eq_refl D_b0f7c R5ra ltac:(lia) Hr2) as MS6.
  set (W5 := fun a => ov + 32 <= a < ov + 32 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M4 model4 fx3 fx5 R4 0xb0e8c R5 r M5v W5 K HH4 AM4 ltac:(eapply msteps_trans; [exact MS5| exact MS6]) MG5).
  { intros a Ha N. apply FZ5; [exact Ha| intros X; apply N; exact X]. }
  { intros a Ha Wa. unfold W5 in Wa. split; [apply (L5SAR.obj_client L ar LB FF 0 0 ov 56 a AOB); lia| lia]. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.

  apply (KONT fx5 R5 M5 model5 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PEAEPP1.KS_aepF3 /\ In k' L5SAR.cs_all /\ In k' PEAEPP1.KS_aepF2 /\ In k' PEAEPP1.KS_aepF1)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; (split; [inl| split; [inl| split; inl]])).
      destruct Y as (Yk1 & Yk2 & Yk3 & Yk4). rewrite (KS5 k' Yk1), (CS4 k' Yk2), (KS3 k' Yk3), (CS2 k' Yk2), (KS1 k' Yk4). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]].
    + rewrite hR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite hR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite hR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite hR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite hR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite hR20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite hR21, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk.
  -
    assert (TW5 : forall a, 0 <= a < 2 ^ 64 -> ~ W5 a -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by exact FR5.
    assert (TV5 : forall a, ov <= a < ov + 56 -> ~ (ov + 32 <= a < ov + 40) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Na. rewrite TW5; [apply TV4; exact Ha| lia| unfold W5; lia]. }
    assert (TB : forall a, b <= a < b + 24 * len -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW5; [| lia| unfold W5; lia]. rewrite T42; [| lia| | lia| lia].
      - apply T20; [lia| | lia|].
        + unfold aclient, aclient_g. left. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; lia].
        + intros X. pose proof (PMAEK.in_shadow_range b (24 * cap) a ltac:(lia) ltac:(lia) X). lia.
      - unfold aclient, aclient_g. left. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; lia]. }
    assert (TSH : forall j, 0 <= j < (24 * cap) / 8 -> M5 (Z_to_bv 64 (S b + j)) = M2 (Z_to_bv 64 (S b + j))).
    { intros j Hj. pose proof (shadow_low b (24 * cap) j ltac:(lia) ltac:(lia) Hj) as SL. rewrite TW5; [| lia| unfold W5; intros XW; destruct OBIG as [YW|YW]; lia].
      apply T42; [lia| | lia| lia]. unfold aclient, aclient_g. do 6 right. exists (b, 24 * cap). split; [exact BIN| cbn [fst snd]; apply PMAEK.sh_in; lia]. }
    unfold PECA.enc_atA. cbn [PEC.en_b PEC.en_k PEC.en_stk PEC.en_depth]. change PEC.ESZ with 24.
    rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. fold len. fold cap.
    split. { apply (L5C.u64_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV0]. }
    split. { apply (L5C.u64_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV8]. }
    split. { apply (PMF.u32_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV16]. }
    split. { apply (L5C.u64_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV24]. }
    split. { replace (b + 24 * (len + 1)) with (b + 24 * len + 24) by lia.
             apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [eapply L5A.avis_sub; [exact OVIS4| lia| lia]| lia| lia| exact G32]. }
    split. { apply (L5C.u64_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV40]. }
    split. { apply (PMF.u32_at_agree RSEGS M M5); [intros i Hi; apply TV5; lia| lia| lia| exact EV48]. }
    split; [apply (L5.defined_grows M4 M5 _ _ MGM5); exact ODEF4|].
    split. { apply (PMFA.accA_agree M4 M5 ov 56); [| exact ACCV4]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply TW5; [lia| unfold W5; destruct OBIG as [YW|YW]; lia]. }
    split; [exact EK|]. split; [lia|]. split; [exact EDEP|]. split; [intros X; exfalso; clear - X Kp; Lia.lia|].
    assert (ZA5 : forall j, 0 <= j < 3 * len + 3 -> M5 (Z_to_bv 64 (S b + j)) = Some (Z_to_bv 8 0)).
    { intros j Hj. rewrite TSH by (rewrite d24; lia). apply ZA2. rewrite d24b. exact Hj. }
    split.
    { intros _. split; [exact B8|]. split; [apply (L5.defined_grows M4 M5 _ _ MGM5); exact BDEF4|]. split; [exact BRNG|].
      split. { unfold PMSPA.accA. apply (L5CB.aacc_of_zero M5 b (3 * len + 3) b (24 * (len + 1)) ZA5); lia. }
      apply (PMAEK.ann_agree M2 M5 b (24 * (len + 1)) (24 * cap)); [exact TSH| lia| lia| | clear - HC; Lia.lia].
      replace (24 * (len + 1)) with (24 * len + 24) by lia. split; [exact ZA2| exact PA2]. }
    intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hl].
    + rewrite app_nth1 by exact Hl. assert (Hil : Z.of_nat i + 1 <= len) by (unfold len; clear - Hl; Lia.lia).
      destruct (EITEMS i Hl) as (I1 & I2 & I3). unfold PEC.eitem_at.
      split; [apply (PMF.u32_at_agree RSEGS M M5); [intros x Hx; apply TB; lia| lia| lia| exact I1]|].
      split; [apply (L5C.u64_at_agree RSEGS M M5); [intros x Hx; apply TB; lia| lia| lia| exact I2]|].
      apply (L5C.u64_at_agree RSEGS M M5); [intros x Hx; apply TB; lia| lia| lia| exact I3].
    + assert (Ei : i = length stk) by (clear - Hi Hl; Lia.lia). subst i. rewrite app_nth2 by (clear; Lia.lia). rewrite Nat.sub_diag. cbn [nth]. fold len.
      assert (TSL : forall a, b + 24 * len <= a < b + 24 * len + 24 -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)) by (intros a Ha; apply TW5; [lia| unfold W5; lia]).
      unfold PEC.eitem_at. cbn [ei_kind ei_len ei_cnt].
      split; [apply (PMF.u32_at_agree RSEGS M4 M5); [intros x Hx; apply TSL; lia| lia| lia| exact G0']|].
      split; [apply (L5C.u64_at_agree RSEGS M4 M5); [intros x Hx; apply TSL; lia| lia| lia| exact ZW8]|].
      apply (L5C.u64_at_agree RSEGS M4 M5); [intros x Hx; apply TSL; lia| lia| lia| exact ZW16].
  -
    assert (EK5 : L5SAR.ek L ar LB FF sp 12288 [(ov + 32, 8)] M4 M5).
    { apply (ek_of_keep LB FF LK cr Aw2 M4 _ sp _ M4 M5 HH4). intros a Ha Hc Ho. apply FR5; [exact Ha|].
      intros X. apply (Ho (ov + 32, 8)); [left; reflexivity|]. unfold L5.in_rng, W5 in *. cbn [fst snd]. lia. }
    apply (PMASK.base_keep L ar C LY LB FF sp 12288 [(ov + 32, 8)] M4 M5 EK5); [| exact BASE4].
    intros a Ha. unfold L5.outside. intros rg [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia.
  -
    apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M5).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (rewrite ELB; apply (L5SAR.aclient_consb L ar LBX FF (b, 24 * cap) sp 12288 a Hc)).
      rewrite ELB in HH.
      assert (NB : ~ (b <= a < b + 24 * cap)) by (exact (PMAEK.own_notclient L ar C HI LY HIok b (24 * cap) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      assert (NS : ~ in_shadow_of b (24 * cap) a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok b (24 * cap) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
      rewrite <- ELB in HH.
      assert (NV : ~ (ov + 24 <= a < ov + 48)) by (intros X; apply (Ho (ov + 24, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]).
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1].
      * rewrite FR5; [| exact Ha| unfold W5; lia]. rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 96) 2560 a HcB); intros x Hx; lia| lia].
        rewrite FR3; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 112) 2304 a HcB); intros x Hx; lia| exact NS].
        apply FR1; [exact Ha| unfold W1; lia].
      * rewrite FR5; [| exact Ha| unfold W5; lia]. rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 96) 2560 a HcB); intros x Hx; lia| lia].
        rewrite FR3; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 112) 2304 a HcB); intros x Hx; lia| exact NS].
        apply FR1; [exact Ha| unfold W1; lia].
    + pose proof ASTK4 as (_ & _ & _ & _ & SD4 & _). apply (L5.defined_grows M4 M5 _ _ MGM5). exact SD4.
    + intros a Ha Hc HM. apply MGM5.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (rewrite ELB; apply (L5SAR.aclient_consb L ar LBX FF (b, 24 * cap) sp 12288 a Hc)).
      rewrite ELB in HH.
      assert (NB : ~ (b <= a < b + 24 * cap)) by (exact (PMAEK.own_notclient L ar C HI LY HIok b (24 * cap) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      assert (NS : ~ in_shadow_of b (24 * cap) a) by (exact (PMAEK.own_sh_notclient L ar C HI LY HIok b (24 * cap) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
      rewrite <- ELB in HH.
      rewrite PRES4; [| exact Ha| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 96) 2560 a HcB); intros x Hx; lia| lia].
      apply MGM3. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 112) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5]. apply (L5LZ.model_rt_trans model model3 model4); [|exact RT4].
    apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM5.
  - exact HH5.
Qed.
End Stage.
End PEAEPF.
