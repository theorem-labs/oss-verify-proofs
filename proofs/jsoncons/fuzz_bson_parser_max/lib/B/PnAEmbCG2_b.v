(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnAEmbCP_b PnAEmbCP3_b PnASrcKit_b PnAEmbCGStmts_b Ba0_code_b13ac_b13b0_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreB_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia.
Ltac nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac dlia := first [ solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_ne ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_ne end ]
                   | solve [ L5FastLia.prune_arith; nodisj; L5FastLia.lia_st ]
                   | solve [ L5FastLia.prune_arith; match goal with H : _ \/ _ |- _ => L5SAR.clear_disj_but H; destruct H; L5FastLia.lia_st end ] ].
Local Ltac lia := dlia.
Module PNAECG2.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac ftac := lazymatch goal with |- PNAECP.aligned _ _ => unfold PNAECP.aligned; first [amod | lia] | |- PNAECP3.aligned _ _ => unfold PNAECP3.aligned; first [amod | lia] end.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem grow2 : PMA.opdel_spec L ar HI -> forall (fx6 : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m q B R6 M6 model6 Aw6,
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> K [] -> PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> Z.of_nat (length stk) = 2 ^ k -> 0 <= k <= 10 -> 0 <= p1 < 2 ^ 47 -> 0 <= p2 < 2 ^ 47 -> 0 <= p3 < 2 ^ 47 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    PNAECGS.gmid L ar HI R M model LBX FF LK Aw cr v b k stk sp p1 p2 p3 m q B R6 M6 model6 Aw6 ->
    (forall (fx' : FPState) R' M' model' LK' Aw' b' lenv, regs_preserved R R' -> 0 <= lenv < 2 ^ 64 -> getr R' (reg 10) = Z_to_bv 64 (b' + 40 * (Z.of_nat (length stk) + 1)) ->
        4096 <= b' -> b' + 40 * 2 ^ (k + 1) < 2 ^ 47 -> PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M' v b' (k + 1) (stk ++ [PNM.BS m lenv q 0 0]) -> (v + 24 <= b' \/ b' + 40 * 2 ^ (k + 1) <= v) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b' (k + 1) ++ LBX) FF LK' (adebit L cr (40 * 2 ^ (k + 1))) Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx6 R6 0xad7f4 M6 model6) K.
Proof.
  intros DEL fx6 R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m q B R6 M6 model6 Aw6 HH K0 ENT AOV V8 LEN Kr RP1 RP2 RP3 BASE MID KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK0 & STKSH0). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  unfold PNAECGS.gmid, PNAECGS.SZ in MID.
  destruct MID as (J2 & J8 & J9 & J18 & J19 & J20 & J21 & J22 & J23 & J24 & JCS & W8 & W16 & W24 & W32 & W40 & W48 & W56 & W64 & W184 & W192 & W120 & W128 & W136 & W144 & W152 & W160
                   & W168 & W176 & W104 & W96 & W88 & W80 & W72 & WVB & WVE & WVC & ACCV6 & Q0 & Q4 & Q16 & Q5 & Q1 & bB & VBf & BDEF6 & QSH6 & BST6 & SLOT6
                   & HH6 & AM6 & MRT6 & IA6 & ASTK & STKSH & BASE6 & CHAIN6 & DK6).
  destruct SLOT6 as (lenv & LV & SLOT6).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM6 as (Mh6 & MI6).
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  assert (P2K : 1 <= 2 ^ k <= 1024) by (clear - Kr; split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]; change 1024 with (2 ^ 10); apply Z.pow_le_mono_r; Lia.lia).
  assert (P2S : 2 ^ (k + 1) = 2 * 2 ^ k) by (clear - Kr; rewrite Z.pow_add_r by Lia.lia; Lia.lia).
  remember (40 * 2 ^ k) as SZ eqn:ESZ.
  set (LB := PNM.bvec_own b k ++ LBX) in *. set (LB2 := (B, 2 * SZ) :: LB) in *. set (cr2 := adebit L cr (2 * SZ)) in *.
  assert (BIN : In (b, SZ) LB) by (left; unfold PNM.bvec_own; rewrite ESZ; reflexivity).
  assert (BIN2 : In (B, 2 * SZ) LB2) by (left; reflexivity). assert (BIN2b : In (b, SZ) LB2) by (right; exact BIN).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & CB1 & CB2 & STOP & _).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b SZ HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & B16 & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 v 24 sp 12288 HH6 AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 HH6) as (HOFF6 & VIS6 & VIMG6 & VFS6 & VBLK6 & VBSH6 & VFSSH6 & VSTSH6).
  set (H6 := ahid Aw6 model6) in *. set (MV6 := mrestrict H6 M6) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH6) as ST6. rewrite (L5A.aly_segs L C LYa) in ST6.
  pose proof (L5A.statics_facts L C M6 LYa ST6) as (GOT6 & CSB6 & CUAR6 & _).
  (* [comment removed for export] *)
  pose proof BASE6 as (ICB6 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB6.
  assert (X0 : L5.img_clear MV6 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB6).
  assert (X1 : L5.u64_at RSEGS MV6 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H6 M6 1309752 2147450880 (VIMG6 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB6).
  assert (X2 : L5.u32_at RSEGS MV6 1309760 1) by (apply (proj2 (L5A.u32_at_vis H6 M6 1309760 1 (VIMG6 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR6).
  assert (X3 : L5.writable RSEGS MV6 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H6 M6 (sp - 4096) 4096 (VIS6 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M6 sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X4 : L5KA.zeros_at MV6 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV6. rewrite (AsanAcct.mrestrict_visible H6 M6). apply (PNAECH.stack_zeros12 M6 sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H6 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH6 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (X5 : L5KA.zeros_at MV6 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 v 24 HH6 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV6). }
  assert (X6 : L5.writable RSEGS MV6 v 24).
  { apply (proj2 (L5A.writable_vis H6 M6 v 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  assert (VV : forall a v0, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M6 a v0 -> L5.u64_at RSEGS MV6 a v0).
  { intros a v0 H1 H2 X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X. }
  assert (VS : forall a v0, sp - 4096 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M6 a v0 -> L5.u64_at RSEGS MV6 a v0).
  { intros a v0 H1 H2 X. apply (proj2 (L5A.u64_at_vis H6 M6 a v0 (VIS6 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  apply VV in WVB; [| lia| lia]. apply VV in WVE; [| lia| lia]. apply VV in WVC; [| lia| lia].
  apply VS in W8; [| lia| lia].
  apply VS in W16; [| lia| lia].
  apply VS in W24; [| lia| lia].
  apply VS in W32; [| lia| lia].
  apply VS in W40; [| lia| lia].
  apply VS in W48; [| lia| lia].
  apply VS in W56; [| lia| lia].
  apply VS in W64; [| lia| lia].
  apply VS in W72; [| lia| lia].
  apply VS in W80; [| lia| lia].
  apply VS in W88; [| lia| lia].
  apply VS in W96; [| lia| lia].
  apply VS in W104; [| lia| lia].
  apply VS in W120; [| lia| lia].
  apply VS in W128; [| lia| lia].
  apply VS in W136; [| lia| lia].
  apply VS in W144; [| lia| lia].
  apply VS in W152; [| lia| lia].
  apply VS in W160; [| lia| lia].
  apply VS in W168; [| lia| lia].
  apply VS in W176; [| lia| lia].
  apply VS in W184; [| lia| lia].
  apply VS in W192; [| lia| lia].
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R (reg 23))) as UR23.
  pose proof (PMAIS1.bvu (getr R (reg 24))) as UR24.
  (* [comment removed for export] *)
  assert (PI : exists fx7 R7 M7v, mem_grows MV6 M7v
    /\ (forall a : word, ~ ((sp - 176) <= bv_unsigned a < (sp - 176) + 176) -> ~ ((v + 0) <= bv_unsigned a < (v + 0) + 24) -> M7v a = MV6 a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((sp - 176) <= i < (sp - 176) + 176) -> ~ ((v + 0) <= i < (v + 0) + 24) -> M7v (Z_to_bv 64 i) = MV6 (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx6 R6 0xad7f4 MV6) (st fx7 R7 0x7ba7c M7v)
        /\ (forall x, In x PNAECP3.KS_azcI0 -> getr R7 (reg x) = getr R6 (reg x))
        /\ getr R7 (reg 1) = Z_to_bv 64 711480 /\ getr R7 (reg 2) = Z_to_bv 64 (sp - 128) /\ getr R7 (reg 5) = Z_to_bv 64 0 /\ getr R7 (reg 8) = Z_to_bv 64 (v + 8)
        /\ getr R7 (reg 10) = Z_to_bv 64 B /\ getr R7 (reg 11) = Z_to_bv 64 (B + 2 * SZ) /\ getr R7 (reg 12) = Z_to_bv 64 (B + 2 * SZ) /\ getr R7 (reg 13) = Z_to_bv 64 (B + (SZ + 40))
        /\ getr R7 (reg 14) = Z_to_bv 64 1 /\ getr R7 (reg 15) = Z_to_bv 64 0 /\ getr R7 (reg 16) = Z_to_bv 64 1 /\ getr R7 (reg 17) = Z_to_bv 64 (B + (SZ + 40))
        /\ getr R7 (reg 18) = Z_to_bv 64 p3 /\ getr R7 (reg 19) = Z_to_bv 64 p2 /\ getr R7 (reg 20) = Z_to_bv 64 p1 /\ getr R7 (reg 21) = Z_to_bv 64 (((v + 8) / 8) + 2147450880)
        /\ getr R7 (reg 22) = Z_to_bv 64 2147450880 /\ getr R7 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23))) /\ getr R7 (reg 24) = Z_to_bv 64 (bv_unsigned (getr R (reg 24)))
        /\ L5.u64_at RSEGS M7v (sp - 128) (v + 8) /\ L5.u64_at RSEGS M7v (sp - 120) 731412 /\ L5.u64_at RSEGS M7v (sp - 88) b
        /\ L5.u64_at RSEGS M7v (v + 16) (B + 2 * SZ) /\ L5.u64_at RSEGS M7v (sp - 96) b /\ L5.u64_at RSEGS M7v (v + 8) (B + SZ + 40)
        /\ L5.u64_at RSEGS M7v (sp - 104) b /\ L5.u64_at RSEGS M7v v B /\ L5.u64_at RSEGS M7v (sp - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M7v (sp - 16) (bv_unsigned (getr R (reg 8))) /\ L5.u64_at RSEGS M7v (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M7v (sp - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M7v (sp - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M7v (sp - 48) (bv_unsigned (getr R (reg 20))) /\ L5.u64_at RSEGS M7v (sp - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M7v (sp - 64) (bv_unsigned (getr R (reg 22))) /\ L5.u64_at RSEGS M7v (sp - 72) v /\ L5.u64_at RSEGS M7v (sp - 80) (b + SZ))).
  { clear KONT. rewrite Z.add_assoc in W88.
    destruct KC as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]; subst k; subst SZ.
    - change (2 * (40 * 2 ^ 0)) with 80 in W80. change (40 * 2 ^ 0) with 40 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI0_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 1)) with 160 in W80. change (40 * 2 ^ 1) with 80 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI1_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 2)) with 320 in W80. change (40 * 2 ^ 2) with 160 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI2_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 3)) with 640 in W80. change (40 * 2 ^ 3) with 320 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI3_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 4)) with 1280 in W80. change (40 * 2 ^ 4) with 640 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI4_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 5)) with 2560 in W80. change (40 * 2 ^ 5) with 1280 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI5_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 6)) with 5120 in W80. change (40 * 2 ^ 6) with 2560 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI6_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 7)) with 10240 in W80. change (40 * 2 ^ 7) with 5120 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI7_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 8)) with 20480 in W80. change (40 * 2 ^ 8) with 10240 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI8_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 9)) with 40960 in W80. change (40 * 2 ^ 9) with 20480 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI9_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (2 * (40 * 2 ^ 10)) with 81920 in W80. change (40 * 2 ^ 10) with 40960 in W96, W88, WVE, WVC.
      LeanFeed.pfeed P (PNAECP3.azcI10_conc fx6 R6 MV6 (fun j => match j with 2%nat => sp | 24%nat => bv_unsigned (getr R (reg 24)) | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P. }
  clear KC X0 X1 X2 X3 X4 X5 X6 VV VS WVB WVE WVC W8 W16 W24 W32 W40 W48 W56 W64 W72 W80 W88 W96 W104 W120 W128 W136 W144 W152 W160 W168 W176 W184 W192.
  destruct PI as (fx7 & R7 & M7v & MG7 & _ & FZ7 & MS7 & KS7 & iR1 & iR2 & iR5 & iR8 & iR10 & iR11 & iR12 & iR13 & iR14 & iR15 & iR16 & iR17 & iR18 & iR19 & iR20 & iR21 & iR22 & iR23 & iR24
                  & I128 & I120 & I88 & I16v & I96 & I8v & I104 & I0v & I8 & I16 & I24 & I32 & I40 & I48 & I56 & I64 & I72 & I80).
  set (W7 := fun a => (sp - 176 <= a < sp - 176 + 176) \/ (v + 0 <= a < v + 0 + 24)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw6 M6 model6 fx6 fx7 R6 0xad7f4 R7 0x7ba7c M7v W7 K HH6 AM6 MS7 MG7).
  { intros a Ha N. apply FZ7; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia]. }
  intros M7 model7 HH7 AM7 MRT7 HID7 VIS7 MGM7 FR7 VV7.
  pose proof AM7 as (Mh7 & MI7).
  assert (ASTK7 : L5CA.astk ar M7 sp 12288) by (apply (L5SAR.astk_grows ar M6 M7 sp 12288 ASTK MGM7)).
  assert (QSH7 : shadow_zero M7 B (2 * SZ / 8)).
  { intros j Hj. pose proof (PNAECH.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at.
    rewrite FR7; [apply QSH6; exact Hj| lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  (* [comment removed for export] *)
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx7 R7 M7 model7 LB2 FF LK cr2 Aw6 K B (2 * SZ) (2 * SZ) (SZ + 40)); clear ANN.
  { exact HH7. }
  { exact Mh7. }
  { exact MI7. }
  { rewrite L5K.rl10. exact iR10. }
  { rewrite L5K.rl11. exact iR11. }
  { rewrite L5K.rl12. exact iR12. }
  { rewrite L5K.rl13. exact iR13. }
  { exact BIN2. }
  { exact Q16. }
  { lia. }
  { lia. }
  { split; [exact QSH7|]. split; [| intros j Hj; lia]. intros X. exfalso. apply X. rewrite ESZ. replace (2 * (40 * 2 ^ k)) with (10 * 2 ^ k * 8) by lia. apply Z.mod_mul. lia. }
  { rewrite L5K.rl4, (KS7 4%nat) by inl. rewrite JCS by (right; left; reflexivity). exact Rtp. }
  { rewrite L5K.rl1, iR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, iR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M7 M7 sp 12288 128 2304 ASTK7 (fun x X => X)); [lia| lia| lia|].
    replace (sp - 128) with (sp + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx8 R8 M8 model8 Aw8 RP8 ANN8 KEEP8 DSH8 SCR8 MRT8 INC8 MI8 HH8.
  rewrite L5K.rl2, iR2, L5.unsigned_lit in KEEP8, SCR8 by lia. rewrite L5K.rl1, iR1.
  assert (AM8 : L5CA.amodel_ok Aw8 model8) by (split; [rewrite (L5LZ.model_rt_halted model7 model8 MRT8); exact Mh7| exact MI8]).
  assert (CS8 : forall k0, In k0 L5SAR.cs_all -> getr R8 (reg k0) = getr R7 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R7 R8 k0 RP8 Hk)).
  assert (ASTK8 : L5CA.astk ar M8 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw6 M7 M7 M8 _ sp 12288 (sp - 128) 2304 HH7 ASTK7 (fun x X => X)).
    - intros a Ha Hs Hns. apply KEEP8; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR8.
    - lia. - lia. - lia. }
  assert (T87 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2432 <= a < sp - 128) -> ~ in_shadow_of B (2 * SZ) a -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply KEEP8; [exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. }
  (* [comment removed for export] *)
  remember (2 ^ (k + 1)) as NC eqn:ENC.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 HH8) as (HOFF8 & VIS8 & VIMG8 & VFS8 & VBLK8 & VBSH8 & VFSSH8 & VSTSH8).
  set (H8 := ahid Aw8 model8) in *. set (MV8 := mrestrict H8 M8) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 v 24 sp 12288 HH8 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF8 & OVIS8 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH8) as ST8. rewrite (L5A.aly_segs L C LYa) in ST8.
  pose proof (L5A.statics_facts L C M8 LYa ST8) as (GOT8 & CSB8 & CUAR8 & _).
  assert (Y0 : L5.img_clear MV8 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT8).
  assert (Y1 : L5.u64_at RSEGS MV8 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H8 M8 1309752 2147450880 (VIMG8 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB8).
  assert (Y2 : L5.u32_at RSEGS MV8 1309760 1) by (apply (proj2 (L5A.u32_at_vis H8 M8 1309760 1 (VIMG8 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR8).
  assert (Y3 : L5.writable RSEGS MV8 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H8 M8 (sp - 4096) 4096 (VIS8 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M8 sp 12288); [exact ASTK8| lia| lia| lia]. }
  assert (STKSH8 : shadow_zero M8 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAECH.S_add8 (sp - 12288) j) as E. pose proof (PNAECH.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T87; [| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia| apply (PNAEK.sh_apart B (2 * SZ)); lia].
    rewrite FR7; [rewrite <- E; apply STKSH; exact Hj| lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  assert (Y4 : L5KA.zeros_at MV8 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV8. rewrite (AsanAcct.mrestrict_visible H8 M8). apply (PNAECH.stack_zeros12 M8 sp STKSH8 A16). exact Hi.
    assert (AV : L5A.avis H8 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH8 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV8 : PMSPA.accA M8 v 24).
  { apply (PMFA.accA_agree M6 M8 v 24); [| exact ACCV6]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx.
    rewrite T87; [| lia| exact (PNAEK.frame_sh_client L ar FF v 24 x LB2 0 0 AOV Hx)| lia| apply (PNAEK.sh_apart B (2 * SZ) x); lia].
    apply FR7; [lia| unfold W7; intros [XW|XW]; [lia| destruct OBIG as [YW|YW]; lia]]. }
  assert (Y5 : L5KA.zeros_at MV8 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 v 24 HH8 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV8). }
  assert (Y6 : L5.writable RSEGS MV8 v 24).
  { apply (proj2 (L5A.writable_vis H8 M8 v 24 OVIS8 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF8. lia. lia. }
  assert (TV8 : forall a, v <= a < v + 24 -> M8 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. apply T87; [lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia|].
    intros X. pose proof (PNAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). destruct OBIG as [YW|YW]; lia. }
  assert (TS8 : forall a v0, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M7v a v0 -> L5.u64_at RSEGS MV8 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H8 M8 a v0 (VIS8 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply T87; [lia| apply L5SAR.stack_client; lia| lia| intros XS; pose proof (PNAEK.in_shadow_range B (2 * SZ) i ltac:(lia) ltac:(lia) XS); lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [apply VIS6; lia| lia| lia| exact X]. }
  assert (TV8' : forall a v0, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M7v a v0 -> L5.u64_at RSEGS MV8 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H8 M8 a v0 ltac:(eapply L5A.avis_sub; [exact OVIS8| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply TV8; lia| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact X]. }
  pose proof (TS8 (sp - 8) _ ltac:(lia) ltac:(lia) I8) as V8x.
  pose proof (TS8 (sp - 16) _ ltac:(lia) ltac:(lia) I16) as V16x.
  pose proof (TS8 (sp - 24) _ ltac:(lia) ltac:(lia) I24) as V24x.
  pose proof (TS8 (sp - 32) _ ltac:(lia) ltac:(lia) I32) as V32x.
  pose proof (TS8 (sp - 40) _ ltac:(lia) ltac:(lia) I40) as V40x.
  pose proof (TS8 (sp - 48) _ ltac:(lia) ltac:(lia) I48) as V48x.
  pose proof (TS8 (sp - 56) _ ltac:(lia) ltac:(lia) I56) as V56x.
  pose proof (TS8 (sp - 64) _ ltac:(lia) ltac:(lia) I64) as V64x.
  pose proof (TS8 (sp - 72) _ ltac:(lia) ltac:(lia) I72) as V72x.
  pose proof (TS8 (sp - 80) _ ltac:(lia) ltac:(lia) I80) as V80x.
  pose proof (TS8 (sp - 88) _ ltac:(lia) ltac:(lia) I88) as V88x.
  pose proof (TS8 (sp - 96) _ ltac:(lia) ltac:(lia) I96) as V96x.
  pose proof (TS8 (sp - 104) _ ltac:(lia) ltac:(lia) I104) as V104x.
  pose proof (TS8 (sp - 120) _ ltac:(lia) ltac:(lia) I120) as V120x.
  pose proof (TS8 (sp - 128) _ ltac:(lia) ltac:(lia) I128) as V128x.
  pose proof (TV8' v _ ltac:(lia) ltac:(lia) I0v) as VV0.
  pose proof (TV8' (v + 8) _ ltac:(lia) ltac:(lia) I8v) as VV8.
  replace (B + 2 * SZ) with (B + 40 * NC) in I16v by lia. pose proof (TV8' (v + 16) _ ltac:(lia) ltac:(lia) I16v) as VV16.
  assert (L2 : getr R8 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite CS8 by inl; exact iR2).
  assert (L8 : getr R8 (reg 8) = Z_to_bv 64 (v + 8)) by (rewrite CS8 by inl; exact iR8).
  assert (L9 : getr R8 (reg 9) = Z_to_bv 64 v) by (rewrite CS8 by inl; rewrite (KS7 9%nat) by inl; exact J9).
  assert (L18 : getr R8 (reg 18) = Z_to_bv 64 p3) by (rewrite CS8 by inl; exact iR18).
  assert (L19 : getr R8 (reg 19) = Z_to_bv 64 p2) by (rewrite CS8 by inl; exact iR19).
  assert (L20 : getr R8 (reg 20) = Z_to_bv 64 p1) by (rewrite CS8 by inl; exact iR20).
  assert (L21 : getr R8 (reg 21) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS8 by inl; exact iR21).
  assert (L22 : getr R8 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS8 by inl; exact iR22).
  assert (L23 : getr R8 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS8 by inl; exact iR23).
  rewrite ESZ in VV8, V80x. assert (AL8 : (40 * 2 ^ k) mod 8 = 0) by (replace (40 * 2 ^ k) with (5 * 2 ^ k * 8) by lia; apply Z.mod_mul; lia).
  LeanFeed.pfeed P (PNAECP.azcJ_conc fx8 R8 MV8 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 54%nat => 2 ^ k | _ => 0 end)) ltac:(first [ftac | assumption | lia]).
  destruct P as (fx9 & R9 & M9v & MG9 & _ & FZ9 & MS9 & KS9 & jR1 & jR2 & jR8 & jR9 & jR10 & jR11 & jR12 & jR13 & jR14 & jR15 & jR16 & jR17
                 & J8c & J16c & J24c & J32c & J40c & J48c & J56c & J64c & J72c & J104c & J96c & J88c & J80c).
  clear Y0 Y1 Y2 Y3 Y4 Y5 Y6 TS8 TV8' VV0 VV8 VV16 V8x V16x V24x V32x V40x V48x V56x V64x V72x V80x V88x V96x V104x V120x V128x.
  set (W9 := fun a => sp - 176 <= a < sp - 176 + 176).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw8 M8 model8 fx8 fx9 R8 0xadb38 R9 0xd39ac M9v W9 K HH8 AM8 MS9 MG9).
  { intros a Ha N. apply FZ9; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W9 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M9 model9 HH9 AM9 MRT9 HID9 VIS9 MGM9 FR9 VV9.
  assert (ASTK9 : L5CA.astk ar M9 sp 12288) by (apply (L5SAR.astk_grows ar M8 M9 sp 12288 ASTK8 MGM9)).
  (* [comment removed for export] *)
  unfold PMA.opdel_spec, PMSPA.opdel_spec, PMSPA.opdel_spec_at in DEL. cbn [pa_opdel PMA.AD ADDR_A] in DEL.
  apply (DEL fx9 R9 M9 model9 K LB2 FF LK Aw8 cr2 b SZ (sp - 112) 731432 HH9 AM9 K0).
  { exact BIN2b. }
  { rewrite L5K.rl10. exact jR10. }
  { rewrite L5K.rl1. exact jR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact jR2. }
  { rewrite L5K.rl4, (KS9 4%nat) by inl. rewrite CS8 by inl. rewrite (KS7 4%nat) by inl. rewrite JCS by (right; left; reflexivity). exact Rtp. }
  { unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M9 M9 sp 12288 112 4096 ASTK9 (fun x X => X)); [lia| lia| lia|].
    replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx10 R10 M10 model10 Aw10 RP10 HP10 MRT10 IA10 AM10 HH10.
  unfold PMSPA.OPDEL_SCR, PMSPA.MALLOC_SCR in HP10.
  assert (ELB : lb_remove b LB2 = (B, 2 * SZ) :: LBX).
  { unfold LB2, LB, PNM.bvec_own, PNM.BSZ. cbn [lb_remove fst app]. rewrite (proj2 (Z.eqb_neq B b)) by lia. rewrite Z.eqb_refl. reflexivity. }
  rewrite ELB in HP10, HH10.
  assert (CS10 : forall k0, In k0 L5SAR.cs_all -> getr R10 (reg k0) = getr R9 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R9 R10 k0 RP10 Hk)).
  assert (KEEP10 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ((B, 2 * SZ) :: LBX) FF (sp - 112) 4096 a -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP10). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  assert (ASTK10 : L5CA.astk ar M10 sp 12288).
  { apply (PMKA.astk_after_ahpres L ar ((B, 2 * SZ) :: LBX) FF M9 M10 sp 12288 (sp - 112) 4096 [] ASTK9 HP10); lia. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 HH10) as (HOFF10 & VIS10 & VIMG10 & VFS10 & VBLK10 & VBSH10 & VFSSH10 & VSTSH10).
  set (H10 := ahid Aw10 model10) in *. set (MV10 := mrestrict H10 M10) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 v 24 sp 12288 HH10 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF10 & OVIS10 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH10) as ST10. rewrite (L5A.aly_segs L C LYa) in ST10.
  pose proof (L5A.statics_facts L C M10 LYa ST10) as (GOT10 & CSB10 & CUAR10 & _).
  assert (Z0' : L5.img_clear MV10 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT10).
  assert (Z1' : L5.u64_at RSEGS MV10 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H10 M10 1309752 2147450880 (VIMG10 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB10).
  assert (Z2' : L5.u32_at RSEGS MV10 1309760 1) by (apply (proj2 (L5A.u32_at_vis H10 M10 1309760 1 (VIMG10 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR10).
  assert (Z3' : L5.writable RSEGS MV10 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H10 M10 (sp - 4096) 4096 (VIS10 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M10 sp 12288); [exact ASTK10| lia| lia| lia]. }
  assert (CLs : forall a LBz, aclient L ar LBX FF 0 0 a -> In (B, 2 * SZ) LBz -> incl LBX LBz -> aclient L ar LBz FF 0 0 a).
  { intros a LBz Hc _ Hi. destruct Hc as [(qb & Hq & Xq)|Hc]; [left; exists qb; split; [apply Hi; exact Hq| exact Xq]|].
    destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|(qb & Hq & Xq)]]]]]; [right; left; exact Hc| right; right; left; exact Hc| right; right; right; left; exact Hc
                                                   | right; right; right; right; left; exact Hc| right; right; right; right; right; left; exact Hc|].
    do 6 right. exists qb. split; [apply Hi; exact Hq| exact Xq]. }
  assert (T9_10 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar ((B, 2 * SZ) :: LBX) FF 0 0 a -> ~ (sp - 4208 <= a < sp - 112) -> M10 (Z_to_bv 64 a) = M9 (Z_to_bv 64 a)).
  { intros a Ha Hc N. apply KEEP10; [exact Ha| apply (L5SAR.aclient_narrow L ar _ FF 0 0); [exact Hc| lia]]. }
  assert (STKSH10 : shadow_zero M10 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAECH.S_add8 (sp - 12288) j) as E. pose proof (PNAECH.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T9_10; [| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia]. rewrite FR9; [| lia| unfold W9; lia]. rewrite <- E. apply STKSH8. exact Hj. }
  assert (Z5' : L5KA.zeros_at MV10 (v / 8 + 2147450880) 3).
  { assert (ACC10 : PMSPA.accA M10 v 24).
    { apply (PMFA.accA_agree M8 M10 v 24); [| exact ACCV8]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx.
      rewrite T9_10; [| lia| exact (PNAEK.frame_sh_client L ar FF v 24 x _ 0 0 AOV Hx)| lia]. apply FR9; [lia| unfold W9; lia]. }
    exact (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 v 24 HH10 AOV V8 ltac:(lia) ltac:(reflexivity) ACC10). }
  assert (Z4' : L5KA.zeros_at MV10 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV10. rewrite (AsanAcct.mrestrict_visible H10 M10). apply (PNAECH.stack_zeros12 M10 sp STKSH10 A16). exact Hi.
    assert (AV : L5A.avis H10 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH10 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Z6' : L5.writable RSEGS MV10 v 24).
  { apply (proj2 (L5A.writable_vis H10 M10 v 24 OVIS10 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF10. lia. lia. }
  assert (TV10 : forall a, v <= a < v + 24 -> M10 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. rewrite T9_10; [| lia| apply (L5SAR.obj_client L ar _ FF 0 0 v 24 a AOB); lia| lia]. rewrite FR9; [| lia| unfold W9; lia]. apply TV8. lia. }
  assert (Z7' : L5.u64_at RSEGS MV10 (v + 8) (B + SZ + 40)).
  { apply (proj2 (L5A.u64_at_vis H10 M10 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS10| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M7); [intros i Hi; apply TV10; lia| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I8v]. }
  assert (TS10 : forall a v0, sp - 112 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M9v a v0 -> L5.u64_at RSEGS MV10 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H10 M10 a v0 (VIS10 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M9); [intros i Hi; apply T9_10; [lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS9); [apply VIS8; lia| lia| lia| exact X]. }
  pose proof (TS10 (sp - 8) _ ltac:(lia) ltac:(lia) J8c) as K8x.
  pose proof (TS10 (sp - 16) _ ltac:(lia) ltac:(lia) J16c) as K16x.
  pose proof (TS10 (sp - 24) _ ltac:(lia) ltac:(lia) J24c) as K24x.
  pose proof (TS10 (sp - 32) _ ltac:(lia) ltac:(lia) J32c) as K32x.
  pose proof (TS10 (sp - 40) _ ltac:(lia) ltac:(lia) J40c) as K40x.
  pose proof (TS10 (sp - 48) _ ltac:(lia) ltac:(lia) J48c) as K48x.
  pose proof (TS10 (sp - 56) _ ltac:(lia) ltac:(lia) J56c) as K56x.
  pose proof (TS10 (sp - 64) _ ltac:(lia) ltac:(lia) J64c) as K64x.
  pose proof (TS10 (sp - 72) _ ltac:(lia) ltac:(lia) J72c) as K72x.
  assert (N2 : getr R10 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS10 by inl; exact jR2).
  assert (N8 : getr R10 (reg 8) = Z_to_bv 64 (B + 40 * 2 ^ k + 40)) by (rewrite CS10 by inl; exact jR8).
  assert (N9 : getr R10 (reg 9) = Z_to_bv 64 v) by (rewrite CS10 by inl; exact jR9).
  assert (N21 : getr R10 (reg 21) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)) by (rewrite CS10 by inl; rewrite (KS9 21%nat) by inl; exact L21).
  assert (N22 : getr R10 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS10 by inl; rewrite (KS9 22%nat) by inl; exact L22).
  assert (N23 : getr R10 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS10 by inl; rewrite (KS9 23%nat) by inl; exact L23).
  LeanFeed.pfeed P (PNAECP.azcK_conc fx10 R10 MV10 (fun j => match j with 2%nat => sp | 33%nat => v | 40%nat => B | 41%nat => B + SZ + 40 | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 54%nat => 2 ^ k | _ => 0 end)) ltac:(first [ftac | assumption | lia]).
  destruct P as (fx11 & R11 & M11v & MG11 & _ & FZ11 & MS11 & KS11 & kR1 & kR2 & kR8 & kR9 & kR10 & kR18 & kR19 & kR20 & kR21 & kR22 & kR23 & K8v).
  assert (R11ra : getr R11 (reg 1) = Z_to_bv 64 r) by (rewrite kR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx11 R11 M11v 0xb2950 W_b13ac r F_b13ac eq_refl D_b13ac R11ra ltac:(lia) Hr2) as MS12.
  set (W11 := fun a => v + 8 <= a < v + 8 + 8).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr2 Aw10 M10 model10 fx10 fx11 R10 0xb2928 R11 r M11v W11 K HH10 AM10 ltac:(eapply msteps_trans; [exact MS11| exact MS12]) MG11).
  { intros a Ha N. apply FZ11; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W11 in Wa. split; [apply (L5SAR.obj_client L ar _ FF 0 0 v 24 a AOB); lia| lia]. }
  intros M11 model11 HH11 AM11 MRT11 HID11 VIS11 MGM11 FR11 VV11.
  (* [comment removed for export] *)
  assert (TB11 : forall a, B <= a < B + 2 * SZ -> M11 (Z_to_bv 64 a) = M6 (Z_to_bv 64 a)).
  { intros a Ha. assert (CB : forall LBz, In (B, 2 * SZ) LBz -> aclient L ar LBz FF 0 0 a) by (intros LBz Hin; unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact Hin| cbn [fst snd]; lia]).
    rewrite FR11; [| lia| unfold W11; lia]. rewrite T9_10; [| lia| apply CB; left; reflexivity| lia]. rewrite FR9; [| lia| unfold W9; lia].
    rewrite T87; [| lia| apply CB; exact BIN2| lia|]. 2:{ intros X. pose proof (PNAEK.in_shadow_range B (2 * SZ) a ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
    apply FR7; [lia| unfold W7; lia]. }
  assert (SH11 : forall j, 0 <= j < 2 * SZ / 8 -> M11 (Z_to_bv 64 (S B + j)) = M8 (Z_to_bv 64 (S B + j))).
  { intros j Hj. pose proof (PNAECH.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL.
    rewrite FR11; [| lia| unfold W11; destruct OBIG as [YW|YW]; lia]. rewrite T9_10; [| lia| | lia]. 2:{ unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [left; reflexivity| cbn [fst snd]; apply PNAEK.sh_in; lia]. }
    apply FR9; [lia| unfold W9; lia]. }
  assert (TV11 : forall a, v <= a < v + 8 \/ v + 16 <= a < v + 24 -> M11 (Z_to_bv 64 a) = M7 (Z_to_bv 64 a)).
  { intros a Ha. rewrite FR11; [| lia| unfold W11; lia]. apply TV10. lia. }
  assert (HP11 : L5CA.ahpres L ar LBX FF sp 12288 [(v, 24)] M M11).
  { apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M11).
      + intros a (Ha & Hc & Ho).
        assert (NV : ~ (v <= a < v + 24)) by (intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]).
        assert (Hc0 : aclient L ar LBX FF 0 0 a) by exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc).
        assert (HcB : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF 0 0 a Hc0)).
        assert (NW : ~ (sp - 12288 <= a < sp)).
        { destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT ltac:(apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc))) as [Z1|Z1]; lia. }
        assert (NS : ~ in_shadow_of B (2 * SZ) a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw6 M6 _ HH6 ltac:(lia) a 0 0 HcB)).
        rewrite FR11; [| exact Ha| unfold W11; lia]. rewrite T9_10; [| exact Ha| apply (CLs a _ Hc0); [left; reflexivity| intros x Hx; right; exact Hx]| lia].
        rewrite FR9; [| exact Ha| unfold W9; lia]. rewrite T87; [| exact Ha| apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a HcB)| lia| exact NS].
        rewrite FR7; [| exact Ha| unfold W7; lia]. apply CHAIN6; [exact Ha| exact Hc0| exact NW| exact NV].
      + pose proof ASTK10 as (_ & _ & _ & _ & SD10 & _). apply (L5.defined_grows M10 M11 _ _ MGM11). exact SD10.
      + intros a Ha Hc HM.
        assert (Hc0 : aclient L ar LBX FF 0 0 a) by exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc).
        assert (HcB : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF 0 0 a Hc0)).
        assert (NW : ~ (sp - 12288 <= a < sp)).
        { destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT ltac:(apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc))) as [Z1|Z1]; lia. }
        assert (NS : ~ in_shadow_of B (2 * SZ) a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw6 M6 _ HH6 ltac:(lia) a 0 0 HcB)).
        apply MGM11. rewrite T9_10; [| exact Ha| apply (CLs a _ Hc0); [left; reflexivity| intros x Hx; right; exact Hx]| lia].
        apply MGM9. rewrite T87; [| exact Ha| apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a HcB)| lia| exact NS].
        apply MGM7. exact (DK6 a Ha Hc0 HM). }
  assert (EK11 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M11).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 12288 sp 12288 [(v, 24)] [(v, 24)] M M11 HP11); [lia| lia| intros a _ Ho; exact Ho]. }
  assert (BASE11 : PMSTA.base_okA RSEGS PMA.AD M11).
  { apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M11 EK11); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (KONT fx11 R11 M11 model11 LK Aw10 B lenv).
  2: exact LV.
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 25; 26; 27]%nat -> getr R11 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PNAECP.KS_azcK /\ In k' L5SAR.cs_all /\ In k' PNAECP.KS_azcJ /\ In k' PNAECP3.KS_azcI0)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (split; [inl| split; [inl| split; inl]])).
      destruct Y as (Yk1 & Yk2 & Yk3 & Yk4). rewrite (KS11 k' Yk1), (CS10 k' Yk2), (KS9 k' Yk3), (CS8 k' Yk2), (KS7 k' Yk4). apply JCS. exact Hk'. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]]]].
    + rewrite kR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite kR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite kR23, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite (KS11 24%nat) by inl. rewrite CS10 by inl. rewrite (KS9 24%nat) by inl. rewrite CS8 by inl. rewrite iR24, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk.
  - rewrite kR10, LEN. f_equal. lia.
  - lia.
  - lia.
  - unfold PNM.bvec_at, PNM.BSZ. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
    rewrite <- ENC. replace (40 * NC) with (2 * SZ) by lia.
    split. { apply (L5C.u64_at_agree RSEGS M7 M11); [intros i Hi; apply TV11; lia| lia| lia|].
             apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I0v]. }
    split. { replace (B + 40 * (Z.of_nat (length stk) + 1)) with (B + SZ + 40) by lia.
             apply (PMAIS1.vis_u64 _ _ _ _ _ VIS11); [eapply L5A.avis_sub; [exact OVIS10| lia| lia]| lia| lia| exact K8v]. }
    split. { apply (L5C.u64_at_agree RSEGS M7 M11); [intros i Hi; apply TV11; lia| lia| lia|].
             replace (B + 2 * SZ) with (B + 40 * NC) by lia.
             apply (PMAIS1.vis_u64 _ _ _ _ _ VIS7); [eapply L5A.avis_sub; [exact OVIS| lia| lia]| lia| lia| exact I16v]. }
    split; [lia|]. split; [lia|]. split; [exact Q16|].
    split. { intros i Hi. rewrite TB11 by lia. apply BDEF6. exact Hi. }
    destruct ANN8 as (ZA8 & PM8 & PA8).
    split. { unfold PMSPA.accA. apply (PMFA.accA_agree M8 M11 B (40 * (Z.of_nat (length stk) + 1))).
             - intros x Hx. assert (Sx : exists j, S x = S B + j /\ 0 <= j < 2 * SZ / 8).
               { exists (S x - S B). split; [lia|]. unfold S, SB. clear - Hx LEN P2K ESZ Q16 Q0. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
               destruct Sx as (j & Ej & Hj). rewrite Ej. apply SH11. exact Hj.
             - unfold PMSPA.accA. apply (L5CB.aacc_of_zero M8 B ((SZ + 40) / 8) B _ ZA8); [lia| lia| lia|].
               Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
               rewrite ESZ. replace (40 * 2 ^ k + 40) with (40 * (2 ^ k + 1)) by lia. rewrite PNAEK.d40. lia. }
    split. { replace (40 * (Z.of_nat (length stk) + 1)) with (SZ + 40) by lia.
             apply (PNAEK.ann_agree M8 M11 B (SZ + 40) (2 * SZ)); [intros j Hj; apply SH11; clear - Hj ESZ; rewrite ESZ in *; Lia.lia| lia| lia| split; [exact ZA8| split; [exact PM8| exact PA8]]]. }
    intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hl].
    + rewrite app_nth1 by exact Hl. apply (PNMF.bstate_at_agree RSEGS M6 M11); [lia| lia| | apply BST6; exact Hl].
      intros x Hx. apply TB11. assert (Z.of_nat i + 1 <= Z.of_nat (length stk)) by lia. lia.
    + assert (Ei : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      replace (B + 40 * Z.of_nat (length stk)) with (B + SZ) by lia.
      apply (PNMF.bstate_at_agree RSEGS M6 M11); [lia| lia| intros x Hx; apply TB11; lia| exact SLOT6].
  - replace (40 * NC) with (2 * SZ) by lia. exact VBf.
  - apply (PMFA.accA_agree M8 M11 v 24); [| exact ACCV8]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx.
    rewrite FR11; [| lia| unfold W11; destruct OBIG as [YW|YW]; lia]. rewrite T9_10; [| lia| exact (PNAEK.frame_sh_client L ar FF v 24 x _ 0 0 AOV Hx)| lia].
    apply FR9; [lia| unfold W9; lia].
  - exact BASE11.
  - exact HP11.
  - apply (L5LZ.model_rt_trans model model10 model11); [|exact MRT11]. apply (L5LZ.model_rt_trans model model9 model10); [|exact MRT10].
    apply (L5LZ.model_rt_trans model model8 model9); [|exact MRT9]. apply (L5LZ.model_rt_trans model model7 model8); [|exact MRT8].
    apply (L5LZ.model_rt_trans model model6 model7); [exact MRT6| exact MRT7].
  - intros x Hx. exact Hx.
  - intros x Hx. apply IA10. apply INC8. apply IA6. exact Hx.
  - exact AM11.
  - unfold PNM.bvec_own, PNM.BSZ. cbn [app]. rewrite <- ENC. replace (40 * NC) with (2 * SZ) by lia. exact HH11.
Qed.
End Stage.
End PNAECG2.
