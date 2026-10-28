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
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnAEmbCP_b PnAEmbCP2_b PnASrcKit_b PnAEmbCGStmts_b.
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
Module PNAECG1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Ltac amod := match goal with H : ?x mod ?m = 0 |- ?x mod ?m = 0 => exact H end.
Ltac ftac := lazymatch goal with |- PNAECP.aligned _ _ => unfold PNAECP.aligned; first [amod | lia] | |- PNAECP2.aligned _ _ => unfold PNAECP2.aligned; first [amod | lia] end.
Ltac edB KC := lazymatch goal with |- ?ed _ _ = _ => unfold ed end; try (lazymatch goal with |- _ _ (?evf _ (S _)) _ = _ => unfold evf end);
  lazymatch goal with |- _ _ ?a ?y = _ => rewrite (PropExec.alu_add a y); unfold PropExec.v_add;
    replace (bv_unsigned y) with 0 by (destruct KC as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E; vm_compute; reflexivity) end;
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma pow2k10 k : 0 <= k <= 10 -> 1 <= 2 ^ k <= 1024.
Proof. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; Lia.lia. Qed.
Lemma pow2s k : 0 <= k -> 2 ^ (k + 1) = 2 * 2 ^ k.
Proof. intros Hk. rewrite Z.pow_add_r by Lia.lia. Lia.lia. Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem grow1 : PMA.opnew_spec L ar HI -> forall (fx : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q,
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) = 2 ^ k -> k <= 10 ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> getr R (reg 13) = Z_to_bv 64 p3 -> p1 mod 4 = 0 -> p2 mod 4 = 0 -> p3 mod 8 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 -> byte_at M (S p3) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 -> PNAEK.argp (ar_sptop ar) FF sp v p3 8 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> L5.u64_at RSEGS M p3 q -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 32 -> 0 <= q < 2 ^ 64 -> acredit_ok L cr (40 * 2 ^ (k + 1)) ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx6 : FPState) R6 M6 model6 Aw6 B, PNAECGS.gmid L ar HI R M model LBX FF LK Aw cr v b k stk sp p1 p2 p3 m q B R6 M6 model6 Aw6 ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx6 R6 0xad7f4 M6 model6) K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb2758 M model) K.
Proof.
  intros OPN fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV VEC LEN K10 A11 A12 A13 P14 P24 P34 SP1 SP2 SP3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ CR BASE KONT.
  unfold PNM.bvec_at, PNM.BSZ in VEC.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VB & VE & VC & Kr & LENk & B16 & BDEF & BACC & BANN & BST).
  assert (KC : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  pose proof (pow2k10 k ltac:(lia)) as P2K. pose proof (pow2s k ltac:(lia)) as P2S.
  remember (40 * 2 ^ k) as SZ eqn:ESZ. remember (2 ^ (k + 1)) as NC eqn:ENC.
  assert (LENz : 40 * Z.of_nat (length stk) = SZ) by lia. rewrite LENz in VE. try rewrite <- ESZ in VC.
  set (LB := PNM.bvec_own b k ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, SZ) LB) by (left; unfold PNM.bvec_own; rewrite ESZ; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b SZ HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p1 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p2 4 HH ASTK ltac:(lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p3 8 HH ASTK ltac:(lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & Pc2 & Pc3 & Pc4 & Pc5 & Pc6).
  pose proof (Pa5 b SZ BIN) as PaB. pose proof (Pb5 b SZ BIN) as PbB. pose proof (Pc5 b SZ BIN) as PcB.
  assert (VBLK : v + 24 <= b \/ b + SZ <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  (* [comment removed for export] *)
  pose proof BASE as (ICB & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB.
  assert (X0 : L5.img_clear MV 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X4 : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M). apply (PNAECH.stack_zeros12 M sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + SZ)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + SZ)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R (reg 23))) as UR23.
  (* [comment removed for export] *)
  assert (PS : exists fx1 R1 M1v, mem_grows MV M1v
    /\ (forall a : word, ~ ((sp - 192) <= bv_unsigned a < (sp - 192) + 192) -> M1v a = MV a)
    /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ ((sp - 192) <= i < (sp - 192) + 192) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
    /\ (msteps RSEGS (st fx R 0xb2758 MV) (st fx1 R1 0x130338 M1v)
        /\ (forall x, In x PNAECP2.KS_azcS0 -> getr R1 (reg x) = getr R (reg x))
        /\ getr R1 (reg 1) = Z_to_bv 64 710136
        /\ getr R1 (reg 2) = Z_to_bv 64 (sp - 176)
        /\ getr R1 (reg 8) = Z_to_bv 64 (sp - 80)
        /\ getr R1 (reg 9) = Z_to_bv 64 NC
        /\ getr R1 (reg 10) = Z_to_bv 64 (2 * SZ)
        /\ getr R1 (reg 11) = Z_to_bv 64 NC
        /\ getr R1 (reg 12) = Z_to_bv 64 1309752
        /\ getr R1 (reg 13) = Z_to_bv 64 v
        /\ getr R1 (reg 14) = Z_to_bv 64 14757395258967641293
        /\ getr R1 (reg 15) = Z_to_bv 64 0
        /\ getr R1 (reg 18) = Z_to_bv 64 (sp - 104)
        /\ getr R1 (reg 19) = Z_to_bv 64 (2 ^ k)
        /\ getr R1 (reg 20) = Z_to_bv 64 (((sp - 80) / 8) + 2147450880)
        /\ getr R1 (reg 21) = Z_to_bv 64 2147450880
        /\ getr R1 (reg 22) = Z_to_bv 64 2147450880
        /\ getr R1 (reg 23) = getr R (reg 23)
        /\ L5.u64_at RSEGS M1v (sp - 128) (v + 8)
        /\ L5.u64_at RSEGS M1v (sp - 120) 731192
        /\ L5.u64_at RSEGS M1v (sp - 80) 0
        /\ L5.u64_at RSEGS M1v (sp - 72) v
        /\ L5.u64_at RSEGS M1v (sp - 64) (bv_unsigned (getr R (reg 22)))
        /\ L5.u64_at RSEGS M1v (sp - 56) (bv_unsigned (getr R (reg 21)))
        /\ L5.u64_at RSEGS M1v (sp - 48) (bv_unsigned (getr R (reg 20)))
        /\ L5.u64_at RSEGS M1v (sp - 40) (bv_unsigned (getr R (reg 19)))
        /\ L5.u64_at RSEGS M1v (sp - 32) (bv_unsigned (getr R (reg 18)))
        /\ L5.u64_at RSEGS M1v (sp - 24) (bv_unsigned (getr R (reg 9)))
        /\ L5.u64_at RSEGS M1v (sp - 16) (bv_unsigned (getr R (reg 8)))
        /\ L5.u64_at RSEGS M1v (sp - 8) (bv_unsigned (getr R (reg 1)))
        /\ L5.u64_at RSEGS M1v (sp - 168) (((v + 8) / 8) + 2147450880)
        /\ L5.u64_at RSEGS M1v (sp - 160) p1
        /\ L5.u64_at RSEGS M1v (sp - 152) p2
        /\ L5.u64_at RSEGS M1v (sp - 144) p3
        /\ L5.u64_at RSEGS M1v (sp - 136) v)).
  { clear KONT.
    destruct KC as [Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|[Ek|Ek]]]]]]]]]]; subst k; subst SZ NC.
    - change (40 * 2 ^ 0) with 40 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS0_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 1) with 80 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 2) with 160 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS2_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 3) with 320 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS3_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 4) with 640 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS4_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 5) with 1280 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS5_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 6) with 2560 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS6_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 7) with 5120 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS7_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 8) with 10240 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS8_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 9) with 20480 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS9_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P.
    - change (40 * 2 ^ 10) with 40960 in X7, X8.
      LeanFeed.pfeed P (PNAECP2.azcS10_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | _ => 0 end)) ltac:(first [ftac | assumption | lia]). exact P. }
  destruct PS as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & sR1 & sR2 & sR8 & sR9 & sR10 & sR11 & sR12 & sR13 & sR14 & sR15 & sR18 & sR19 & sR20 & sR21 & sR22 & sR23
                  & T128 & T120 & T80 & T72 & T64 & T56 & T48 & T40 & T32 & T24 & T16 & T8 & T168 & T160 & T152 & T144 & T136).
  clear X0 X1 X2 X3 X4 X5 X6 X7 X8 KC FSIMG.
  set (W1 := fun a => sp - 192 <= a < sp - 192 + 192).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb2758 R1 0x130338 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  unfold PMA.opnew_spec, PMSPA.opnew_spec in OPN. cbn [pa_opnew PMA.AD ADDR_A] in OPN.
  apply (OPN fx1 R1 M1 model1 K LB FF LK Aw cr (2 * SZ) (sp - 176) 710136 HH1 AM1 K0).
  { rewrite L5K.rl10. exact sR10. }
  { lia. }
  { replace (2 * SZ) with (40 * NC) by lia. exact CR. }
  { rewrite L5K.rl1. exact sR1. }
  { split; [lia| reflexivity]. }
  { rewrite L5K.rl2. exact sR2. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR. apply (L5SAR.astk_sub ar M1 M1 sp 12288 176 (16 + 4096) (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X)); [lia| lia| lia|].
    replace (sp - 176) with (sp + (-11) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  intros fx2 R2 M2 model2 Aw2 B RB RP2 FRESH HP2 MRT2 IA2 AM2 HH2.
  unfold PMSPA.OPNEW_SCR, PMSPA.MALLOC_SCR in HP2. change (16 + 4096) with 4112 in HP2. rewrite L5K.rl10 in RB.
  destruct FRESH as (QR & QAP & QFA & QDEF & QSH). pose proof QR as (Q0 & Q1 & Q16 & _ & Q4 & Q5). unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Q5.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Q1.
  set (LB2 := (B, 2 * SZ) :: LB) in *. set (cr2 := adebit L cr (2 * SZ)) in *.
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - 176) 4112 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hc. apply (proj1 HP2). split; [exact Ha|]. split; [exact Hc| intros rg []]. }
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 4288 <= a < sp) -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N. rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]]. apply FR1; [exact Ha| unfold W1; lia]. }
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK cr Aw M1 M1 M2 _ sp 12288 (sp - 176) 4112 [] HH1 (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1) (fun x X => X) HP2); lia. }
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p1 4 B (2 * SZ) ASTK ltac:(lia) AG1 QFA Q4 ltac:(lia)) as PB1.
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p2 4 B (2 * SZ) ASTK ltac:(lia) AG2 QFA Q4 ltac:(lia)) as PB2.
  pose proof (PNAEK.arg_fresh_apart ar M FF LK sp 12288 v p3 8 B (2 * SZ) ASTK ltac:(lia) AG3 QFA Q4 ltac:(lia)) as PB3.
  assert (VBf : v + 24 <= B \/ B + 2 * SZ <= v).
  { destruct AOV as (f & Hf & Yv1 & Yv2). destruct (QFA f ltac:(apply in_or_app; left; exact Hf)) as [Y|Y]; [right; lia| left; lia]. }
  assert (bB : B + 2 * SZ <= b \/ b + SZ <= B) by (destruct (QAP (b, SZ) BIN) as [Y|Y]; cbn [fst snd] in Y; lia).
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 v 24 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAECH.S_add8 (sp - 12288) j) as E. pose proof (PNAECH.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia]. }
  assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (PNAECH.stack_zeros12 M2 sp STKSH2 A16). exact Hi.
    assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV2 : PMSPA.accA M2 v 24).
  { apply (PMFA.accA_agree M M2 v 24); [| exact ACCV]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia].
    exact (PNAEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx). }
  assert (Y5 : L5KA.zeros_at MV2 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 v 24 HH2 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV2). }
  assert (TV : forall a, v <= a < v + 24 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia]. }
  assert (Y7 : L5.u64_at RSEGS MV2 v b).
  { apply (proj2 (L5A.u64_at_vis H2 M2 v b ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
  assert (Y8 : L5.u64_at RSEGS MV2 (v + 8) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
  assert (Y9 : L5.u64_at RSEGS MV2 (v + 16) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB2 FF LK cr2 Aw2 M2 model2 sp 12288 v p1 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB2 FF LK cr2 Aw2 M2 model2 sp 12288 v p2 4 HH2 ASTK2 ltac:(lia) AG2 ltac:(lia)) as (AV2 & AVS2).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB2 FF LK cr2 Aw2 M2 model2 sp 12288 v p3 8 HH2 ASTK2 ltac:(lia) AG3 ltac:(lia)) as (AV3 & AVS3).
  assert (TP : forall p x, 6905856 <= p -> p + 4 <= 2 ^ 47 -> (sp <= p \/ p + 4 <= ahl_ceil ar) -> (forall i sp' scr', 0 <= i < 4 -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)) ->
             p <= x < p + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros p x Q0' Q1' Q3 CLp Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia]. }
  assert (TPS : forall p, PNAEK.argp (ar_sptop ar) FF sp v p 4 -> 0 <= p < 2 ^ 47 -> byte_at M (S p) 0 -> byte_at M2 (S p) 0).
  { intros p AP Hp X. pose proof (PNAECH.S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia].
    exact (PNAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 v p 4 HH ASTK ltac:(lia) AP ltac:(lia) LB 0 0). }
  assert (TP8 : forall p x, 6905856 <= p -> p + 8 <= 2 ^ 47 -> (sp <= p \/ p + 8 <= ahl_ceil ar) -> (forall i sp' scr', 0 <= i < 8 -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)) ->
             p <= x < p + 8 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros p x Q0' Q1' Q3 CLp Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia]. }
  assert (TPS8 : forall p, PNAEK.argp (ar_sptop ar) FF sp v p 8 -> 0 <= p < 2 ^ 47 -> byte_at M (S p) 0 -> byte_at M2 (S p) 0).
  { intros p AP Hp X. pose proof (PNAECH.S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia].
    exact (PNAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 v p 8 HH ASTK ltac:(lia) AP ltac:(lia) LB 0 0). }
  assert (Y10 : L5.u32_at RSEGS MV2 p1 m).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p1 m AV1 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p1 i Pa0 Pa1 Pa4 Pa6 Hi)| lia| lia| exact U1]. }
  assert (Y11 : L5.u32_at RSEGS MV2 p2 n).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p2 n AV2 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p2 i Pb0 Pb1 Pb4 Pb6 Hi)| lia| lia| exact U2]. }
  assert (Y11b : L5.u64_at RSEGS MV2 p3 q).
  { apply (proj2 (L5A.u64_at_vis H2 M2 p3 q AV3 ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply (TP8 p3 i Pc0 Pc1 Pc4 Pc6 Hi)| lia| lia| exact U3]. }
  assert (Y12 : L5KA.zeros_at MV2 (p1 / 8 + 2147450880) 1).
  { apply PNAECH.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p1 AG1 ltac:(lia) SP1)|].
    pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13 : L5KA.zeros_at MV2 (p2 / 8 + 2147450880) 1).
  { apply PNAECH.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p2 AG2 ltac:(lia) SP2)|].
    pose proof (AVS2 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13b : L5KA.zeros_at MV2 (p3 / 8 + 2147450880) 1).
  { apply PNAECH.zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS8 p3 AG3 ltac:(lia) SP3)|].
    pose proof (AVS3 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  assert (BIN2 : In (B, 2 * SZ) LB2) by (left; reflexivity).
  assert (Y14 : L5KA.zeros_at MV2 ((B + SZ) / 8 + 2147450880) 5).
  { destruct QSH as (ZB & _). rewrite (PNAEK.sh_idx B SZ) by (clear - Q16 ESZ; lia). intros i Hi.
    assert (E8 : SZ / 8 = 5 * 2 ^ k) by (rewrite ESZ; apply PNAEK.d40).
    assert (AV : L5A.avis H2 (S B + SZ / 8 + i) 1).
    { apply (VBSH2 B (2 * SZ) _ 1 BIN2). intros j Hj. replace (S B + SZ / 8 + i + j) with (S B + (SZ / 8 + i + j)) by lia.
      apply PNAEK.sh_in; [lia| lia| lia|]. split; [lia|]. apply (Z.lt_le_trans _ (SZ / 8 + 5)); [lia|]. rewrite E8. replace (2 * SZ) with (40 * (2 * 2 ^ k)) by lia. rewrite PNAEK.d40. lia. }
    unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
    - replace (S B + SZ / 8 + i) with (S B + (SZ / 8 + i)) by lia. apply ZB. replace (2 * SZ) with (40 * (2 * 2 ^ k)) by lia. rewrite PNAEK.d40. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15 : L5.writable RSEGS MV2 (B + SZ) 40).
  { apply (proj2 (L5A.writable_vis H2 M2 (B + SZ) 40 (VBLK2 B (2 * SZ) (B + SZ) 40 BIN2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 B (2 * SZ)); [exact QDEF| lia| lia]| lia| lia]. }
  (* [comment removed for export] *)
  assert (TS : forall a v0, sp - 176 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  pose proof (TS (sp - 24) _ ltac:(lia) ltac:(lia) T24) as Z24.
  pose proof (TS (sp - 32) _ ltac:(lia) ltac:(lia) T32) as Z32.
  pose proof (TS (sp - 40) _ ltac:(lia) ltac:(lia) T40) as Z40.
  pose proof (TS (sp - 48) _ ltac:(lia) ltac:(lia) T48) as Z48.
  pose proof (TS (sp - 56) _ ltac:(lia) ltac:(lia) T56) as Z56.
  pose proof (TS (sp - 64) _ ltac:(lia) ltac:(lia) T64) as Z64.
  pose proof (TS (sp - 72) _ ltac:(lia) ltac:(lia) T72) as Z72.
  pose proof (TS (sp - 80) _ ltac:(lia) ltac:(lia) T80) as Z80.
  pose proof (TS (sp - 120) _ ltac:(lia) ltac:(lia) T120) as Z120.
  pose proof (TS (sp - 128) _ ltac:(lia) ltac:(lia) T128) as Z128.
  pose proof (TS (sp - 136) _ ltac:(lia) ltac:(lia) T136) as Z136.
  pose proof (TS (sp - 144) _ ltac:(lia) ltac:(lia) T144) as Z144.
  pose proof (TS (sp - 152) _ ltac:(lia) ltac:(lia) T152) as Z152.
  pose proof (TS (sp - 160) _ ltac:(lia) ltac:(lia) T160) as Z160.
  pose proof (TS (sp - 168) _ ltac:(lia) ltac:(lia) T168) as Z168.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 176)) by (rewrite CS2 by inl; exact sR2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 (sp - 80)) by (rewrite CS2 by inl; exact sR8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 NC) by (rewrite CS2 by inl; exact sR9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 (sp - 104)) by (rewrite CS2 by inl; exact sR18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (2 ^ k)) by (rewrite CS2 by inl; exact sR19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 (((sp - 80) / 8) + 2147450880)) by (rewrite CS2 by inl; exact sR20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact sR21).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact sR22).
  assert (J23 : getr R2 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS2 by inl; rewrite sR23; symmetry; apply Z_to_bv_bv_unsigned).
  LeanFeed.pfeed P (PNAECP.azcG_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | 54%nat => 2 ^ k | _ => 0 end)) ltac:(first [ftac | assumption | rewrite <- ?ESZ; first [ftac | assumption | lia]]).
  rewrite <- ESZ in P. destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8 & gR9 & gR10 & gR11 & gR12 & gR13 & gR14 & gR15 & gR16 & gR17 & gR18 & gR19 & gR20
                 & G176 & G168 & G152 & G144 & G136 & G128 & G120 & G96 & G88 & G104 & G8 & G16 & G24 & G32 & G40 & G48 & G56 & G64 & G72 & G80
                 & G208 & G200 & G192 & G184 & G160 & GS32 & GS24 & GS16 & GS0).
  clear Y0 Y1 Y2 Y3 Y4 Y5 Y7 Y8 Y9 Y10 Y11 Y12 Y13 Y14 Y15 TS Z8 Z16 Z24 Z32 Z40 Z48 Z56 Z64 Z72 Z80 Z120 Z128 Z136 Z144 Z152 Z160 Z168.
  set (W3 := fun a => (sp - 224 <= a < sp - 224 + 224) \/ (B + SZ + 0 <= a < B + SZ + 0 + 40)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw2 M2 model2 fx2 fx3 R2 0xad5f8 R3 0x7ba7c M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; right; exact X| intros X; apply N; left; exact X]. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [|lia]. unfold aclientw, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  pose proof AM3 as (Mh3 & MI3).
  assert (ASTK3 : L5CA.astk ar M3 sp 12288) by (apply (L5SAR.astk_grows ar M2 M3 sp 12288 ASTK2 MGM3)).
  (* [comment removed for export] *)
  assert (BIN2b : In (b, SZ) LB2) by (right; exact BIN).
  assert (BANN' : HAJ.ann_shadow M b SZ SZ).
  { unfold PMSPA.annA in BANN. rewrite LENz in BANN. exact BANN. }
  assert (ANN3 : HAJ.ann_shadow M3 b SZ SZ).
  { apply (PNAEK.ann_agree M M3 b SZ SZ); [| lia| lia| exact BANN'].
    intros j Hj. pose proof (PNAEK.shadow_lowU b SZ j ltac:(lia) ltac:(lia) Hj) as SL.
    rewrite FR3; [| lia| unfold W3; intros [XW|XW]; [lia| destruct Q5 as (_ & [YW|YW] & _); lia]].
    apply T20; [lia| | lia]. unfold aclient, aclient_g. do 6 right. exists (b, SZ). split; [exact BIN| cbn [fst snd]; apply PNAEK.sh_in; lia]. }
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx3 R3 M3 model3 LB2 FF LK cr2 Aw2 K b SZ SZ SZ); clear ANN.
  { exact HH3. }
  { exact Mh3. }
  { exact MI3. }
  { rewrite L5K.rl10. exact gR10. }
  { rewrite L5K.rl11. exact gR11. }
  { rewrite L5K.rl12. exact gR12. }
  { rewrite L5K.rl13. exact gR13. }
  { exact BIN2b. }
  { exact B16. }
  { lia. }
  { lia. }
  { exact ANN3. }
  { rewrite L5K.rl4, (KS3 4%nat) by inl. rewrite CS2 by inl. rewrite (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, gR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, gR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M3 M3 sp 12288 208 2304 ASTK3 (fun x X => X)); [lia| lia| lia|].
    replace (sp - 208) with (sp + (-13) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx4 R4 M4 model4 Aw4 RP4 ANN4 KEEP4 DSH4 SCR4 MRT4 INC4 MI4 HH4.
  rewrite L5K.rl2, gR2, L5.unsigned_lit in KEEP4, SCR4 by lia. rewrite L5K.rl1, gR1.
  assert (AM4 : L5CA.amodel_ok Aw4 model4) by (split; [rewrite (L5LZ.model_rt_halted model3 model4 MRT4); exact Mh3| exact MI4]).
  assert (CS4 : forall k0, In k0 L5SAR.cs_all -> getr R4 (reg k0) = getr R3 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R3 R4 k0 RP4 Hk)).
  assert (ASTK4 : L5CA.astk ar M4 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw2 M3 M3 M4 _ sp 12288 (sp - 208) 2304 HH3 ASTK3 (fun x X => X)).
    - intros a Ha Hs Hns. apply KEEP4; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR4.
    - lia. - lia. - lia. }
  assert (T43 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2512 <= a < sp - 208) -> ~ in_shadow_of b SZ a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. apply KEEP4; [exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. }
  assert (T42 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2512 <= a < sp) -> ~ in_shadow_of b SZ a -> ~ (B + SZ <= a < B + SZ + 40) -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2 N3. rewrite T43; [| exact Ha| exact Hc| lia| exact N2]. apply FR3; [exact Ha| unfold W3; lia]. }
  (* [comment removed for export] *)
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB2 FF LK cr2 Aw4 M4 model4 HH4) as (HOFF4 & VIS4 & VIMG4 & VFS4 & VBLK4 & VBSH4 & VFSSH4 & VSTSH4).
  set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB2 FF LK cr2 Aw4 M4 model4 v 24 sp 12288 HH4 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & OVIS4 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH4) as ST4. rewrite (L5A.aly_segs L C LYa) in ST4.
  pose proof (L5A.statics_facts L C M4 LYa ST4) as (GOT4 & CSB4 & CUAR4 & _).
  assert (HHb : ri_inv HI ((b, SZ) :: LBX) FF LK cr Aw M (vml_of model)) by (unfold LB, PNM.bvec_own, PNM.BSZ in HH; rewrite <- ESZ in HH; exact HH).
  assert (CL4 : forall a, aclient L ar LBX FF 0 0 a -> aclient L ar LB2 FF 0 0 a /\ aclient L ar LB FF 0 0 a).
  { intros a Hc. assert (X : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF 0 0 a Hc)).
    split; [apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a X)| exact X]. }
  assert (CHAIN4 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. destruct (CL4 a Hc) as (Hc2 & Hc1).
           assert (NB : ~ (B <= a < B + 2 * SZ)) by (exact (PNAEK.own_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw2 M2 _ HH2 a 0 0 Hc1)).
           assert (NS : ~ in_shadow_of b SZ a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok b SZ LBX FF LK cr Aw M _ HHb ltac:(lia) a 0 0 Hc)).
           rewrite T43; [| exact Ha| exact Hc2| lia| exact NS].
           rewrite FR3; [| exact Ha| unfold W3; lia]. apply T20; [exact Ha| exact Hc1| lia]. }
  assert (BASE4 : PMSTA.base_okA RSEGS PMA.AD M4). { assert (EK04 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M4).
           { intros a (Ha & Hc & Ho).
             assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc)).
             destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
               (apply CHAIN4; [exact Ha| exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc)| lia| intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]]). }
           apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M4 EK04); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  pose proof BASE4 as (ICB4 & _). cbn [pa_rw_lo PMA.AD ADDR_A] in ICB4.
  assert (Z0' : L5.img_clear MV4 65536 1282048) by (apply L5A.img_clear_mrestrict; exact ICB4).
  assert (Z1' : L5.u64_at RSEGS MV4 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H4 M4 1309752 2147450880 (VIMG4 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB4).
  assert (Z2' : L5.u32_at RSEGS MV4 1309760 1) by (apply (proj2 (L5A.u32_at_vis H4 M4 1309760 1 (VIMG4 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR4).
  assert (Z3' : L5.writable RSEGS MV4 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H4 M4 (sp - 4096) 4096 (VIS4 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M4 sp 12288); [exact ASTK4| lia| lia| lia]. }
  assert (STKSH4 : shadow_zero M4 (sp - 12288) 1536).
  { intros j Hj. pose proof (PNAECH.S_add8 (sp - 12288) j) as E. pose proof (PNAECH.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T42; [rewrite <- E; apply STKSH2; exact Hj| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia| apply (PNAEK.sh_apart b SZ); lia| lia]. }
  assert (Z4' : L5KA.zeros_at MV4 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4). apply (PNAECH.stack_zeros12 M4 sp STKSH4 A16). exact Hi.
    assert (AV : L5A.avis H4 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH4 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (ACCV4 : PMSPA.accA M4 v 24).
  { apply (PMFA.accA_agree M2 M4 v 24); [| exact ACCV2]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx. apply T42; [lia| | lia| apply (PNAEK.sh_apart b SZ x); lia| lia].
    exact (PNAEK.frame_sh_client L ar FF v 24 x LB2 0 0 AOV Hx). }
  assert (Z5' : L5KA.zeros_at MV4 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB2 FF LK cr2 Aw4 M4 model4 v 24 HH4 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV4). }
  assert (TV4 : forall a, v <= a < v + 24 -> M4 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite T42; [apply TV; lia| lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia| | lia].
    intros X. pose proof (PNAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct OBIG as [YW|YW]; lia. }
  assert (Z7' : L5.u64_at RSEGS MV4 v b).
  { apply (proj2 (L5A.u64_at_vis H4 M4 v b ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact VB]. }
  assert (Z8' : L5.u64_at RSEGS MV4 (v + 8) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact VE]. }
  assert (Z9' : L5.u64_at RSEGS MV4 (v + 16) (b + SZ)).
  { apply (proj2 (L5A.u64_at_vis H4 M4 (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS4| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M4); [intros i Hi; apply TV4; lia| lia| lia| exact VC]. }
  assert (SHB4 : forall j, 0 <= j < (2 * SZ) / 8 -> M4 (Z_to_bv 64 (S B + j)) = M2 (Z_to_bv 64 (S B + j))).
  { intros j Hj. pose proof (PNAECH.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. apply T42; [lia| | lia| | ].
    - unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; apply PNAEK.sh_in; lia].
    - intros X. unfold in_shadow_of in X. pose proof (PNAEK.sh_in B (2 * SZ) j ltac:(clear - Q16; lia) ltac:(clear - ESZ; lia) ltac:(clear - Q0; lia) Hj) as Y. unfold in_shadow_of in Y.
      clear - X Y bB Bq0 Q0 B16 Q16. unfold S, SB in *. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
    - intros X. destruct Q5 as (_ & [YW|YW] & _); lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (QSH4 : shadow_zero M4 B (2 * SZ / 8)).
  { destruct QSH as (ZB & _). intros j Hj. unfold byte_at. rewrite SHB4 by exact Hj. apply ZB. exact Hj. }
  assert (Y14' : L5KA.zeros_at MV4 ((B + SZ) / 8 + 2147450880) 5).
  { rewrite (PNAEK.sh_idx B SZ) by (clear - Q16 ESZ; lia). intros i Hi.
    assert (E8 : SZ / 8 = 5 * 2 ^ k) by (rewrite ESZ; apply PNAEK.d40).
    assert (E16 : 2 * SZ / 8 = 10 * 2 ^ k) by (replace (2 * SZ) with (40 * (2 * 2 ^ k)) by lia; rewrite PNAEK.d40; lia).
    assert (AV : L5A.avis H4 (S B + SZ / 8 + i) 1).
    { apply (VBSH4 B (2 * SZ) _ 1 BIN2). intros j Hj. replace (S B + SZ / 8 + i + j) with (S B + (SZ / 8 + i + j)) by lia.
      apply PNAEK.sh_in; [lia| lia| lia| lia]. }
    unfold MV4. rewrite (AsanAcct.mrestrict_visible H4 M4).
    - replace (S B + SZ / 8 + i) with (S B + (SZ / 8 + i)) by lia. apply QSH4. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (BDEF4 : L5.defined M4 B (2 * SZ)).
  { intros i Hi. rewrite T43; [apply (L5.defined_grows M2 M3 _ _ MGM3 QDEF i Hi)| lia| | lia|].
    - unfold aclient, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia].
    - intros X. pose proof (PNAEK.in_shadow_range b SZ (B + i) ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
  assert (Y15' : L5.writable RSEGS MV4 (B + SZ) 40).
  { apply (proj2 (L5A.writable_vis H4 M4 (B + SZ) 40 (VBLK4 B (2 * SZ) (B + SZ) 40 BIN2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M4 B (2 * SZ)); [exact BDEF4| lia| lia]| lia| lia]. }
  assert (TS4 : forall a v0, sp - 208 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M3v a v0 -> L5.u64_at RSEGS MV4 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H4 M4 a v0 (VIS4 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M3); [intros i Hi; apply T43; [lia| apply L5SAR.stack_client; lia| lia|]| lia| lia|].
    - intros XS. pose proof (PNAEK.in_shadow_range b SZ i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply VIS2; lia| lia| lia| exact X]. }
  pose proof (TS4 (sp - 8) _ ltac:(lia) ltac:(lia) G8) as V8x.
  pose proof (TS4 (sp - 16) _ ltac:(lia) ltac:(lia) G16) as V16x.
  pose proof (TS4 (sp - 24) _ ltac:(lia) ltac:(lia) G24) as V24x.
  pose proof (TS4 (sp - 32) _ ltac:(lia) ltac:(lia) G32) as V32x.
  pose proof (TS4 (sp - 40) _ ltac:(lia) ltac:(lia) G40) as V40x.
  pose proof (TS4 (sp - 48) _ ltac:(lia) ltac:(lia) G48) as V48x.
  pose proof (TS4 (sp - 56) _ ltac:(lia) ltac:(lia) G56) as V56x.
  pose proof (TS4 (sp - 64) _ ltac:(lia) ltac:(lia) G64) as V64x.
  pose proof (TS4 (sp - 72) _ ltac:(lia) ltac:(lia) G72) as V72x.
  pose proof (TS4 (sp - 80) _ ltac:(lia) ltac:(lia) G80) as V80x.
  pose proof (TS4 (sp - 88) _ ltac:(lia) ltac:(lia) G88) as V88x.
  pose proof (TS4 (sp - 96) _ ltac:(lia) ltac:(lia) G96) as V96x.
  pose proof (TS4 (sp - 104) _ ltac:(lia) ltac:(lia) G104) as V104x.
  pose proof (TS4 (sp - 120) _ ltac:(lia) ltac:(lia) G120) as V120x.
  pose proof (TS4 (sp - 128) _ ltac:(lia) ltac:(lia) G128) as V128x.
  pose proof (TS4 (sp - 136) _ ltac:(lia) ltac:(lia) G136) as V136x.
  pose proof (TS4 (sp - 144) _ ltac:(lia) ltac:(lia) G144) as V144x.
  pose proof (TS4 (sp - 152) _ ltac:(lia) ltac:(lia) G152) as V152x.
  pose proof (TS4 (sp - 168) _ ltac:(lia) ltac:(lia) G168) as V168x.
  pose proof (TS4 (sp - 176) _ ltac:(lia) ltac:(lia) G176) as V176x.
  pose proof (TS4 (sp - 160) _ ltac:(lia) ltac:(lia) G160) as V160x.
  pose proof (TS4 (sp - 184) _ ltac:(lia) ltac:(lia) G184) as V184x.
  pose proof (TS4 (sp - 192) _ ltac:(lia) ltac:(lia) G192) as V192x.
  pose proof (TS4 (sp - 200) _ ltac:(lia) ltac:(lia) G200) as V200x.
  pose proof (TS4 (sp - 208) _ ltac:(lia) ltac:(lia) G208) as V208x.
  assert (K2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 208)) by (rewrite CS4 by inl; exact gR2).
  assert (K8 : getr R4 (reg 8) = Z_to_bv 64 (sp - 104)) by (rewrite CS4 by inl; exact gR8).
  assert (K9 : getr R4 (reg 9) = Z_to_bv 64 v) by (rewrite CS4 by inl; exact gR9).
  assert (K18 : getr R4 (reg 18) = Z_to_bv 64 p3) by (rewrite CS4 by inl; exact gR18).
  assert (K19 : getr R4 (reg 19) = Z_to_bv 64 p2) by (rewrite CS4 by inl; exact gR19).
  assert (K20 : getr R4 (reg 20) = Z_to_bv 64 p1) by (rewrite CS4 by inl; exact gR20).
  assert (K21 : getr R4 (reg 21) = Z_to_bv 64 2147450880) by (rewrite CS4 by inl; rewrite (KS3 21%nat) by inl; exact J21).
  assert (K22 : getr R4 (reg 22) = Z_to_bv 64 2147450880) by (rewrite CS4 by inl; rewrite (KS3 22%nat) by inl; exact J22).
  assert (K23 : getr R4 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS4 by inl; rewrite (KS3 23%nat) by inl; exact J23).
  assert (V192y : L5.u64_at RSEGS MV4 (sp - 192) (bv_unsigned (getr R4 (reg 24)))) by (rewrite CS4 by inl; rewrite (KS3 24%nat) by inl; exact V192x).
  LeanFeed.pfeed P (PNAECP.azcH_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 36%nat => b | 38%nat => m | 39%nat => n | 40%nat => B | 42%nat => NC | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | 52%nat => p3 | 53%nat => q | 54%nat => 2 ^ k | _ => 0 end)) ltac:(first [ftac | assumption | rewrite <- ?ESZ; first [ftac | assumption | lia | (rewrite !Z.mod_small by lia; lia)]]).
  rewrite <- ESZ in P. destruct P as (fx5 & R5 & M5v & MG5 & _ & FZ5 & MS5 & KS5 & hR1 & hR2 & hR10 & hR11 & hR12 & hR13 & hR14 & hR18 & hR19 & hR20 & hR22 & hR23 & hR24
                 & H8 & H16 & H24 & H32 & H40 & H48 & H56 & H64 & H72 & H120 & H128 & H136 & H144 & H152 & H104 & H96 & H88 & H80 & H160 & H168 & H176).
  clear Z0' Z1' Z2' Z3' Z4' Z5' Z7' Z8' Z9' Y14' Y15' TS4 V8x V16x V24x V32x V40x V48x V56x V64x V72x V80x V88x V96x V104x V120x V128x V136x V144x V152x V160x V168x V176x V192y V200x V208x.
  assert (KC' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10) by lia.
  assert (hR10' : getr R5 (reg 10) = Z_to_bv 64 B) by (rewrite hR10; edB KC').
  assert (hR20' : getr R5 (reg 20) = Z_to_bv 64 B) by (rewrite hR20; edB KC').
  clear hR10 hR20 hR13.
  set (W5 := fun a => sp - 176 <= a < sp - 176 + 176).
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK cr2 Aw4 M4 model4 fx4 fx5 R4 0xab864 R5 0x77c94 M5v W5 K HH4 AM4 MS5 MG5).
  { intros a Ha N. apply FZ5; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W5 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
  pose proof AM5 as (Mh5 & MI5).
  assert (ASTK5 : L5CA.astk ar M5 sp 12288) by (apply (L5SAR.astk_grows ar M4 M5 sp 12288 ASTK4 MGM5)).
  (* [comment removed for export] *)
  assert (TB5 : forall a, b <= a < b + SZ -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite FR5; [| lia| unfold W5; lia].
    assert (Ca : forall LBz, In (b, SZ) LBz -> aclient L ar LBz FF 0 0 a) by (intros LBz Hin; unfold aclient, aclient_g; left; exists (b, SZ); split; [exact Hin| cbn [fst snd]; lia]).
    rewrite T43; [| lia| apply Ca; exact BIN2b| lia|].
    2:{ intros X. pose proof (PNAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct Bq6 as [YW|YW]; lia. }
    rewrite FR3; [| lia| unfold W3; lia]. apply T20; [lia| apply Ca; exact BIN| lia]. }
  assert (BDEF5 : L5.defined M5 b SZ).
  { intros i Hi. rewrite TB5 by lia. apply BDEF. exact Hi. }
  destruct (PMCG.rdn_some RSEGS M5 (Z.to_nat SZ) b ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)) as (bs & RDN & Lbs).
  { intros i Hi. rewrite Z2Nat.id in Hi by lia. apply BDEF5. lia. }
  (* [comment removed for export] *)
  pose proof (HAJ.aior_memcpy _ _ _ _ _ HIok) as MCP. unfold amemcpy_spec, amemcpy_spec_at, amem_pre, amem_post in MCP.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memcpy L C LYa), (L5A.aly_scr_mem L C LYa) in MCP.
  assert (U160 : bv_unsigned (getr R5 2%bv) = sp - 192) by (rewrite L5K.rl2, hR2; apply L5.unsigned_lit; lia).
  assert (QSH5 : shadow_zero M5 B (2 * SZ / 8)).
  { intros j Hj. pose proof (PNAECH.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at. rewrite FR5; [apply QSH4; exact Hj| lia| unfold W5; lia]. }
  assert (BSH5 : shadow_zero M5 b (SZ / 8)).
  { destruct ANN4 as (ZA4 & _). intros j Hj. pose proof (PNAECH.shadow_low b SZ j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at. rewrite FR5; [apply ZA4; exact Hj| lia| unfold W5; lia]. }
  apply (MCP fx5 R5 M5 model5 LB2 FF LK cr2 Aw4 B b SZ bs K); clear MCP.
  { split; [exact HH5|]. split; [exact Mh5|]. split; [exact MI5|].
    split; [rewrite L5K.rl10; exact hR10'|]. split; [rewrite L5K.rl12; exact hR12|]. split; [lia|].
    split; [rewrite L5K.rl4, (KS5 4%nat) by inl; rewrite CS4 by inl; rewrite (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    split; [rewrite L5K.rl1, hR1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; reflexivity|].
    split. { rewrite U160. apply (L5SAR.astack_ok_of_astk L ar C LYa M5 M5 sp 12288 192 2560 ASTK5 (fun x X => X)); [lia| lia| lia|].
             replace (sp - 192) with (sp + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
    split. { apply (L5CB.aacc_of_zero M5 B (2 * SZ / 8) B SZ QSH5); [lia| lia| lia|]. replace (2 * SZ) with (40 * (2 * 2 ^ k)) by lia. rewrite PNAEK.d40. lia. }
    split. { intros i Hi. rewrite U160. unfold aclientw, aclient_g. left. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; lia]. }
    split. { intros i m0 Hi Hm. apply (L5C.writable_of_defined RSEGS M5 B (2 * SZ)); [apply (L5.defined_grows M4 M5 _ _ MGM5); exact BDEF4| lia| lia| lia| lia]. }
    split; [exact K0|]. unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. destruct Q5 as (_ & [YW|YW] & _); lia. }
  { rewrite L5K.rl11. exact hR11. }
  { apply (L5CB.aacc_of_zero M5 b (SZ / 8) b SZ BSH5); [lia| lia| lia|]. rewrite ESZ, PNAEK.d40. lia. }
  { lia. }
  { unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI. destruct Bq6 as [YW|YW]; lia. }
  { intros i Hi. right. rewrite U160. unfold aclient, aclient_g. left. exists (b, SZ). split; [exact BIN2b| cbn [fst snd]; lia]. }
  { exact RDN. }
  { intros _; lia. }
  intros R6 M6 model6 mR10 RP6 BYTES PRES6 SDEF6 RT6 MI6 HH6. rewrite U160 in PRES6, SDEF6. rewrite L5K.rl1, hR1.
  assert (Mh6 : m_halted model6 = None) by (rewrite (L5LZ.model_rt_halted _ _ RT6); exact Mh5).
  assert (CS6 : forall k0, In k0 L5SAR.cs_all -> getr R6 (reg k0) = getr R5 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R5 R6 k0 RP6 Hk)).
  assert (ASTK6 : L5CA.astk ar M6 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB2 FF LK cr2 Aw4 M5 M5 M6 _ sp _ (sp - 192) 2560 HH5 ASTK5 (fun x X => X)).
    - intros a Ha Hs Hns. apply PRES6. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
    - exact SDEF6.
    - lia. - lia. - lia. }
  (* [comment removed for export] *)
  assert (COPY : forall i, 0 <= i < SZ -> M5 (Z_to_bv 64 (b + i)) <> None /\ M6 (Z_to_bv 64 (B + i)) = M5 (Z_to_bv 64 (b + i))).
  { intros i Hi. split; [apply BDEF5; lia|]. destruct (BYTES i Hi) as (w & (Ew & Rw) & Bw). unfold byte_at in Bw. rewrite Bw.
    pose proof (PNAEK.rdn_nth RSEGS M5 (Z.to_nat SZ) b bs RDN (Z.to_nat i) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    rewrite (X ltac:(apply BDEF5; lia)). symmetry. exact Ew. }
  (* [comment removed for export] *)
  apply (KONT fx5 R6 M6 model6 Aw4 B).
  unfold PNAECGS.gmid, PNAECGS.SZ. rewrite <- ESZ.
  assert (T65 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB2 FF 0 0 a -> ~ (sp - 2752 <= a < sp) -> ~ (B <= a < B + SZ) -> M6 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite PRES6; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc| lia]| exact N2]. apply FR5; [exact Ha| unfold W5; lia]. }
  assert (TS6 : forall a v0, sp - 192 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M5v a v0 -> L5.u64_at RSEGS M6 a v0).
  { intros a v0 Ha Ha' X. apply (L5C.u64_at_agree RSEGS M5); [intros i Hi; apply PRES6; [lia| apply L5SAR.stack_client; lia| lia]| lia| lia|].
    apply (PMAIS1.vis_u64 _ _ _ _ _ VIS5); [apply VIS4; lia| lia| lia| exact X]. }
  split; [rewrite CS6 by inl; exact hR2|]. split; [rewrite CS6 by inl; rewrite (KS5 8%nat) by inl; exact K8|].
  split; [rewrite CS6 by inl; rewrite (KS5 9%nat) by inl; exact K9|]. split; [rewrite CS6 by inl; exact hR18|].
  split; [rewrite CS6 by inl; exact hR19|]. split; [rewrite CS6 by inl; exact hR20'|].
  split; [rewrite CS6 by inl; rewrite (KS5 21%nat) by inl; exact K21|]. split; [rewrite CS6 by inl; exact hR22|].
  split; [rewrite CS6 by inl; exact hR23|]. split; [rewrite CS6 by inl; exact hR24|].
  split. { intros x Hx. assert (Y : In x L5SAR.cs_all /\ In x PNAECP.KS_azcH /\ In x PNAECP.KS_azcG /\ In x PNAECP2.KS_azcS0)
             by (destruct Hx as [<-|[<-|[<-|[<-|[<-|[]]]]]]; (split; [inl| split; [inl| split; inl]])).
           destruct Y as (Yk1 & Yk2 & Yk3 & Yk4). rewrite (CS6 x Yk1), (KS5 x Yk2), (CS4 x Yk1), (KS3 x Yk3), (CS2 x Yk1), (KS1 x Yk4). reflexivity. }
  split; [apply (TS6 (sp - 8) _ ltac:(lia) ltac:(lia) H8)|].
  split; [apply (TS6 (sp - 16) _ ltac:(lia) ltac:(lia) H16)|].
  split; [apply (TS6 (sp - 24) _ ltac:(lia) ltac:(lia) H24)|].
  split; [apply (TS6 (sp - 32) _ ltac:(lia) ltac:(lia) H32)|].
  split; [apply (TS6 (sp - 40) _ ltac:(lia) ltac:(lia) H40)|].
  split; [apply (TS6 (sp - 48) _ ltac:(lia) ltac:(lia) H48)|].
  split; [apply (TS6 (sp - 56) _ ltac:(lia) ltac:(lia) H56)|].
  split; [apply (TS6 (sp - 64) _ ltac:(lia) ltac:(lia) H64)|].
  split; [apply (TS6 (sp - 184) _ ltac:(lia) ltac:(lia)); apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply FZ5; lia| lia| lia| exact V184x]|].
  split; [rewrite <- (KS1 24%nat), <- (CS2 24%nat) by inl; apply (TS6 (sp - 192) _ ltac:(lia) ltac:(lia)); apply (L5C.u64_at_agree RSEGS MV4 M5v); [intros i Hi; apply FZ5; lia| lia| lia| exact V192x]|].
  split; [apply (TS6 (sp - 120) _ ltac:(lia) ltac:(lia) H120)|].
  split; [apply (TS6 (sp - 128) _ ltac:(lia) ltac:(lia) H128)|].
  split; [apply (TS6 (sp - 136) _ ltac:(lia) ltac:(lia) H136)|].
  split; [apply (TS6 (sp - 144) _ ltac:(lia) ltac:(lia) H144)|].
  split; [apply (TS6 (sp - 152) _ ltac:(lia) ltac:(lia) H152)|].
  split; [apply (TS6 (sp - 160) _ ltac:(lia) ltac:(lia) H160)|].
  split; [apply (TS6 (sp - 168) _ ltac:(lia) ltac:(lia) H168)|].
  split; [apply (TS6 (sp - 176) _ ltac:(lia) ltac:(lia) H176)|].
  split; [apply (TS6 (sp - 104) _ ltac:(lia) ltac:(lia) H104)|].
  split; [apply (TS6 (sp - 96) _ ltac:(lia) ltac:(lia) H96)|].
  split; [replace (B + (SZ + 40)) with (B + SZ + 40) by lia; apply (TS6 (sp - 88) _ ltac:(lia) ltac:(lia) H88)|].
  split; [replace (B + 2 * SZ) with (B + 40 * NC) by lia; apply (TS6 (sp - 80) _ ltac:(lia) ltac:(lia) H80)|].
  split; [apply (TS6 (sp - 72) _ ltac:(lia) ltac:(lia) H72)|].
  assert (TV6 : forall a, v <= a < v + 24 -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite T65; [apply TV4; lia| lia| apply (L5SAR.obj_client L ar LB2 FF 0 0 v 24 a AOB); lia| lia| lia]. }
  split; [apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact VB]|].
  split; [apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact VE]|].
  split; [apply (L5C.u64_at_agree RSEGS M M6); [intros i Hi; apply TV6; lia| lia| lia| exact VC]|].
  split. { apply (PMFA.accA_agree M4 M6 v 24); [| exact ACCV4]. intros x Hx. pose proof (PNAECH.S_range x ltac:(lia)) as SRx. apply T65; [lia| | lia| destruct Q5 as (_ & [YW|YW] & _); lia].
           exact (PNAEK.frame_sh_client L ar FF v 24 x LB2 0 0 AOV Hx). }
  split; [lia|]. split; [lia|]. split; [exact Q16|]. split; [unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI; exact Q5|]. split; [exact Q1|].
  split; [exact bB|]. split; [exact VBf|].
  assert (BDEF6 : L5.defined M6 B (2 * SZ)).
  { intros i Hi. destruct (Z_lt_le_dec i SZ) as [Li|Li].
    - destruct (COPY i ltac:(lia)) as (D5 & E6). rewrite E6. exact D5.
    - rewrite T65; [apply BDEF4; exact Hi| lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia| lia]. }
  split; [exact BDEF6|].
  split. { intros j Hj. pose proof (PNAECH.shadow_low B (2 * SZ) j ltac:(lia) ltac:(lia) Hj) as SL. unfold byte_at.
           rewrite PRES6; [apply QSH5; exact Hj| lia| | destruct Q5 as (_ & [YW|YW] & _); lia].
           unfold aclient, aclient_g. do 6 right. exists (B, 2 * SZ). split; [exact BIN2| cbn [fst snd]; apply PNAEK.sh_in; lia]. }
  split. { intros i Hi. assert (Hi' : 40 * Z.of_nat i + 40 <= SZ) by lia.
           apply (PNAEK.bstate_copy RSEGS M5 M6 (b + 40 * Z.of_nat i) (B + 40 * Z.of_nat i)).
           - intros j Hj. replace (b + 40 * Z.of_nat i + j) with (b + (40 * Z.of_nat i + j)) by lia. replace (B + 40 * Z.of_nat i + j) with (B + (40 * Z.of_nat i + j)) by lia. apply COPY. lia.
           - apply (PNMF.bstate_at_agree RSEGS M M5); [lia| lia| intros x Hx; apply TB5; lia| apply BST; exact Hi]. }
  split. { assert (AVB : forall a n0, B <= a -> a + n0 <= B + 2 * SZ -> L5A.avis (ahid Aw2 model2) a n0) by (intros a n0 Ya1 Ya2; apply (VBLK2 B (2 * SZ) a n0 BIN2); lia).
           assert (TSL : forall a, B + SZ <= a < B + SZ + 40 -> M6 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
           { intros a Ha. rewrite T65; [| lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia| lia].
             apply T43; [lia| unfold aclient, aclient_g; left; exists (B, 2 * SZ); split; [exact BIN2| cbn [fst snd]; lia]| lia|].
             intros X. pose proof (PNAEK.in_shadow_range b SZ a ltac:(lia) ltac:(lia) X). destruct Q5 as (_ & [YW|YW] & _); lia. }
           assert (SDEF8 : L5.defined M6 (B + SZ + 8) 8) by (apply (L5.defined_sub M6 B (2 * SZ)); [exact BDEF6| lia| lia]).
           destruct (PMCG.u64_of_defined RSEGS M6 (B + SZ + 8) ltac:(lia) ltac:(lia) SDEF8) as (lenv & LV & GS8).
           exists lenv. split; [exact LV|].
           unfold PNM.bstate_at. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
           split; [apply (PMF.u32_at_agree RSEGS M3 M6); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u32 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS0]]|].
           split; [exact GS8|].
           split; [apply (L5C.u64_at_agree RSEGS M3 M6); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS16]]|].
           split; [apply (L5C.u8_at_agree RSEGS M3 M6); [intros i Hi; apply TSL; lia| lia| lia| apply (PNAECH.vis_u8 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS24]]|].
           apply (L5C.u64_at_agree RSEGS M3 M6); [intros i Hi; apply TSL; lia| lia| lia| apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact GS32]]. }
  split; [exact HH6|]. split; [split; [exact Mh6| exact MI6]|].
  split. { apply (L5LZ.model_rt_trans model model5 model6); [|exact RT6]. apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5].
           apply (L5LZ.model_rt_trans model model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3].
           apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2]. }
  split; [intros x Hx; apply INC4; apply IA2; exact Hx|]. split; [exact ASTK6|].
  split. { intros j Hj. pose proof (PNAECH.S_add8 (sp - 12288) j) as E. pose proof (PNAECH.S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
           unfold byte_at. rewrite E. rewrite PRES6; [| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia].
           rewrite FR5; [rewrite <- E; apply STKSH4; exact Hj| lia| unfold W5; lia]. }
  assert (CL : forall a, aclient L ar LBX FF 0 0 a -> aclient L ar LB2 FF 0 0 a /\ aclient L ar LB FF 0 0 a).
  { intros a Hc. assert (X : aclient L ar LB FF 0 0 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF 0 0 a Hc)).
    split; [apply (L5SAR.aclient_consb L ar LB FF (B, 2 * SZ) 0 0 a X)| exact X]. }
  assert (CHAIN6 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LBX FF 0 0 a -> ~ (sp - 12288 <= a < sp) -> ~ (v <= a < v + 24) -> M6 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. destruct (CL a Hc) as (Hc2 & Hc1).
           assert (NB : ~ (B <= a < B + 2 * SZ)) by (exact (PNAEK.own_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw2 M2 _ HH2 a 0 0 Hc1)).
           assert (NS : ~ in_shadow_of b SZ a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok b SZ LBX FF LK cr Aw M _ HHb ltac:(lia) a 0 0 Hc)).
           rewrite T65; [| exact Ha| exact Hc2| lia| lia]. rewrite T43; [| exact Ha| exact Hc2| lia| exact NS].
           rewrite FR3; [| exact Ha| unfold W3; lia]. apply T20; [exact Ha| exact Hc1| lia]. }
  split. { assert (EK06 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M6).
           { intros a (Ha & Hc & Ho).
             assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc)).
             destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
               (apply CHAIN6; [exact Ha| exact (L5SAR.aclient_00 L ar LBX FF sp 12288 a Hc)| lia| intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]]). }
           apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M6 EK06); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  split; [exact CHAIN6|].
  intros a Ha Hc HM. destruct (CL a Hc) as (Hc2 & Hc1).
  assert (NS : ~ in_shadow_of b SZ a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok b SZ LBX FF LK cr Aw M _ HHb ltac:(lia) a 0 0 Hc)).
  destruct (L5SAR.rng_dec a (B) (B + SZ)) as [IB|NB].
  - exfalso. exact (PNAEK.own_notclient L ar C HI LY HIok B (2 * SZ) LB FF LK cr2 Aw2 M2 _ HH2 a 0 0 Hc1 ltac:(lia)).
  - destruct (L5SAR.rng_dec a (sp - 12288) sp) as [IW|NW].
    + pose proof ASTK6 as (_ & _ & _ & _ & SD6 & _). replace a with (sp - 12288 + (a - (sp - 12288))) by lia. apply SD6. lia.
    + rewrite PRES6; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB2 FF 0 0); [exact Hc2| lia]| exact NB].
      apply MGM5. rewrite T43; [| exact Ha| exact Hc2| lia| exact NS]. apply MGM3. rewrite KEEP2; [| exact Ha| apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc1| lia]].
      apply MGM1. exact HM.
Qed.
End Stage.
End PNAECG1.
