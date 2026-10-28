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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnAIss1_b PnAEmbKit_b PnAEmbRP_b PnASrcKit_b Ba0_code_ac29c_ac2a0_b.
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
Module PNAERF.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
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
Lemma stk_sh_idx sp i : sp mod 16 = 0 -> 0 <= i < 512 -> sp / 8 + 2147450368 + i = S (sp - 4096 + 8 * i).
Proof. unfold S, SB. intros. Lia.lia. Qed.
Lemma d32 x : (32 * x) / 8 = 4 * x.
Proof. Lia.lia. Qed.
Lemma d32b x : (32 * x + 32) / 8 = 4 * x + 4.
Proof. Lia.lia. Qed.
Lemma pow2k k : 0 <= k <= 11 -> 1 <= 2 ^ k <= 2048.
Proof. intros Hk. split; [pose proof (Z.pow_pos_nonneg 2 k ltac:(Lia.lia) ltac:(Lia.lia)); Lia.lia|]. change 2048 with (2 ^ 11). apply Z.pow_le_mono_r; Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMA.EXT.
Let LYa := PMA.ly_as0 L C LY.

Theorem fast : forall (fx : FPState) R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q,
    ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PMA.AD L ar R M sp r 0 ->
    getr R (reg 10) = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M v b k stk -> Z.of_nat (length stk) < 2 ^ k ->
    getr R (reg 11) = Z_to_bv 64 p1 -> getr R (reg 12) = Z_to_bv 64 p2 -> getr R (reg 13) = Z_to_bv 64 p3 -> p1 mod 4 = 0 -> p2 mod 4 = 0 -> p3 mod 4 = 0 ->
    byte_at M (S p1) 0 -> byte_at M (S p2) 0 -> byte_at M (S p3) 0 ->
    PNAEK.argp (ar_sptop ar) FF sp v p1 4 -> PNAEK.argp (ar_sptop ar) FF sp v p2 4 -> PNAEK.argp (ar_sptop ar) FF sp v p3 4 ->
    L5.u32_at RSEGS M p1 m -> L5.u32_at RSEGS M p2 n -> L5.u32_at RSEGS M p3 q -> 0 <= m < 2 ^ 31 -> 0 <= n < 2 ^ 31 -> 0 <= q < 2 ^ 31 ->
    PMSTA.base_okA RSEGS PMA.AD M ->
    (forall (fx' : FPState) R' M' model' LK' Aw', regs_preserved R R' -> PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA M' v b k (stk ++ [PNM.BS m n q 0 0]) ->
        (v + 24 <= b \/ b + PNM.BSZ * 2 ^ k <= v) ->
        PMSPA.accA M' v 24 -> PMSTA.base_okA RSEGS PMA.AD M' -> L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v, 24)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PNM.bvec_own b k ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xacf40 M model) K.
Proof.
  intros fx R M model K LBX FF LK Aw cr v b k stk sp r p1 p2 p3 m n q HH AM K0 ENT A10 AOV V8 ACCV VEC LEN A11 A12 A13 P14 P24 P34 SP1 SP2 SP3 AG1 AG2 AG3 U1 U2 U3 RM RN RQ BASE KONT.
  unfold PNM.bvec_at, PNM.BSZ in VEC.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  destruct VEC as (VB & VE & VC & Kr & LENk & B16 & BDEF & BACC & BANN & BST).
  set (len := Z.of_nat (length stk)) in *.
  set (LB := PNM.bvec_own b k ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, 40 * 2 ^ k) LB) by (left; reflexivity).
  destruct (PNAEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (40 * 2 ^ k) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (pow2k k Kr) as P2K.
  pose proof (PMKA.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p1 4 HH ASTK ltac:(lia) AG1 ltac:(lia)) as (Pa0 & Pa1 & Pa2 & Pa3 & Pa4 & Pa5 & Pa6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p2 4 HH ASTK ltac:(lia) AG2 ltac:(lia)) as (Pb0 & Pb1 & Pb2 & Pb3 & Pb4 & Pb5 & Pb6).
  destruct (PNAEK.arg_facts L ar C HI LY HIok LB FF LK cr Aw M _ sp 12288 v p3 4 HH ASTK ltac:(lia) AG3 ltac:(lia)) as (Pc0 & Pc1 & Pc2 & Pc3 & Pc4 & Pc5 & Pc6).
  pose proof (Pa5 b (40 * 2 ^ k) BIN) as PaB. pose proof (Pb5 b (40 * 2 ^ k) BIN) as PbB. pose proof (Pc5 b (40 * 2 ^ k) BIN) as PcB.
  (* [comment removed for export] *)
  assert (VBLK : v + 24 <= b \/ b + 40 * 2 ^ k <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
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
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + 40 * len)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + 40 * 2 ^ k)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).
  assert (KB : 2 ^ k <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia). assert (LB40 : 0 <= 40 * len <= 163840) by (subst len; lia).
  LeanFeed.pfeed P (PNAERP.azrF1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 52%nat => p3 | 36%nat => b | 37%nat => 40 * len | 38%nat => m | 39%nat => n | 41%nat => b + 40 * 2 ^ k  | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR8 & fR9 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & fR17 & fR18 & fR19 & fR20 & fR21 & fR22 & fR23
                 & T72 & T64 & T56 & T48 & T40 & T32 & T24 & T16 & T8 & T80).
  set (W1 := fun a => sp - 128 <= a < sp - 128 + 128).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xacf40 R1 0x7ba7c M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 128 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).
  (* [comment removed for export] *)
  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMA.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMA.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (40 * 2 ^ k) (40 * len) (40 * len + 40)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12. exact fR12. }
  { rewrite L5K.rl13, fR13. f_equal. lia. }
  { exact BIN. }
  { exact B16. }
  { lia. }
  { lia. }
  { apply (PNAEK.ann_agree M M1 b (40 * len) (40 * 2 ^ k)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (shadow_low b (40 * 2 ^ k) j ltac:(lia) ltac:(lia) ltac:(clear -Hj P2K; Lia.lia)) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 80 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 80) with (sp + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2432 <= a < sp) -> ~ in_shadow_of b (40 * 2 ^ k) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 80) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 v 24 sp 12288 HH2 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }
  assert (STKSH2 : shadow_zero M2 (sp - 12288) 1536).
  { intros j Hj. pose proof (S_add8 (sp - 12288) j) as E.
    pose proof (S_range (sp - 12288 + 8 * j) ltac:(lia)) as SRj.
    unfold byte_at. rewrite E. rewrite T20; [rewrite <- E; apply STKSH; exact Hj| lia| apply (PNAEK.stack_sh_client L ar FF); lia| lia|].
    apply (PNAEK.sh_apart b (40 * 2 ^ k) (sp - 12288 + 8 * j)); lia. }
  assert (Y4 : L5KA.zeros_at MV2 (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2). apply (stack_zeros12 M2 sp STKSH2 A16). exact Hi.
    assert (AV : L5A.avis H2 (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH2 (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB. clear - SLO SHI A16 Hi Hj.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  assert (ACCV2 : PMSPA.accA M2 v 24).
  { apply (PMFA.accA_agree M M2 v 24); [| exact ACCV]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply T20; [lia| | lia|].
    - exact (PNAEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
    - apply (PNAEK.sh_apart b (40 * 2 ^ k) x); lia. }
  assert (Y5 : L5KA.zeros_at MV2 (v / 8 + 2147450880) 3).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 v 24 HH2 AOV V8 ltac:(lia) ltac:(reflexivity) ACCV2). }
  assert (TV : forall a, v <= a < v + 24 -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
    intros X. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia. }
  assert (Y6 : L5.writable RSEGS MV2 v 24).
  { apply (proj2 (L5A.writable_vis H2 M2 v 24 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
  assert (Y7 : L5.u64_at RSEGS MV2 v b).
  { apply (proj2 (L5A.u64_at_vis H2 M2 v b ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
  assert (Y8 : L5.u64_at RSEGS MV2 (v + 8) (b + 40 * len)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
  assert (Y9 : L5.u64_at RSEGS MV2 (v + 16) (b + 40 * 2 ^ k)).
  { apply (proj2 (L5A.u64_at_vis H2 M2 (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS2| lia| lia]) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M M2); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
  (* [comment removed for export] *)
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p1 4 HH2 ASTK2 ltac:(lia) AG1 ltac:(lia)) as (AV1 & AVS1).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p2 4 HH2 ASTK2 ltac:(lia) AG2 ltac:(lia)) as (AV2 & AVS2).
  destruct (PNAEK.arg_vis L ar C HI LY HIok LB FF LK cr Aw2 M2 model2 sp 12288 v p3 4 HH2 ASTK2 ltac:(lia) AG3 ltac:(lia)) as (AV3 & AVS3).
  assert (TP : forall p q' x, PNAEK.argp (ar_sptop ar) FF sp v p 4 -> (6905856 <= p /\ p + 4 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= p \/ p + 4 <= 2147446784)
             /\ (sp <= p \/ p + 4 <= ahl_ceil ar)) -> (forall i sp' scr', 0 <= i < 4 -> sp' <= sp -> aclient L ar LB FF sp' scr' (p + i)) ->
             (p + 4 <= b \/ b + 40 * 2 ^ k <= p) -> q' = p -> p <= x < p + 4 -> M2 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
  { intros p q' x AP (Q0 & Q1 & Q2 & Q3) CLp Bp Eq Hx. apply T20; [lia| replace x with (p + (x - p)) by lia; apply CLp; lia| lia|].
    intros X. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) x ltac:(lia) ltac:(lia) X). lia. }
  assert (TPS : forall p, PNAEK.argp (ar_sptop ar) FF sp v p 4 -> (p + 4 <= b \/ b + 40 * 2 ^ k <= p) -> 0 <= p < 2 ^ 47 -> byte_at M (S p) 0 -> byte_at M2 (S p) 0).
  { intros p AP Bp Hp X. pose proof (S_range p Hp) as SRp. unfold byte_at in *. rewrite T20; [exact X| lia| | lia|].
    - exact (PNAEK.arg_client L ar HI LB FF LK cr Aw M _ sp 12288 v p 4 HH ASTK ltac:(lia) AP ltac:(lia) LB 0 0).
    - apply (PNAEK.sh_apart b (40 * 2 ^ k) p); lia. }
  assert (Y10 : L5.u32_at RSEGS MV2 p1 m).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p1 m AV1 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p1 p1 i AG1 (conj Pa0 (conj Pa1 (conj Pa2 Pa4))) Pa6 PaB eq_refl Hi)| lia| lia| exact U1]. }
  assert (Y11 : L5.u32_at RSEGS MV2 p2 n).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p2 n AV2 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p2 p2 i AG2 (conj Pb0 (conj Pb1 (conj Pb2 Pb4))) Pb6 PbB eq_refl Hi)| lia| lia| exact U2]. }
  assert (Y11b : L5.u32_at RSEGS MV2 p3 q).
  { apply (proj2 (L5A.u32_at_vis H2 M2 p3 q AV3 ltac:(lia) ltac:(lia))).
    apply (PMF.u32_at_agree RSEGS M M2); [intros i Hi; apply (TP p3 p3 i AG3 (conj Pc0 (conj Pc1 (conj Pc2 Pc4))) Pc6 PcB eq_refl Hi)| lia| lia| exact U3]. }
  assert (Y12 : L5KA.zeros_at MV2 (p1 / 8 + 2147450880) 1).
  { apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p1 AG1 PaB ltac:(lia) SP1)|].
    pose proof (AVS1 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13 : L5KA.zeros_at MV2 (p2 / 8 + 2147450880) 1).
  { apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p2 AG2 PbB ltac:(lia) SP2)|].
    pose proof (AVS2 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y13b : L5KA.zeros_at MV2 (p3 / 8 + 2147450880) 1).
  { apply zsh1. unfold byte_at, MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact (TPS p3 AG3 PcB ltac:(lia) SP3)|].
    pose proof (AVS3 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  assert (TS : forall a v0, sp - 80 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMAIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
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
  (* [comment removed for export] *)
  assert (BDEF2 : L5.defined M2 b (40 * 2 ^ k)).
  { intros i Hi. rewrite KEEP2; [apply (L5.defined_grows M M1 _ _ MGM1 BDEF i Hi)| lia| |].
    - unfold aclient, aclient_g. left. exists (b, 40 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) (b + i) ltac:(lia) ltac:(lia) X). lia. }
  assert (Y14 : L5KA.zeros_at MV2 ((b + 40 * len) / 8 + 2147450880) 5).
  { rewrite (PNAEK.sh_idx b (40 * len)) by lia. rewrite PNAEK.d40. destruct ANN2 as (ZA & _). rewrite PNAEK.d40b in ZA. intros i Hi.
    assert (AV : L5A.avis H2 (S b + 5 * len + i) 1).
    { apply (VBSH2 b (40 * 2 ^ k) _ 1 BIN). intros j Hj. replace (S b + 5 * len + i + j) with (S b + (5 * len + i + j)) by lia.
      apply PNAEK.sh_in; [lia| lia| lia|]. rewrite PNAEK.d40. lia. }
    unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2).
    - replace (S b + 5 * len + i) with (S b + (5 * len + i)) by lia. apply ZA. lia.
    - pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (Y15 : L5.writable RSEGS MV2 (b + 40 * len) 40).
  { apply (proj2 (L5A.writable_vis H2 M2 (b + 40 * len) 40 (VBLK2 b (40 * 2 ^ k) (b + 40 * len) 40 BIN ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M2 b (40 * 2 ^ k)); [exact BDEF2| lia| lia]| lia| lia]. }
  pose proof (eq_trans (CS2 2%nat ltac:(inl)) fR2) as J2. pose proof (eq_trans (CS2 8%nat ltac:(inl)) fR8) as J8.
  pose proof (eq_trans (CS2 9%nat ltac:(inl)) fR9) as J9. pose proof (eq_trans (CS2 18%nat ltac:(inl)) fR18) as J18.
  pose proof (eq_trans (CS2 19%nat ltac:(inl)) fR19) as J19.
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 (bv_unsigned (getr R (reg 20)))) by (rewrite CS2 by inl; rewrite fR20; symmetry; apply Z_to_bv_bv_unsigned).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 (bv_unsigned (getr R (reg 21)))) by (rewrite CS2 by inl; rewrite fR21; symmetry; apply Z_to_bv_bv_unsigned).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 (bv_unsigned (getr R (reg 22)))) by (rewrite CS2 by inl; rewrite fR22; symmetry; apply Z_to_bv_bv_unsigned).
  assert (J23 : getr R2 (reg 23) = Z_to_bv 64 (bv_unsigned (getr R (reg 23)))) by (rewrite CS2 by inl; rewrite fR23; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (PMAIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMAIS1.bvu (getr R (reg 8))) as UR8. pose proof (PMAIS1.bvu (getr R (reg 9))) as UR9.
  pose proof (PMAIS1.bvu (getr R (reg 18))) as UR18. pose proof (PMAIS1.bvu (getr R (reg 19))) as UR19. pose proof (PMAIS1.bvu (getr R (reg 20))) as UR20.
  pose proof (PMAIS1.bvu (getr R (reg 21))) as UR21. pose proof (PMAIS1.bvu (getr R (reg 22))) as UR22. pose proof (PMAIS1.bvu (getr R (reg 23))) as UR23.
  LeanFeed.pfeed P (PNAERP.azrF2_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => p1 | 35%nat => p2 | 52%nat => p3 | 36%nat => b | 37%nat => 40 * len | 38%nat => m | 39%nat => n | 53%nat => q | 41%nat => b + 40 * 2 ^ k  | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | 45%nat => bv_unsigned (getr R (reg 9)) | 46%nat => bv_unsigned (getr R (reg 18)) | 47%nat => bv_unsigned (getr R (reg 19)) | 48%nat => bv_unsigned (getr R (reg 20)) | 49%nat => bv_unsigned (getr R (reg 21)) | 50%nat => bv_unsigned (getr R (reg 22)) | 51%nat => bv_unsigned (getr R (reg 23)) | _ => 0 end)) ltac:(first [assumption | unfold PNAERP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8 & gR9 & gR10 & gR11 & gR12 & gR13 & gR14 & gR15 & gR18 & gR19 & gR20 & gR21 & gR22 & gR23
                 & G8 & G32 & G24 & G16 & G8b & G0).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xad09c W_ac29c r F_ac29c eq_refl D_ac29c R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a => (b + 40 * len + 0 <= a < b + 40 * len + 0 + 40) \/ (v + 8 <= a < v + 8 + 8) \/ (sp - 128 <= a < sp - 128 + 128)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xad550 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a Ha [Wa|[Wa|Wa]].
    - split; [|lia]. unfold aclientw, aclient_g. left. exists (b, 40 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  (* [comment removed for export] *)
  assert (HP03 : L5CA.ahpres L ar LBX FF sp 12288 [(v, 24)] M M3).
  { apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc)).
      assert (NB : ~ (b <= a < b + 40 * 2 ^ k)) by (exact (PNAEK.own_notclient L ar C HI LY HIok b (40 * 2 ^ k) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      assert (NS : ~ in_shadow_of b (40 * 2 ^ k) a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok b (40 * 2 ^ k) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
      assert (NV : ~ (v <= a < v + 24)) by (intros X; apply (Ho (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]).
      assert (TW3' : forall a', 0 <= a' < 2 ^ 64 -> ~ W3 a' -> M3 (Z_to_bv 64 a') = M2 (Z_to_bv 64 a')) by exact FR3.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1].
      * rewrite TW3'; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
        apply FR1; [exact Ha| unfold W1; lia].
      * rewrite TW3'; [| exact Ha| unfold W3; lia]. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
        apply FR1; [exact Ha| unfold W1; lia].
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, 40 * 2 ^ k)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (40 * 2 ^ k) a) by (exact (PNAEK.own_sh_notclient L ar C HI LY HIok b (40 * 2 ^ k) LBX FF LK cr Aw M _ HH ltac:(lia) a sp 12288 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 80) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM. }
  assert (EK03 : L5SAR.ek L ar LBX FF sp 12288 [(v, 24)] M M3).
  { apply (L5SAR.ek_callee L ar LBX [] FF [] sp 12288 sp 12288 [(v, 24)] [(v, 24)] M M3 HP03); [lia| lia| intros a _ Ho; exact Ho]. }
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (PMASK.base_keep L ar C LY LBX FF sp 12288 [(v, 24)] M M3 EK03); [| exact BASE]. intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. lia. }
  apply (KONT fx3 R3 M3 model3 LK Aw2).
  3: exact VBLK.
  4: exact BASE3.
  4: exact HP03.
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PNAERP.KS_azrF2 /\ In k' L5SAR.cs_all /\ In k' PNAERP.KS_azrF1)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Hk]]]]]]]]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR9, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR18, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR19, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR20, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR21, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR22, Z_to_bv_bv_unsigned; reflexivity.
    + rewrite gR23, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH; right; right; exact Hk.
  - (* [comment removed for export] *)
    assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> ~ W3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by exact FR3.
    assert (TB : forall a, b <= a < b + 40 * len -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3; [| lia| unfold W3; lia]. apply T20; [lia| | lia|].
      - unfold aclient, aclient_g. left. exists (b, 40 * 2 ^ k). split; [exact BIN| cbn [fst snd]; lia].
      - intros X. pose proof (PNAEK.in_shadow_range b (40 * 2 ^ k) a ltac:(lia) ltac:(lia) X). lia. }
    assert (TSH : forall j, 0 <= j < (40 * 2 ^ k) / 8 -> M3 (Z_to_bv 64 (S b + j)) = M2 (Z_to_bv 64 (S b + j))).
    { intros j Hj. pose proof (shadow_low b (40 * 2 ^ k) j ltac:(lia) ltac:(lia) Hj) as SL. apply TW3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]]. }
    unfold PNM.bvec_at, PNM.BSZ. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1. fold len.
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; rewrite TW3; [apply TV; lia| lia| unfold W3; lia]| lia| lia| exact VB]. }
    split. { replace (b + 40 * (len + 1)) with (b + 40 * len + 40) by lia.
             apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [eapply L5A.avis_sub; [exact OVIS2| lia| lia]| lia| lia| exact G8]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; rewrite TW3; [apply TV; lia| lia| unfold W3; lia]| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [exact B16|].
    split; [apply (L5.defined_grows M2 M3 _ _ MGM3); exact BDEF2|].
    destruct ANN2 as (ZA2 & PM2 & PA2).
    split. { unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b (40 * (len + 1))).
             - intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply TW3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]].
             - unfold PMSPA.accA. apply (L5CB.aacc_of_zero M2 b ((40 * len + 40) / 8) b (40 * (len + 1)) ZA2); [lia| lia| lia| rewrite PNAEK.d40b; lia]. }
    split. { apply (PNAEK.ann_agree M2 M3 b (40 * (len + 1)) (40 * 2 ^ k)); [intros j Hj; apply TSH; clear -Hj P2K; Lia.lia| lia| lia|].
             replace (40 * (len + 1)) with (40 * len + 40) by lia. split; [exact ZA2| split; [exact PM2| exact PA2]]. }
    intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Hl|Hl].
    + rewrite app_nth1 by exact Hl. apply (PNMF.bstate_at_agree RSEGS M M3); [lia| lia| | apply BST; exact Hl].
      intros x Hx. apply TB. split; [lia|]. assert (Z.of_nat i + 1 <= len) by (unfold len; lia). lia.
    + assert (Ei : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. fold len.
      assert (AVB : forall a n0, b <= a -> a + n0 <= b + 40 * 2 ^ k -> L5A.avis H2 a n0) by (intros a n0 Ya1 Ya2; apply (VBLK2 b (40 * 2 ^ k) a n0 BIN); lia).
      unfold PNM.bstate_at. cbn [PNM.bs_mode PNM.bs_len PNM.bs_pos PNM.bs_type PNM.bs_idx].
      split; [apply (PMAIS1.vis_u32 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G0]|].
      split; [apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G8b]|].
      split; [apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G16]|].
      split; [apply (vis_u8 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G24]|].
      apply (PMAIS1.vis_u64 _ _ _ _ _ VIS3); [apply AVB; lia| lia| lia| exact G32].
  - apply (PMFA.accA_agree M2 M3 v 24); [| exact ACCV2]. intros x Hx. pose proof (S_range x ltac:(lia)) as SRx. apply FR3; [lia| unfold W3; intros [XW|XW]; [destruct Bq6 as [YW|YW]; lia| destruct OBIG as [YW|YW]; lia]].
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.
End Stage.
End PNAERF.
