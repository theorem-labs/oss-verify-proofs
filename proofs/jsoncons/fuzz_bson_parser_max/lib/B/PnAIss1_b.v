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
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAIssStmts_b PnAIssPA_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
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
Module PMAIS1.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma bvu (w : word) : 0 <= bv_unsigned w < 2 ^ 64.
Proof. pose proof (bv_unsigned_in_range 64 w) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. Qed.
(* [comment removed for export] *)
Lemma loc_ok_agree M M' b : (forall a, (0x672532 <= a < 0x672c70 \/ 0x673398 <= a < 0x6733f0) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PMST.loc_ok RSEGS PMA.AD M b -> PMST.loc_ok RSEGS PMA.AD M' b.
Proof.
  intros AG. unfold PMST.loc_ok. cbn [pa_glocale pa_classic_imp pa_loc_foot PMA.AD ADDR_A]. destruct b.
  - intros (G & P). split.
    + apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact G].
    + apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; lia| lia| lia| exact P].
  - intros C iv Hin i Hi. rewrite AG; [apply (C iv Hin i Hi)|]. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hi; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma zeros_sub34 M b j : L5KA.zeros_at M (b / 8 + 2147450880) 34 -> b mod 8 = 0 -> 0 <= j < 272 -> L5KA.zeros_at M ((b + j) / 8 + 2147450880) 1.
Proof. intros Z3 B8 Hj i Hi. replace ((b + j) / 8 + 2147450880 + i) with (b / 8 + 2147450880 + j / 8) by Lia.lia. apply Z3. Lia.lia. Qed.
(* [comment removed for export] *)
Lemma stack_zeros M sp : shadow_zero M (sp - 20480) 2560 -> sp mod 16 = 0 -> L5KA.zeros_at M (sp / 8 + 2147450368) 512.
Proof.
  intros SZ S16 i Hi. pose proof (SZ (2048 + i) ltac:(Lia.lia)) as X. unfold byte_at, S, SB in X.
  replace (sp / 8 + 2147450368 + i) with ((sp - 20480) / 8 + 2147450880 + (2048 + i)) by Lia.lia. exact X.
Qed.
Lemma sub8 x c : x mod 16 = 0 -> c mod 8 = 0 -> (x - c) mod 8 = 0.
Proof. intros. Lia.lia. Qed.
Lemma div_ois ois : ois mod 8 = 0 -> (ois + 120) / 8 = ois / 8 + 15 /\ (ois + 16) / 8 = ois / 8 + 2.
Proof. intros. Lia.lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma dep_img a : PMST.dep PMA.AD a -> 0x6722c0 <= a < 0x694074.
Proof.
  unfold PMST.dep, pm_foot, pm_initc. cbn [pa_errcat_guard pa_syscat_guard pa_loc_foot pa_atexit pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A app].
  intros [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
  - lia.
  - repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; lia|]). destruct Hin.
Qed.
(* [comment removed for export] *)
Definition brg (a : Z) : Prop := 65536 <= a < 0x139000 \/ 0x693d40 <= a < 0x693d48 \/ 0x693f93 <= a < 0x693f94 \/ 0x694070 <= a < 0x694074.
Lemma base_ok_agree M M' : (forall a, brg a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> PMSTA.base_okA RSEGS PMA.AD M -> PMSTA.base_okA RSEGS PMA.AD M'.
Proof.
  intros AG (RO0 & (can & Hcan & CAN) & NL & LL). unfold PMSTA.base_okA. cbn [pa_rw_lo pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A] in *. unfold brg in AG.
  split; [|split; [|split]].
  - intros i Hi. rewrite AG by Lia.lia. apply RO0. exact Hi.
  - exists can. split; [exact Hcan|]. apply (L5C.u64_at_agree RSEGS M M'); [intros i Hi; apply AG; Lia.lia| Lia.lia| Lia.lia| exact CAN].
  - apply (L5C.u8_at_agree RSEGS M M'); [intros i Hi; apply AG; Lia.lia| Lia.lia| Lia.lia| exact NL].
  - apply (PMF.u32_at_agree RSEGS M M'); [intros i Hi; apply AG; Lia.lia| Lia.lia| Lia.lia| exact LL].
Qed.
Lemma ffroom_incl h h' FF LK LK' : PMSPA.ffroomA h FF LK -> incl LK' LK -> NoDup (map ff_addr (FF ++ LK')) -> h' <= h -> PMSPA.ffroomA h' FF LK'.
Proof.
  intros FR I ND Hh k Hk. specialize (FR k Hk).
  assert (CI : (ff_count k (FF ++ LK') <= ff_count k (FF ++ LK))%nat).
  { apply L5SAR.ff_count_incl.
    - intros x Hx. apply in_app_or in Hx. apply in_or_app. destruct Hx as [X|X]; [left; exact X| right; apply I; exact X].
    - apply (list_monad.list.NoDup_fmap_1 ff_addr). exact ND. }
  Lia.lia.
Qed.
(* [comment removed for export] *)
Lemma d4cell LB FF LK cr Aw M V a w v : ri_inv HI LB FF LK cr Aw M V -> In (a, w, v) L5A.AS0_ALY_CELLS_D4 -> cell_is RSEGS M a (Z.to_nat w) v.
Proof.
  intros HH Hin. pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & CS). rewrite (L5A.aly_segs L C LYa) in CS.
  rewrite Forall_forall in CS. exact (CS (a, w, v) (L5A.aly_cells L C LYa _ Hin)).
Qed.

Lemma vis_u64 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 8 -> 0 <= a -> a + 8 <= 2 ^ 64 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u64_at_vis H M1 a v AV H0 H1) X). Qed.
Lemma vis_u32 H M1 M1v a v : mrestrict H M1 = M1v -> L5A.avis H a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at RSEGS M1v a v -> L5.u32_at RSEGS M1 a v.
Proof. intros E AV H0 H1 X. rewrite <- E in X. exact (proj1 (L5A.u32_at_vis H M1 a v AV H0 H1) X). Qed.
Lemma vis_zeros H M1 M1v a n : mrestrict H M1 = M1v -> L5A.avis H a n -> L5KA.zeros_at M1v a n -> L5KA.zeros_at M1 a n.
Proof. intros E AV X. rewrite <- E in X. exact (proj1 (L5A.zeros_at_vis H M1 a n AV) X). Qed.

Theorem head : PMA.locale_ctor_spec L ar HI ->
  forall (fx : FPState) R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b,
    PMAIS.pre L ar HI R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b ->
    (forall (fx1 : FPState) R1 M1 model1 LK1 Aw1, PMAIS.mid L ar HI R0 M0 model0 LB FF LK0 Aw0 cr ois os sp s b R1 M1 model1 LK1 Aw1 ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx1) R1 0xac2a8 M1 model1) K) ->
    srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx) R0 0xa8b74 M0 model0) K.
Proof.
  intros LOC fx R0 M0 model0 K LB FF LK0 Aw0 cr ois os sp r s b PRE KONT.
  destruct PRE as (HH & AM & K0 & ENT & FRM & FRS & A10 & A11 & A12 & AO & AOS & EOS & O8 & OS8 & ODEF & ACC & VS & INCL & SZ & LNG & BASE & LOCb & CRED).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp.
  change (PMSPA.pm_scr 4) with 20480 in *. change (20480 / 8) with 2560 in STKSH.
  assert (EOS' : os = ois - 64) by lia. subst os.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw0 model0) in *. set (MV := mrestrict H M0) in *.
  pose proof (PMKA.aobj_of_aobjA FF ois 272 AO O8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 ois 272 sp 20480 HH AOB ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
  change (272 / 8) with 34 in OVSH, OCLSH.
  (* [comment removed for export] *)
  assert (OCLS : (6905920 <= ois <= 2147446512) \/ (17594333495360 <= ois <= 140737488355047)).
  { destruct AOS as (f & Hf & X1 & X2). destruct AO as (g & Hg & Y1 & Y2). pose proof (WF f Hf) as (F1 & F2 & _). pose proof (WF g Hg) as (G1 & G2 & _).
    rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in FSIMG. unfold app_mem, FS_BYTES, BIGSHADOW_LO, BIGSHADOW_HI in *.
    assert (HB : 0 < ff_bytes (ff_class g) <= 2048).
    { destruct (WF g Hg) as (_ & _ & _ & Y4 & _). destruct Y4 as [E|[E|[E|[E|[E|[E|[]]]]]]]; rewrite <- E;
        [change (ff_bytes 0) with 64 | change (ff_bytes 1) with 128 | change (ff_bytes 2) with 256 | change (ff_bytes 3) with 512 | change (ff_bytes 4) with 1024 | change (ff_bytes 5) with 2048]; lia. }
    destruct FSAPP as (FA0 & [FA|FA] & FA2); destruct FSIMG as [FI|FI]; [left; lia| left; lia| right; lia| right; lia]. }
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M0 LYa ST) as (GOT & CSB & CUAR & _).
  assert (VU8 : forall x v0, 0x10000 <= x < 0x696000 -> L5.u8_at RSEGS M0 x v0 -> L5.u8_at RSEGS MV x v0).
  { intros x v0 Hx X. apply (proj2 (L5A.u8_at_vis H M0 x v0 (VIMG x 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (VU64 : forall x v0, 0x10000 <= x -> x + 8 <= 0x696000 -> L5.u64_at RSEGS M0 x v0 -> L5.u64_at RSEGS MV x v0).
  { intros x v0 Hx Hx' X. apply (proj2 (L5A.u64_at_vis H M0 x v0 (VIMG x 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  assert (V0 : L5.img_clear MV 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (V1 : L5.u64_at RSEGS MV 1309752 2147450880) by (apply VU64; [lia| lia| exact CSB]).
  assert (V2 : L5.u32_at RSEGS MV 1309760 1) by (apply (proj2 (L5A.u32_at_vis H M0 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (W4096 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M0 (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M0 sp 20480); [exact ASTK| lia| lia| lia]. }
  assert (OZv : L5KA.zeros_at MV (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 ois 272 HH AO O8 ltac:(lia) ltac:(reflexivity) ACC). }
  assert (OWv : L5.writable RSEGS MV ois 272).
  { apply (proj2 (L5A.writable_vis H M0 ois 272 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  (* [comment removed for export] *)
  assert (XC1 : L5.u64_at RSEGS MV 1275072 1309752) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1275072 8 1309752 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 4 right; left; reflexivity))]).
  assert (XC2 : L5.u64_at RSEGS MV 1275080 1313064) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1275080 8 1313064 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 5 right; left; reflexivity))]).
  assert (XC3 : L5.u64_at RSEGS MV 1313064 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1313064 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 6 right; left; reflexivity))]).
  assert (XC4 : L5.u64_at RSEGS MV 1275088 1313072) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1275088 8 1313072 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 7 right; left; reflexivity))]).
  assert (XC5 : L5.u64_at RSEGS MV 1313072 0) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1313072 8 0 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 8 right; left; reflexivity))]).
  assert (XC6 : L5.u64_at RSEGS MV 1275096 1313056) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1275096 8 1313056 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 9 right; left; reflexivity))]).
  assert (XC7 : L5.u64_at RSEGS MV 1313056 140737488355327) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1313056 8 140737488355327 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 10 right; left; reflexivity))]).
  assert (XC8 : L5.u64_at RSEGS MV 1277992 1313049) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1277992 8 1313049 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 11 right; left; reflexivity))]).
  assert (XC9 : L5.u8_at RSEGS MV 1313049 1) by (apply VU8; [lia| exact (d4cell _ _ _ _ _ _ _ 1313049 1 1 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 12 right; left; reflexivity))]).
  assert (XC10 : L5.u64_at RSEGS MV 1283280 1219844) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1283280 8 1219844 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 2 right; left; reflexivity))]).
  assert (XC11 : L5.u64_at RSEGS MV 1283272 1218816) by (apply VU64; [lia| lia| exact (d4cell _ _ _ _ _ _ _ 1283272 8 1218816 HH ltac:(unfold L5A.AS0_ALY_CELLS_D4; do 13 right; left; reflexivity))]).
  assert (IMGSH : L5KA.zeros_at MV 2147609117 32).
  { destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH 0x1350e8 256) as (ZB & SA).
    - rewrite (L5A.aly_img_lo L C LYa). lia. - rewrite (L5A.aly_img_hi L C LYa). lia. - lia.
    - rewrite (aicl_poison IL ILY). repeat constructor; cbn [fst snd]; lia.
    - intros i Hi. assert (AV : L5A.avis H (2147609117 + i) 1).
      { apply (L5A.avis_of_shadow_allowed Aw0 model0 0x1350e8 256). exact SA. intros j Hj. unfold in_shadow_of, S, SB. lia. }
      pose proof (ZB (2147609117 + i) ltac:(unfold in_shadow_of, S, SB; lia)) as Z1. unfold byte_at in Z1.
      unfold MV. rewrite (AsanAcct.mrestrict_visible H M0); [exact Z1|]. pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (STZ : L5KA.zeros_at MV (sp / 8 + 2147450368) 512).
  { intros i Hi. unfold MV. rewrite (AsanAcct.mrestrict_visible H M0). apply (stack_zeros M0 sp STKSH A16). exact Hi.
    assert (AV : L5A.avis H (sp / 8 + 2147450368 + i) 1).
    { apply (VSTSH (sp / 8 + 2147450368 + i) 1). intros j Hj. unfold in_shadow_of, S, SB.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  (* [comment removed for export] *)
  pose proof (PMAISPA.aicAl_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R0 MV (fun j => match j with 2%nat => sp | 33%nat => ois | _ => 0 end)) as PL.
  cbn beta iota in PL.
  let T := type of PL in let G := L5SAR.feed_concl T in assert (P : G).
  { destruct OCLS as [CL|CL].
    - L5SAR.feed PL ltac:(first [assumption | unfold PMAISPA.aligned; lia | lia]). exact PL.
    - LeanFeed.pfeed PH (PMAISPA.aicAh_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx R0 MV (fun j => match j with 2%nat => sp | 33%nat => ois | _ => 0 end)) ltac:(first [assumption | unfold PMAISPA.aligned; lia | lia]). exact PH. }
  clear PL.
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27
                 & Z176 & C152 & C144 & C136 & C128 & C160 & C156 & C8 & C120 & C0 & C168 & S104 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
  set (W1 := fun a => (sp - 4096 <= a < sp - 4096 + 4096) \/ (ois + 0 <= a < ois + 0 + 16) \/ (ois + 120 <= a < ois + 120 + 136)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 model0 fx fx1 R0 0xa8b74 R1 0xfee68 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; left; exact X| intros X; apply N; right; right; exact X]. }
  { intros a Ha [Wa|[Wa|Wa]].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  assert (WAPP : PMKA.wapp (PMAIS.WF ois b)).
  { unfold PMAIS.WF. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    destruct b; [apply PMKA.wapp_nil|]. unfold PMSPA.loc_W. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO; lia|]. apply PMKA.wapp_nil. }
  assert (OUTW : forall a, (a < ois \/ ois + 272 <= a) -> (a < 0x672532 \/ 0x6733f0 <= a) -> L5.outside (PMAIS.WF ois b) a).
  { intros a H1 H2 rg Hin Hr. unfold PMAIS.WF in Hin. destruct Hin as [<-|Hin].
    - unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia.
    - destruct b; [destruct Hin|]. unfold PMSPA.loc_W in Hin. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd] in Hin.
      destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia. }
  assert (EKO : forall M' M'' (P : Z -> Prop), (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M'' (Z_to_bv 64 a) = M' (Z_to_bv 64 a)) ->
            (forall a, P a -> sp - 20480 <= a < sp \/ ois <= a < ois + 272) -> L5SAR.ek L ar LB FF sp 20480 [(ois, 272)] M' M'').
  { intros M' M'' P FRM0 HP. apply (L5SAR.ek_piece L ar LB FF sp 20480 [(ois, 272)] M' M'' P FRM0). intros a Ha Hc Ho X. destruct (HP a X) as [Y|Y].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK0 cr Aw0 M0 _ sp 20480 a HH SPT Hc) as [Z1|Z1]; lia.
    - apply (Ho (ois, 272)). left; reflexivity. unfold L5.in_rng; cbn [fst snd]. exact Y. }
  assert (OWF : forall a, L5.outside (PMAIS.WF ois b) a -> L5.outside [(ois, 272)] a).
  { intros a O rg [<-|[]] Hr. apply (O (ois, 272)); [left; reflexivity| exact Hr]. }
  assert (EK01n : L5SAR.ek L ar LB FF sp 20480 [(ois, 272)] M0 M1) by (apply (EKO M0 M1 W1 FR1); intros a [X|[X|X]]; lia).
  assert (EK01 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M1) by (apply (L5SAR.ek_W L ar LB FF sp 20480 _ _ M0 M1 EK01n OWF)).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
  { intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). unfold app_mem, FS_BYTES in *. lia. }
  assert (ASTK1 : L5CA.astk ar M1 sp 20480) by (apply (L5SAR.astk_grows ar M0 M1 sp 20480 ASTK MGM1)).
  assert (STKSH1 : shadow_zero M1 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M1 EK01 WAPP); [lia| lia| lia| | lia| exact STKSH].
    apply sub8; [exact A16| reflexivity]. }
  assert (STD : forall a, PMST.dep PMA.AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(ois, 272)] a).
  { intros a D. pose proof (dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (SRO : forall a, 65536 <= a < pa_rw_lo PMA.AD -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside [(ois, 272)] a).
  { intros a Ha. cbn [pa_rw_lo PMA.AD ADDR_A] in Ha. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    split; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|]. intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1) by (apply (PMKA.base_ok_keepA RSEGS PMA.AD L ar LB FF sp 20480 [(ois, 272)] M0 M1 EK01n PMA.addrs_wf_A STD SRO BASE)).
  assert (LOC1 : PMST.loc_ok RSEGS PMA.AD M1 b).
  { apply (loc_ok_agree M0 M1 b); [|exact LOCb]. intros a Ha. apply FR1; [lia| unfold W1; lia]. }
  (* [comment removed for export] *)
  unfold PMA.locale_ctor_spec, PMSPA.locale_ctor_spec in LOC. cbn [pa_locale_ctor PMA.AD ADDR_A] in LOC.
  apply (LOC fx1 R1 M1 model1 K LB FF LK0 Aw0 cr (ois + 168) (sp - 112) 691404 b HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact B1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact B2|].
    split; [rewrite L5K.rl3, (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split.
    - apply (L5SAR.astk_sub ar M1 M1 sp 20480 112 16384 ASTK1 (fun x X => X)); [lia| lia| lia|].
      replace (sp - 112) with (sp + (-7) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
    - change (16384 / 8) with 2048. apply (PMKA.shadow_zero_sub M1 (sp - 20480) 2560 (sp - 112 - 16384) 2048);
        [apply sub8; [exact A16| reflexivity]| replace (sp - 112 - 16384) with (sp - 16496) by lia; apply sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH1]. }
  { unfold PMSPA.ffroomA in *. intros k Hk. specialize (FRM k Hk). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact B10. }
  { destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf| lia]. }
  { replace (ois + 168) with (ois + 21 * 8) by lia. rewrite Z.mod_add by lia. exact O8. }
  { apply (L5.defined_grows M0 M1 _ _ MGM1). apply (L5.defined_sub M0 ois 272); [exact ODEF| lia| lia]. }
  { exact BASE1. }
  { exact LOC1. }
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 C168' LOC2 HP2 MRT2 INC2 IA2 AM2 HH2.
  change (PMSPA.pm_scr 2) with 16384 in HP2.
  set (W2 := (ois + 168, 8) :: (if b then [] else PMSPA.loc_W PMA.AD)) in HP2.
  assert (EK12 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M1 M2).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 112) 16384 (PMAIS.WF ois b) W2 M1 M2 HP2); [lia| lia|].
    intros a Hc Ho rg Hin Hr. unfold W2 in Hin. destruct Hin as [<-|Hin].
    - apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia].
    - apply (Ho rg); [right; exact Hin| exact Hr]. }
  assert (DK12 : L5SAR.dk L ar LB FF sp 20480 M1 M2) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 112) 16384 W2 M1 M2 HP2); lia).
  assert (ASTK2 : L5CA.astk ar M2 sp 20480).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK0 cr Aw0 M1 M1 M2 _ sp 20480 (sp - 112) 16384 W2 HH1 ASTK1 (fun x X => X) HP2); lia. }
  assert (EK02 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M2) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M1 M2 EK01 EK12)).
  (* [comment removed for export] *)
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 112 - 16384 <= a < sp - 112) -> ~ (ois + 168 <= a < ois + 176) -> (a < 0x672532 \/ 0x6733f0 <= a) ->
                  aclient L ar LB FF 0 0 a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha N0 N1 N2 Hc. apply (proj1 HP2). split; [lia|]. split.
    - apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia].
    - intros rg Hin Hr. unfold W2 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia|].
      destruct b; [destruct Hin|]. unfold PMSPA.loc_W in Hin. cbn [map pa_loc_foot PMA.AD ADDR_A fst snd] in Hin.
      destruct Hin as [<-|[<-|[]]]; unfold L5.in_rng in Hr; cbn [fst snd] in Hr; lia. }
  assert (BASE2 : PMSTA.base_okA RSEGS PMA.AD M2).
  { apply (base_ok_agree M1 M2); [|exact BASE1]. intros a Ha. unfold brg in Ha. apply KEEP2; [lia| lia| lia| lia|].
    unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
    destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
    apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
    destruct Ha as [Ha|[Ha|Ha]];
      [right; left; lia
      | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
      | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  (* [comment removed for export] *)
  assert (CS2 : forall k, In k L5SAR.cs_all -> getr R2 (reg k) = getr R1 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R1 R2 k RP2 Hk)).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 sp 20480 HH2 AOB ltac:(lia) ltac:(reflexivity))
    as (_ & _ & ODEF2 & OVIS2 & OVSH2 & _ & _).
  change (272 / 8) with 34 in OVSH2.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (ACC2 : PMSPA.accA M2 ois 272) by (apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M0 M2 EK02 WAPP FRB ois 272 AO ACC)).
  assert (Y0 : L5.img_clear MV2 1249280 1282048) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (Y1 : L5.u64_at RSEGS MV2 1309752 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1309752 2147450880 (VIMG2 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (Y2 : L5.u32_at RSEGS MV2 1309760 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1309760 1 (VIMG2 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 20480); [exact ASTK2| lia| lia| lia]. }
  assert (YZ : L5KA.zeros_at MV2 (ois / 8 + 2147450880) 34).
  { exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 ois 272 HH2 AO O8 ltac:(lia) ltac:(reflexivity) ACC2). }
  assert (YZ267 : L5KA.zeros_at MV2 ((ois + 267) / 8 + 2147450880) 1) by (apply zeros_sub34; [exact YZ| exact O8| lia]).
  assert (YW : L5.writable RSEGS MV2 ois 272).
  { apply (proj2 (L5A.writable_vis H2 M2 ois 272 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF2. lia. lia. }
  assert (YIMG : L5KA.zeros_at MV2 2147609117 32).
  { destruct (aic_img_shadow _ _ _ _ _ ICok _ _ _ _ _ _ _ HH2 0x1350e8 256) as (ZB & SA).
    - rewrite (L5A.aly_img_lo L C LYa). lia. - rewrite (L5A.aly_img_hi L C LYa). lia. - lia.
    - rewrite (aicl_poison IL ILY). repeat constructor; cbn [fst snd]; lia.
    - intros i Hi. assert (AV : L5A.avis H2 (2147609117 + i) 1).
      { apply (L5A.avis_of_shadow_allowed Aw2 model2 0x1350e8 256). exact SA. intros j Hj. unfold in_shadow_of, S, SB. lia. }
      pose proof (ZB (2147609117 + i) ltac:(unfold in_shadow_of, S, SB; lia)) as Z1. unfold byte_at in Z1.
      unfold MV2. rewrite (AsanAcct.mrestrict_visible H2 M2); [exact Z1|]. pose proof (AV 0 ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X. }
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 112)) by (rewrite CS2 by inl; exact B2).
  assert (J8 : getr R2 (reg 8) = Z_to_bv 64 ois) by (rewrite CS2 by inl; exact B8).
  assert (J9 : getr R2 (reg 9) = Z_to_bv 64 (ois + 120)) by (rewrite CS2 by inl; exact B9).
  assert (J18 : getr R2 (reg 18) = Z_to_bv 64 8) by (rewrite CS2 by inl; exact B18).
  assert (J19 : getr R2 (reg 19) = Z_to_bv 64 (ois - 64)) by (rewrite CS2 by inl; exact B19).
  assert (J20 : getr R2 (reg 20) = Z_to_bv 64 1266032) by (rewrite CS2 by inl; exact B20).
  assert (J21 : getr R2 (reg 21) = Z_to_bv 64 (ois + 16)) by (rewrite CS2 by inl; exact B21).
  assert (J22 : getr R2 (reg 22) = Z_to_bv 64 (ois + 120)) by (rewrite CS2 by inl; exact B22).
  assert (J23 : getr R2 (reg 23) = Z_to_bv 64 ((ois / 8) + 2147450880)) by (rewrite CS2 by inl; exact B23).
  assert (J24 : getr R2 (reg 24) = Z_to_bv 64 2147450880) by (rewrite CS2 by inl; exact B24).
  assert (J25 : getr R2 (reg 25) = Z_to_bv 64 1265968) by (rewrite CS2 by inl; exact B25).
  assert (J26 : getr R2 (reg 26) = Z_to_bv 64 (((ois + 120) / 8) + 2147450880)) by (rewrite CS2 by inl; exact B26).
  assert (J27 : getr R2 (reg 27) = Z_to_bv 64 1266008) by (rewrite CS2 by inl; exact B27).
  LeanFeed.pfeed P (PMAISPA.aicB_conc as0_icpt_fill as0_icpt_copy as0_icpt_tls fx2 R2 MV2 (fun j => match j with 2%nat => sp | 33%nat => ois | _ => 0 end)) ltac:(first [assumption | unfold PMAISPA.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & D1 & D2 & D8 & D9 & D10 & D11 & D12 & D19 & D20 & D21 & D22 & D23 & D24 & D26 & E16 & T184 & T176 & T168 & T160 & T152 & T144 & T136 & T128 & T120 & E120 & E0 & F267 & F266 & F265 & F264 & F256).
  set (W3 := fun a => (sp - 192 <= a < sp - 192 + 80) \/ (ois + 0 <= a < ois + 0 + 8) \/ (ois + 16 <= a < ois + 16 + 8) \/ (ois + 120 <= a < ois + 120 + 8)
                      \/ (ois + 256 <= a < ois + 256 + 12)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xa8ccc R3 0xfee68 M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha N. apply FZ3; [exact Ha| | | | |]; intros X; apply N; unfold W3; tauto. }
  { intros a Ha [Wa|Wa].
    - split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia].
    - split; [apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia| lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (EK23n : L5SAR.ek L ar LB FF sp 20480 [(ois, 272)] M2 M3) by (apply (EKO M2 M3 W3 FR3); intros a X; unfold W3 in X; lia).
  assert (EK23 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M2 M3) by (apply (L5SAR.ek_W L ar LB FF sp 20480 _ _ M2 M3 EK23n OWF)).
  assert (EK03 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M3) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M2 M3 EK02 EK23)).
  assert (ASTK3 : L5CA.astk ar M3 sp 20480) by (apply (L5SAR.astk_grows ar M2 M3 sp 20480 ASTK2 MGM3)).
  assert (BASE3 : PMSTA.base_okA RSEGS PMA.AD M3).
  { apply (base_ok_agree M2 M3); [|exact BASE2]. intros a Ha. unfold brg in Ha. apply FR3; [lia| unfold W3; lia]. }
  assert (LOC3 : PMST.loc_ok RSEGS PMA.AD M3 true).
  { apply (loc_ok_agree M2 M3 true); [|exact LOC2]. intros a Ha. apply FR3; [lia| unfold W3; lia]. }
  assert (STKSH3 : shadow_zero M3 (sp - 20480) 2560).
  { apply (PMKA.stksh_keepA L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M3 EK03 WAPP); [lia| lia| lia| | lia| exact STKSH].
    apply sub8; [exact A16| reflexivity]. }
  assert (ND3 : NoDup (map ff_addr (FF ++ LK2))).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH3) as WF3. cbn zeta in WF3. tauto. }
  (* [comment removed for export] *)
  apply (LOC fx3 R3 M3 model3 K LB FF LK2 Aw2 cr (ois + 24) (sp - 192) 705192 true HH3 AM3 K0).
  { split; [rewrite L5K.rl1; exact D1|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact D2|].
    split; [rewrite L5K.rl3, (KS3 3%nat) by inl; rewrite CS2 by inl; rewrite (KS1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (KS3 4%nat) by inl; rewrite CS2 by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 2) with 16384. split.
    - apply (L5SAR.astk_sub ar M3 M3 sp 20480 192 16384 ASTK3 (fun x X => X)); [lia| lia| lia|].
      replace (sp - 192) with (sp + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact A16.
    - change (16384 / 8) with 2048. apply (PMKA.shadow_zero_sub M3 (sp - 20480) 2560 (sp - 192 - 16384) 2048);
        [apply sub8; [exact A16| reflexivity]| replace (sp - 192 - 16384) with (sp - 16576) by lia; apply sub8; [exact A16| reflexivity]| lia| lia| lia| exact STKSH3]. }
  { apply (ffroom_incl 4 2 FF LK0 LK2 FRM INC2 ND3). lia. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { rewrite L5K.rl10. exact D10. }
  { destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf| lia]. }
  { replace (ois + 24) with (ois + 3 * 8) by lia. rewrite Z.mod_add by lia. exact O8. }
  { apply (L5.defined_grows M2 M3 _ _ MGM3). apply (L5.defined_sub M2 ois 272); [exact ODEF2| lia| lia]. }
  { exact BASE3. }
  { exact LOC3. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 C24 LOC4 HP4 MRT4 INC4 IA4 AM4 HH4.
  change (PMSPA.pm_scr 2) with 16384 in HP4. change ((ois + 24, 8) :: (if true then [] else PMSPA.loc_W PMA.AD)) with [(ois + 24, 8)] in HP4.
  assert (EK34 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M3 M4).
  { apply (L5SAR.ek_callee L ar LB [] FF [] sp 20480 (sp - 192) 16384 (PMAIS.WF ois b) [(ois + 24, 8)] M3 M4 HP4); [lia| lia|].
    intros a Hc Ho rg [<-|[]] Hr. apply (Ho (ois, 272)); [left; reflexivity| unfold L5.in_rng in *; cbn [fst snd] in *; lia]. }
  assert (DK34 : L5SAR.dk L ar LB FF sp 20480 M3 M4) by (apply (L5SAR.dk_callee L ar LB [] FF [] sp 20480 (sp - 192) 16384 [(ois + 24, 8)] M3 M4 HP4); lia).
  assert (ASTK4 : L5CA.astk ar M4 sp 20480).
  { apply (L5SAR.astk_after L ar C HI HIok LB FF LK2 cr Aw2 M3 M3 M4 _ sp 20480 (sp - 192) 16384 [(ois + 24, 8)] HH3 ASTK3 (fun x X => X) HP4); lia. }
  assert (EK04 : L5SAR.ek L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M4) by (apply (L5SAR.ek_trans L ar LB FF sp 20480 _ M0 M3 M4 EK03 EK34)).
  assert (DK04 : L5SAR.dk L ar LB FF sp 20480 M0 M4).
  { apply (L5SAR.dk_trans L ar LB FF sp 20480 M0 M1 M4 (L5SAR.dk_grows L ar LB FF sp 20480 M0 M1 MGM1)).
    apply (L5SAR.dk_trans L ar LB FF sp 20480 M1 M2 M4 DK12).
    apply (L5SAR.dk_trans L ar LB FF sp 20480 M2 M3 M4 (L5SAR.dk_grows L ar LB FF sp 20480 M2 M3 MGM3) DK34). }
  assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 192 - 16384 <= a < sp - 192) -> ~ (ois + 24 <= a < ois + 32) ->
                  aclient L ar LB FF 0 0 a -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha N0 N1 Hc. apply (proj1 HP4). split; [lia|]. split.
    - apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia].
    - intros rg [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. lia. }
  (* [comment removed for export] *)
  assert (CL : forall a, ois <= a < ois + 272 -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply (L5SAR.obj_client L ar LB FF 0 0 ois 272 a AOB); lia).
  assert (SCL : forall a, sp - 20480 <= a < sp -> aclient L ar LB FF 0 0 a) by (intros a Ha; apply L5SAR.stack_client; lia).
  (* [comment removed for export] *)
  assert (AG14 : forall a, (ois <= a < ois + 272 /\ ~ (ois <= a < ois + 8) /\ ~ (ois + 16 <= a < ois + 32) /\ ~ (ois + 120 <= a < ois + 128) /\ ~ (ois + 256 <= a < ois + 268)
                            /\ ~ (ois + 168 <= a < ois + 176)) \/ (sp - 104 <= a < sp) -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. assert (CLa : aclient L ar LB FF 0 0 a) by (destruct Ha as [Ha|Ha]; [apply CL; lia| apply SCL; lia]).
    rewrite KEEP4; [| lia| lia| lia| exact CLa]. rewrite FR3; [| lia| unfold W3; lia]. apply KEEP2; [lia| lia| lia| lia| exact CLa]. }
  assert (AG34 : forall a, (ois <= a < ois + 272 /\ ~ (ois + 24 <= a < ois + 32)) \/ (sp - 192 <= a < sp - 112) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
  { intros a Ha. assert (CLa : aclient L ar LB FF 0 0 a) by (destruct Ha as [Ha|Ha]; [apply CL; lia| apply SCL; lia]).
    apply KEEP4; [lia| lia| lia| exact CLa]. }
  assert (AG24 : forall a, ois + 168 <= a < ois + 176 -> M4 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
  { intros a Ha. rewrite AG34 by lia. apply FR3; [lia| unfold W3; lia]. }
  assert (V1a : forall a n, (ois <= a /\ a + n <= ois + 272) \/ (sp - 4096 <= a /\ a + n <= sp) -> L5A.avis H a n).
  { intros a n [Ha|Ha]; [eapply L5A.avis_sub; [exact OVIS| lia| lia]| apply VIS; lia]. }
  assert (V3a : forall a n, (ois <= a /\ a + n <= ois + 272) \/ (sp - 4096 <= a /\ a + n <= sp) -> L5A.avis H2 a n).
  { intros a n [Ha|Ha]; [eapply L5A.avis_sub; [exact OVIS2| lia| lia]| apply VIS2; lia]. }
  Ltac t64 AG V VIS X Ms := apply (L5C.u64_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG")| (lia || fail 1 "B1")| (lia || fail 1 "B2")|];
                            apply (vis_u64 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V") | (lia || fail 1 "B3") | (lia || fail 1 "B4") | exact X].
  Ltac t32 AG V VIS X Ms := apply (PMF.u32_at_agree RSEGS Ms); [intros i Hi; apply AG; (lia || fail 1 "AG32")| (lia || fail 1 "C1")| (lia || fail 1 "C2")|];
                            apply (vis_u32 _ _ _ _ _ VIS); [apply V; (lia || fail 1 "V32") | (lia || fail 1 "C3") | (lia || fail 1 "C4") | exact X].
  pose proof (bvu (getr R0 (reg 1))) as UR1. pose proof (bvu (getr R0 (reg 8))) as UR8.
  apply (KONT fx4 R4 M4 model4 LK4 Aw4).
  assert (CS4 : forall k, In k L5SAR.cs_all -> getr R4 (reg k) = getr R3 (reg k)) by (intros k Hk; apply (L5SAR.cs_of_preserved R3 R4 k RP4 Hk)).
  split; [rewrite CS4 by inl; exact D2|]. split; [rewrite CS4 by inl; exact D8|]. split; [rewrite CS4 by inl; exact D9|].
  split; [rewrite CS4 by inl; rewrite (KS3 18%nat) by inl; exact J18|]. split; [rewrite CS4 by inl; exact D19|].
  split; [rewrite CS4 by inl; exact D20|]. split; [rewrite CS4 by inl; exact D21|].
  split; [rewrite CS4 by inl; exact D22|]. split; [rewrite CS4 by inl; exact D23|]. split; [rewrite CS4 by inl; exact D24|].
  split; [rewrite CS4 by inl; rewrite (KS3 25%nat) by inl; exact J25|]. split; [rewrite CS4 by inl; exact D26|].
  split; [rewrite CS4 by inl; rewrite (KS3 27%nat) by inl; exact J27|].
  split. { intros k Hk. rewrite CS4 by (destruct Hk as [<-|[<-|[]]]; inl). rewrite (KS3 k) by (destruct Hk as [<-|[<-|[]]]; inl).
           rewrite CS2 by (destruct Hk as [<-|[<-|[]]]; inl). apply KS1. destruct Hk as [<-|[<-|[]]]; inl. }
  unfold PMAIS.midc.
  split. { unfold PMAIS.saves_iss.
           split; [t64 AG14 V1a VIS1 S8 M1|]. split; [t64 AG14 V1a VIS1 S16 M1|]. split; [t64 AG14 V1a VIS1 S24 M1|]. split; [t64 AG14 V1a VIS1 S32 M1|].
           split; [t64 AG14 V1a VIS1 S40 M1|]. split; [t64 AG14 V1a VIS1 S48 M1|]. split; [t64 AG14 V1a VIS1 S56 M1|]. split; [t64 AG14 V1a VIS1 S64 M1|].
           split; [t64 AG14 V1a VIS1 S72 M1|]. split; [t64 AG14 V1a VIS1 S80 M1|]. split; [t64 AG14 V1a VIS1 S88 M1|]. split; [t64 AG14 V1a VIS1 S96 M1| t64 AG14 V1a VIS1 S104 M1]. }
  split. { unfold PMAIS.saves_sb.
           split; [t64 AG34 V3a VIS3 T120 M3|]. split; [t64 AG34 V3a VIS3 T128 M3|]. split; [t64 AG34 V3a VIS3 T136 M3|]. split; [t64 AG34 V3a VIS3 T144 M3|].
           split; [t64 AG34 V3a VIS3 T152 M3|]. split; [t64 AG34 V3a VIS3 T160 M3|]. split; [t64 AG34 V3a VIS3 T168 M3|]. split; [t64 AG34 V3a VIS3 T176 M3|].
           t64 AG34 V3a VIS3 T184 M3. }
  split. { unfold PMAIS.head_cells. cbn [pa_vp_iss pa_classic_imp pa_vp_iss_ios PMA.AD ADDR_A].
           split; [t64 AG34 V3a VIS3 E0 M3|]. split; [exact C24|]. split; [t64 AG34 V3a VIS3 E120 M3|].
           split; [t32 AG14 V1a VIS1 C152 M1|]. split; [t32 AG14 V1a VIS1 C156 M1|]. split; [t64 AG14 V1a VIS1 C160 M1|].
           split; [apply (L5C.u64_at_agree RSEGS M2); [intros i Hi; apply AG24; lia| lia| lia| exact C168']|].
           apply (PMF.zeros_at_agree M1); [intros i Hi; apply AG14; lia|]. apply (vis_zeros _ _ _ _ _ VIS1); [apply V1a; lia| exact Z176]. }
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK4 cr Aw4 M4 model4 ois 272 sp 20480 HH4 AOB ltac:(lia) ltac:(reflexivity)) as (_ & _ & ODEF4 & _).
  pose proof (WB) as WB0.
  split; [exact ODEF4|].
  split; [apply (PMKA.acc_keepA' L ar LB FF sp 20480 _ M0 M4 EK04 WAPP FRB ois 272 AO ACC)|].
  split. { apply (PMKA.vstr_keepA RSEGS L ar LB FF sp 20480 _ M0 M4 EK04 WAPP FRB); [| exact AOS| exact INCL| | | exact VS].
           - intros bq Hbq. destruct (proj1 (WB0 bq Hbq)) as (X0 & _ & _ & _ & X4 & _). lia.
           - intros i Hi. apply OUTW; lia.
           - intros c n p E j Hj. apply OUTW.
             + subst s. destruct (proj1 (WB0 (p, c) (INCL (p, c) (or_introl eq_refl)))) as (X0 & X1 & _ & _ & X4 & _).
               pose proof (proj2 (proj2 (proj2 (proj2 (WB0 (p, c) (INCL (p, c) (or_introl eq_refl))))))) as (_ & FA & _).
               destruct AO as (g & Hg & Yg1 & Yg2). pose proof (FA g ltac:(apply in_or_app; left; exact Hg)) as Zg. cbn [fst snd ff_addr ff_class] in *. lia.
             + subst s. destruct (proj1 (WB0 (p, c) (INCL (p, c) (or_introl eq_refl)))) as (X0 & X1 & _). cbn [fst snd] in *.
               rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in X1. lia. }
  split; [exact ASTK4|].
  split. { unfold PMAIS.SCR. change (20480 / 8) with 2560. apply (PMKA.stksh_keepA L ar LB FF sp 20480 (PMAIS.WF ois b) M0 M4 EK04 WAPP); [lia| lia| lia| | lia| exact STKSH].
           apply sub8; [exact A16| reflexivity]. }
  split. { apply (base_ok_agree M3 M4); [|exact BASE3]. intros a Ha. unfold brg in Ha. apply KEEP4; [lia| lia| lia|].
           unfold aclient, aclient_g. right; right; left. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [lia|].
           destruct Ha as [Ha|Ha]; [intros X; pose proof (L5A.aly_static_lo L C LYa a X); lia|].
           apply (fun D_ => PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D_)). unfold PMST.dep, pm_initc. cbn [pa_canary pa_need_locks pa_locale_lock PMA.AD ADDR_A].
           destruct Ha as [Ha|[Ha|Ha]];
             [right; left; lia
             | right; right; exists (0x693f93, 0x693f94); split; [left; reflexivity| cbn [fst snd]; lia]
             | right; right; exists (0x694070, 0x694074); split; [right; left; reflexivity| cbn [fst snd]; lia]]. }
  split; [exact LOC4|].
  split; [exact HH4|]. split; [exact AM4|].
  split. { apply (L5LZ.model_rt_trans model0 model3 model4); [|exact MRT4]. apply (L5LZ.model_rt_trans model0 model2 model3); [|exact MRT3].
           apply (L5LZ.model_rt_trans model0 model1 model2); [exact MRT1| exact MRT2]. }
  split; [intros x Hx; apply INC2; apply INC4; exact Hx|].
  split; [intros x Hx; apply IA4; apply IA2; exact Hx|].
  split; [exact EK04| exact DK04].
Qed.
End Stage.
End PMAIS1.
