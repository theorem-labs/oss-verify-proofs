(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PnModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA
     PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnSpecsAX_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgV8A_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b PnRunAa_b
     PmModelFactsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnStepA_b PnStepA2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import XIcptAs0_b PnAIss1_b PnAReaderCtorStmts_b PnAReaderCtor1_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b L5CoreB_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNARCK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma frame_aobj FF fb a n : PNRA.frame_okB FF fb -> fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof. intros ((rs & Hfb) & FB8) H1 H2. exists (fb, 5, rs). split; [exact Hfb| cbn; change (ff_bytes 5) with 2048; lia]. Qed.
Lemma fb16 FF fb : PNRA.frame_okB FF fb -> fb mod 16 = 0.
Proof. intros ((rs & Hfb) & FB8). apply Z.mod_divide; [lia|]. apply (Z.divide_trans 16 2048 fb); [exists 128; reflexivity| apply Z.mod_divide; [lia| exact FB8]]. Qed.

(* [comment removed for export] *)
Lemma vfacts LB FF LK cr Aw M model sp fb oo :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PNRA.frame_okB FF fb -> L5CA.astk ar M sp 24576 -> PMSPA.aobjA FF oo 24 -> oo mod 8 = 0 ->
  PMSPA.accA M (fb + 464) 416 -> PMSPA.accA M (fb + 96) 272 -> PMSPA.accA M oo 24 -> L5.defined M (fb + 464) 416 ->
  let MV := mrestrict (ahid Aw model) M in
  L5.writable RSEGS MV (sp - 4096) 4096 /\ L5.img_clear MV 1249280 1282048 /\ L5.u64_at RSEGS MV 1309752 2147450880 /\ L5.u32_at RSEGS MV 1309760 1
  /\ L5KA.zeros_at MV ((fb + 464 - 368) / 8 + 2147450880) 34 /\ L5KA.zeros_at MV (oo / 8 + 2147450880) 3
  /\ L5.writable RSEGS MV (fb + 464) 416 /\ L5KA.zeros_at MV ((fb + 464) / 8 + 2147450880) 52
  /\ L5KA.zeros_at MV 2147607348 64 /\ L5KA.zeros_at MV 2147609117 32
  /\ 6905856 <= fb + 96 /\ fb + 2048 + 4096 + 24576 <= sp /\ (2147446784 + 17592186048512 <= fb + 96 \/ fb + 880 <= 2147446784)
  /\ fb mod 16 = 0 /\ fb + 2048 <= 2 ^ 47
  /\ 6905856 <= oo /\ oo + 24 + 4096 + 24576 <= sp /\ (2147446784 + 17592186048512 <= oo \/ oo + 24 <= 2147446784) /\ oo + 32 <= 2 ^ 47.
Proof.
  intros HH FOK ASTK AOO OO8 ACC ACCI ACCO ODEF MV.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (fb16 FF fb FOK) as F16. destruct FOK as ((rs & Hfb) & FB8).
  assert (FOK : PNRA.frame_okB FF fb) by (split; [exists rs; exact Hfb| exact FB8]).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn in F1, F2. change (ff_bytes 5) with 2048 in F2.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *.
  assert (AOP : PMSPA.aobjA FF (fb + 464) 416) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (O8 : (fb + 464) mod 8 = 0) by lia. assert (OIS8 : (fb + 96) mod 8 = 0) by lia.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 464) 416 sp 24576 HH (PMKA.aobj_of_aobjA FF _ _ AOP O8) ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model oo 24 sp 24576 HH (PMKA.aobj_of_aobjA FF _ _ AOO OO8) ltac:(lia) ltac:(reflexivity))
    as (OOR & OOBIG & _).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 2008 sp 24576 HH
                (PMKA.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
    as (FR & FBIG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  split. { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
           apply (L5SAR.astk_writable ar M sp 24576); [exact ASTK| lia| lia| lia]. }
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1309752 2147450880 (VIMG 1309752 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1309760 1 (VIMG 1309760 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split. { replace (fb + 464 - 368) with (fb + 96) by lia.
           exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 96) 272 HH AOIS OIS8 ltac:(lia) ltac:(reflexivity) ACCI). }
  split; [exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model oo 24 HH AOO OO8 ltac:(lia) ltac:(reflexivity) ACCO)|].
  split. { apply (proj2 (L5A.writable_vis H M (fb + 464) 416 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  split; [exact (PMKA.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 464) 416 HH AOP O8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split. { pose proof (PNARC1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x1319a0 512 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  split. { pose proof (PNARC1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x1350e8 256 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma svis LB FF LK cr Aw M model sp a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.astk ar M sp 24576 -> sp - 4096 <= a -> a + 8 <= sp ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
  intros HH ASTK H1 H2 X. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & _).
  apply (proj2 (L5A.u64_at_vis _ M a v (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X.
Qed.
Lemma fvis LB FF LK cr Aw M model fb a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PNRA.frame_okB FF fb -> fb + 32 <= a -> a + 8 <= fb + 2040 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
  intros HH FOK H1 H2 X. pose proof (fb16 FF fb FOK) as F16.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 2008 0 0 HH
                (PMKA.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
    as (FR & FBIG & _ & FVIS & _).
  apply (proj2 (L5A.u64_at_vis _ M a v ltac:(eapply L5A.avis_sub; [exact FVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X.
Qed.

(* [comment removed for export] *)
Lemma amset LB FF LK cr Aw sp fr o sz (fx0 : FPState) Ra Ma modela Kc d n ra :
  L5CA.aobj FF o sz -> 0 <= d -> d + n <= sz -> 0 < n <= 96 ->
  ri_inv HI LB FF LK cr Aw Ma (vml_of modela) -> L5CA.amodel_ok Aw modela -> L5CA.astk ar Ma sp 24576 -> PMSPA.accA Ma o sz -> L5.defined Ma o sz ->
  0 <= fr -> fr + 2560 <= 24576 -> (sp - fr) mod 16 = 0 ->
  getr Ra (reg 10) = Z_to_bv 64 (o + d) -> getr Ra (reg 11) = Z_to_bv 64 0 -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (sp - fr) -> Kc [] ->
  (forall Rb Mb modelb, getr Rb (reg 10) = Z_to_bv 64 (o + d) -> regs_preserved Ra Rb -> PM.zeros_at Mb (o + d) n ->
     (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - fr) 2560 a -> ~ (o + d <= a < o + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
     (forall a, sp - fr - 2560 <= a < sp - fr -> Mb (Z_to_bv 64 a) <> None) ->
     L5.defined Mb (o + d) n -> model_rt modela modelb -> L5CA.amodel_ok Aw modelb -> ri_inv HI LB FF LK cr Aw Mb (vml_of modelb) ->
     srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Rb ra Mb modelb) Kc) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Ra 0x78130 Ma modela) Kc.
Proof.
  intros AOB Hd Hdn Hn HHa AMa ASTKa ACCa DEFa Hfr Hfr' F16 Ra10 Ra11 Ra12 Ra4 Ra1 Hra Hra' Ra2 Ka KC.
  pose proof (HAJ.aior_memset _ _ _ _ _ HIok) as MS. unfold amemset_spec, amem_pre, amem_post in MS.
  rewrite (L5A.aly_segs L C LYa), (L5A.aly_memset L C LYa), (L5A.aly_scr_mem L C LYa) in MS.
  assert (U2 : bv_unsigned (getr Ra 2%bv) = sp - fr).
  { rewrite L5K.rl2, Ra2. pose proof ASTKa as (_ & SLO & SHI & SPT & _).
    pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHa) as (_ & _ & FSAPP & FSCEIL & _). unfold app_mem, FS_BYTES in FSAPP, FSCEIL.
    apply L5.unsigned_lit. lia. }
  assert (OB : 0 <= o /\ o + sz <= 2 ^ 47).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHa) as (_ & WF & FSAPP & _). pose proof AOB as (f & Hf & X1 & X2 & _).
    destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. lia. }
  unfold PMSPA.cfg. apply (MS fx0 Ra Ma modela LB FF LK cr Aw (o + d) 0 n Kc); clear MS.
  - split; [exact HHa|]. split; [exact (proj1 AMa)|]. split; [exact (proj2 AMa)|].
    split; [rewrite L5K.rl10; exact Ra10|]. split; [rewrite L5K.rl12; exact Ra12|]. split; [lia|].
    split; [rewrite L5K.rl4; exact Ra4|]. split; [rewrite L5K.rl1, Ra1; apply Hoare.ret_ok_even; rewrite L5.unsigned_lit by lia; exact Hra|].
    split. { rewrite U2. apply (L5SAR.astack_ok_of_astk L ar C LYa Ma Ma sp 24576 fr 2560 ASTKa (fun x X => X)); [lia| lia| lia| exact F16]. }
    split. { intros a Ha. apply ACCa. lia. }
    split. { intros i Hi. rewrite U2. apply (L5SAR.obj_client L ar LB FF _ _ o sz (o + d + i) AOB). lia. }
    split. { intros i m Hi Hm. pose proof (L5C.writable_of_defined RSEGS Ma o sz DEFa ltac:(lia) ltac:(lia)) as W.
             replace (o + d + i) with (o + (d + i)) by lia. apply W; lia. }
    split; [exact Ka|]. apply (L5SAR.app_rng_aobj L ar C HI HIok LB FF LK cr Aw Ma _ o sz (o + d) n HHa AOB); lia.
  - rewrite L5K.rl11. exact Ra11.
  - intros Rb Mb modelb Rb10 RPb BYTES PRES SDEFb RTb MIb HHb. rewrite U2 in PRES, SDEFb. rewrite L5K.rl1, Ra1.
    assert (ZB : PM.zeros_at Mb (o + d) n).
    { intros i Hi. destruct (BYTES i Hi) as (v & Ev & Bv). unfold byte_at in Bv. rewrite Bv. subst v. reflexivity. }
    apply (KC Rb Mb modelb); [rewrite <- L5K.rl10; exact Rb10| exact RPb| exact ZB| exact PRES| exact SDEFb| | exact RTb| | exact HHb].
    + intros i Hi. rewrite (ZB i Hi). discriminate.
    + split; [rewrite (L5LZ.model_rt_halted _ _ RTb); exact (proj1 AMa)| exact MIb].
Qed.

(* [comment removed for export] *)
Lemma mset_post LB FF LK cr Aw sp fr o sz Ma Mb modela d n :
  ri_inv HI LB FF LK cr Aw Ma (vml_of modela) -> L5CA.astk ar Ma sp 24576 -> L5CA.aobj FF o sz -> 0 <= fr -> fr + 2560 <= 24576 -> 0 <= d -> d + n <= sz ->
  (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - fr) 2560 a -> ~ (o + d <= a < o + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
  (forall a, sp - fr - 2560 <= a < sp - fr -> Mb (Z_to_bv 64 a) <> None) -> L5.defined Mb (o + d) n ->
  L5SAR.ek L ar LB FF sp 24576 [(o, sz)] Ma Mb /\ L5SAR.dk L ar LB FF sp 24576 Ma Mb /\ L5CA.astk ar Mb sp 24576.
Proof.
  intros HH ASTK AOB Hfr Hfr' Hd Hdn PRES SDEF DEF. pose proof ASTK as (A16 & SLO & SHI & SPT & SD & SUP).
  assert (OB : 0 <= o /\ o + sz <= ahl_ceil ar).
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & WF & FSAPP & FSCEIL & _). pose proof AOB as (f & Hf & X1 & X2 & _).
    destruct (WF f Hf) as (Y1 & Y2 & _). unfold app_mem, FS_BYTES in *. lia. }
  split. { apply (L5SAR.ek_mem L ar LB FF sp 24576 (sp - fr) 2560 (fun a => o + d <= a < o + d + n) [(o, sz)] Ma Mb PRES); [lia| lia|].
           intros a Hc Ho X. apply (Ho (o, sz)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  split. { apply (L5SAR.dk_mem L ar LB FF sp 24576 (sp - fr) 2560 (fun a => o + d <= a < o + d + n) Ma Mb PRES SDEF); [| | lia| lia].
           - intros a Ha. replace a with (o + d + (a - (o + d))) by lia. apply DEF. lia.
           - intros a. destruct (L5SAR.rng_dec a (o + d) (o + d + n)) as [X|X]; [left; exact X| right; exact X]. }
  apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw Ma Ma Mb _ sp _ (sp - fr) 2560 HH ASTK (fun x X => X)).
  - intros a Ha Hs Hns. apply PRES. exact Ha. apply L5SAR.stack_client. exact Hs. exact Hns. lia.
  - exact SDEF.
  - lia. - lia. - lia.
Qed.
(* [comment removed for export] *)
Lemma ri_swap12 x y l FF LK cr Aw M V : ri_inv HI (x :: y :: l) FF LK cr Aw M V -> ri_inv HI (y :: x :: l) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ (y :: x :: l) FF FF LK cr Aw M V HH).
  - intros b. cbn [In]. tauto.
  - cbn [map] in *. assert (P : y.1 :: x.1 :: map fst l ≡ₚ x.1 :: y.1 :: map fst l) by apply perm_swap. rewrite P. exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

(* [comment removed for export] *)
Lemma rd_credit cr : PMSP.credit_le (PNARCS.cost L ar) cr ->
  acredit_ok L cr 16384 /\ acredit_ok L (adebit L cr 16384) 40 /\ PMSP.credit_keep cr (adebit L (adebit L cr 16384) 40) (PNARCS.cost L ar) (PMSPA.scA L PMSP.cr0).
Proof.
  unfold PNARCS.cost. intros (C1 & C2). destruct (PMA.ly_cost L C LY) as (K1 & K2 & K3).
  unfold PMSPA.scA, PM.credit_add, PM.cost1, PMSPA.HV, LibIfaceAB.heap_view, PM.CHUNK in *. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *.
  unfold acredit_ok, adebit, PMSP.credit_keep, PMSP.cr0, PMSPA.scA. cbn [fst snd]. rewrite K1, K2, K3 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma bparser_init_at M op ois q b :
  L5.u64_at RSEGS M op (pa_vp_parser PMA.AD) -> L5.defined M op 416 -> PMSPA.accA M op 416 ->
  L5.u8_at RSEGS M (op + 8) 1 -> L5.u8_at RSEGS M (op + 9) 0 -> L5.u8_at RSEGS M (op + 10) 0 -> L5.u32_at RSEGS M (op + 12) 0 ->
  L5.u64_at RSEGS M (op + 24) (pa_vp_nullis PMA.AD) -> L5.u64_at RSEGS M (op + 40) (pa_vp_nullbuf PMA.AD) -> L5.u64_at RSEGS M (op + 48) (pa_classic_imp PMA.AD) ->
  L5.u64_at RSEGS M (op + 104) (pa_vp_nullis_ios PMA.AD) -> L5.u32_at RSEGS M (op + 136) 0 -> L5.u32_at RSEGS M (op + 140) 0 -> L5.u64_at RSEGS M (op + 144) (op + 40) ->
  L5.u64_at RSEGS M (op + 152) (pa_classic_imp PMA.AD) -> PM.zeros_at M (op + 160) 80 ->
  L5.u64_at RSEGS M (op + 256) ois -> L5.u64_at RSEGS M (op + 264) (ois + 16) -> L5.u64_at RSEGS M (op + 280) q -> L5.u64_at RSEGS M (op + 288) PM.CHUNK ->
  L5.u64_at RSEGS M (op + 296) q -> L5.u64_at RSEGS M (op + 304) 0 ->
  q mod 16 = 0 -> L5.defined M q PM.CHUNK -> PMSPA.accA M q PM.CHUNK ->
  L5.u32_at RSEGS M (op + 312) 1024 ->
  L5.u64_at RSEGS M (op + 320) 0 -> L5.u64_at RSEGS M (op + 328) 0 -> L5.u64_at RSEGS M (op + 336) 0 ->
  L5.u8_at RSEGS M (op + 344) 0 -> L5.u8_at RSEGS M (op + 368) 0 ->
  PNM.bvec_at RSEGS PMSPA.accA PNRA.annA M (op + 392) b 0 [PNM.bs_root] -> 0 <= op -> op + 416 <= 2 ^ 64 ->
  PNM.bparser_at RSEGS PMA.AD PMSPA.accA PNRA.annA (pa_vp_parser PMA.AD) M op ois (PNRA.bparser_init q b).
Proof.
  intros P0 PD PA P8 P9 P10 P12 P24 P40 P48 P104 P136 P140 P144 P152 P160 P256 P264 P280 P288 P296 P304 Q16 QD QA P312 P320 P328 P336 P344 P368 VEC B0 B1.
  assert (PAs : forall a n, op <= a -> a + n <= op + 416 -> PMSPA.accA M a n) by (intros a n H1 H2; unfold PMSPA.accA in *; apply (L5CB.aacc_sub M op 416); [exact PA| lia| lia]).
  assert (PDs : forall a n, op <= a -> a + n <= op + 416 -> L5.defined M a n) by (intros a n H1 H2; apply (L5.defined_sub M op 416); [exact PD| lia| lia]).
  unfold PNM.bparser_at, PNRA.bparser_init. cbn [PNM.b_more PNM.b_done PNM.b_src PNM.b_bb PNM.b_nb PNM.b_tb PNM.b_sb PNM.b_sk PNM.b_stk PM.sr_qc PM.sr_de PM.sr_rem].
  unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.PSIZE, PNM.MAX_DEPTH.
  split; [exact P0|]. split; [exact PD|]. split; [apply PAs; lia|].
  split; [exact P8|]. split; [exact P9|]. split; [exact P10|]. split; [exact P12|].
  split. { unfold PM.nullis_at, PM.iosb_at. replace (op + 16 + 8) with (op + 24) by lia.
           split; [exact P24|]. split; [apply PDs; lia|]. split; [apply PAs; lia|].
           split; [replace (op + 24 + 16) with (op + 40) by lia; exact P40|]. split; [replace (op + 24 + 24) with (op + 48) by lia; exact P48|].
           split; [replace (op + 24 + 80) with (op + 104) by lia; exact P104|].
           split; [replace (op + 24 + 80 + 32) with (op + 136) by lia; exact P136|].
           split; [replace (op + 24 + 80 + 36) with (op + 140) by lia; exact P140|].
           split; [replace (op + 24 + 80 + 40) with (op + 144) by lia; replace (op + 24 + 16) with (op + 40) by lia; exact P144|].
           split; [replace (op + 24 + 80 + 48) with (op + 152) by lia; exact P152|].
           split; [replace (op + 24 + 80 + 56) with (op + 160) by lia; exact P160|].
           split; [apply PDs; lia|]. split; [apply PAs; lia|]. left; reflexivity. }
  split. { unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
           split; [replace (op + 16 + 240) with (op + 256) by lia; exact P256|]. split; [replace (op + 16 + 248) with (op + 264) by lia; exact P264|].
           split; [apply PDs; lia|].
           split; [replace (op + 16 + 264) with (op + 280) by lia; exact P280|]. split; [replace (op + 16 + 272) with (op + 288) by lia; exact P288|].
           split; [replace (op + 16 + 280) with (op + 296) by lia; exact P296|]. split; [replace (op + 16 + 288) with (op + 304) by lia; exact P304|].
           split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact Q16|]. split; [exact QD|]. split; [exact QA|].
           apply PAs; lia. }
  split; [exact P312|]. split; [apply PAs; lia|].
  split. { unfold PGV8.v8_at. split; [apply PDs; lia|]. split; [apply PAs; lia|].
           split; [exact P320|]. split; [replace (op + 320 + 8) with (op + 328) by lia; exact P328| replace (op + 320 + 16) with (op + 336) by lia; exact P336]. }
  split. { unfold PM.vstr_at. split; [apply PDs; lia|]. split; [apply PAs; lia|]. split; [lia| exact P344]. }
  split. { unfold PM.vstr_at. split; [apply PDs; lia|]. split; [apply PAs; lia|]. split; [lia| exact P368]. }
  split; [exact VEC|]. split; [right; reflexivity| left; reflexivity].
Qed.
End Kit.
End PNARCK.
