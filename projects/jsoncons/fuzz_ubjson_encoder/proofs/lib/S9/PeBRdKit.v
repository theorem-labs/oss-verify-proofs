(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PmStep PeStepAB0 PeStepB2 PmCertKitG XIcptAs0B0 PeBIss1 PeBCRdCtor1 PeBCRdCtorStmts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import XIcptAB0S9 XIcptAs0KitB0S9 L5CoreBB0S9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PMBRDK.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Section Kit.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Lemma frame_aobj FF fb a n : PECA.frame_ok5 FF fb -> fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n.
Proof. intros ((rs & Hfb) & FB8) H1 H2. exists (fb, 5, rs). split; [exact Hfb| cbn; change (ff_bytes 5) with 2048; lia]. Qed.
Lemma fb16 FF fb : PECA.frame_ok5 FF fb -> fb mod 16 = 0.
Proof. intros ((rs & Hfb) & FB8). apply Z.mod_divide; [lia|]. apply (Z.divide_trans 16 2048 fb); [exists 128; reflexivity| apply Z.mod_divide; [lia| exact FB8]]. Qed.

Lemma vfacts LB FF LK cr Aw M model sp fb :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb -> L5CA.astk ar M sp 24576 ->
  PMSPA.accA M (fb + 592) 384 -> PMSPA.accA M (fb + 96) 272 -> PMSPA.accA M (fb + 1056) 32 -> L5.defined M (fb + 592) 384 ->
  let MV := mrestrict (ahid Aw model) M in
  L5.writable RSEGS MV (sp - 4096) 4096 /\ L5.img_clear MV 1273856 1306624 /\ L5.u64_at RSEGS MV 1335544 2147450880 /\ L5.u32_at RSEGS MV 1335552 1
  /\ L5KA.zeros_at MV ((fb + 592 - 496) / 8 + 2147450880) 34 /\ L5KA.zeros_at MV ((fb + 592 + 464) / 8 + 2147450880) 4
  /\ L5.writable RSEGS MV (fb + 592) 384 /\ L5KA.zeros_at MV ((fb + 592) / 8 + 2147450880) 48
  /\ L5KA.zeros_at MV 2147610480 64 /\ L5KA.zeros_at MV 2147612318 32
  /\ 6930432 <= fb + 96 /\ fb + 1024 + 4096 + 24576 <= sp /\ (2147446784 + 17592186048512 <= fb + 96 \/ fb + 1088 <= 2147446784)
  /\ fb mod 16 = 0 /\ fb + 2048 <= 2 ^ 47.
Proof.
  intros HH FOK ASTK ACC ACCI ACCO ODEF MV.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (fb16 FF fb FOK) as F16. destruct FOK as ((rs & Hfb) & FB8).
  assert (FOK : PECA.frame_ok5 FF fb) by (split; [exists rs; exact Hfb| exact FB8]).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _).
  pose proof (WF _ Hfb) as (F1 & F2 & _). cbn in F1, F2. change (ff_bytes 5) with 2048 in F2.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *.
  assert (AOP : PMSPA.aobjA FF (fb + 592) 384) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (AOIS : PMSPA.aobjA FF (fb + 96) 272) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (AOO : PMSPA.aobjA FF (fb + 1056) 32) by (apply (frame_aobj FF fb); [exact FOK| lia| lia]).
  assert (O8 : (fb + 592) mod 8 = 0) by lia. assert (OIS8 : (fb + 96) mod 8 = 0) by lia. assert (OO8 : (fb + 1056) mod 8 = 0) by lia.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 592) 384 sp 24576 HH (PMKB.aobj_of_aobjA FF _ _ AOP O8) ltac:(lia) ltac:(reflexivity))
    as (OR & OBIG & ODEF' & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 2008 sp 24576 HH
                (PMKB.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
    as (FR & FBIG & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  split. { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
           apply (L5SAR.astk_writable ar M sp 24576); [exact ASTK| lia| lia| lia]. }
  split; [apply L5A.img_clear_mrestrict; exact GOT|].
  split; [apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB|].
  split; [apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR|].
  split. { replace (fb + 592 - 496) with (fb + 96) by lia.
           exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 96) 272 HH AOIS OIS8 ltac:(lia) ltac:(reflexivity) ACCI). }
  split. { replace (fb + 592 + 464) with (fb + 1056) by lia.
           exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 1056) 32 HH AOO OO8 ltac:(lia) ltac:(reflexivity) ACCO). }
  split. { apply (proj2 (L5A.writable_vis H M (fb + 592) 384 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS). exact ODEF. lia. lia. }
  split; [exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 592) 384 HH AOP O8 ltac:(lia) ltac:(reflexivity) ACC)|].
  split. { pose proof (PMBRD1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x137b80 512 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  split. { pose proof (PMBRD1.img_sh_vis L ar C IL HI LY ICok ILY LB FF LK cr Aw M model 0x13b4f0 256 HH ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(reflexivity)
                         ltac:(repeat constructor; cbn [fst snd]; lia)) as X. exact X. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F16| lia].
Qed.

Lemma svis LB FF LK cr Aw M model sp a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.astk ar M sp 24576 -> sp - 4096 <= a -> a + 8 <= sp ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
  intros HH ASTK H1 H2 X. pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & _).
  apply (proj2 (L5A.u64_at_vis _ M a v (VIS a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X.
Qed.
Lemma fvis LB FF LK cr Aw M model fb a v :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PECA.frame_ok5 FF fb -> fb + 32 <= a -> a + 8 <= fb + 2040 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a v.
Proof.
  intros HH FOK H1 H2 X. pose proof (fb16 FF fb FOK) as F16.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model (fb + 32) 2008 0 0 HH
                (PMKB.aobj_of_aobjA FF _ _ (frame_aobj FF fb (fb + 32) 2008 FOK ltac:(lia) ltac:(lia)) ltac:(lia)) ltac:(lia) ltac:(reflexivity))
    as (FR & FBIG & _ & FVIS & _).
  apply (proj2 (L5A.u64_at_vis _ M a v ltac:(eapply L5A.avis_sub; [exact FVIS| lia| lia]) ltac:(lia) ltac:(lia))). exact X.
Qed.

Lemma amset LB FF LK cr Aw sp fr o sz (fx0 : FPState) Ra Ma modela Kc d n ra :
  L5CA.aobj FF o sz -> 0 <= d -> d + n <= sz -> 0 < n <= 48 ->
  ri_inv HI LB FF LK cr Aw Ma (vml_of modela) -> L5CA.amodel_ok Aw modela -> L5CA.astk ar Ma sp 24576 -> PMSPA.accA Ma o sz -> L5.defined Ma o sz ->
  0 <= fr -> fr + 2560 <= 24576 -> (sp - fr) mod 16 = 0 ->
  getr Ra (reg 10) = Z_to_bv 64 (o + d) -> getr Ra (reg 11) = Z_to_bv 64 0 -> getr Ra (reg 12) = Z_to_bv 64 n -> getr Ra (reg 4) = Z_to_bv 64 (hl_tp L) ->
  getr Ra (reg 1) = Z_to_bv 64 ra -> ra mod 2 = 0 -> 0 <= ra < 2 ^ 64 -> getr Ra (reg 2) = Z_to_bv 64 (sp - fr) -> Kc [] ->
  (forall Rb Mb modelb, getr Rb (reg 10) = Z_to_bv 64 (o + d) -> regs_preserved Ra Rb -> PM.zeros_at Mb (o + d) n ->
     (forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF (sp - fr) 2560 a -> ~ (o + d <= a < o + d + n) -> Mb (Z_to_bv 64 a) = Ma (Z_to_bv 64 a)) ->
     (forall a, sp - fr - 2560 <= a < sp - fr -> Mb (Z_to_bv 64 a) <> None) ->
     L5.defined Mb (o + d) n -> model_rt modela modelb -> L5CA.amodel_ok Aw modelb -> ri_inv HI LB FF LK cr Aw Mb (vml_of modelb) ->
     srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Rb ra Mb modelb) Kc) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS (fx:=fx0) Ra 0x792dc Ma modela) Kc.
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

Lemma ri_swap12 x y l FF LK cr Aw M V : ri_inv HI (x :: y :: l) FF LK cr Aw M V -> ri_inv HI (y :: x :: l) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ (y :: x :: l) FF FF LK cr Aw M V HH).
  - intros b. cbn [In]. tauto.
  - cbn [map] in *. assert (P : y.1 :: x.1 :: map fst l ≡ₚ x.1 :: y.1 :: map fst l) by apply perm_swap. rewrite P. exact ND.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

Lemma rd_credit cr : PMSPA.credit_le (PMBRS.cost L ar) cr ->
  acredit_ok L cr 16384 /\ acredit_ok L (adebit L cr 16384) 32 /\ PMSPA.credit_keep cr (adebit L (adebit L cr 16384) 32) (PMBRS.cost L ar) PMSPA.cr0.
Proof.
  unfold PMBRS.cost. intros (C1 & C2). destruct (PMB.ly_cost L C LY) as (K1 & K2 & K3).
  unfold PMSPA.scA, PM.credit_add, PM.cost1, PMSPA.HV, LibIfaceAB.heap_view, PM.CHUNK in *. cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *.
  unfold acredit_ok, adebit, PMSPA.credit_keep, PMSPA.cr0. cbn [fst snd]. rewrite K1, K2, K3 in *. lia.
Qed.

Lemma parser_init_at M op ois q b :
  L5.u64_at RSEGS M op (pa_vp_parser PeCLayoutB.CADDR_B) -> L5.defined M op 384 -> PMSPA.accA M op 384 ->
  L5.u8_at RSEGS M (op + 8) 1 -> L5.u8_at RSEGS M (op + 9) 0 -> L5.u32_at RSEGS M (op + 12) 0 -> L5.u8_at RSEGS M (op + 16) 0 -> L5.u32_at RSEGS M (op + 20) 0 ->
  L5.u64_at RSEGS M (op + 32) (pa_vp_nullis PeCLayoutB.CADDR_B) -> L5.u64_at RSEGS M (op + 48) (pa_vp_nullbuf PeCLayoutB.CADDR_B) -> L5.u64_at RSEGS M (op + 56) (pa_classic_imp PeCLayoutB.CADDR_B) ->
  L5.u64_at RSEGS M (op + 112) (pa_vp_nullis_ios PeCLayoutB.CADDR_B) -> L5.u32_at RSEGS M (op + 144) 0 -> L5.u32_at RSEGS M (op + 148) 0 -> L5.u64_at RSEGS M (op + 152) (op + 48) ->
  L5.u64_at RSEGS M (op + 160) (pa_classic_imp PeCLayoutB.CADDR_B) -> PM.zeros_at M (op + 168) 80 ->
  L5.u64_at RSEGS M (op + 264) ois -> L5.u64_at RSEGS M (op + 272) (ois + 16) -> L5.u64_at RSEGS M (op + 288) q -> L5.u64_at RSEGS M (op + 296) PM.CHUNK ->
  L5.u64_at RSEGS M (op + 304) q -> L5.u64_at RSEGS M (op + 312) 0 ->
  q mod 16 = 0 -> L5.defined M q PM.CHUNK -> PMSPA.accA M q PM.CHUNK ->
  L5.u32_at RSEGS M (op + 320) PM.MAX_DEPTH -> L5.u64_at RSEGS M (op + 328) PM.MAX_ITEMS -> L5.u8_at RSEGS M (op + 336) 0 ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA M (op + 360) b 0 [PM.ps_root] -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois (PMSPA.parser_init q b).
Proof.
  intros P0 PD PA P8 P9 P12 P16 P20 P32 P48 P56 P112 P144 P148 P152 P160 P168 P264 P272 P288 P296 P304 P312 Q16 QD QA P320 P328 P336 VEC B0 B1.
  assert (PAs : forall a n, op <= a -> a + n <= op + 384 -> PMSPA.accA M a n) by (intros a n H1 H2; unfold PMSPA.accA in *; apply (L5CB.aacc_sub M op 384); [exact PA| lia| lia]).
  assert (PDs : forall a n, op <= a -> a + n <= op + 384 -> L5.defined M a n) by (intros a n H1 H2; apply (L5.defined_sub M op 384); [exact PD| lia| lia]).
  unfold PM.parser_at, PMSPA.parser_init. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_b PM.p_k PM.p_stk].
  split; [exact P0|]. split; [exact PD|]. split; [apply PAs; lia|].
  split; [exact P8|]. split; [exact P9|]. split; [exact P12|]. split; [exact P16|]. split; [exact P20|].
  split. { unfold PM.nullis_at, PM.iosb_at.
           split; [exact P32|]. split; [apply PDs; lia|]. split; [apply PAs; lia|].
           split; [replace (op + 32 + 16) with (op + 48) by lia; exact P48|]. split; [replace (op + 32 + 24) with (op + 56) by lia; exact P56|].
           split; [replace (op + 32 + 80) with (op + 112) by lia; exact P112|].
           split; [replace (op + 32 + 80 + 32) with (op + 144) by lia; exact P144|].
           split; [replace (op + 32 + 80 + 36) with (op + 148) by lia; exact P148|].
           split; [replace (op + 32 + 80 + 40) with (op + 152) by lia; replace (op + 32 + 16) with (op + 48) by lia; exact P152|].
           split; [replace (op + 32 + 80 + 48) with (op + 160) by lia; exact P160|].
           split; [replace (op + 32 + 80 + 56) with (op + 168) by lia; exact P168|].
           split; [apply PDs; lia|]. split; [apply PAs; lia|]. left; reflexivity. }
  split. { unfold PM.src_fields_at. cbn [PM.sr_qc PM.sr_de PM.sr_rem].
           split; [replace (op + 24 + 240) with (op + 264) by lia; exact P264|]. split; [replace (op + 24 + 248) with (op + 272) by lia; exact P272|].
           split; [apply PDs; lia|].
           split; [replace (op + 24 + 264) with (op + 288) by lia; exact P288|]. split; [replace (op + 24 + 272) with (op + 296) by lia; exact P296|].
           split; [replace (op + 24 + 280) with (op + 304) by lia; exact P304|]. split; [replace (op + 24 + 288) with (op + 312) by lia; exact P312|].
           split; [lia|]. split; [lia|]. split; [unfold PM.CHUNK; lia|]. split; [exact Q16|]. split; [exact QD|]. split; [exact QA|].
           apply PAs; lia. }
  split; [exact P320|]. split; [exact P328|]. split; [apply PAs; lia|].
  split. { unfold PM.vstr_at. split; [apply PDs; lia|]. split; [apply PAs; lia|]. split; [lia| exact P336]. }
  split; [exact VEC|]. split; [right; reflexivity|]. split; [left; reflexivity|]. unfold PM.MAX_DEPTH; lia.
Qed.
End Kit.
End PMBRDK.
