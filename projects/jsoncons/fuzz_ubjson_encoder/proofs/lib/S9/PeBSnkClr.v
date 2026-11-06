(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAb PgV8 PnModel PnModelFacts PeSpecsAX PmModelFactsA PmStep PeStepAB0 PeStepB2 PmCertKitG PeBIss1 PeBEmbKit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeSpecsBX PeBDtorHP PeBSnkAnn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.asan Require Import L5CoreBB0S9.
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
Module PEBSKC.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition clear_b_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b n c : Z) (sp r : Z),
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 ->
    PEBSKAN.bat segs M v b n c ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> PEBSKAN.bat segs M' v b 0 c ->
        (forall a, b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ([(b, c)] ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
End Specs.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma negmod x : 0 < x < 2 ^ 64 -> (18446744073709551615 * x) mod 2 ^ 64 = 2 ^ 64 - x.
Proof.
  intros Hx. replace (18446744073709551615 * x) with ((2 ^ 64 - x) + (x - 1) * 2 ^ 64) by (change (2 ^ 64) with 18446744073709551616; Lia.lia).
  rewrite Z_mod_plus_full. apply Z.mod_small. Lia.lia.
Qed.
Definition KC : list nat := [1; 2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma clear_core : PEBSKAN.ann_shrink_b_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab24c ->
  forall (fx : FPState) R M model K LBX FF LK Aw cr v b n c sp r,
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PeCLayoutB.CADDR_B L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 ->
    PEBSKAN.bat RSEGS M v b n c ->
    (exists fx1 R1 M1v, mem_grows (mrestrict (ahid Aw model) M) M1v
       /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp - 16 + 16) -> ~ (v + 8 <= i < v + 8 + 8) -> M1v (Z_to_bv 64 i) = mrestrict (ahid Aw model) M (Z_to_bv 64 i))
       /\ msteps RSEGS (st fx R 0xab104 (mrestrict (ahid Aw model) M)) (st fx1 R1 0xab24c M1v)
       /\ (forall k, In k KC -> getr R1 (reg k) = getr R (reg k))
       /\ getr R1 (reg 11) = Z_to_bv 64 n
       /\ L5.u64_at RSEGS M1v (v + 8) b) ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' -> PEBSKAN.bat RSEGS M' v b 0 c ->
        (forall a, b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ([(b, c)] ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xab104 M model) K.
Proof.
  intros ASH fx R M model K LBX FF LK Aw cr v b n c sp r HH AM K0 ENT FRS A10 AOV V8 VAT RUN KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  unfold PEBSKAN.bat in VAT. destruct VAT as (VDEF & VACC & VX).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  destruct RUN as (fx1 & R1 & M1v & MG1 & FZ1 & MS1 & KS1 & fR11 & T8).
  set (W1 := fun a => (sp - 16 <= a < sp - 16 + 16) \/ (v + 8 <= a < v + 8 + 8)).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xab104 R1 0xab24c M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| intros Q; apply N; left; exact Q| intros Q; apply N; right; exact Q]. }
  { intros a Ha Wa. split.
    - destruct Wa as [Q|Q]; unfold aclientw, aclient_g.
      + right; left. split; [lia| intros Y; lia].
      + do 3 right; left. destruct AOV as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. split; [lia| intros Y; lia].
    - destruct Wa as [Q|Q]; lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.

  assert (NSH : forall a, 2147450880 <= a < 2147450880 + 2 ^ 44 -> ~ W1 a).
  { intros a Ha [Q|Q]; [clear - Ha Q SLO SPT; lia|]. destruct OBIG as [Y|Y]; clear - Ha Q Y; lia. }
  assert (SHK : forall a, 2147450880 <= a < 2147450880 + 2 ^ 44 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. apply FR1; [clear - Ha; lia| exact (NSH a Ha)]. }
  assert (AGS : forall a m, 0 <= a -> a + m <= 2 ^ 47 -> PMFA.agsh M M1 a m).
  { intros a m Ha Hn z Hz. apply SHK. exact (PNBEK.S_range z ltac:(clear - Ha Hn Hz; lia)). }
  assert (ASTK1 : L5CA.astk ar M1 sp 12288) by exact (L5SAR.astk_grows ar M M1 sp 12288 ASTK MGM1).
  assert (SZ1 : shadow_zero M1 (sp - 12288) 1536).
  { intros j Hj. unfold byte_at. rewrite SHK; [exact (STKSH j Hj)|]. unfold S, SB.
    assert (Q1 : 0 <= (sp - 12288) / 8) by (apply Z.div_pos; clear - SLO SHI SPT; lia).
    assert (Q2 : (sp - 12288) / 8 <= 2 ^ 44 - 1536) by (apply Z.div_le_upper_bound; [clear; lia| clear - SHI SPT; lia]).
    clear - Hj Q1 Q2. lia. }
  assert (E1 : forall k, In k KC -> getr R1 (reg k) = getr R (reg k)) by exact KS1.
  assert (VH1 : forall a w, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M1v a w -> L5.u64_at RSEGS M1 a w).
  { intros a w Ha1 Ha2 U. rewrite <- VIS1 in U.
    exact (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a w (L5A.avis_sub _ v 24 a 8 OVIS ltac:(clear - Ha1; lia) ltac:(clear - Ha2; lia)) ltac:(clear - Ha1 OR; lia) ltac:(clear - Ha2 OR; lia)) U). }
  apply VH1 in T8; [| clear; lia| clear; lia].
  assert (KEEPW : forall a w, v <= a -> a + 8 <= v + 24 -> (a + 8 <= v + 8 \/ v + 16 <= a) -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M1 a w).
  { intros a w Ha1 Ha2 Ha3 U. apply (L5C.u64_at_agree RSEGS M M1); [| clear - Ha1 OR; lia| clear - Ha2 OR; lia| exact U].
    intros i Hi. apply FR1; [clear - Hi Ha1 Ha2 OR; lia|]. intros [Q|Q]; [clear - Q Hi Ha1 Ha2 OR SLO; lia| clear - Q Hi Ha3; lia]. }

  unfold PEBSKAN.ann_shrink_b_spec in ASH.
  apply (ASH fx1 R1 M1 model1 K LBX FF LK Aw cr v n b 0 c sp r).
  { exact HH1. }
  { exact AM1. }
  { exact K0. }
  { split; [rewrite L5K.rl1, (E1 1%nat) by inl; exact Rra|]. split; [exact RAok|].
    split; [rewrite L5K.rl2, (E1 2%nat) by inl; exact Rsp|].
    split; [rewrite L5K.rl3, (E1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4, (E1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1|]. change (12288 / 8) with 1536. exact SZ1. }
  { exact FRS. }
  { rewrite L5K.rl10, (E1 10%nat) by inl. exact A10. }
  { rewrite L5K.rl11. exact fR11. }
  { exact AOV. }
  { exact V8. }
  { apply (PMFA.accA_agree M M1 v 24); [| exact VACC]. apply AGS; [clear - OR; lia| clear - OR; lia]. }
  { unfold PEBSKAN.bhdr. split; [exact (L5.defined_grows M M1 _ _ MGM1 VDEF)|].
      destruct VX as (X0 & X8 & X16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
      split; [apply (KEEPW v b); [clear; lia| clear; lia| left; clear; lia| exact X0]|].
      split; [replace (b + 0) with b by (clear; lia); exact T8|].
      split; [apply (KEEPW (v + 16) (b + c)); [clear; lia| clear; lia| right; clear; lia| exact X16]|].
      split; [clear - NC; lia|]. split; [exact C27|]. split; [exact B4096|]. split; [exact B16|]. exact (L5.defined_grows M M1 _ _ MGM1 BDEF). }
  { destruct VX as (_ & _ & _ & NC & _). clear - NC. lia. }
  { destruct VX as (X0 & X8 & X16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
    assert (BIN : In (b, c) LB) by (left; reflexivity).
    destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _).
    split.
    - apply (PMFA.accA_agree M M1 b n); [| exact BACC]. apply AGS; [clear - Bq0; lia| clear - Bq3 NC; lia].
    - apply (PNBEK.ann_agree M M1 b n c); [| clear - NC; lia| clear - NC; lia| exact BANN].
      intros j Hj. apply SHK. exact (PNBEK.shadow_lowU b c j ltac:(clear - Bq0; lia) Bq3 Hj). }
  intros fx2 R2 M2 model2 LK2 Aw2 RP2 VAT2 BK2 AHP2 RT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in AHP2.
  apply (KONT fx2 R2 M2 model2 LK2 Aw2).
  - apply (L5SAR.regs_preserved_trans R R1 R2); [| exact RP2]. apply L5SAR.preserved_by_index. intros k Hk. apply E1. revert k Hk. apply (L5K.incl_b L5SAR.cs_all KC). vm_compute. reflexivity.
  - exact VAT2.
  - intros a Ha. rewrite (BK2 a Ha).
    destruct VX as (X0 & X8 & X16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
    assert (BIN : In (b, c) LB) by (left; reflexivity).
    destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
    apply FR1; [clear - Ha Bq0 Bq3; lia|]. intros [Q|Q]; [clear - Q Ha Bq2 SLO; lia|].
    destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; clear - Q Ha Y Y1 Y2; lia.
  - destruct AHP2 as (EK2 & SD2 & DK2). apply (L5SAR.ahpres_of L ar LBX FF sp 12288 [(v + 8, 8)] M M2).
    + eapply L5SAR.ek_trans.
      * apply (L5SAR.ek_piece L ar LBX FF sp 12288 [(v + 8, 8)] M M1 W1 FR1). intros a Ha Hc Ho [Q|Q].
        -- destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M (vml_of model) sp 12288 a HH ltac:(clear - SPT; lia) ltac:(apply L5SAR.aclient_appb; exact Hc)) as [(Y1 & Y2)|Y]; [apply Y2; clear - Q; lia| clear - Y Q SLO; lia].
        -- apply (Ho (v + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Q; lia].
      * apply (L5SAR.ek_W L ar LBX FF sp 12288 [(v + 8, 8)] [] M1 M2 EK2). intros a _ rr [].
    + exact SD2.
    + eapply L5SAR.dk_trans; [apply (L5SAR.dk_grows L ar LBX FF sp 12288 M M1 MGM1)| exact DK2].
  - eapply L5LZ.model_rt_trans; [exact MRT1| exact RT2].
  - exact ILK2.
  - exact IAW2.
  - exact AM2.
  - exact HH2.
Qed.

Theorem clear_b_of : PEBSKAN.ann_shrink_b_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab24c -> clear_b_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab104.
Proof.
  intros ASH. unfold clear_b_spec.
  intros fx R M model K LBX FF LK Aw cr v b n c sp r HH AM K0 ENT FRS A10 AOV V8 VAT KONT.
  apply (clear_core ASH fx R M model K LBX FF LK Aw cr v b n c sp r HH AM K0 ENT FRS A10 AOV V8 VAT); [| exact KONT].
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  unfold PEBSKAN.bat in VAT. destruct VAT as (VDEF & VACC & VX).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear (mrestrict (ahid Aw model) M) 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS (mrestrict (ahid Aw model) M) 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis _ M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS (mrestrict (ahid Aw model) M) 1335552 1) by (apply (proj2 (L5A.u32_at_vis _ M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS (mrestrict (ahid Aw model) M) (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis _ M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at (mrestrict (ahid Aw model) M) (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) VACC). }
  assert (X9 : L5.writable RSEGS (mrestrict (ahid Aw model) M) v 24).
  { apply (proj2 (L5A.writable_vis _ M v 24 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact VDEF| lia| lia]. }
  assert (UV : forall a w, v <= a -> a + 8 <= v + 24 -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS (mrestrict (ahid Aw model) M) a w).
  { intros a w Ha1 Ha2 U. exact (proj2 (L5A.u64_at_vis _ M a w (L5A.avis_sub _ v 24 a 8 OVIS ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) U). }
  assert (Q1 : 0 <= sp < 2 ^ 64) by lia. assert (Q2 : 0 <= v < 2 ^ 64) by lia.
  assert (Q3 : 140735332491264 <= sp <= 140737488355328) by lia.
  assert (Q4 : 6930432 <= v <= 140737488355295) by lia.
  assert (Q5 : 2147446784 + 17592186048512 <= v \/ v + 24 <= 2147446784) by lia.
  assert (Q6 : (sp - 4096) + 4096 <= v \/ v + 24 <= (sp - 4096)) by lia.
  assert (Q7 : 65536 + 6864896 <= v \/ v + 24 <= 65536) by lia.
  remember (mrestrict (ahid Aw model) M) as MV eqn:EMV.
  - destruct VX as (W0 & W8 & W16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
    assert (BIN : In (b, c) LB) by (left; reflexivity).
    destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _).
    apply UV in W0; [| lia| lia]. apply UV in W8; [| lia| lia]. apply UV in W16; [| lia| lia].
    assert (Q8 : 0 <= b < 2 ^ 64) by lia. assert (Q9 : 0 <= c < 2 ^ 64) by lia. assert (Q10 : 4096 <= b <= 140737488355327) by lia. assert (QC : 1 <= c <= 140737488355328) by lia.
    destruct (Z.eq_dec n 0) as [N0|N1].
    +
      subst n. replace (b + 0) with b in W8 by lia.
      pose proof (PEBDHP.hkcE_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 41%nat => c | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | exact V8 | exact A16 | exact B16]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR11 & _ & _ & _ & T8).
      exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|]. split; [| split; [exact fR11| exact T8]].
      intros k Hk. apply KS1. revert k Hk. apply (L5K.incl_b KC PEBDHP.KS_hkcE). vm_compute. reflexivity.
    +
      assert (Q11 : 0 <= n < 2 ^ 64) by lia. assert (Q12 : 1 <= n <= 140737488355328) by lia. assert (Q13 : 0 <= c - n <= 140737488355328) by lia.
      pose proof (PEBDHP.hkcA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P. cbn beta iota in P.
      L5SAR.feed P ltac:(first [assumption | exact V8 | exact A16 | exact B16]).
      destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & [(MS1 & KS1 & fR11 & _ & _ & _ & _ & _ & T8 & _)|(_ & _ & _ & _ & _ & _ & _ & _ & _ & TRAP & _)]).
      * exists fx1, R1, M1v. split; [exact MG1|]. split; [exact FZ1|]. split; [exact MS1|]. split; [| split; [exact fR11| exact T8]].
        intros k Hk. apply KS1. revert k Hk. apply (L5K.incl_b KC PEBDHP.KS_hkcA_0). vm_compute. reflexivity.
      * exfalso. rewrite (negmod n), (negmod b) in TRAP by (clear - Q10 Q12; Lia.lia).
        replace (2 ^ 64 - b + (2 ^ 64 - n)) with ((2 ^ 64 - b - n) + 1 * 2 ^ 64) in TRAP by (clear; Lia.lia).
        rewrite Z_mod_plus_full, Z.mod_small in TRAP by (clear - Q10 Q12; Lia.lia). clear - TRAP Q10. Lia.lia.
Qed.

Theorem clear_b_ok (EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT) : clear_b_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xab104.
Proof. exact (clear_b_of (PEBSKAN.ann_shrink_b_ok L ar C HI LY HIok EXT)). Qed.
End Stage.
End PEBSKC.
