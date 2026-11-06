(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx IcptIfaceA
     L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PnLayoutA PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs PmSpecsA PmSpecsAX PnSpecsAa
     PmModelFactsA PnStepA PmStep PnASrcKit PnAVu8GrowP Ba0_code_b3ec4_b3ec8 PgSrc PgSrcA PgV8 PgV8A PgV8KitA PnLayout PnRunA PnSpecsAX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGVRZA.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Theorem vu8_resize_ok :
  PGV8A.vu8_append_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_append PMA.AN) ->
  PNSAX.ann_shrink_v8_spec RSEGS AD L ar HI 0xab138 ->
  PGV8A.vu8_resize_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_resize PMA.AN).
Proof.
  intros APP ANNS. unfold PGV8A.vu8_resize_spec, PGV8A.vu8_grow_spec.
  intros fx R M model K LB FF LK Aw cr v a sp r g x HH AM K0 ENT FRM FRS A10 A11 AO V8 ACC VS OK Ha GOK CRL KONT.
  cbn [PNL.pn_vu8_resize PMA.AN NADDR_A].
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11.
  change (PMSPA.pm_scr 1) with 14336 in ASTK, STKSH. change (14336 / 8) with 1792 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & _).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 14336 16 HH ASTK ltac:(lia)) as (SL16 & SH16 & V3).
  pose proof (PGV8KA.v8_visG L ar C HI LY HIok _ FF LK cr Aw M model v x HH AO V8 VS) as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & _ & TFS1 & TFS2).
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, TFS1, TFS2.
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  assert (X0 : L5.img_clear MV 1236992 1269760) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1300408 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1300408 2147450880 (VIMG 1300408 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1300416 1) by (apply (proj2 (L5A.u32_at_vis H M 1300416 1 (VIMG 1300416 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (VSP : v + 24 <= sp - 16 \/ sp <= v) by (left; clear - TCE SL16; lia).
  destruct VS as (VD & VC & VR).
  (* [comment removed for export] *)
  assert (HW : exists b n0, L5.u64_at RSEGS M v b /\ L5.u64_at RSEGS M (v + 8) (b + n0) /\ 0 <= b <= 2 ^ 47 /\ 0 <= n0 <= 2 ^ 27 /\ PGV8.v8_data x = b /\ PGV8.v8_size x = n0 /\ n0 <= PGV8.v8_cap x).
  { destruct x as [|b n0 c]; cbn [PGV8.v8_size PGV8.v8_cap PGV8.v8_data].
    - destruct VR as (U0 & U8 & _). exists 0, 0. split; [exact U0|]. split; [exact U8|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity| lia].
    - destruct VR as (U0 & U8 & _ & Hn & Hc & Hb & _).
      destruct (BRB (b, c) ltac:(left; reflexivity)) as (Q0 & Q1). cbn [fst snd] in Q0, Q1.
      exists b, n0. split; [exact U0|]. split; [exact U8|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity| lia]. }
  destruct HW as (b & n0 & U0 & U8 & Hb & Hn0 & XB & XN & XC).
  assert (Ha27 : 0 <= a <= 2 ^ 27).
  { unfold PGV8.v8_grow_ok in GOK. destruct x as [|b' n' c']; cbn [PGV8.v8_cap] in GOK, XC; [lia|]. destruct VR as (_ & _ & _ & _ & Hc & _). lia. }
  LeanFeed.pfeed PP (PMAVGP.avzA_conc fx R MV (fun j => match j with 2%nat => sp | 37%nat => v | 40%nat => b | 41%nat => n0 | 43%nat => a | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ v _ => unfold MV, H; vis64 TAV
      | |- L5.u64_at _ _ (v + _) _ => unfold MV, H; vis64 TAV
      | |- PMAVGP.aligned _ _ => unfold PMAVGP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun i => (sp - 16 <= i < sp - 16 + 16) \/ (v + 8 <= i < v + 8 + 8)).
  assert (FZ : forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi N. apply FRZ1; [exact Hi| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  assert (WOB : forall i, 0 <= i < 2 ^ 64 -> P i -> aclientw L ar (PGV8.v8_own x ++ LB) FF 0 0 i /\ ~ (0x10000 <= i < 0x694000)).
  { intros i Hi [Wa|Wa]; (split; [|lia]).
    - unfold aclientw, aclient_g. right; left. split; [lia| lia].
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & Y1 & Y2). exists f. split; [exact Hf|]. clear - Wa Y1 Y2. lia. }
  (* [comment removed for export] *)
  assert (POST : forall M1, mrestrict H M1 = M1v -> mem_grows M M1 -> (forall i, 0 <= i < 2 ^ 64 -> ~ P i -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
            L5SAR.ek L ar LB FF sp 14336 [(v, 24)] M M1 /\ L5CA.astk ar M1 sp 14336 /\ shadow_zero M1 (sp - 14336) 1792 /\ PMSPA.accA M1 v 24 /\ L5.defined M1 v 24
            /\ L5.u64_at RSEGS M1 v b /\ (forall q, L5.u64_at RSEGS M1v (v + 8) q -> L5.u64_at RSEGS M1 (v + 8) q)
            /\ (forall b' n' c', x = PGV8.V8Blk b' n' c' -> L5.u64_at RSEGS M1 (v + 16) (b' + c') /\ L5.defined M1 b' c' /\ (forall u, 0 <= u <= c' -> PMSPA.accA M b' u -> PMSPA.accA M1 b' u)
                                 /\ (forall u, 0 <= u <= c' -> PGV8A.annA M b' u c' -> PGV8A.annA M1 b' u c'))
            /\ (x = PGV8.V8Null -> L5.u64_at RSEGS M1 (v + 16) 0)).
  { intros M1 VIS1 MGM1 FR1.
    assert (AG : forall i m, 0 <= i -> i + m <= 2 ^ 64 -> (i + m <= v + 8 \/ v + 16 <= i) -> (i + m <= sp - 16 \/ sp <= i) -> L5C.agree_on M M1 i m).
    { intros i m Hi Hm X Y j Hj. apply FR1; [lia| unfold P; lia]. }
    assert (AGSH : forall i m, 0 <= i -> i + m <= 2 ^ 47 -> PMFA.agsh M M1 i m).
    { intros i m Hi Hm xs Hx. pose proof (PMKA.S_in_shadow xs ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
      apply FR1; [lia| unfold P; destruct TBIG; lia]. }
    split.
    { apply (L5SAR.ek_piece L ar LB FF sp 14336 [(v, 24)] M M1 P FR1). intros i Hi CA OWx [Pa|Pa].
      - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 14336 i HH SPT (L5SAR.aclient_appb L ar LB (PGV8.v8_own x) FF sp 14336 i CA)) as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
      - apply (OWx (v, 24)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
    split; [exact (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1)|].
    split.
    { intros j Hj. pose proof (STKSH j Hj) as Z1. unfold byte_at in *.
      assert (M8 : (sp - 14336) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 14336) with (sp + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
      rewrite (PMFA.S_granule (sp - 14336) j M8 ltac:(lia)) in *.
      pose proof (PMKA.S_in_shadow (sp - 14336 + 8 * j) ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
      rewrite FR1; [exact Z1| lia| unfold P; destruct TBIG; lia]. }
    split; [apply (PMFA.accA_agree M M1 v 24); [apply AGSH; lia| exact VC]|].
    split; [intros i Hi; apply MGM1; apply VD; exact Hi|].
    split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U0]|].
    split.
    { intros q Q. apply (proj1 (L5A.u64_at_vis H M1 (v + 8) q ltac:(apply TAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact Q. }
    split.
    { intros b' n' c' E. subst x. destruct VR as (_ & _ & U16 & Hn' & Hc' & Hb' & Hb16 & BD & BA & BN).
      destruct (BRB (b', c') ltac:(left; reflexivity)) as (Q0 & Q1). cbn [fst snd] in Q0, Q1.
      split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U16]|].
      split; [intros i Hi; apply MGM1; apply BD; exact Hi|].
      split; [intros u Hu AU; apply (PMFA.accA_agree M M1 b' u); [intros xs Hx; pose proof (PMKA.S_in_shadow xs ltac:(lia)) as SX; unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; apply FR1; [lia| unfold P; destruct TBIG; lia]| exact AU]|].
      intros u Hu AN. apply (PGV8KA.annA_agree M M1 b' u c'); [exact Hu| apply PMKA.mod16_8'; exact Hb16| apply AGSH; lia| exact AN]. }
    intros ->. destruct VR as (_ & _ & U16). apply (L5C.u64_at_agree RSEGS M M1); [apply AG; lia| lia| lia| exact U16]. }
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E11 & _ & _ & _ & _ & Hlt & _ & C8) | [(MS & KS1 & E11 & _ & _ & _ & _ & C8 & Hlt & _ & _) | (MS & KS1 & _ & _ & _ & _ & Hle1 & Hle2 & _ & C8)]].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3e90 R1 0xb3f2c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    destruct (POST M1 VIS1 MGM1 FR1) as (EK1 & STK1 & SH1 & ACC1 & VD1 & W0 & W8 & WBLK & WNUL).
    pose proof (W8 _ C8) as W8'.
    assert (VS1 : v8_atA M1 v x).
    { split; [exact VD1|]. split; [exact ACC1|]. destruct x as [|b' n' c']; cbn [PGV8.v8_size PGV8.v8_data] in XN, XB.
      - subst b n0. split; [exact W0|]. split; [exact W8'| exact (WNUL eq_refl)].
      - subst b n0. destruct (WBLK b' n' c' eq_refl) as (U16' & BD' & ACCK & ANNK). destruct VR as (_ & _ & _ & Hn' & Hc' & Hb' & Hb16 & _ & BA & BN).
        split; [exact W0|]. split; [exact W8'|]. split; [exact U16'|]. split; [exact Hn'|]. split; [exact Hc'|]. split; [exact Hb'|]. split; [exact Hb16|].
        split; [exact BD'|]. split; [exact (ACCK n' Hn' BA)| exact (ANNK n' Hn' BN)]. }
    pose proof APP as AP. unfold PGV8A.vu8_append_spec, PGV8A.vu8_grow_spec in AP. cbn [PNL.pn_vu8_append PMA.AN NADDR_A] in AP.
    apply (AP fx1 R1 M1 model1 K LB FF LK Aw cr v (a - n0) sp r g x HH1 AM1 K0).
    { split; [rewrite L5K.rl1, (KS1 1%nat) by inl; exact Rra|]. split; [exact RAok|]. split; [rewrite L5K.rl2, (KS1 2%nat) by inl; exact Rsp|].
      split; [rewrite L5K.rl3, (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 1) with 14336. split; [exact STK1|]. change (14336 / 8) with 1792. exact SH1. }
    { exact FRM. } { exact FRS. }
    { rewrite L5K.rl10, (KS1 10%nat) by inl. exact A10. }
    { rewrite L5SAR.r11, E11. f_equal. lia. }
    { exact AO. } { exact V8. } { exact ACC1. } { exact VS1. } { exact OK. }
    { rewrite XN. split; lia. }
    { rewrite XN. replace (n0 + (a - n0)) with a by lia. exact GOK. }
    { exact CRL. }
    intros fx' R' M' model' LK' Aw' x' g' cr' RP VS' SZ' OK' CAPLE OWN CL HP CK MRT' ILK' IAW' AM' HH'.
    rewrite XN in SZ', CL. replace (n0 + (a - n0)) with a in SZ', CL by lia.
    apply (KONT fx' R' M' model' LK' Aw' x' g' cr'); try assumption.
    + apply L5SAR.preserved_by_index. intros xr Hx. rewrite (L5SAR.cs_of_preserved R1 R' xr RP) by exact Hx. apply KS1.
      unfold L5SAR.cs_all in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx.
    + destruct HP as (EKp & DSp & DKp). change (PMSPA.pm_scr 1) with 14336 in *.
      apply (L5SAR.ahpres_of L ar LB FF sp 14336 _ M M'); [exact (L5SAR.ek_trans L ar LB FF sp 14336 [(v, 24)] M M1 M' EK1 EKp)| exact DSp|].
      apply (L5SAR.dk_trans L ar LB FF sp 14336 M M1 M'); [apply L5SAR.dk_grows; exact MGM1| exact DKp].
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT'].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3e90 R1 0xab138 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    destruct (POST M1 VIS1 MGM1 FR1) as (EK1 & STK1 & SH1 & ACC1 & VD1 & W0 & W8 & WBLK & WNUL).
    pose proof (W8 _ C8) as W8'.
    destruct x as [|b' n' c']; cbn [PGV8.v8_size PGV8.v8_data PGV8.v8_cap] in XN, XB, XC; [exfalso; clear - XN Hlt Ha27; lia|]. subst b n0.
    destruct (WBLK b' n' c' eq_refl) as (U16' & BD' & ACCK & ANNK). destruct VR as (_ & _ & _ & Hn' & Hc' & Hb' & Hb16 & _ & BA & BN).
    assert (A16' : (sp - 0) mod 16 = 0) by (rewrite Z.sub_0_r; exact A16).
    pose proof (L5SAR.astk_sub ar M1 M1 sp 14336 0 12288 STK1 (fun _ Y => Y) ltac:(lia) ltac:(lia) ltac:(lia) A16') as STK0. rewrite Z.sub_0_r in STK0.
    assert (M8a : (sp - 14336) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 14336) with (sp + (-896) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (sp - 12288) mod 8 = 0) by (apply PMKA.mod16_8'; replace (sp - 12288) with (sp + (-768) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    pose proof (PMKA.shadow_zero_sub M1 (sp - 14336) 1792 (sp - 12288) 1536 M8a M8b ltac:(lia) ltac:(lia) ltac:(lia) SH1) as SH0.
    pose proof ANNS as ASH. unfold PNSAX.ann_shrink_v8_spec in ASH.
    apply (ASH fx1 R1 M1 model1 K LB FF LK Aw cr v n' (PGV8.V8Blk b' a c') sp r HH1 AM1 K0).
    { split; [rewrite L5K.rl1, (KS1 1%nat) by inl; exact Rra|]. split; [exact RAok|]. split; [rewrite L5K.rl2, (KS1 2%nat) by inl; exact Rsp|].
      split; [rewrite L5K.rl3, (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4, (KS1 4%nat) by inl; exact Rtp|].
      change (PMSPA.pm_scr 0) with 12288. split; [exact STK0|]. change (12288 / 8) with 1536. exact SH0. }
    { exact FRS. }
    { rewrite L5K.rl10, (KS1 10%nat) by inl. exact A10. }
    { rewrite L5SAR.r11. exact E11. }
    { exact AO. } { exact V8. } { exact ACC1. }
    { split; [exact VD1|]. split; [exact W0|]. split; [exact W8'|]. split; [exact U16'|]. split; [lia|]. split; [exact Hc'|]. split; [exact Hb'|]. split; [exact Hb16| exact BD']. }
    { cbn [PGV8.v8_size PGV8.v8_cap]. lia. }
    { intros b2 n2 c2 E. injection E as <- <- <-. split; [exact (ACCK n' Hn' BA)| exact (ANNK n' Hn' BN)]. }
    intros fx' R' M' model' LK' Aw' RP VS' PAY' HP MRT' ILK' IAW' AM' HH'.
    apply (KONT fx' R' M' model' LK' Aw' (PGV8.V8Blk b' a c') g cr); try assumption; try reflexivity; try exact VS'; try exact OK.
    all: try (cbn [PGV8.v8_cap PGV8.v8_size]; lia).
    all: try (intros _; split; [reflexivity|]; split; reflexivity).
    all: try (left; reflexivity).
    all: try (eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT']).
    all: try (unfold PMSP.credit_keep, PMSPA.scA, PGV8.pot_v8; cbn [fst snd PGV8.v8_cap]; lia).
    + apply L5SAR.preserved_by_index. intros xr Hx. rewrite (L5SAR.cs_of_preserved R1 R' xr RP) by exact Hx. apply KS1.
      unfold L5SAR.cs_all in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx.
    + change (PMSPA.pm_scr 0) with 12288 in HP. change (PMSPA.pm_scr 1) with 14336.
      apply (L5SAR.ahpres_of L ar LB FF sp 14336 _ M M').
      * apply (L5SAR.ek_trans L ar LB FF sp 14336 [(v, 24)] M M1 M' EK1).
        apply (L5SAR.ek_callee L ar LB [] FF [] sp 14336 sp 12288 [(v, 24)] [] M1 M' HP); [lia| lia| intros i _ _ r0 []].
      * apply (PMKA.astk_after_ahpres L ar LB FF M1 M' sp 14336 sp 12288 [] STK1 HP); lia.
      * apply (L5SAR.dk_trans L ar LB FF sp 14336 M M1 M'); [apply L5SAR.dk_grows; exact MGM1|].
        apply (L5SAR.dk_callee L ar LB [] FF [] sp 14336 sp 12288 [] M1 M' HP); lia.
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3e90 R1 0xb3f14 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    destruct (POST M1 VIS1 MGM1 FR1) as (EK1 & STK1 & SH1 & ACC1 & VD1 & W0 & W8 & WBLK & WNUL).
    pose proof (W8 _ C8) as W8'.
    assert (VS1 : v8_atA M1 v x).
    { split; [exact VD1|]. split; [exact ACC1|]. destruct x as [|b' n' c']; cbn [PGV8.v8_size PGV8.v8_data] in XN, XB.
      - subst b n0. split; [exact W0|]. split; [exact W8'| exact (WNUL eq_refl)].
      - subst b n0. destruct (WBLK b' n' c' eq_refl) as (U16' & BD' & ACCK & ANNK). destruct VR as (_ & _ & _ & Hn' & Hc' & Hb' & Hb16 & _ & BA & BN).
        split; [exact W0|]. split; [exact W8'|]. split; [exact U16'|]. split; [exact Hn'|]. split; [exact Hc'|]. split; [exact Hb'|]. split; [exact Hb16|].
        split; [exact BD'|]. split; [exact (ACCK n' Hn' BA)| exact (ANNK n' Hn' BN)]. }
    assert (RA1 : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra).
    apply (PMASK.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K _ FF LK cr Aw 0xb3f14 r W_b3ec4 HH1 AM1 F_b3ec4 eq_refl D_b3ec4 RA1 ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK Aw x g cr); try assumption; try reflexivity.
    all: try (rewrite XN; clear - Hle1 Hle2; lia).
    all: try (intros _; split; [reflexivity|]; split; reflexivity).
    all: try (left; reflexivity).
    all: try (eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2]).
    all: try (unfold PMSP.credit_keep, PMSPA.credit_keep; lia).
    all: try apply incl_refl.
    all: try lia.
    + apply L5SAR.preserved_by_index. intros xr Hx. apply KS1. unfold L5SAR.cs_all in Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [inl|]). destruct Hx.
    + change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LB FF sp 14336 _ M M1); [exact EK1| destruct STK1 as (_ & _ & _ & _ & D & _); exact D| apply L5SAR.dk_grows; exact MGM1].
Qed.

End WithHeap.
End PGVRZA.
