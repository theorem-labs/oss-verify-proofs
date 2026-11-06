(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAb PmModelFactsA PmStep PeStepAB0 PmParKit PeBSrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeShZ PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAb PeCFrame PeCFrameA PeBCReset1 PeBPbIndSpec PeBPbIndP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b27d0_b27d4.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBPBI.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.
Abbreviation mst fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)).
Abbreviation SBL := 2147450880.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.
Hypothesis PB : PESKA.push_back_specA RSEGS AD EE L ar HI P.

Lemma slot_facts LB FF LK cr Aw M model (q sp scr : Z) :
  ri_inv HI LB FF LK cr Aw M (vml_of model) -> PMSPA.aobjA FF q 8 -> q mod 8 = 0 -> PMSPA.accA M q 8 ->
  let H := ahid Aw model in
  6930432 <= q /\ q + 8 <= ahl_ceil ar /\ (2147446784 + 17592186048512 <= q \/ q + 8 <= 2147446784) /\ L5A.avis H q 8
  /\ L5KA.zeros_at (mrestrict H M) (q / 8 + SBL) 1.
Proof.
  intros HH AO Q8 ACC.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model q 8 sp scr HH (PMKB.aobj_of_aobjA FF q 8 AO Q8) ltac:(lia) ltac:(reflexivity)) as ((Q1 & Q2 & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & _).
  pose proof (PMKB.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model q 8 HH AO Q8 ltac:(lia) ltac:(reflexivity) ACC) as Z1. unfold SB in Z1. change (8 / 8) with 1 in Z1.
  split; [exact Q1|]. split; [exact Q2|]. split; [exact QBIG|]. split; [exact QVIS| exact Z1].
Qed.

Theorem push_back_ind_ok : PEPBI.push_back_indZ_specA RSEGS AD L ar HI 0xb2794 P.
Proof.
  unfold PEPBI.push_back_indZ_specA. intros PMODE fx R M model K LBX FF LK Aw cr q rr o pv sp r k HH AM K0 ENT FRM FRS A10 A11 QRR RR8 RR0 RRO O0 QDEF QACC QAO Q8 RAO RDEF RACC SKA AOo ALo
    (PDEF & PVO & PVZ) GROW CRED KONT.
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in ASTK, STKSH. change (14336 / 8) with 1792 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2). pose proof AM as (Mh & MI).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & NDF & _).
  set (LB := PESK.sink_own k ++ LBX) in *.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  destruct (slot_facts LB FF LK cr Aw M model q sp 14336 HH QAO Q8 QACC) as (Q1 & Q2 & QBIG & QVIS & ZQ). fold H MV in ZQ. fold H in QVIS.
  destruct (slot_facts LB FF LK cr Aw M model rr sp 14336 HH RAO RR8 RACC) as (R1' & R2' & RBIG & RVIS & ZR). fold H MV in ZR. fold H in RVIS.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model o 24 sp 14336 HH (PMKB.aobj_of_aobjA FF o 24 AOo ALo) ltac:(lia) ltac:(reflexivity)) as ((K1 & K2 & K3 & _) & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (IC0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1335544 SBL) by (apply (proj2 (L5A.u64_at_vis H M 1335544 SBL (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 14336 32 HH ASTK ltac:(lia)) as (_ & _ & SWR).
  assert (QRRv : L5.u64_at RSEGS MV q rr) by (apply (proj2 (L5A.u64_at_vis H M q rr QVIS ltac:(lia) ltac:(lia))); exact QRR).
  assert (RROv : L5.u64_at RSEGS MV rr o) by (apply (proj2 (L5A.u64_at_vis H M rr o RVIS ltac:(lia) ltac:(lia))); exact RRO).

  destruct (M (Z_to_bv 64 pv)) as [bb|] eqn:EPV; [| exfalso; apply (PDEF 0 ltac:(lia)); rewrite Z.add_0_r; exact EPV].
  set (nb := bv_unsigned bb). pose proof (bv_unsigned_in_range 8 bb) as NB. change (bv_modulus 8) with 256 in NB.
  assert (PVB : L5.u8_at RSEGS M pv nb) by (unfold L5.u8_at; cbn [rdn]; rewrite EPV; unfold nb; rewrite Z_to_bv_bv_unsigned; reflexivity).

  assert (PVF : L5A.avis H pv 1 /\ L5KA.zeros_at MV (pv / 8 + SBL) 1 /\ 6930432 <= pv /\ pv + 1 <= 2 ^ 47 /\ (2147446784 + 17592186048512 <= pv \/ pv + 1 <= 2147446784)
               /\ (pv + 1 <= sp - 32 \/ sp <= pv)).
  { destruct PVZ as [(SPV & TPV & BPV0)|(base & BAO & B8 & BPV & BACC)].
    - split; [apply VIS; clear - SPV TPV SLO SPT; lia|]. split.
      + intros i Hi. replace (pv / 8 + SBL + i) with (HeapIfaceA.S pv) by (unfold HeapIfaceA.S, SB; clear - Hi; lia).
        pose proof (VSTSH (HeapIfaceA.S pv) 1 ltac:(intros j Hj; unfold in_shadow_of, HeapIfaceA.S, SB; replace (pv / 8 + 2147450880 + j) with (pv / 8 + 2147450880) by (clear - Hj; lia);
                                               split; [apply Z.add_le_mono_r; apply Z.div_le_mono; [clear; lia| clear - SPV SLO; lia] | apply Z.add_le_mono_r; apply Z.div_le_mono; [clear; lia| clear - TPV; lia]])) as AVS.
        pose proof (AVS 0 ltac:(clear; lia)) as H0. rewrite Z.add_0_r in H0. unfold MV. rewrite (mrestrict_visible H M _ H0). exact BPV0.
      + repeat split; clear - SPV TPV SLO SHI SPT; lia.
    - destruct (slot_facts LB FF LK cr Aw M model base sp 14336 HH BAO B8 BACC) as (B1 & B2 & BBIG & BVIS & ZB). fold H MV in ZB. fold H in BVIS.
      split; [exact (L5A.avis_sub H base 8 pv 1 BVIS ltac:(lia) ltac:(lia))|]. split.
      + assert (DQ : base / 8 = pv / 8) by (apply (Z.div_unique pv 8 (base / 8) (pv - base)); [left; clear - BPV; lia| pose proof (Z.div_mod base 8 ltac:(lia)) as E8; clear - E8 B8 BPV; lia]).
        rewrite <- DQ. exact ZB.
      + repeat split; clear - B1 B2 BBIG BPV SPT SLO; lia. }
  destruct PVF as (PVIS & ZPV & PV1 & PV2 & PVBIG & PVSP).
  assert (PVv : L5.u8_at RSEGS MV pv nb) by (apply (proj2 (L5A.u8_at_vis H M pv nb PVIS ltac:(lia) ltac:(lia))); exact PVB).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as RB8. change (bv_modulus 64) with (2 ^ 64) in RB8.
  assert (HQ : bv_unsigned (getr R (reg 10)) = q) by (rewrite A10; apply L5.unsigned_lit; lia).
  assert (HPV : bv_unsigned (getr R (reg 11)) = pv) by (rewrite A11; apply L5.unsigned_lit; lia).

  pose proof (PEBPBIP.bpiA_conc fx R MV (fun j => match j with 2%nat => sp | 35%nat => rr | 40%nat => nb | 41%nat => o | _ => 0 end)) as PA. cbn beta iota in PA. rewrite !HQ, !HPV in PA.
  L5SAR.feed PA ltac:(first [assumption | unfold PEBPBIP.aligned; assumption | lia]).
  destruct PA as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T10 & T11 & T12 & T13 & C17 & S16 & S8).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb2794 R1 0xb120c M1v (fun a0 => sp - 32 <= a0 < sp - 32 + 32) K HH AM MS1 MG1).
  { intros a0 Ha0 Hn. apply FRZ1; [exact Ha0| exact Hn]. }
  { intros a0 Ha0 Wa. split.
    - unfold aclientw, aclient_g. right; left. split; [clear - Wa SLO SHI SPT; lia| intros Y; clear - Y; lia].
    - clear - Wa SLO SPT; lia. }
  intros M1 md1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (RB : forall a0 v, sp - 32 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1v a0 v -> L5.u64_at RSEGS M1 a0 v).
  { intros a0 v Ha1 Ha2 U. apply (proj1 (L5A.u64_at_vis H M1 a0 v (VIS a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))). rewrite VIS1. exact U. }
  assert (S8' : L5.u64_at RSEGS M1 (sp - 8) r) by (rewrite Rra, L5.unsigned_lit in S8 by (clear - Hr1; lia); apply RB; [lia| lia| exact S8]).
  assert (S16' : L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (apply RB; [lia| lia| exact S16]).
  assert (EK01 : L5SAR.ek L ar LB FF sp 14336 [] M M1).
  { apply (PMKB.ek_own_frame L ar C HI LYa HIok LB FF LK cr Aw M M1 _ sp 14336 [] (sp - 32) (sp - 32 + 32) HH SPT); [clear - SLO; lia| clear; lia| clear; lia| exact FR1]. }
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMBSK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (SP8 : forall d, d mod 8 = 0 -> (sp - d) mod 8 = 0).
  { intros d Hd. pose proof (Z.div_mod sp 16 ltac:(lia)) as E0. rewrite A16, Z.add_0_r in E0. pose proof (Z.div_mod d 8 ltac:(lia)) as E1. rewrite Hd, Z.add_0_r in E1.
    rewrite E0, E1. replace (16 * (sp / 16) - 8 * (d / 8)) with ((2 * (sp / 16) - d / 8) * 8) by lia. apply Z_mod_mult. }
  assert (ASTK1 : L5CA.astk ar M1 sp 14336) by exact (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1).
  assert (SZ1 : shadow_zero M1 (sp - 14336) 1792).
  { apply (PMKB.stksh_keepA L ar LB FF sp 14336 [] M M1 EK01 PMKB.wapp_nil (sp - 14336) 1792); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| apply SP8; reflexivity| clear; lia| exact STKSH]. }
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 o k).
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 14336 [] M M1 EK01 PMKB.wapp_nil FRB BRB P o k AOo); [intros i _ r0 []| unfold LB; apply incl_appl; apply incl_refl| intros _ i _ r0 []| exact SKA]. }
  pose proof SKA1 as (_ & _ & _ & _ & _ & KZC & KCAP & KC0 & KBLK). pose proof ASTK1 as (_ & _ & _ & _ & SDEF1 & _).

  pose proof PB as PBX. unfold PESKA.push_back_specA in PBX. cbn [pe_push_back EE PeCLayoutB.EADDR_B] in PBX.
  apply (PBX PMODE fx1 R1 M1 md1 K LBX FF LK Aw cr o (sp - 17) (sp - 32) 0xb2810 k HH1 AM1 K0); clear PBX.
  { split; [rewrite L5K.rl1; exact T1|]. split; [split; [clear; lia| reflexivity]|]. split; [rewrite L5K.rl2; exact T2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. change (12288 / 8) with 1536. split.
    - apply (L5SAR.astk_sub ar M1 M1 sp 14336 32 12288 ASTK1); [intros w D; exact D| clear; lia| clear; lia| clear; lia|].
      replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
    - apply (PMKB.shadow_zero_sub M1 (sp - 14336) 1792); [apply SP8; reflexivity| replace (sp - 32 - 12288) with (sp - 12320) by lia; apply SP8; reflexivity| clear; lia| clear; lia| clear; lia| exact SZ1]. }
  { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { rewrite L5K.rl10. exact T10. }
  { rewrite L5K.rl11. exact T11. }
  { exact SKA1. }
  { exact AOo. }
  { exact ALo. }
  { split; [apply (L5.defined_sub M1 (sp - 14336) 14336 (sp - 17) 1 SDEF1); clear; lia|].
    split; [apply (PESHZ.bat0_of_shadow_zero M1 (sp - 14336) 1792 (sp - 17) SZ1); [apply SP8; reflexivity| clear; lia| clear; lia]|].
    split; [right; clear - K2 SLO; lia|]. left. split; [clear; lia| clear - SHI; lia]. }
  { exact GROW. }
  { exact CRED. }
  intros fx2 R2 M2 md2 LK2 Aw2 cr2 b2 RP2 SKA2 HP2 CK2 MRT2 ILK2 IAW2 AM2 HH2.
  change (PMSPA.pm_scr 0) with 12288 in HP2.

  assert (FRAME12 : forall a0, sp - 32 <= a0 < sp -> M2 (Z_to_bv 64 a0) = M1 (Z_to_bv 64 a0)).
  { intros a0 Ha0. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha0 SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha0 SLO SHI SPT; lia| intros Y; clear - Ha0 Y; lia].
    - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha0 K2 SLO; lia. }
  assert (ASTK2 : L5CA.astk ar M2 sp 14336).
  { apply (PMKB.astk_after_ahpres L ar LBX FF M1 M2 sp 14336 (sp - 32) 12288 [(o, 24)] ASTK1 HP2); [clear; lia| clear; lia| clear; lia| exact STOP]. }
  pose proof ASTK2 as (_ & _ & _ & _ & SDEF2 & _). pose proof AM2 as (Mh2 & MI2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 md2 HH2) as (_ & VIS2 & VIMG2 & _).
  set (H2 := ahid Aw2 md2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  assert (IC2 : L5.img_clear MV2 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (CSB2v : L5.u64_at RSEGS MV2 1335544 SBL) by (apply (proj2 (L5A.u64_at_vis H2 M2 1335544 SBL (VIMG2 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (CUAR2v : L5.u32_at RSEGS MV2 1335552 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1335552 1 (VIMG2 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK2 cr2 Aw2 M2 md2 sp 14336 32 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  assert (SVV : forall a0 v, sp - 32 <= a0 -> a0 + 8 <= sp -> L5.u64_at RSEGS M1 a0 v -> L5.u64_at RSEGS MV2 a0 v).
  { intros a0 v Ha1 Ha2 U. apply (proj2 (L5A.u64_at_vis H2 M2 a0 v (VIS2 a0 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRAME12; clear - Hi Ha1 Ha2; lia| clear - Ha1 SLO SPT; lia| clear - Ha2 SHI SPT; lia| exact U]. }
  pose proof (bv_unsigned_in_range 64 (getr R2 (reg 10))) as B10. pose proof (bv_unsigned_in_range 64 (getr R2 (reg 11))) as B11. pose proof (bv_unsigned_in_range 64 (getr R2 (reg 12))) as B12.
  change (bv_modulus 64) with (2 ^ 64) in B10, B11, B12.
  assert (G10 : getr R2 (reg 10) = Z_to_bv 64 (bv_unsigned (getr R2 (reg 10)))) by (symmetry; apply PMPK.word_id).
  assert (G11 : getr R2 (reg 11) = Z_to_bv 64 (bv_unsigned (getr R2 (reg 11)))) by (symmetry; apply PMPK.word_id).
  assert (G12 : getr R2 (reg 12) = Z_to_bv 64 (bv_unsigned (getr R2 (reg 12)))) by (symmetry; apply PMPK.word_id).
  assert (G2' : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact T2).
  assert (G8' : getr R2 (reg 8) = Z_to_bv 64 q) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; rewrite T8; exact A10).
  pose proof (PEBPBIP.bpiB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 10%nat => q | 44%nat => r | 45%nat => bv_unsigned (getr R (reg 8))
      | 55%nat => bv_unsigned (getr R2 (reg 10)) | 56%nat => bv_unsigned (getr R2 (reg 11)) | 57%nat => bv_unsigned (getr R2 (reg 12)) | _ => 0 end)) as PBc. cbn beta iota in PBc.
  L5SAR.feed PBc ltac:(first [assumption | unfold PEBPBIP.aligned; assumption | apply SVV; [lia| lia| assumption] | lia]).
  destruct PBc as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & U1 & U2 & U8 & U10).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xb2820 W_b27d0 r F_b27d0 eq_refl D_b27d0 U1 ltac:(lia) Hr2) as MSR.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 md2 fx2 fx3 R2 0xb2810 R3 r M3v K HH2 AM2 (msteps_trans _ _ _ _ MS3 MSR) MG3 FRZ3).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 AG3. pose proof (L5SAR.mem_eq_of_agree M2 M3 AG3) as EM. subst M3.
  apply (KONT fx3 R3 M2 md3 LK2 Aw2 cr2 b2).
  - apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite U2; exact (eq_sym Rsp) | rewrite U8; apply PMPK.word_id
                                            | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; apply KS1; inl ] |]). destruct Hj.
  - exact SKA2.
  - change (PMSPA.pm_scr 1) with 14336. apply (L5SAR.ahpres_of L ar LBX FF sp 14336 _ M M2); [| exact SDEF2|].
    + apply (L5SAR.ek_trans L ar LBX FF sp 14336 _ M M1 M2).
      { apply (L5SAR.ek_W L ar LBX FF sp 14336 _ [] M M1); [exact (PMKB.ek_sublb L ar LB LBX FF sp 14336 [] M M1 ltac:(unfold LB; apply incl_appr; apply incl_refl) EK01)| intros a0 _ r0 []]. }
      apply (L5SAR.ek_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 _ [(o, 24)] M1 M2 HP2); [clear; lia| clear; lia| intros a0 _ O; exact O].
    + apply (L5SAR.dk_trans L ar LBX FF sp 14336 M M1 M2); [apply L5SAR.dk_grows; exact MGM1|].
      apply (L5SAR.dk_callee L ar LBX [] FF [] sp 14336 (sp - 32) 12288 [(o, 24)] M1 M2 HP2); clear; lia.
  - exact CK2.
  - exact (L5LZ.model_rt_trans model md1 md3 MRT1 (L5LZ.model_rt_trans md1 md2 md3 MRT2 MRT3)).
  - exact ILK2.
  - exact IAW2.
  - exact AM3.
  - exact HH3.
Qed.
End WithHeap.
End PEBPBI.
