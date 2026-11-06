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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeBSnkAnn PeBEstkHP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b10cc_b10d0 Eb0_code_b0af8_b0afc Eb0_code_b0aac_b0ac0.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
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
Module PEBEKAN.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Definition ann_shrink_e_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v old b n c : Z) (sp r : Z),
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 old -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 -> PMSPA.accA M v 24 ->
    PEBSKAN.bhdr segs M v b n c -> n <= 24 * old <= c -> PMSPA.accA M b (24 * old) /\ PMSPA.annA M b (24 * old) c ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)),
        regs_preserved R R' -> PEBSKAN.bat segs M' v b n c ->
        (forall a, b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ([(b, c)] ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes segs SCFG (@PMSPA.cfg segs fx' R' r M' model') K) ->
    srealizes segs SCFG (@PMSPA.cfg segs fx R pc M model) K.
End Specs.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

Lemma rstep fx R R' M (pc : Z) (W : bv 32) :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W ->
  RiscvSemantics.step RSEGS (mkst R (Z_to_bv 64 pc) M (seg_rom RSEGS)) = MachineOk (mkst R' (v_addi (Z_to_bv 64 pc) 4) M (seg_rom RSEGS)) ->
  0 <= pc -> pc + 4 < 2 ^ 64 ->
  msteps RSEGS (st fx R pc M) (st fx R' (pc + 4) M).
Proof.
  intros HF HS H0 H1. eapply mst_step; [reflexivity| | apply mst_refl].
  rewrite HS. f_equal. f_equal. unfold v_addi. rewrite L5.unsigned_lit by Lia.lia. reflexivity.
Qed.
Lemma reg_index_neq (i j : nat) : (i < 32)%nat -> (j < 32)%nat -> i <> j -> (reg i) <> (reg j).
Proof.
  intros Hi Hj Hne E. apply Hne. apply (f_equal (@bv_unsigned 5)) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
  change (bv_modulus 5) with 32 in E. rewrite !Z.mod_small in E by Lia.lia. Lia.lia.
Qed.

Lemma ovf_guard fx R M old :
  getr R (reg 12) = Z_to_bv 64 old -> getr R (reg 16) = Z_to_bv 64 (24 * old) -> getr R (reg 17) = Z_to_bv 64 24 -> 0 <= old <= 5864062014805 ->
  exists R', msteps RSEGS (st fx R 0xb0afc M) (st fx R' 0xb0b10 M)
    /\ (forall j, j <> 12%nat -> j <> 16%nat -> (j < 32)%nat -> getr R' (reg j) = getr R (reg j))
    /\ getr R' (reg 12) = Z_to_bv 64 0 /\ getr R' (reg 16) = Z_to_bv 64 0.
Proof.
  intros A12 A16 A17 Hold.
  assert (S24 : bv_signed (Z_to_bv 64 24) = 24) by (vm_compute; reflexivity).
  assert (SO : bv_signed (Z_to_bv 64 old) = old).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
    rewrite (Z.mod_small old) by Lia.lia. rewrite Z.mod_small by Lia.lia. Lia.lia. }
  assert (S24O : bv_signed (Z_to_bv 64 (24 * old)) = 24 * old).
  { unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
    rewrite (Z.mod_small (24 * old)) by Lia.lia. rewrite Z.mod_small by Lia.lia. Lia.lia. }
  assert (MH : v_mulh (Z_to_bv 64 old) (Z_to_bv 64 24) = Z_to_bv 64 0).
  { unfold v_mulh. rewrite SO, S24. rewrite Z.shiftr_div_pow2 by Lia.lia. rewrite Z.div_small by Lia.lia. reflexivity. }
  assert (SR : v_srai (Z_to_bv 64 (24 * old)) 63 = Z_to_bv 64 0).
  { unfold v_srai. rewrite S24O. rewrite Z.shiftr_div_pow2 by Lia.lia. rewrite Z.div_small by Lia.lia. reflexivity. }
  set (R1 := regupd R (reg 12) (v_mulh (getr R (reg 12)) (getr R (reg 17)))).
  set (R2 := regupd R1 (reg 16) (v_srai (getr R1 (reg 16)) 63)).
  set (R3 := regupd R2 (reg 12) (v_xor (getr R2 (reg 12)) (getr R2 (reg 16)))).
  set (R4 := regupd R3 (reg 12) (v_sltu (getr R3 (reg 0)) (getr R3 (reg 12)))).
  assert (N12 : (reg 12) <> 0%bv) by (intros X; discriminate X). assert (N16 : (reg 16) <> 0%bv) by (intros X; discriminate X).
  assert (E1_12 : getr R1 (reg 12) = Z_to_bv 64 0) by (unfold R1; rewrite (getr_same _ _ _ N12), A12, A17; exact MH).
  assert (E1o : forall j, j <> 12%nat -> (j < 32)%nat -> getr R1 (reg j) = getr R (reg j)).
  { intros j Hj Hl. unfold R1. apply getr_other. apply reg_index_neq; Lia.lia. }
  assert (E2_16 : getr R2 (reg 16) = Z_to_bv 64 0) by (unfold R2; rewrite (getr_same _ _ _ N16), (E1o 16%nat) by Lia.lia; rewrite A16; exact SR).
  assert (E2o : forall j, j <> 16%nat -> (j < 32)%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj Hl. unfold R2. apply getr_other. apply reg_index_neq; Lia.lia. }
  assert (E3_12 : getr R3 (reg 12) = Z_to_bv 64 0).
  { unfold R3. rewrite (getr_same _ _ _ N12), (E2o 12%nat) by Lia.lia. rewrite E1_12, E2_16. vm_compute. reflexivity. }
  assert (E3o : forall j, j <> 12%nat -> (j < 32)%nat -> getr R3 (reg j) = getr R2 (reg j)).
  { intros j Hj Hl. unfold R3. apply getr_other. apply reg_index_neq; Lia.lia. }
  assert (E4_12 : getr R4 (reg 12) = Z_to_bv 64 0).
  { unfold R4. rewrite (getr_same _ _ _ N12). rewrite E3_12. unfold getr at 1. cbn [bv_eqb Z.eqb]. vm_compute. reflexivity. }
  assert (E4o : forall j, j <> 12%nat -> (j < 32)%nat -> getr R4 (reg j) = getr R3 (reg j)).
  { intros j Hj Hl. unfold R4. apply getr_other. apply reg_index_neq; Lia.lia. }
  exists R4. split; [| split; [| split; [exact E4_12| rewrite (E4o 16%nat), (E3o 16%nat) by Lia.lia; exact E2_16]]].
  - eapply msteps_trans.
    { apply (rstep fx R R1 M 0xb0afc W_b0aac F_b0aac); [| Lia.lia| Lia.lia].
      rewrite (step_mulh RSEGS R (Z_to_bv 64 0xb0afc) M (seg_rom RSEGS) W_b0aac _ _ _ F_b0aac eq_refl D_b0aac). reflexivity. }
    eapply msteps_trans.
    { apply (rstep fx R1 R2 M 0xb0b00 W_b0ab0 F_b0ab0); [| Lia.lia| Lia.lia].
      rewrite (step_srai RSEGS R1 (Z_to_bv 64 0xb0b00) M (seg_rom RSEGS) W_b0ab0 _ _ _ F_b0ab0 eq_refl D_b0ab0). reflexivity. }
    eapply msteps_trans.
    { apply (rstep fx R2 R3 M 0xb0b04 W_b0ab4 F_b0ab4); [| Lia.lia| Lia.lia].
      rewrite (step_xor RSEGS R2 (Z_to_bv 64 0xb0b04) M (seg_rom RSEGS) W_b0ab4 _ _ _ F_b0ab4 eq_refl D_b0ab4). reflexivity. }
    eapply msteps_trans.
    { apply (rstep fx R3 R4 M 0xb0b08 W_b0ab8 F_b0ab8); [| Lia.lia| Lia.lia].
      rewrite (step_sltu RSEGS R3 (Z_to_bv 64 0xb0b08) M (seg_rom RSEGS) W_b0ab8 _ _ _ F_b0ab8 eq_refl D_b0ab8). reflexivity. }
    apply (rstep fx R4 R4 M 0xb0b0c W_b0abc F_b0abc); [| Lia.lia| Lia.lia].
    rewrite (step_bne_ft RSEGS R4 (Z_to_bv 64 0xb0b0c) M (seg_rom RSEGS) W_b0abc _ _ _ F_b0abc eq_refl D_b0abc); [reflexivity|].
    rewrite L5K.rl12, E4_12. unfold getr. cbn [bv_eqb Z.eqb]. apply c_eq_refl.
  - intros j H12 H16 Hl. rewrite (E4o j), (E3o j), (E2o j), (E1o j) by Lia.lia. reflexivity.
Qed.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Hypothesis EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT.
Let LYa := PMB.ly_as0 L C LY.

Theorem ann_delete_e_ok : PEBSKAN.ann_delete_b_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb108c.
Proof.
  unfold PEBSKAN.ann_delete_b_spec.
  intros fx R M model K LBX FF LK Aw cr v b n c sp r HH AM K0 ENT FRS A10 AOV V8 ACCV VEC KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  unfold PEBSKAN.bat in VEC. destruct VEC as (VDEF & VACC & VB & VE & VC & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (c) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (VBLK : v + 24 <= b \/ b + c <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + n)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + c)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).

  pose proof (PEBEHP.hkuA_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBEHP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & FZ1 & MS1 & KS1 & fR1 & fR2 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16 & T16 & T8).
  set (W1 := fun a => sp - 32 <= a < sp - 32 + 32).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb108c R1 0x7cc28 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 32 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).

  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMB.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMB.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (c) (n) (c)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12. exact fR12. }
  { rewrite L5K.rl13. exact fR13. }
  { exact BIN. }
  { exact B16. }
  { lia. }
  { lia. }
  { apply (PNBEK.ann_agree M M1 b (n) (c)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (PNBEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 16 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2320 <= a < sp) -> ~ in_shadow_of b (c) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 16) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }

  assert (TS : forall a v0, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNBEK.in_shadow_range b (c) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMBIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite CS2 by inl; exact fR2).
  pose proof (PMBIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMBIS1.bvu (getr R (reg 8))) as UR8.

  pose proof (PEBEHP.hkuB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBEHP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xb111c W_b10cc r F_b10cc eq_refl D_b10cc R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a : Z => False).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xb1110 R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by (intros a Ha; apply FR3; [exact Ha| intros []]).
  assert (TB : forall a, b <= a < b + c -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite TW3 by lia. apply T20; [lia| | lia|].
    - unfold aclient, aclient_g. left. exists (b, c). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }

  apply (KONT fx3 R3 M3 model3 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PEBEHP.KS_hkuB /\ In k' L5SAR.cs_all /\ In k' PEBEHP.KS_hkuA)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|Hk]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; inl.
  -   unfold PEBSKAN.bhdr.
    assert (TV : forall a, v <= a < v + 24 -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3 by lia. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
      intros X. pose proof (PNBEK.in_shadow_range b c a ltac:(lia) ltac:(lia) X). lia. }
    split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
    intros i Hi. rewrite TB by lia. exact (BDEF i Hi).
  - apply (PMFA.accA_agree M M3 v 24); [| exact ACCV]. intros x Hx. pose proof (PNBEK.S_range x ltac:(lia)) as SRx.
    rewrite TW3 by lia. apply T20; [lia| | lia|].
    + exact (PNBEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
    + apply (PNBEK.sh_apartU b c x v); lia.
  - destruct ANN2 as (ZA2 & PZ2 & _). unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b c).
    + intros x Hx. apply TW3. pose proof (PNBEK.S_range x ltac:(lia)). lia.
    + apply (L5CB.aacc_of_blk M2 b c b c (conj ZA2 PZ2)); lia.
  - intros a Ha. apply TB. exact Ha.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite TW3 by exact Ha. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
        (apply FR1; [exact Ha| unfold W1; lia]).
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.

Definition KSA : list nat := [3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Theorem ann_shrink_e_ok : ann_shrink_e_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb0aa8.
Proof.
  unfold ann_shrink_e_spec.
  intros fx R M model K LBX FF LK Aw cr v old b n c sp r HH AM K0 ENT FRS A10 A11 AOV V8 ACCV HDR OLD BAN KONT.
  unfold PEBSKAN.bhdr in HDR. destruct HDR as (VDEF & VB & VE & VC & NC & C27 & B4096 & B16 & BDEF).
  destruct BAN as (BACC & BANN).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSPA.pm_scr 0) with 12288 in *. change (12288 / 8) with 1536 in STKSH.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof AM as (Mh & MI).
  set (LB := [(b, c)] ++ LBX) in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & _ & _ & CB1 & CB2 & STOP & _).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b (c) HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _ & Bq5 & Bq6 & _ & Bq8).
  pose proof (PMKB.aobj_of_aobjA FF v 24 AOV V8) as AOB.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok LB FF LK cr Aw M model v 24 sp 12288 HH AOB ltac:(lia) ltac:(reflexivity)) as (OR & OBIG & ODEF & OVIS & OVSH & OCL & OCLSH).
  assert (VBLK : v + 24 <= b \/ b + c <= v).
  { destruct AOV as (f & Hf & Y1 & Y2). destruct (Bq8 f Hf) as [Y|Y]; [right; lia| left; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK' & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
  assert (X0 : L5.img_clear MV 1273856 1306624) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (X1 : L5.u64_at RSEGS MV 1335544 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1335544 2147450880 (VIMG 1335544 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (X2 : L5.u32_at RSEGS MV 1335552 1) by (apply (proj2 (L5A.u32_at_vis H M 1335552 1 (VIMG 1335552 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (X3 : L5.writable RSEGS MV (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H M (sp - 4096) 4096 (VIS (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M sp 12288); [exact ASTK| lia| lia| lia]. }
  assert (X5 : L5KA.zeros_at MV (v / 8 + 2147450880) 3).
  { exact (PMKB.obj_shadow_vis L ar C HI LYa HIok LB FF LK cr Aw M model v 24 HH AOV V8 ltac:(lia) ltac:(reflexivity) ACCV). }
  assert (X6 : L5.u64_at RSEGS MV v b) by (apply (proj2 (L5A.u64_at_vis H M v b ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VB).
  assert (X7 : L5.u64_at RSEGS MV (v + 8) (b + n)) by (apply (proj2 (L5A.u64_at_vis H M (v + 8) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VE).
  assert (X8 : L5.u64_at RSEGS MV (v + 16) (b + c)) by (apply (proj2 (L5A.u64_at_vis H M (v + 16) _ ltac:(eapply L5A.avis_sub; [exact OVIS| lia| lia]) ltac:(lia) ltac:(lia))); exact VC).

  assert (OLDB : 0 <= old <= 5864062014805) by (clear - OLD NC Bq0 Bq3; Lia.lia).
  assert (QCN : 0 <= c - n <= 140737488355328) by lia.
  pose proof (PEBEHP.hktA1_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 34%nat => old | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBEHP.aligned; lia | lia]).
  destruct P as (fxa & Ra & Ma & MGa & _ & FZa & MSa & KSa & aR2 & aR11 & aR12 & aR13 & aR14 & aR15 & aR16 & aR17 & T16a & T8a).
  destruct (ovf_guard fxa Ra Ma old aR12 aR16 aR17 OLDB) as (Rh & MSh & KSh & hR12 & hR16).
  assert (FACTa : forall a w, 0 <= a -> a + 8 <= sp - 16 -> L5.u64_at RSEGS MV a w -> L5.u64_at RSEGS Ma a w).
  { intros a w Ha Ha' X. apply (L5C.u64_at_agree RSEGS MV Ma a w); [| clear - Ha; Lia.lia| lia| exact X]. intros i Hi. apply FZa; lia. }
  pose proof (PEBEHP.hktA2_conc fxa Rh Ma (fun j => match j with 2%nat => sp | 33%nat => v | 35%nat => 24 * old + b | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P.
  cbn beta iota in P.
  assert (Y1 : 0 <= 24 * old + b < 2 ^ 64) by (clear - OLDB Bq0 Bq3 OLD; Lia.lia).
  assert (Y2 : getr Rh (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (KSh 2%nat) by lia; exact aR2).
  assert (Y10 : getr Rh (reg 10) = Z_to_bv 64 v) by (rewrite (KSh 10%nat) by lia; rewrite (KSa 10%nat) by inl; exact A10).
  assert (Y11 : getr Rh (reg 11) = Z_to_bv 64 (24 * old + b)) by (rewrite (KSh 11%nat) by lia; exact aR11).
  assert (Y13 : getr Rh (reg 13) = Z_to_bv 64 2147450880) by (rewrite (KSh 13%nat) by lia; exact aR13).
  assert (Y14 : getr Rh (reg 14) = Z_to_bv 64 b) by (rewrite (KSh 14%nat) by lia; exact aR14).
  assert (Y15 : getr Rh (reg 15) = Z_to_bv 64 1) by (rewrite (KSh 15%nat) by lia; exact aR15).
  assert (Y17 : getr Rh (reg 17) = Z_to_bv 64 24) by (rewrite (KSh 17%nat) by lia; exact aR17).
  assert (YW : L5.writable RSEGS Ma (sp - 4096) 4096) by exact (L5.writable_grows RSEGS MV Ma (sp - 4096) 4096 MGa X3).
  assert (YI : L5.img_clear Ma 1273856 1306624) by (intros i Hi; rewrite FZa by lia; exact (X0 i Hi)).
  assert (YS1 : L5.u64_at RSEGS Ma 1335544 2147450880) by (apply FACTa; [clear; Lia.lia| lia| exact X1]).
  assert (YS2 : L5.u32_at RSEGS Ma 1335552 1).
  { apply (PMF.u32_at_agree RSEGS MV Ma 1335552 1); [| clear; Lia.lia| clear; Lia.lia| exact X2]. intros i Hi. apply FZa; lia. }
  assert (YZ : L5KA.zeros_at Ma (v / 8 + 2147450880) 3).
  { intros j Hj. unfold L5KA.zeros_at in X5. rewrite <- (X5 j Hj). unfold byte_at. rewrite FZa; [reflexivity| |].
    - pose proof (PNBEK.S_range v ltac:(clear - OR; lia)) as SRg. unfold S, SB in SRg. clear - SRg Hj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
    - pose proof (PNBEK.S_range v ltac:(clear - OR; lia)) as SRg. unfold S, SB in SRg. clear - SRg Hj SLO SHI SPT Hr1 Hr2; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (OSP : v + 24 <= sp - 16) by lia.
  assert (Y6 : L5.u64_at RSEGS Ma v b) by (apply FACTa; [clear - OR; lia| clear - OSP; Lia.lia| exact X6]).
  assert (Y7 : L5.u64_at RSEGS Ma (v + 8) (b + n)) by (apply FACTa; [clear - OR; lia| clear - OSP; Lia.lia| exact X7]).
  assert (Y8 : L5.u64_at RSEGS Ma (v + 16) (b + c)) by (apply FACTa; [clear - OR; lia| clear - OSP; Lia.lia| exact X8]).
  L5SAR.feed P ltac:(first [assumption | unfold PEBEHP.aligned; lia | lia]).
  destruct P as (fx1 & R1 & M1v & MGb & _ & FZb & MSb & KSb & fR1 & fR10 & fR11 & fR12 & fR13 & fR14 & fR15 & fR16).
  pose proof (mem_grows_trans MV Ma M1v MGa MGb) as MG1.
  assert (FZ1 : forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> M1v (Z_to_bv 64 i) = MV (Z_to_bv 64 i)).
  { intros i Hi N. rewrite (FZb i Hi) by (clear - N; lia). apply (FZa i Hi). clear - N; lia. }
  assert (MS1 : msteps RSEGS (st fx R 0xb0aa8 MV) (st fx1 R1 0x7cc28 M1v)).
  { eapply msteps_trans; [exact MSa|]. eapply msteps_trans; [exact MSh| exact MSb]. }
  assert (KS1 : forall x, In x KSA -> getr R1 (reg x) = getr R (reg x)).
  { intros x Hx. rewrite (KSb x) by (revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx).
    rewrite (KSh x) by (revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [Lia.lia|]); destruct Hx).
    apply KSa. revert Hx; clear; intros Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx. }
  assert (fR2 : getr R1 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (KSb 2%nat) by inl; exact Y2).
  assert (CSV : forall a w, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS Ma a w -> L5.u64_at RSEGS M1v a w).
  { intros a w Ha Ha' X. apply (L5C.u64_at_agree RSEGS Ma M1v a w); [| lia| lia| exact X]. intros i Hi. apply FZb; lia. }
  pose proof (CSV (sp - 16) _ ltac:(clear; lia) ltac:(clear; lia) T16a) as T16. pose proof (CSV (sp - 8) _ ltac:(clear; lia) ltac:(clear; lia) T8a) as T8.
  set (W1 := fun a => sp - 32 <= a < sp - 32 + 32).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb0aa8 R1 0x7cc28 M1v W1 K HH AM MS1 MG1).
  { intros a Ha N. apply FZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold W1 in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  pose proof AM1 as (Mh1 & MI1).
  assert (SH01 : forall x, 0 <= x < 2 ^ 64 -> x < sp - 32 -> M1 (Z_to_bv 64 x) = M (Z_to_bv 64 x)) by (intros x Hx Hx'; apply FR1; [exact Hx| unfold W1; lia]).

  pose proof (HAJ.aex_annotate _ _ _ _ _ EXT) as ANN. unfold HAJ.annotate_spec in ANN.
  cbn [PMB.EXT HAJ.ec_ann_pc HAJ.ec_ann_scr paa_annotate PMB.AAD AADDR_A] in ANN. rewrite (L5A.aly_segs L C LYa) in ANN.
  apply (ANN fx1 R1 M1 model1 LB FF LK cr Aw K b (c) (24 * old) (n)); clear ANN.
  { exact HH1. }
  { exact Mh1. }
  { exact MI1. }
  { rewrite L5K.rl10. exact fR10. }
  { rewrite L5K.rl11. exact fR11. }
  { rewrite L5K.rl12, fR12. f_equal. lia. }
  { rewrite L5K.rl13. exact fR13. }
  { exact BIN. }
  { exact B16. }
  { lia. }
  { lia. }
  { apply (PNBEK.ann_agree M M1 b (24 * old) (c)); [| lia| lia| exact BANN].
    intros j Hj. pose proof (PNBEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj) as SL. apply SH01; lia. }
  { rewrite L5K.rl4, (KS1 4%nat) by inl. exact Rtp. }
  { rewrite L5K.rl1, fR1. vm_compute. reflexivity. }
  { rewrite L5K.rl2, fR2, L5.unsigned_lit by lia.
    apply (L5SAR.astack_ok_of_astk L ar C LYa M M1 sp 12288 16 2304 ASTK MGM1); [lia| lia| lia|].
    replace (sp - 16) with (sp + (-1) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { exact K0. }
  intros fx2 R2 M2 model2 Aw2 RP2 ANN2 KEEP2 DSH2 SCR2 MRT2 INC2 MI2 HH2.
  rewrite L5K.rl2, fR2, L5.unsigned_lit in KEEP2, SCR2 by lia. rewrite L5K.rl1, fR1.
  assert (AM2 : L5CA.amodel_ok Aw2 model2) by (split; [rewrite (L5LZ.model_rt_halted model1 model2 MRT2); exact Mh1| exact MI2]).
  assert (CS2 : forall k0, In k0 L5SAR.cs_all -> getr R2 (reg k0) = getr R1 (reg k0)) by (intros k0 Hk; apply (L5SAR.cs_of_preserved R1 R2 k0 RP2 Hk)).
  assert (T20 : forall a, 0 <= a < 2 ^ 64 -> aclient L ar LB FF 0 0 a -> ~ (sp - 2320 <= a < sp) -> ~ in_shadow_of b (c) a -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hc N1 N2. rewrite (KEEP2 a Ha ltac:(apply (L5SAR.aclient_narrow L ar LB FF 0 0); [exact Hc| lia]) N2). apply FR1; [exact Ha| unfold W1; lia]. }
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 HH2) as (HOFF2 & VIS2 & VIMG2 & VFS2 & VBLK2 & VBSH2 & VFSSH2 & VSTSH2).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  assert (ASTK2 : L5CA.astk ar M2 sp 12288).
  { apply (L5SAR.astk_after_eq L ar C HI HIok LB FF LK cr Aw M M1 M2 _ sp 12288 (sp - 16) 2304 HH ASTK MGM1).
    - intros a Ha Hs Hns. apply KEEP2; [exact Ha| apply L5SAR.stack_client; [exact Hs| exact Hns]|].
      intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia.
    - exact SCR2.
    - lia. - lia. - lia. }
  assert (Y3 : L5.writable RSEGS MV2 (sp - 4096) 4096).
  { apply (proj2 (L5A.writable_vis H2 M2 (sp - 4096) 4096 (VIS2 (sp - 4096) 4096 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5SAR.astk_writable ar M2 sp 12288); [exact ASTK2| lia| lia| lia]. }

  assert (TS : forall a v0, sp - 16 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v0 -> L5.u64_at RSEGS MV2 a v0).
  { intros a v0 Ha Ha' X. apply (proj2 (L5A.u64_at_vis H2 M2 a v0 (VIS2 a 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
    apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply KEEP2; [lia| apply L5SAR.stack_client; lia|]| lia| lia|].
    - intros XS. pose proof (PNBEK.in_shadow_range b (c) i ltac:(lia) ltac:(lia) XS). lia.
    - apply (PMBIS1.vis_u64 _ _ _ _ _ VIS1); [apply VIS; lia| lia| lia| exact X]. }
  pose proof (TS (sp - 8) _ ltac:(lia) ltac:(lia) T8) as Z8.
  pose proof (TS (sp - 16) _ ltac:(lia) ltac:(lia) T16) as Z16.
  assert (J2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite CS2 by inl; exact fR2).
  pose proof (PMBIS1.bvu (getr R (reg 1))) as UR1. pose proof (PMBIS1.bvu (getr R (reg 8))) as UR8.

  pose proof (PEBEHP.hktB_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 43%nat => bv_unsigned (getr R (reg 1)) | 44%nat => bv_unsigned (getr R (reg 8)) | _ => 0 end)) as P.
  cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | unfold PEBEHP.aligned; lia | lia]).
  destruct P as (fx3 & R3 & M3v & MG3 & _ & FZ3 & MS3 & KS3 & gR1 & gR2 & gR8).
  assert (R3ra : getr R3 (reg 1) = Z_to_bv 64 r) by (rewrite gR1, Z_to_bv_bv_unsigned; exact Rra).
  pose proof (PMK.ret_to RSEGS fx3 R3 M3v 0xb0b48 W_b0af8 r F_b0af8 eq_refl D_b0af8 R3ra ltac:(lia) Hr2) as MS4.
  set (W3 := fun a : Z => False).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw2 M2 model2 fx2 fx3 R2 0xb0b3c R3 r M3v W3 K HH2 AM2 ltac:(eapply msteps_trans; [exact MS3| exact MS4]) MG3).
  { intros a Ha N. apply FZ3; exact Ha. }
  { intros a Ha Wa. destruct Wa. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
  assert (TW3 : forall a, 0 <= a < 2 ^ 64 -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)) by (intros a Ha; apply FR3; [exact Ha| intros []]).
  assert (TB : forall a, b <= a < b + c -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha. rewrite TW3 by lia. apply T20; [lia| | lia|].
    - unfold aclient, aclient_g. left. exists (b, c). split; [exact BIN| cbn [fst snd]; lia].
    - intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }

  apply (KONT fx3 R3 M3 model3 LK Aw2).
  - apply L5SAR.preserved_by_index. intros k0 Hk.
    assert (CH : forall k', In k' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R3 (reg k') = getr R (reg k')).
    { intros k' Hk'. assert (Y : In k' PEBEHP.KS_hktB /\ In k' L5SAR.cs_all /\ In k' KSA)
        by (destruct Hk' as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]; (split; [inl| split; inl])).
      destruct Y as (Yk1 & Yk2 & Yk3). rewrite (KS3 k' Yk1), (CS2 k' Yk2), (KS1 k' Yk3). reflexivity. }
    unfold L5SAR.cs_all in Hk. destruct Hk as [<-|[<-|[<-|[<-|Hk]]]].
    + rewrite gR2. exact (eq_sym Rsp).
    + apply CH; left; reflexivity.
    + apply CH; right; left; reflexivity.
    + rewrite gR8, Z_to_bv_bv_unsigned; reflexivity.
    + apply CH. destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]; inl.
  - assert (TV : forall a, v <= a < v + 24 -> M3 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite TW3 by lia. apply T20; [lia| apply (L5SAR.obj_client L ar LB FF 0 0 v 24 a AOB); lia| lia|].
      intros X. pose proof (PNBEK.in_shadow_range b (c) a ltac:(lia) ltac:(lia) X). lia. }
    destruct ANN2 as (ZA2 & PM2 & PA2).
      unfold PEBSKAN.bat.
    split. { intros i Hi. rewrite TV by lia. exact (VDEF i Hi). }
    split. { apply (PMFA.accA_agree M M3 v 24); [| exact ACCV]. intros x Hx. pose proof (PNBEK.S_range x ltac:(lia)) as SRx.
             rewrite TW3 by lia. apply T20; [lia| | lia|].
             + exact (PNBEK.frame_sh_client L ar FF v 24 x LB 0 0 AOV Hx).
             + apply (PNBEK.sh_apartU b c x v); lia. }
    cbn. split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VB]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VE]. }
    split. { apply (L5C.u64_at_agree RSEGS M M3); [intros i Hi; apply TV; lia| lia| lia| exact VC]. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact B16|].
    split. { intros i Hi. rewrite TB by lia. exact (BDEF i Hi). }
    split. { unfold PMSPA.accA. apply (PMFA.accA_agree M2 M3 b n).
             - intros x Hx. apply TW3. pose proof (PNBEK.S_range x ltac:(lia)). lia.
             - apply (L5CB.aacc_of_blk M2 b n b n (conj ZA2 PM2)); lia. }
    apply (PNBEK.ann_agree M2 M3 b n c); [| lia| lia| split; [exact ZA2| split; [exact PM2| exact PA2]]].
    intros j Hj. apply TW3. pose proof (PNBEK.shadow_lowU b c j ltac:(lia) ltac:(lia) Hj). lia.
  - intros a Ha. apply TB. exact Ha.
  - apply (L5SAR.ahpres_of L ar LBX FF sp 12288 _ M M3).
    + intros a (Ha & Hc & Ho).
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite TW3 by exact Ha. rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok LB FF LK cr Aw M _ sp 12288 a HH SPT HcB) as [Z1|Z1];
        (apply FR1; [exact Ha| unfold W1; lia]).
    + pose proof ASTK2 as (_ & _ & _ & _ & SD2 & _). apply (L5.defined_grows M2 M3 _ _ MGM3). exact SD2.
    + intros a Ha Hc HM. apply MGM3.
      assert (HcB : aclient L ar LB FF sp 12288 a) by (apply (L5SAR.aclient_appb L ar LBX [(b, c)] FF sp 12288 a Hc)).
      assert (NS : ~ in_shadow_of b (c) a) by (exact (PNBEK.own_sh_notclientU L ar C HI LY HIok b (c) LBX FF LK cr Aw M _ HH a sp 12288 Hc)).
      rewrite (KEEP2 a Ha); [| apply (L5SAR.aclient_mono L ar LB FF sp 12288 (sp - 16) 2304 a HcB); intros x Hx; lia| exact NS].
      apply MGM1. exact HM.
  - apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3]. apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
  - intros x Hx. exact Hx.
  - exact INC2.
  - exact AM3.
  - exact HH3.
Qed.

End Stage.
End PEBEKAN.
