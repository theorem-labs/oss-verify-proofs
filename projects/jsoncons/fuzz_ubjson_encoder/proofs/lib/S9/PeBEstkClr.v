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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PeSpecsAb PgV8 PnModel PnModelFacts PeSpecsAX PmModelFactsA PmStep PeStepAB0 PeStepB2 PmCertKitG PeBIss1 PeBEmbKit PeBReset1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeSpecsBX PeBSnkAnn PeBEstkHP PeBEstkAnn.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_b48d4_b48dc.
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
Module PEBEKC.

Section Specs.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition clear_e_spec (pc : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (v b n c m : Z) (sp r : Z),
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA A L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 ->
    PEBSKAN.bat segs M v b n c -> n = 24 * m -> L5.img_clear M 65536 1306624 ->
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

Lemma v_mul_magic24 m : 0 <= m <= 2 ^ 60 -> v_mul (Z_to_bv 64 (24 * m / 8)) (Z_to_bv 64 12297829382473034411) = Z_to_bv 64 m.
Proof.
  intros Hm. unfold v_mul. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (24 * m / 8) with (3 * m) by Lia.lia. rewrite (Z.mod_small (3 * m)) by Lia.lia. rewrite (Z.mod_small 12297829382473034411) by Lia.lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (3 * m * 12297829382473034411) with (m + (2 * m) * 2 ^ 64) by Lia.lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Definition KSL : list nat := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
Section Loop.
Variable M : word -> option byte.
Variables (Sp b : Z).
Hypothesis HS : 140735332491264 <= Sp <= 140737488355328.
Hypothesis A16 : Sp mod 16 = 0.
Hypothesis WR : L5.writable RSEGS M (Sp - 4096) 4096.
Hypothesis Hb : 4096 <= b <= 140737488355327.

Lemma round fx R p :
  getr R (reg 2) = Z_to_bv 64 (Sp - 16) -> getr R (reg 13) = Z_to_bv 64 b -> getr R (reg 15) = Z_to_bv 64 24 -> getr R (reg 16) = Z_to_bv 64 p ->
  b + 24 <= p -> p <= 140737488355327 ->
  exists fx' R', (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)) /\
    (   (msteps RSEGS (st fx R 0xb4900 M) (st fx' R' 0xb4900 M) /\ getr R' (reg 16) = Z_to_bv 64 (p - 24) /\ p - 24 <> b)
     \/ (msteps RSEGS (st fx R 0xb4900 M) (st fx' R' 0xb4910 M) /\ p - 24 = b)).
Proof.
  intros R2 R13 R15 R16 Hp1 Hp2.
  assert (Q1 : 0 <= Sp < 2 ^ 64) by (clear - HS; Lia.lia). assert (Q2 : 0 <= b < 2 ^ 64) by (clear - Hb; Lia.lia).
  assert (Q3 : 0 <= p < 2 ^ 64) by (clear - Hb Hp1 Hp2; Lia.lia). assert (Q4 : 4120 <= p <= 140737488355327) by (clear - Hb Hp1 Hp2; Lia.lia).
  pose proof (PEBEHP.hkfL_conc fx R M (fun j => match j with 2%nat => Sp | 34%nat => b | 35%nat => p | _ => 0 end)) as PL. cbn beta iota in PL.
  L5SAR.feed PL ltac:(first [assumption | unfold PEBEHP.aligned; exact A16]).
  destruct PL as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & L16).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
  assert (R1_2 : getr R1 (reg 2) = Z_to_bv 64 (Sp - 16)) by (rewrite (KS1 2%nat) by inl; exact R2).
  assert (R1_13 : getr R1 (reg 13) = Z_to_bv 64 b) by (rewrite (KS1 13%nat) by inl; exact R13).
  assert (R1_15 : getr R1 (reg 15) = Z_to_bv 64 24) by (rewrite (KS1 15%nat) by inl; exact R15).
  assert (Q5 : 0 <= p - 24 < 2 ^ 64) by (clear - Hb Hp1 Hp2; Lia.lia).
  pose proof (PEBEHP.hkfM_conc fx1 R1 M (fun j => match j with 2%nat => Sp | 34%nat => b | 35%nat => p - 24 | _ => 0 end)) as PM. cbn beta iota in PM.
  L5SAR.feed PM ltac:(first [assumption | unfold PEBEHP.aligned; exact A16]).
  destruct PM as (fx2 & R2' & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M) by (apply functional_extensionality; exact FR2). subst M2.
  assert (MODE : (p - 24 - b) mod 2 ^ 64 = p - 24 - b) by (apply Z.mod_small; clear - Hb Hp1 Hp2; Lia.lia).
  exists fx2, R2'. destruct EX as [(MS2 & KS2 & F)|(MS2 & KS2 & F)]; rewrite MODE in F.
  - split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (L5K.incl_b KSL PEBEHP.KS_hkfM_0); vm_compute; reflexivity).
             apply KS1. revert x Hx. apply (L5K.incl_b KSL PEBEHP.KS_hkfL). vm_compute. reflexivity. }
    left. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [rewrite (KS2 16%nat) by inl; exact L16|]. clear - F. Lia.lia.
  - split. { intros x Hx. rewrite (KS2 x) by (revert x Hx; apply (L5K.incl_b KSL PEBEHP.KS_hkfM_1); vm_compute; reflexivity).
             apply KS1. revert x Hx. apply (L5K.incl_b KSL PEBEHP.KS_hkfL). vm_compute. reflexivity. }
    right. split; [eapply msteps_trans; [exact MS1| exact MS2]| clear - F Hp1; Lia.lia].
Qed.

Lemma loop_ms (j : nat) : forall fx R,
  getr R (reg 2) = Z_to_bv 64 (Sp - 16) -> getr R (reg 13) = Z_to_bv 64 b -> getr R (reg 15) = Z_to_bv 64 24 -> getr R (reg 16) = Z_to_bv 64 (b + 24 * (Z.of_nat j + 1)) ->
  b + 24 * (Z.of_nat j + 1) <= 140737488355327 ->
  exists fx' R', msteps RSEGS (st fx R 0xb4900 M) (st fx' R' 0xb4910 M) /\ (forall x, In x KSL -> getr R' (reg x) = getr R (reg x)).
Proof.
  induction j as [|j IH]; intros fx R R2 R13 R15 R16 HB.
  - destruct (round fx R (b + 24 * (Z.of_nat 0 + 1)) R2 R13 R15 R16 ltac:(clear; Lia.lia) HB) as (fx1 & R1 & KS1 & [(MS & _ & X)|(MS & _)]); [exfalso; clear - X; Lia.lia|].
    exists fx1, R1. split; [exact MS| exact KS1].
  - destruct (round fx R (b + 24 * (Z.of_nat (Datatypes.S j) + 1)) R2 R13 R15 R16 ltac:(clear; Lia.lia) HB) as (fx1 & R1 & KS1 & [(MS & L16 & X)|(MS & X)]); [|exfalso; clear - X; Lia.lia].
    destruct (IH fx1 R1) as (fx2 & R2' & MS2 & KS2).
    + rewrite (KS1 2%nat) by inl. exact R2.
    + rewrite (KS1 13%nat) by inl. exact R13.
    + rewrite (KS1 15%nat) by inl. exact R15.
    + rewrite L16. f_equal. clear; Lia.lia.
    + clear - HB; Lia.lia.
    + exists fx2, R2'. split; [eapply msteps_trans; [exact MS| exact MS2]|]. intros x Hx. rewrite (KS2 x Hx). apply KS1. exact Hx.
Qed.
End Loop.

Section Stage.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma clear_core : PEBEKAN.ann_shrink_e_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb0aa8 ->
  forall (fx : FPState) R M model K LBX FF LK Aw cr v b n c m sp r,
    ri_inv HI ([(b, c)] ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    PMSPA.entryA PeCLayoutB.CADDR_B L ar R M sp r 0 -> PMSPA.ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 v -> PMSPA.aobjA FF v 24 -> v mod 8 = 0 ->
    PEBSKAN.bat RSEGS M v b n c -> n = 24 * m ->
    (exists fx1 R1 M1v, mem_grows (mrestrict (ahid Aw model) M) M1v
       /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 16 <= i < sp - 16 + 16) -> ~ (v + 8 <= i < v + 8 + 8) -> M1v (Z_to_bv 64 i) = mrestrict (ahid Aw model) M (Z_to_bv 64 i))
       /\ msteps RSEGS (st fx R 0xb48b4 (mrestrict (ahid Aw model) M)) (st fx1 R1 0xb0aa8 M1v)
       /\ (forall k, In k KC -> getr R1 (reg k) = getr R (reg k))
       /\ getr R1 (reg 11) = Z_to_bv 64 m
       /\ L5.u64_at RSEGS M1v (v + 8) b) ->
    (forall (fx' : FPState) R' M' model' LK' Aw',
        regs_preserved R R' -> PEBSKAN.bat RSEGS M' v b 0 c ->
        (forall a, b <= a < b + c -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 0) [(v + 8, 8)] M M' ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ([(b, c)] ++ LBX) FF LK' cr Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K) ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb48b4 M model) K.
Proof.
  intros ASH fx R M model K LBX FF LK Aw cr v b n c m sp r HH AM K0 ENT FRS A10 AOV V8 VAT En RUN KONT.
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
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R 0xb48b4 R1 0xb0aa8 M1v W1 K HH AM MS1 MG1).
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
  assert (AGS : forall a m0, 0 <= a -> a + m0 <= 2 ^ 47 -> PMFA.agsh M M1 a m0).
  { intros a m0 Ha Hn z Hz. apply SHK. exact (PNBEK.S_range z ltac:(clear - Ha Hn Hz; lia)). }
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

  unfold PEBEKAN.ann_shrink_e_spec in ASH.
  apply (ASH fx1 R1 M1 model1 K LBX FF LK Aw cr v m b 0 c sp r).
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
  { destruct VX as (_ & _ & _ & NC & _). clear - NC En. Lia.lia. }
  { destruct VX as (X0 & X8 & X16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
    assert (BIN : In (b, c) LB) by (left; reflexivity).
    destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _).
    rewrite <- En. split.
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

Theorem clear_e_of : PEBEKAN.ann_shrink_e_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb0aa8 -> clear_e_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb48b4.
Proof.
  intros ASH. unfold clear_e_spec.
  intros fx R M model K LBX FF LK Aw cr v b n c m sp r HH AM K0 ENT FRS A10 AOV V8 VAT En IMG KONT.
  apply (clear_core ASH fx R M model K LBX FF LK Aw cr v b n c m sp r HH AM K0 ENT FRS A10 AOV V8 VAT En); [| exact KONT].
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
  assert (X0 : L5.img_clear (mrestrict (ahid Aw model) M) 65536 1306624) by (apply L5A.img_clear_mrestrict; exact IMG).
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
  assert (OSP : v + 24 <= sp - 4096) by lia.
  remember (mrestrict (ahid Aw model) M) as MV eqn:EMV.
  destruct VX as (W0 & W8 & W16 & NC & C27 & B4096 & B16 & BDEF & BACC & BANN).
  assert (BIN : In (b, c) LB) by (left; reflexivity).
  destruct (PNBEK.blk_facts L ar C HI LY HIok _ FF LK cr Aw M _ b c HH BIN) as (Bq0 & Bq1 & Bq2 & Bq3 & _).
  apply UV in W0; [| lia| lia]. apply UV in W8; [| lia| lia]. apply UV in W16; [| lia| lia].
  assert (Q8 : 0 <= b < 2 ^ 64) by lia. assert (Q9 : 0 <= c < 2 ^ 64) by lia. assert (Q10 : 4096 <= b <= 140737488355327) by lia. assert (QC : 1 <= c <= 140737488355328) by lia.
  assert (Q11 : 0 <= n < 2 ^ 64) by lia. assert (Q12 : 0 <= n <= 140737488355328) by lia.
  assert (Hm : 0 <= m /\ 24 * m <= 140737488355328) by (clear - NC En Bq3 Bq0; Lia.lia).

  pose proof (PEBEHP.hkfX_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 41%nat => c | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | exact V8 | exact A16 | exact B16]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FZ1 & EX1).

  assert (J1 : exists fx2 R2, msteps RSEGS (st fx R 0xb48b4 MV) (st fx2 R2 0xb4910 M1)
            /\ (forall x, In x KC -> x <> 2%nat -> getr R2 (reg x) = getr R (reg x))
            /\ getr R2 (reg 2) = Z_to_bv 64 (sp - 16) /\ getr R2 (reg 12) = Z_to_bv 64 ((v + 8) / 8 + 2147450880)
            /\ getr R2 (reg 13) = Z_to_bv 64 b /\ getr R2 (reg 14) = Z_to_bv 64 (b + n)
            /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (reg 1)))).
  { destruct EX1 as [(MS1 & KS1 & r2 & r11 & r12 & r13 & r14 & r15 & r16 & NE & C8)|(MS1 & KS1 & r2 & r11 & r12 & r13 & r14 & EQ & C8)].
    -
      assert (NZ : n <> 0).
      { intros N0. rewrite N0, Z.add_0_r, (Z.mod_small b), Z.sub_diag, Zmod_0_l in NE by (clear - Q8; Lia.lia). clear - NE. Lia.lia. }
      assert (M1' : 1 <= m) by (clear - NZ En Hm NC; Lia.lia).
      assert (WR1 : L5.writable RSEGS M1 (sp - 4096) 4096) by exact (L5.writable_grows RSEGS MV M1 (sp - 4096) 4096 MG1 X3).
      destruct (loop_ms M1 sp b Q3 A16 WR1 Q10 (Z.to_nat (m - 1)) fx1 R1 r2 r13 r15) as (fx2 & R2 & MS2 & KS2).
      + rewrite r16. f_equal. rewrite Z2Nat.id by (clear - M1'; Lia.lia). clear - En M1'. Lia.lia.
      + rewrite Z2Nat.id by (clear - M1'; Lia.lia). clear - En M1' NC Bq2 SLO SHI SPT; Lia.lia.
      + exists fx2, R2. split; [eapply msteps_trans; [exact MS1| exact MS2]|].
        split. { intros x Hx Hx2. rewrite (KS2 x) by (revert Hx Hx2; clear; intros Hx Hx2; unfold KC in Hx; repeat (destruct Hx as [<-|Hx]; [first [inl | exfalso; apply Hx2; reflexivity]|]); destruct Hx).
                 apply KS1. revert Hx Hx2; clear; intros Hx Hx2; unfold KC in Hx; repeat (destruct Hx as [<-|Hx]; [first [inl | exfalso; apply Hx2; reflexivity]|]); destruct Hx. }
        split; [rewrite (KS2 2%nat) by inl; exact r2|]. split; [rewrite (KS2 12%nat) by inl; exact r12|].
        split; [rewrite (KS2 13%nat) by inl; exact r13|]. split; [rewrite (KS2 14%nat) by inl; exact r14| exact C8].
    -
      exists fx1, R1. split; [exact MS1|].
      split. { intros x Hx Hx2. apply KS1. revert Hx Hx2; clear; intros Hx Hx2; unfold KC in Hx; repeat (destruct Hx as [<-|Hx]; [first [inl | exfalso; apply Hx2; reflexivity]|]); destruct Hx. }
      split; [exact r2|]. split; [exact r12|]. split; [exact r13|]. split; [exact r14| exact C8]. }
  clear EX1. destruct J1 as (fx2 & R2 & MS2 & KS2 & g2 & g12 & g13 & g14 & C8).

  assert (FACT1 : forall a w, 0 <= a -> a + 8 <= sp - 16 -> L5.u64_at RSEGS MV a w -> L5.u64_at RSEGS M1 a w).
  { intros a w Ha Ha' X. apply (L5C.u64_at_agree RSEGS MV M1 a w); [| clear - Ha; Lia.lia| lia| exact X]. intros i Hi. apply FZ1; lia. }
  assert (YI : L5.img_clear M1 65536 1306624) by (intros i Hi; rewrite FZ1 by lia; exact (X0 i Hi)).
  assert (YS1 : L5.u64_at RSEGS M1 1335544 2147450880) by (apply FACT1; [clear; Lia.lia| lia| exact X1]).
  assert (YS2 : L5.u32_at RSEGS M1 1335552 1).
  { apply (PMF.u32_at_agree RSEGS MV M1 1335552 1); [| clear; Lia.lia| clear; Lia.lia| exact X2]. intros i Hi. apply FZ1; lia. }
  assert (YW : L5.writable RSEGS M1 (sp - 4096) 4096) by exact (L5.writable_grows RSEGS MV M1 (sp - 4096) 4096 MG1 X3).
  assert (YZ : L5KA.zeros_at M1 (v / 8 + 2147450880) 3).
  { intros j Hj. unfold L5KA.zeros_at in X5. rewrite <- (X5 j Hj). unfold byte_at. rewrite FZ1; [reflexivity| |].
    - pose proof (PNBEK.S_range v ltac:(clear - OR; lia)) as SRg. unfold S, SB in SRg. clear - SRg Hj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Lia.lia.
    - pose proof (PNBEK.S_range v ltac:(clear - OR; lia)) as SRg. unfold S, SB in SRg. clear - SRg Hj SLO SHI SPT Q3; lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (YZ8 : L5KA.zeros_at M1 ((v + 8) / 8 + 2147450880) 1).
  { intros j Hj. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    replace ((v + 8) / 8 + 2147450880 + j) with (v / 8 + 2147450880 + 1) by (clear - V8 Hj; Lia.lia). apply (YZ 1). clear; Lia.lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (Y6 : L5.u64_at RSEGS M1 v b) by (apply FACT1; [clear - OR; lia| clear - OSP; Lia.lia| exact W0]).
  assert (Y7 : L5.u64_at RSEGS M1 (v + 8) (b + n)) by (apply FACT1; [clear - OR; lia| clear - OSP; Lia.lia| exact W8]).
  assert (Y8 : L5.u64_at RSEGS M1 (v + 16) (b + c)) by (apply FACT1; [clear - OR; lia| clear - OSP; Lia.lia| exact W16]).
  assert (G10 : getr R2 (reg 10) = Z_to_bv 64 v) by (rewrite (KS2 10%nat ltac:(inl) ltac:(clear; Lia.lia)); exact A10).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  assert (QZ : 0 <= (v + 8) / 8 + 2147450880 < 2 ^ 64) by (clear - Q4; Lia.lia).
  assert (QZ2 : 2147483648 <= (v + 8) / 8 + 2147450880 <= 19791209299968) by (clear - Q4; Lia.lia).
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (QBN : 0 <= b + n < 2 ^ 64) by (clear - Q8 Q12 Bq3 NC; Lia.lia).
  pose proof (PEBEHP.hkfT_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 33%nat => v | 36%nat => b | 37%nat => n | 38%nat => (v + 8) / 8 + 2147450880 | 41%nat => c | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | exact V8 | exact A16 | exact B16]).
  destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & MS3 & KS3 & t11 & t12 & t14).
  assert (EM : M3 = M1) by (apply functional_extensionality; exact FR3). subst M3.

  pose proof (PMBRS1.srai_to fx3 R3 M1 0xb4924 W_b48d4 _ _ _ F_b48d4 eq_refl D_b48d4 eq_refl ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) as MSR.
  set (R3t := regupd R3 14%bv (v_srai (getr R3 14%bv) (bv_unsigned (3%bv : bv 6)))) in MSR.
  assert (N14 : (14%bv : bv 5) <> 0%bv) by (intros X; discriminate X). assert (N11 : (11%bv : bv 5) <> 0%bv) by (intros X; discriminate X).
  assert (T14t : getr R3t (reg 14) = Z_to_bv 64 (24 * m / 8)).
  { unfold R3t. rewrite <- L5K.rl14. rewrite (getr_same R3 14%bv _ N14). rewrite L5K.rl14, t14, En. change (bv_unsigned (3%bv : bv 6)) with 3.
    rewrite PNBEK.v_srai3_small by (clear - Hm; Lia.lia). reflexivity. }
  assert (TOt : forall j, j <> 14%nat -> (j < 32)%nat -> getr R3t (reg j) = getr R3 (reg j)).
  { intros j Hj Hl. unfold R3t. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (14%bv : bv 5)) with 14 in E.
    rewrite Z.mod_small in E by Lia.lia. Lia.lia. }
  pose proof (PNBEK.mul_to fx3 R3t M1 0xb4928 W_b48d8 _ _ _ F_b48d8 eq_refl D_b48d8 eq_refl ltac:(clear; Lia.lia) ltac:(clear; Lia.lia)) as MSM.
  set (R3m := regupd R3t 11%bv (v_mul (getr R3t 14%bv) (getr R3t 11%bv))) in MSM.
  assert (T11 : getr R3m (reg 11) = Z_to_bv 64 m).
  { unfold R3m. rewrite <- L5K.rl11. rewrite (getr_same R3t 11%bv _ N11). rewrite L5K.rl14, T14t. rewrite L5K.rl11, (TOt 11%nat) by Lia.lia. rewrite t11.
    apply v_mul_magic24. clear - Hm; Lia.lia. }
  assert (TOm : forall j, j <> 11%nat -> j <> 14%nat -> (j < 32)%nat -> getr R3m (reg j) = getr R3 (reg j)).
  { intros j Hj Hj' Hl. unfold R3m. rewrite getr_other; [apply TOt; [exact Hj'| exact Hl]|]. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
    rewrite Z.mod_small in E by Lia.lia. Lia.lia. }

  assert (Hm2 : 0 <= m < 2 ^ 64) by (clear - Hm; Lia.lia). assert (Hm3 : 0 <= m <= 5864062014805) by (clear - Hm; Lia.lia).
  assert (U2 : getr R3m (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (TOm 2%nat) by Lia.lia; rewrite (KS3 2%nat) by inl; exact g2).
  assert (U10 : getr R3m (reg 10) = Z_to_bv 64 v) by (rewrite (TOm 10%nat) by Lia.lia; rewrite (KS3 10%nat) by inl; exact G10).
  assert (U13 : getr R3m (reg 13) = Z_to_bv 64 b) by (rewrite (TOm 13%nat) by Lia.lia; rewrite (KS3 13%nat) by inl; exact g13).
  assert (UR1 : getr R3m (reg 1) = getr R (reg 1)) by (rewrite (TOm 1%nat) by Lia.lia; rewrite (KS3 1%nat) by inl; exact (KS2 1%nat ltac:(inl) ltac:(clear; Lia.lia))).
  assert (C8' : L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R3m (reg 1)))) by (rewrite UR1; exact C8).
  assert (YW9 : L5.writable RSEGS M1 v 24) by exact (L5.writable_grows RSEGS MV M1 v 24 MG1 X9).
  pose proof (PEBEHP.hkfU_conc fx3 R3m M1 (fun j => match j with 2%nat => sp | 33%nat => v | 35%nat => m | 36%nat => b | 41%nat => c | _ => 0 end)) as P. cbn beta iota in P.
  L5SAR.feed P ltac:(first [assumption | exact V8 | exact A16 | exact B16]).
  destruct P as (fx4 & R4 & M4 & MG4 & _ & FZ4 & MS4 & KS4 & u2 & T8).
  exists fx4, R4, M4. split; [exact (mem_grows_trans MV M1 M4 MG1 MG4)|].
  split. { intros i Hi N1 N2. rewrite (FZ4 i Hi N2). exact (FZ1 i Hi N1). }
  split. { eapply msteps_trans; [exact MS2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MSR|]. eapply msteps_trans; [exact MSM| exact MS4]. }
  split.
  { intros k Hk. destruct (Nat.eq_dec k 2%nat) as [->|Hk2]; [rewrite u2; exact (eq_sym Rsp)|].
    rewrite (KS4 k) by (revert Hk Hk2; clear; intros Hk Hk2; unfold KC in Hk; repeat (destruct Hk as [<-|Hk]; [first [inl | exfalso; apply Hk2; reflexivity]|]); destruct Hk).
    rewrite (TOm k) by (revert Hk Hk2; clear; intros Hk Hk2; unfold KC in Hk; repeat (destruct Hk as [<-|Hk]; [Lia.lia|]); destruct Hk).
    rewrite (KS3 k) by (revert Hk Hk2; clear; intros Hk Hk2; unfold KC in Hk; repeat (destruct Hk as [<-|Hk]; [first [inl | exfalso; apply Hk2; reflexivity]|]); destruct Hk).
    apply (KS2 k Hk Hk2). }
  split; [rewrite (KS4 11%nat) by inl; exact T11| exact T8].
Qed.

Theorem clear_e_ok (EXT : HAJ.asan_ext_ok L ar SCFG HI PMB.EXT) : clear_e_spec RSEGS PeCLayoutB.CADDR_B L ar HI 0xb48b4.
Proof. exact (clear_e_of (PEBEKAN.ann_shrink_e_ok L ar C HI LY HIok EXT)). Qed.
End Stage.
End PEBEKC.
