(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem U0FuzzBase U0Fuzz_code FuzzCrcLib U0Fuzz_crcA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.

Definition UKBB : list reg := [2; 3; 4; 5; 10; 12]%bv.

Lemma UKBB_UKB : forall regs r, lkeeps UKBB regs r -> lkeeps UKB regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.

Section CRCB.
Context {RCa1 : RunCtx}.
  Variables (m rom : word -> option byte) (BA : Z -> Z) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hba : forall a, adr0 <= a < adr0 + len0 -> byte_at (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a = BA a.
  Hypothesis BA_rng : forall a, 0 <= BA a < 256.
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation WD := (Wd BA).

  Lemma WD_rng : forall a, 0 <= WD a < two32.
  Proof. intros. apply Wd_range. exact BA_rng. Qed.

  Lemma rd4 : forall a, adr0 <= a -> a + 4 <= adr0 + len0 ->
    exists bs, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (WD a)).
  Proof.
    intros a Ha Ha4. apply (rd4_bytes_at_v (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) m a (WD a)); [lia | lia | |].
    - intros i Hi. destruct (Hrd (a + i - adr0) ltac:(lia)) as [b Hb]. exists b.
      replace (adr0 + (a + i - adr0)) with (a + i) in Hb by lia. exact Hb.
    - unfold Wd, wle. rewrite !Hba by lia. reflexivity.
  Qed.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption | solve_kb] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].
  Ltac notrap F D := stepb_ft F D ltac:(zcond).

  Ltac lw_pl F D Hbs Hv :=
    chain_step;
    [ reflexivity
    | eapply step_lw; [exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
          match type of Hbs with rdn _ _ (Z_to_bv 64 ?y) _ = _ => replace x with y by lia end end;
        exact Hbs
      | exact Hv ]
    | step_simpl; gres; rewrite zv_lw by apply WD_rng ].

  Ltac lw_btab F D k idx fv :=
    chain_step;
    [ reflexivity
    | eapply step_lw with (v := Z_to_bv 64 (btab k idx));
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi; rewrite ?land_1020_6, ?land_1020_14;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with (BTAB + 1024 * k + 4 * idx) by (unfold BTAB; lia) end;
        apply rd_btab; [exact Himg | lia | first [apply land_255_range | apply shiftr24_low32_range] ]
      | apply btab_bs_v; [lia | first [apply land_255_range | apply shiftr24_low32_range] ] ]
    | step_simpl; gres; rewrite zv_lw by apply btab_range32; change (sx32 (btab k idx)) with fv ].

  Ltac srliR F D y Hy := stepi F D; znorm; rewrite (zv_srli y _) by exact Hy.

  Definition UBH (regs : bvmap 5 word) (x0 x1 x2 x3 x4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 x0 /\ getr regs 6 = Z_to_bv 64 x1 /\ getr regs 17 = Z_to_bv 64 x2
    /\ getr regs 16 = Z_to_bv 64 x3 /\ getr regs 15 = Z_to_bv 64 x4 /\ getr regs 11 = Z_to_bv 64 a
    /\ getr regs 18 = Z_to_bv 64 BTAB /\ getr regs 19 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 20 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 21 = Z_to_bv 64 (BTAB + 3072)
    /\ getr regs 31 = Z_to_bv 64 (-13) /\ getr regs 8 = Z_to_bv 64 (-17) /\ getr regs 9 = Z_to_bv 64 (-21)
    /\ getr regs 28 = Z_to_bv 64 0.

  Definition UB1 (regs : bvmap 5 word) (y0 y1 y2 y3 y4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 y0 /\ getr regs 6 = Z_to_bv 64 y1 /\ getr regs 17 = Z_to_bv 64 y2
    /\ getr regs 16 = Z_to_bv 64 y3 /\ getr regs 15 = Z_to_bv 64 y4 /\ getr regs 11 = Z_to_bv 64 a
    /\ getr regs 18 = Z_to_bv 64 BTAB /\ getr regs 19 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 20 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 21 = Z_to_bv 64 (BTAB + 3072)
    /\ getr regs 31 = Z_to_bv 64 (-13) /\ getr regs 8 = Z_to_bv 64 (-17) /\ getr regs 9 = Z_to_bv 64 (-21)
    /\ getr regs 28 = Z_to_bv 64 0
    /\ getr regs 22 = Z_to_bv 64 (BTAB + Z.land y0 255 * 2 ^ 2)
    /\ getr regs 23 = Z_to_bv 64 (BTAB + Z.land y1 255 * 2 ^ 2)
    /\ getr regs 24 = Z_to_bv 64 (BTAB + Z.land y2 255 * 2 ^ 2)
    /\ getr regs 25 = Z_to_bv 64 (BTAB + Z.land y3 255 * 2 ^ 2)
    /\ getr regs 26 = Z_to_bv 64 (BTAB + Z.land y4 255 * 2 ^ 2)
    /\ getr regs 27 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y0 6) 1020)
    /\ getr regs 1 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y1 6) 1020)
    /\ getr regs 13 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y2 6) 1020)
    /\ getr regs 29 = Z_to_bv 64 (Z.shiftr y3 6)
    /\ getr regs 30 = Z_to_bv 64 (Z.shiftr y4 6).

  Lemma ub1 : forall regs (x0 x1 x2 x3 x4 a cnt : Z),
    UBH regs x0 x1 x2 x3 x4 a -> getr regs 7 = Z_to_bv 64 cnt -> lrng (x0, x1, x2, x3, x4) ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x1469c : word) m rom) (mkst r (0x14750 : word) m rom)
      /\ UB1 r (Z.lxor (sx32 (WD a)) x0) (Z.lxor (sx32 (WD (a + 4))) x1) (Z.lxor (sx32 (WD (a + 8))) x2)
             (Z.lxor (sx32 (WD (a + 12))) x3) (Z.lxor (sx32 (WD (a + 16))) x4) a
      /\ getr r 7 = Z_to_bv 64 (cnt - 1)
      /\ lkeeps UKBB regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a cnt (R14 & R6 & R17 & R16 & R15 & R11 & R18 & R19 & R20 & R21 & R31 & R8 & R9 & R28) R7 HL Ha Ha20.
    cbn [lrng] in HL. destruct HL as (Hx0 & Hx1 & Hx2 & Hx3 & Hx4).
    destruct (rd4 a ltac:(lia) ltac:(lia)) as (bs0 & Hbs0 & Hv0).
    destruct (rd4 (a + 4) ltac:(lia) ltac:(lia)) as (bs1 & Hbs1 & Hv1).
    destruct (rd4 (a + 8) ltac:(lia) ltac:(lia)) as (bs2 & Hbs2 & Hv2).
    destruct (rd4 (a + 12) ltac:(lia) ltac:(lia)) as (bs3 & Hbs3 & Hv3).
    destruct (rd4 (a + 16) ltac:(lia) ltac:(lia)) as (bs4 & Hbs4 & Hv4).
    pose proof (lxor_range64 _ _ (sx32_range _ (WD_rng a)) Hx0) as Hy0.
    pose proof (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 4))) Hx1) as Hy1.
    pose proof (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 8))) Hx2) as Hy2.
    pose proof (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 12))) Hx3) as Hy3.
    pose proof (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 16))) Hx4) as Hy4.
    set (y0 := Z.lxor (sx32 (WD a)) x0) in *.
    set (y1 := Z.lxor (sx32 (WD (a + 4))) x1) in *.
    set (y2 := Z.lxor (sx32 (WD (a + 8))) x2) in *.
    set (y3 := Z.lxor (sx32 (WD (a + 12))) x3) in *.
    set (y4 := Z.lxor (sx32 (WD (a + 16))) x4) in *.
    eexists. split.
    - notrap F_1463c D_1463c.
      stepz F_14640 D_14640. notrap F_14644 D_14644.
      stepz F_14648 D_14648. notrap F_1464c D_1464c.
      notrap F_14650 D_14650. notrap F_14654 D_14654. notrap F_14658 D_14658.
      lw_pl F_1465c D_1465c Hbs0 Hv0.
      lw_pl F_14660 D_14660 Hbs1 Hv1.
      lw_pl F_14664 D_14664 Hbs2 Hv2.
      lw_pl F_14668 D_14668 Hbs3 Hv3.
      lw_pl F_1466c D_1466c Hbs4 Hv4.
      stepz F_14670 D_14670.
      stepz F_14674 D_14674. fold y0.
      stepz F_14678 D_14678. fold y1.
      stepz F_1467c D_1467c. fold y2.
      stepz F_14680 D_14680. fold y3.
      stepz F_14684 D_14684. fold y4.
      stepz F_14688 D_14688. stepz F_1468c D_1468c. stepz F_14690 D_14690. stepz F_14694 D_14694. stepz F_14698 D_14698.
      srliR F_1469c D_1469c y0 Hy0. srliR F_146a0 D_146a0 y1 Hy1. srliR F_146a4 D_146a4 y2 Hy2.
      srliR F_146a8 D_146a8 y3 Hy3. srliR F_146ac D_146ac y4 Hy4.
      stepz F_146b0 D_146b0. stepz F_146b4 D_146b4. stepz F_146b8 D_146b8. stepz F_146bc D_146bc. stepz F_146c0 D_146c0.
      stepz F_146c4 D_146c4. stepz F_146c8 D_146c8. stepz F_146cc D_146cc.
      stepz F_146d0 D_146d0. stepz F_146d4 D_146d4. stepz F_146d8 D_146d8. stepz F_146dc D_146dc. stepz F_146e0 D_146e0.
      stepz F_146e4 D_146e4. stepz F_146e8 D_146e8. stepz F_146ec D_146ec.
      apply mst_refl.
    - unfold UB1. post.
  Qed.

  Definition L01 (y : Z) : Z := Z.lxor (bT1 y) (bT0 y).

  Definition UB2 (regs : bvmap 5 word) (y0 y1 y2 y3 y4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 (Z.shiftr (y0 mod two32) 24) /\ getr regs 6 = Z_to_bv 64 (Z.shiftr (y1 mod two32) 24)
    /\ getr regs 17 = Z_to_bv 64 (Z.shiftr (y2 mod two32) 24) /\ getr regs 16 = Z_to_bv 64 (Z.shiftr (y3 mod two32) 24)
    /\ getr regs 15 = Z_to_bv 64 (Z.shiftr (y4 mod two32) 24) /\ getr regs 11 = Z_to_bv 64 a
    /\ getr regs 18 = Z_to_bv 64 BTAB /\ getr regs 19 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 20 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 21 = Z_to_bv 64 (BTAB + 3072)
    /\ getr regs 31 = Z_to_bv 64 (-13) /\ getr regs 8 = Z_to_bv 64 (-17) /\ getr regs 9 = Z_to_bv 64 (-21)
    /\ getr regs 28 = Z_to_bv 64 0
    /\ getr regs 22 = Z_to_bv 64 (L01 y0) /\ getr regs 23 = Z_to_bv 64 (L01 y1) /\ getr regs 13 = Z_to_bv 64 (L01 y2)
    /\ getr regs 29 = Z_to_bv 64 (L01 y3) /\ getr regs 30 = Z_to_bv 64 (L01 y4)
    /\ getr regs 27 = Z_to_bv 64 (bT2 y0) /\ getr regs 1 = Z_to_bv 64 (bT2 y1)
    /\ getr regs 24 = Z_to_bv 64 (Z.land (Z.shiftr y2 14) 1020)
    /\ getr regs 25 = Z_to_bv 64 (Z.land (Z.shiftr y3 14) 1020)
    /\ getr regs 26 = Z_to_bv 64 (Z.land (Z.shiftr y4 14) 1020).

  Lemma ub2 : forall regs (y0 y1 y2 y3 y4 a : Z),
    UB1 regs y0 y1 y2 y3 y4 a ->
    0 <= y0 < two64 -> 0 <= y1 < two64 -> 0 <= y2 < two64 -> 0 <= y3 < two64 -> 0 <= y4 < two64 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x14750 : word) m rom) (mkst r (0x147e8 : word) m rom)
      /\ UB2 r y0 y1 y2 y3 y4 a
      /\ getr r 7 = getr regs 7
      /\ lkeeps UKBB regs r.
  Proof.
    intros regs y0 y1 y2 y3 y4 a HB Hy0 Hy1 Hy2 Hy3 Hy4.
    destruct HB as (R14 & R6 & R17 & R16 & R15 & R11 & R18 & R19 & R20 & R21 & R31 & R8 & R9 & R28
                    & R22 & R23 & R24 & R25 & R26 & R27 & R1 & R13 & R29 & R30).
    eexists. split.
    - lw_btab F_146f0 D_146f0 0 (Z.land y4 255) (bT0 y4).
      lw_btab F_146f4 D_146f4 1 (Z.land (Z.shiftr y0 8) 255) (bT1 y0).
      lw_btab F_146f8 D_146f8 0 (Z.land y0 255) (bT0 y0).
      lw_btab F_146fc D_146fc 0 (Z.land y1 255) (bT0 y1).
      lw_btab F_14700 D_14700 0 (Z.land y2 255) (bT0 y2).
      lw_btab F_14704 D_14704 0 (Z.land y3 255) (bT0 y3).
      lw_btab F_14708 D_14708 1 (Z.land (Z.shiftr y1 8) 255) (bT1 y1).
      lw_btab F_1470c D_1470c 1 (Z.land (Z.shiftr y2 8) 255) (bT1 y2).
      stepz F_14710 D_14710. change (Z.lxor (bT1 y0) (bT0 y0)) with (L01 y0).
      srliR F_14714 D_14714 y0 Hy0.
      stepz F_14718 D_14718. change (Z.lxor (bT1 y1) (bT0 y1)) with (L01 y1).
      srliR F_1471c D_1471c y1 Hy1.
      stepz F_14720 D_14720. change (Z.lxor (bT1 y2) (bT0 y2)) with (L01 y2).
      srliR F_14724 D_14724 y2 Hy2.
      stepz F_14728 D_14728. stepz F_1472c D_1472c. stepz F_14730 D_14730. stepz F_14734 D_14734.
      stepz F_14738 D_14738. stepz F_1473c D_1473c. stepz F_14740 D_14740. stepz F_14744 D_14744.
      lw_btab F_14748 D_14748 1 (Z.land (Z.shiftr y3 8) 255) (bT1 y3).
      lw_btab F_1474c D_1474c 1 (Z.land (Z.shiftr y4 8) 255) (bT1 y4).
      lw_btab F_14750 D_14750 2 (Z.land (Z.shiftr y0 16) 255) (bT2 y0).
      lw_btab F_14754 D_14754 2 (Z.land (Z.shiftr y1 16) 255) (bT2 y1).
      stepz F_14758 D_14758. change (Z.lxor (bT1 y3) (bT0 y3)) with (L01 y3).
      srliR F_1475c D_1475c y3 Hy3.
      stepz F_14760 D_14760. change (Z.lxor (bT1 y4) (bT0 y4)) with (L01 y4).
      srliR F_14764 D_14764 y4 Hy4.
      stepz F_14768 D_14768. stepz F_1476c D_1476c. stepz F_14770 D_14770. stepz F_14774 D_14774. stepz F_14778 D_14778.
      stepz F_1477c D_1477c. stepz F_14780 D_14780. stepz F_14784 D_14784.
      apply mst_refl.
    - unfold UB2. post.
  Qed.

  Lemma ub3 : forall regs (y0 y1 y2 y3 y4 a : Z),
    UB2 regs y0 y1 y2 y3 y4 a ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x147e8 : word) m rom) (mkst r (0x14868 : word) m rom)
      /\ UBH r (mlaneY y0) (mlaneY y1) (mlaneY y2) (mlaneY y3) (mlaneY y4) (a + 20)
      /\ getr r 7 = getr regs 7
      /\ lkeeps UKBB regs r.
  Proof.
    intros regs y0 y1 y2 y3 y4 a HB.
    destruct HB as (R14 & R6 & R17 & R16 & R15 & R11 & R18 & R19 & R20 & R21 & R31 & R8 & R9 & R28
                    & R22 & R23 & R13 & R29 & R30 & R27 & R1 & R24 & R25 & R26).
    eexists. split.
    - stepz F_14788 D_14788. stepz F_1478c D_1478c. stepz F_14790 D_14790. stepz F_14794 D_14794. stepz F_14798 D_14798.
      stepz F_1479c D_1479c. stepz F_147a0 D_147a0. stepz F_147a4 D_147a4.
      stepz F_147a8 D_147a8. stepz F_147ac D_147ac. stepz F_147b0 D_147b0. stepz F_147b4 D_147b4. stepz F_147b8 D_147b8.
      lw_btab F_147bc D_147bc 2 (Z.land (Z.shiftr y2 16) 255) (bT2 y2).
      lw_btab F_147c0 D_147c0 2 (Z.land (Z.shiftr y3 16) 255) (bT2 y3).
      lw_btab F_147c4 D_147c4 2 (Z.land (Z.shiftr y4 16) 255) (bT2 y4).
      lw_btab F_147c8 D_147c8 3 (Z.shiftr (y0 mod two32) 24) (bT3 y0).
      lw_btab F_147cc D_147cc 3 (Z.shiftr (y1 mod two32) 24) (bT3 y1).
      lw_btab F_147d0 D_147d0 3 (Z.shiftr (y2 mod two32) 24) (bT3 y2).
      lw_btab F_147d4 D_147d4 3 (Z.shiftr (y3 mod two32) 24) (bT3 y3).
      lw_btab F_147d8 D_147d8 3 (Z.shiftr (y4 mod two32) 24) (bT3 y4).
      stepz F_147dc D_147dc. stepz F_147e0 D_147e0. stepz F_147e4 D_147e4. stepz F_147e8 D_147e8. stepz F_147ec D_147ec.
      stepz F_147f0 D_147f0. change (Z.lxor (Z.lxor (bT3 y0) (bT2 y0)) (L01 y0)) with (mlaneY y0).
      stepz F_147f4 D_147f4. change (Z.lxor (Z.lxor (bT3 y1) (bT2 y1)) (L01 y1)) with (mlaneY y1).
      stepz F_147f8 D_147f8. change (Z.lxor (Z.lxor (bT3 y2) (bT2 y2)) (L01 y2)) with (mlaneY y2).
      stepz F_147fc D_147fc. change (Z.lxor (Z.lxor (bT3 y3) (bT2 y3)) (L01 y3)) with (mlaneY y3).
      stepz F_14800 D_14800. change (Z.lxor (Z.lxor (bT3 y4) (bT2 y4)) (L01 y4)) with (mlaneY y4).
      stepz F_14804 D_14804.
      apply mst_refl.
    - unfold UBH. post.
  Qed.

  Lemma ubbody : forall regs (x0 x1 x2 x3 x4 a cnt : Z),
    UBH regs x0 x1 x2 x3 x4 a -> getr regs 7 = Z_to_bv 64 cnt -> lrng (x0, x1, x2, x3, x4) ->
    adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x1469c : word) m rom) (mkst r (0x14868 : word) m rom)
      /\ UBH r (mlane x0 (WD a)) (mlane x1 (WD (a + 4))) (mlane x2 (WD (a + 8))) (mlane x3 (WD (a + 12))) (mlane x4 (WD (a + 16))) (a + 20)
      /\ getr r 7 = Z_to_bv 64 (cnt - 1)
      /\ lkeeps UKBB regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a cnt HB R7 HL Ha Ha20.
    pose proof HL as HL'. cbn [lrng] in HL'. destruct HL' as (Hx0 & Hx1 & Hx2 & Hx3 & Hx4).
    destruct (ub1 regs x0 x1 x2 x3 x4 a cnt HB R7 HL Ha Ha20) as (r1 & M1 & HB1 & S7 & K1).
    destruct (ub2 r1 _ _ _ _ _ a HB1
                (lxor_range64 _ _ (sx32_range _ (WD_rng a)) Hx0)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 4))) Hx1)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 8))) Hx2)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 12))) Hx3)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 16))) Hx4)) as (r2 & M2 & HB2 & T7 & K2).
    destruct (ub3 r2 _ _ _ _ _ a HB2) as (r3 & M3 & HB3 & U7 & K3).
    exists r3. split; [|split; [|split]].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
    - rewrite !mlane_Y. exact HB3.
    - rewrite U7, T7. exact S7.
    - solve_kb.
  Qed.

  Lemma ubloop : forall (k : nat) regs (x : lanes) (a : Z),
    (let '(x0, x1, x2, x3, x4) := x in UBH regs x0 x1 x2 x3 x4 a) -> lrng x ->
    getr regs 7 = Z_to_bv 64 (Z.of_nat k) -> (1 <= k)%nat ->
    adr0 <= a -> a + 20 * Z.of_nat k <= adr0 + len0 ->
    exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments USEGS rc_inp rc_sp rc_mb) (mkst regs (0x1469c : word) m rom) (mkst r (0x1486c : word) m rom)
      /\ (let '(x0, x1, x2, x3, x4) := mrun BA k a x in UBH r x0 x1 x2 x3 x4 (a + 20 * Z.of_nat k))
      /\ lkeeps UKBB regs r.
  Proof.
    induction k as [|k IH]; intros regs x a HB HL R7 Hk Ha Hak; [lia|].
    destruct x as [[[[x0 x1] x2] x3] x4].
    destruct (ubbody regs x0 x1 x2 x3 x4 a (Z.of_nat (S k)) HB R7 HL Ha ltac:(lia)) as (r1 & M1 & HB1 & S7 & K1).
    destruct (Nat.eq_dec k 0) as [-> | Hk'].
    - eexists. split; [|split].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_14808 D_14808 ltac:(zcond).
        apply mst_refl.
      + cbn [mrun mstep]. replace (a + 20 * Z.of_nat 1) with (a + 20) by lia. exact HB1.
      + exact K1.
    - destruct (IH r1 (mstep BA a (x0, x1, x2, x3, x4)) (a + 20)) as (r2 & M2 & HB2 & K2).
      + cbn [mstep]. exact HB1.
      + apply mstep_rng.
      + rewrite S7. zbv.
      + lia.
      + lia.
      + lia.
      + exists r2. split; [|split].
        * eapply msteps_trans; [exact M1|].
          stepb_tk F_14808 D_14808 ltac:(zcond).
          exact M2.
        * cbn [mrun]. replace (a + 20 * Z.of_nat (S k)) with (a + 20 + 20 * Z.of_nat k) by lia. exact HB2.
        * solve_kb.
  Qed.
End CRCB.
