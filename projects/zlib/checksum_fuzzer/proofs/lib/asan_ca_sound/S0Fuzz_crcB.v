(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ FuzzCk FuzzMem S0FuzzBase S0Fuzz_code FuzzCrcLib S0Fuzz_crcA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque ctab btab crc_byte.
Section FXG. Context {fx : FPState}.

Definition KBB : list reg := [1; 2; 3; 4; 25; 26; 27; 6; 7; 10; 12; 13; 28; 29; 30]%bv.

Lemma KBB_KB : forall regs r, lkeeps KBB regs r -> lkeeps KB regs r.
Proof. intros regs r H. eapply lkeeps_incl; [|exact H]. incl_dec. Qed.

Section CRCB.
  Variables (m rom : word -> option byte) (adr0 len0 : Z).
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len0 -> exists b : byte, rdn RSEGS m (Z_to_bv 64 (adr0 + i)) 1 = Some [b].
  Hypothesis Hnw : adr0 + len0 < two64.
  Hypothesis Ha0 : 0 <= adr0.

  #[local] Abbreviation BA := (byte_at RSEGS m).
  #[local] Abbreviation WD := (Wd (byte_at RSEGS m)).

  Lemma BA_rng : forall a, 0 <= BA a < 256.
  Proof. intros. apply byte_at_range. Qed.

  Lemma WD_rng : forall a, 0 <= WD a < two32.
  Proof. intros. apply Wd_range. apply BA_rng. Qed.

  Lemma rd4 : forall a, adr0 <= a -> a + 4 <= adr0 + len0 ->
    exists bs, rdn RSEGS m (Z_to_bv 64 a) 4 = Some bs /\ bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (WD a)).
  Proof.
    intros a Ha Ha4. apply (rd4_bytes_at_v RSEGS m a (WD a)); [lia | lia | | reflexivity].
    intros i Hi. destruct (Hrd (a + i - adr0) ltac:(lia)) as [b Hb]. exists b.
    replace (adr0 + (a + i - adr0)) with (a + i) in Hb by lia. exact Hb.
  Qed.

  Ltac solve_kb := first [ assumption | apply lkeeps_refl | solve_lkeeps
                         | eapply lkeeps_trans; [eassumption|]; first [assumption | solve_lkeeps | eapply lkeeps_trans; eassumption] ].
  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_kb ].

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

  Definition BH (regs : bvmap 5 word) (x0 x1 x2 x3 x4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 x0 /\ getr regs 5 = Z_to_bv 64 x1 /\ getr regs 17 = Z_to_bv 64 x2
    /\ getr regs 16 = Z_to_bv 64 x3 /\ getr regs 15 = Z_to_bv 64 x4 /\ getr regs 11 = Z_to_bv 64 a
    /\ getr regs 7 = Z_to_bv 64 BTAB /\ getr regs 28 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 29 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 30 = Z_to_bv 64 (BTAB + 3072).

  Definition B1 (regs : bvmap 5 word) (y0 y1 y2 y3 y4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 y0 /\ getr regs 5 = Z_to_bv 64 y1 /\ getr regs 17 = Z_to_bv 64 y2
    /\ getr regs 16 = Z_to_bv 64 y3 /\ getr regs 15 = Z_to_bv 64 y4 /\ getr regs 11 = Z_to_bv 64 (a + 20)
    /\ getr regs 7 = Z_to_bv 64 BTAB /\ getr regs 28 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 29 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 30 = Z_to_bv 64 (BTAB + 3072)
    /\ getr regs 31 = Z_to_bv 64 (BTAB + Z.land y0 255 * 2 ^ 2)
    /\ getr regs 8 = Z_to_bv 64 (BTAB + Z.land y1 255 * 2 ^ 2)
    /\ getr regs 9 = Z_to_bv 64 (BTAB + Z.land y2 255 * 2 ^ 2)
    /\ getr regs 18 = Z_to_bv 64 (BTAB + Z.land y3 255 * 2 ^ 2)
    /\ getr regs 19 = Z_to_bv 64 (BTAB + Z.land y4 255 * 2 ^ 2)
    /\ getr regs 20 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y0 6) 1020)
    /\ getr regs 21 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y1 6) 1020)
    /\ getr regs 22 = Z_to_bv 64 (BTAB + 1024 + Z.land (Z.shiftr y2 6) 1020)
    /\ getr regs 23 = Z_to_bv 64 (Z.shiftr y3 6)
    /\ getr regs 24 = Z_to_bv 64 (Z.shiftr y4 6).

  Lemma bb1 : forall regs (x0 x1 x2 x3 x4 a : Z),
    BH regs x0 x1 x2 x3 x4 a -> lrng (x0, x1, x2, x3, x4) -> adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14674 : word) m rom) (mkst r (0x14708 : word) m rom)
      /\ B1 r (Z.lxor (sx32 (WD a)) x0) (Z.lxor (sx32 (WD (a + 4))) x1) (Z.lxor (sx32 (WD (a + 8))) x2)
             (Z.lxor (sx32 (WD (a + 12))) x3) (Z.lxor (sx32 (WD (a + 16))) x4) a
      /\ lkeeps KBB regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a (R14 & R5 & R17 & R16 & R15 & R11 & R7 & R28 & R29 & R30) HL Ha Ha20.
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
    - lw_pl F_14614 D_14614 Hbs0 Hv0.
      lw_pl F_14618 D_14618 Hbs1 Hv1.
      lw_pl F_1461c D_1461c Hbs2 Hv2.
      lw_pl F_14620 D_14620 Hbs3 Hv3.
      lw_pl F_14624 D_14624 Hbs4 Hv4.
      stepz F_14628 D_14628.
      stepz F_1462c D_1462c. fold y0.
      stepz F_14630 D_14630. fold y1.
      stepz F_14634 D_14634. fold y2.
      stepz F_14638 D_14638. fold y3.
      stepz F_1463c D_1463c. fold y4.
      stepz F_14640 D_14640. stepz F_14644 D_14644. stepz F_14648 D_14648. stepz F_1464c D_1464c. stepz F_14650 D_14650.
      srliR F_14654 D_14654 y0 Hy0. srliR F_14658 D_14658 y1 Hy1. srliR F_1465c D_1465c y2 Hy2.
      srliR F_14660 D_14660 y3 Hy3. srliR F_14664 D_14664 y4 Hy4.
      stepz F_14668 D_14668. stepz F_1466c D_1466c. stepz F_14670 D_14670. stepz F_14674 D_14674. stepz F_14678 D_14678.
      stepz F_1467c D_1467c. stepz F_14680 D_14680. stepz F_14684 D_14684.
      stepz F_14688 D_14688. stepz F_1468c D_1468c. stepz F_14690 D_14690. stepz F_14694 D_14694. stepz F_14698 D_14698.
      stepz F_1469c D_1469c. stepz F_146a0 D_146a0. stepz F_146a4 D_146a4.
      apply mst_refl.
    - unfold B1. post.
  Qed.

  Definition L01 (y : Z) : Z := Z.lxor (bT1 y) (bT0 y).

  Definition B2 (regs : bvmap 5 word) (y0 y1 y2 y3 y4 a : Z) : Prop :=
    getr regs 14 = Z_to_bv 64 (Z.shiftr (y0 mod two32) 24) /\ getr regs 5 = Z_to_bv 64 (Z.shiftr (y1 mod two32) 24)
    /\ getr regs 17 = Z_to_bv 64 (Z.shiftr (y2 mod two32) 24) /\ getr regs 16 = Z_to_bv 64 (Z.shiftr (y3 mod two32) 24)
    /\ getr regs 15 = Z_to_bv 64 (Z.shiftr (y4 mod two32) 24) /\ getr regs 11 = Z_to_bv 64 (a + 20)
    /\ getr regs 7 = Z_to_bv 64 BTAB /\ getr regs 28 = Z_to_bv 64 (BTAB + 1024)
    /\ getr regs 29 = Z_to_bv 64 (BTAB + 2048) /\ getr regs 30 = Z_to_bv 64 (BTAB + 3072)
    /\ getr regs 31 = Z_to_bv 64 (L01 y0) /\ getr regs 8 = Z_to_bv 64 (L01 y1) /\ getr regs 9 = Z_to_bv 64 (L01 y2)
    /\ getr regs 18 = Z_to_bv 64 (L01 y3) /\ getr regs 19 = Z_to_bv 64 (L01 y4)
    /\ getr regs 20 = Z_to_bv 64 (bT2 y0) /\ getr regs 21 = Z_to_bv 64 (bT2 y1)
    /\ getr regs 22 = Z_to_bv 64 (Z.land (Z.shiftr y2 14) 1020)
    /\ getr regs 23 = Z_to_bv 64 (Z.land (Z.shiftr y3 14) 1020)
    /\ getr regs 24 = Z_to_bv 64 (Z.land (Z.shiftr y4 14) 1020).

  Lemma bb2 : forall regs (y0 y1 y2 y3 y4 a : Z),
    B1 regs y0 y1 y2 y3 y4 a ->
    0 <= y0 < two64 -> 0 <= y1 < two64 -> 0 <= y2 < two64 -> 0 <= y3 < two64 -> 0 <= y4 < two64 ->
    exists r, msteps RSEGS (mkst regs (0x14708 : word) m rom) (mkst r (0x147a0 : word) m rom)
      /\ B2 r y0 y1 y2 y3 y4 a
      /\ lkeeps KBB regs r.
  Proof.
    intros regs y0 y1 y2 y3 y4 a HB Hy0 Hy1 Hy2 Hy3 Hy4.
    destruct HB as (R14 & R5 & R17 & R16 & R15 & R11 & R7 & R28 & R29 & R30 & R31 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24).
    eexists. split.
    - lw_btab F_146a8 D_146a8 0 (Z.land y4 255) (bT0 y4).
      lw_btab F_146ac D_146ac 1 (Z.land (Z.shiftr y0 8) 255) (bT1 y0).
      lw_btab F_146b0 D_146b0 0 (Z.land y0 255) (bT0 y0).
      lw_btab F_146b4 D_146b4 0 (Z.land y1 255) (bT0 y1).
      lw_btab F_146b8 D_146b8 0 (Z.land y2 255) (bT0 y2).
      lw_btab F_146bc D_146bc 0 (Z.land y3 255) (bT0 y3).
      lw_btab F_146c0 D_146c0 1 (Z.land (Z.shiftr y1 8) 255) (bT1 y1).
      lw_btab F_146c4 D_146c4 1 (Z.land (Z.shiftr y2 8) 255) (bT1 y2).
      stepz F_146c8 D_146c8. change (Z.lxor (bT1 y0) (bT0 y0)) with (L01 y0).
      srliR F_146cc D_146cc y0 Hy0.
      stepz F_146d0 D_146d0. change (Z.lxor (bT1 y1) (bT0 y1)) with (L01 y1).
      srliR F_146d4 D_146d4 y1 Hy1.
      stepz F_146d8 D_146d8. change (Z.lxor (bT1 y2) (bT0 y2)) with (L01 y2).
      srliR F_146dc D_146dc y2 Hy2.
      stepz F_146e0 D_146e0. stepz F_146e4 D_146e4. stepz F_146e8 D_146e8. stepz F_146ec D_146ec.
      stepz F_146f0 D_146f0. stepz F_146f4 D_146f4. stepz F_146f8 D_146f8. stepz F_146fc D_146fc.
      lw_btab F_14700 D_14700 1 (Z.land (Z.shiftr y3 8) 255) (bT1 y3).
      lw_btab F_14704 D_14704 1 (Z.land (Z.shiftr y4 8) 255) (bT1 y4).
      lw_btab F_14708 D_14708 2 (Z.land (Z.shiftr y0 16) 255) (bT2 y0).
      lw_btab F_1470c D_1470c 2 (Z.land (Z.shiftr y1 16) 255) (bT2 y1).
      stepz F_14710 D_14710. change (Z.lxor (bT1 y3) (bT0 y3)) with (L01 y3).
      srliR F_14714 D_14714 y3 Hy3.
      stepz F_14718 D_14718. change (Z.lxor (bT1 y4) (bT0 y4)) with (L01 y4).
      srliR F_1471c D_1471c y4 Hy4.
      stepz F_14720 D_14720. stepz F_14724 D_14724. stepz F_14728 D_14728. stepz F_1472c D_1472c. stepz F_14730 D_14730.
      stepz F_14734 D_14734. stepz F_14738 D_14738. stepz F_1473c D_1473c.
      apply mst_refl.
    - unfold B2. post.
  Qed.

  Lemma bb3 : forall regs (y0 y1 y2 y3 y4 a : Z),
    B2 regs y0 y1 y2 y3 y4 a ->
    exists r, msteps RSEGS (mkst regs (0x147a0 : word) m rom) (mkst r (0x1481c : word) m rom)
      /\ BH r (mlaneY y0) (mlaneY y1) (mlaneY y2) (mlaneY y3) (mlaneY y4) (a + 20)
      /\ lkeeps KBB regs r.
  Proof.
    intros regs y0 y1 y2 y3 y4 a HB.
    destruct HB as (R14 & R5 & R17 & R16 & R15 & R11 & R7 & R28 & R29 & R30 & R31 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24).
    eexists. split.
    - stepz F_14740 D_14740. stepz F_14744 D_14744. stepz F_14748 D_14748. stepz F_1474c D_1474c. stepz F_14750 D_14750.
      stepz F_14754 D_14754. stepz F_14758 D_14758. stepz F_1475c D_1475c.
      stepz F_14760 D_14760. stepz F_14764 D_14764. stepz F_14768 D_14768. stepz F_1476c D_1476c. stepz F_14770 D_14770.
      lw_btab F_14774 D_14774 2 (Z.land (Z.shiftr y2 16) 255) (bT2 y2).
      lw_btab F_14778 D_14778 2 (Z.land (Z.shiftr y3 16) 255) (bT2 y3).
      lw_btab F_1477c D_1477c 2 (Z.land (Z.shiftr y4 16) 255) (bT2 y4).
      lw_btab F_14780 D_14780 3 (Z.shiftr (y0 mod two32) 24) (bT3 y0).
      lw_btab F_14784 D_14784 3 (Z.shiftr (y1 mod two32) 24) (bT3 y1).
      lw_btab F_14788 D_14788 3 (Z.shiftr (y2 mod two32) 24) (bT3 y2).
      lw_btab F_1478c D_1478c 3 (Z.shiftr (y3 mod two32) 24) (bT3 y3).
      lw_btab F_14790 D_14790 3 (Z.shiftr (y4 mod two32) 24) (bT3 y4).
      stepz F_14794 D_14794. stepz F_14798 D_14798. stepz F_1479c D_1479c. stepz F_147a0 D_147a0. stepz F_147a4 D_147a4.
      stepz F_147a8 D_147a8. change (Z.lxor (Z.lxor (bT3 y0) (bT2 y0)) (L01 y0)) with (mlaneY y0).
      stepz F_147ac D_147ac. change (Z.lxor (Z.lxor (bT3 y1) (bT2 y1)) (L01 y1)) with (mlaneY y1).
      stepz F_147b0 D_147b0. change (Z.lxor (Z.lxor (bT3 y2) (bT2 y2)) (L01 y2)) with (mlaneY y2).
      stepz F_147b4 D_147b4. change (Z.lxor (Z.lxor (bT3 y3) (bT2 y3)) (L01 y3)) with (mlaneY y3).
      stepz F_147b8 D_147b8. change (Z.lxor (Z.lxor (bT3 y4) (bT2 y4)) (L01 y4)) with (mlaneY y4).
      apply mst_refl.
    - unfold BH. post.
  Qed.

  Lemma bbody : forall regs (x0 x1 x2 x3 x4 a : Z),
    BH regs x0 x1 x2 x3 x4 a -> lrng (x0, x1, x2, x3, x4) -> adr0 <= a -> a + 20 <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14674 : word) m rom) (mkst r (0x1481c : word) m rom)
      /\ BH r (mlane x0 (WD a)) (mlane x1 (WD (a + 4))) (mlane x2 (WD (a + 8))) (mlane x3 (WD (a + 12))) (mlane x4 (WD (a + 16))) (a + 20)
      /\ lkeeps KBB regs r.
  Proof.
    intros regs x0 x1 x2 x3 x4 a HB HL Ha Ha20.
    pose proof HL as HL'. cbn [lrng] in HL'. destruct HL' as (Hx0 & Hx1 & Hx2 & Hx3 & Hx4).
    destruct (bb1 regs x0 x1 x2 x3 x4 a HB HL Ha Ha20) as (r1 & M1 & HB1 & K1).
    destruct (bb2 r1 _ _ _ _ _ a HB1
                (lxor_range64 _ _ (sx32_range _ (WD_rng a)) Hx0)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 4))) Hx1)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 8))) Hx2)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 12))) Hx3)
                (lxor_range64 _ _ (sx32_range _ (WD_rng (a + 16))) Hx4)) as (r2 & M2 & HB2 & K2).
    destruct (bb3 r2 _ _ _ _ _ a HB2) as (r3 & M3 & HB3 & K3).
    exists r3. split; [|split].
    - eapply msteps_trans; [exact M1|]. eapply msteps_trans; [exact M2 | exact M3].
    - rewrite !mlane_Y. exact HB3.
    - eapply lkeeps_trans; [exact K1|]. eapply lkeeps_trans; [exact K2 | exact K3].
  Qed.

  Lemma bloop : forall (k : nat) regs (x : lanes) (a : Z),
    (let '(x0, x1, x2, x3, x4) := x in BH regs x0 x1 x2 x3 x4 a) -> lrng x ->
    getr regs 6 = Z_to_bv 64 (a + 20 * Z.of_nat k) -> (1 <= k)%nat ->
    adr0 <= a -> a + 20 * Z.of_nat k <= adr0 + len0 ->
    exists r, msteps RSEGS (mkst regs (0x14674 : word) m rom) (mkst r (0x14820 : word) m rom)
      /\ (let '(x0, x1, x2, x3, x4) := mrun BA k a x in BH r x0 x1 x2 x3 x4 (a + 20 * Z.of_nat k))
      /\ lkeeps KBB regs r.
  Proof.
    induction k as [|k IH]; intros regs x a HB HL R6 Hk Ha Hak; [lia|].
    destruct x as [[[[x0 x1] x2] x3] x4].
    destruct (bbody regs x0 x1 x2 x3 x4 a HB HL Ha ltac:(lia)) as (r1 & M1 & HB1 & K1).
    assert (S6 : getr r1 6 = Z_to_bv 64 (a + 20 * Z.of_nat (S k))) by (rewrite (K1 6%bv) by (cbv; (first [solve [liafast_keep_section; tauto] | tauto])); exact R6).
    pose proof HB1 as HB1'. destruct HB1' as (S14 & S5 & S17 & S16 & S15 & S11 & _).
    destruct (Nat.eq_dec k 0) as [-> | Hk'].
    - eexists. split; [|split].
      + eapply msteps_trans; [exact M1|].
        stepb_ft F_147bc D_147bc ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_eq; lia).
        apply mst_refl.
      + cbn [mrun mstep]. replace (a + 20 * Z.of_nat 1) with (a + 20) by lia. exact HB1.
      + exact K1.
    - destruct (IH r1 (mstep BA a (x0, x1, x2, x3, x4)) (a + 20)) as (r2 & M2 & HB2 & K2).
      + cbn [mstep]. exact HB1.
      + apply mstep_rng.
      + rewrite S6. zbv.
      + lia.
      + lia.
      + lia.
      + exists r2. split; [|split].
        * eapply msteps_trans; [exact M1|].
          stepb_tk F_147bc D_147bc ltac:(rwR; rewrite zc_eq by lia; apply Z.eqb_neq; lia).
          exact M2.
        * cbn [mrun]. replace (a + 20 * Z.of_nat (S k)) with (a + 20 + 20 * Z.of_nat k) by lia. exact HB2.
        * eapply lkeeps_trans; [exact K1 | exact K2].
  Qed.
End CRCB.
End FXG.
