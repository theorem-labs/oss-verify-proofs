(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi
     RZ_hft_fdec_l1 RZ_hft_fdec_t1 RZ_hft_fdec_l3 RZ_hft_fdec_t2 RZ_hft_fdec_ini RZ_hft_fdec_bi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section INIF.
  Hypothesis INITDS : fse_initds_stmt.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Hypothesis LOS2 : lo <= SPV - 384.
  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis WKR0 : 0 <= wksz.
  Hypothesis FAST1 : fast = 1.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FDm := (FD s0 s1 s2 s3 s4 s5 s6 s7 ra m SPV lo DST cap WK wksz SRCI DT srci tb).

  Notation FDIm := (FDI ra s0 s1 s2 s3 s4 s5 s6 s7 m SPV lo DST cap WK wksz SRCI DT tl srci tb).
  Notation FDCm := (FDC ra s0 s1 s2 s3 s4 s5 s6 s7 m SPV lo DST cap WK wksz SRCI DT srci tb).
  Ltac open_fdc I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & FS2 & FS1 & FBD & FSAV & MI & MU & WM);
                     unfold bitd_cells in FBD.

  (* [comment removed for export] *)
  Lemma fd3_loop0 : forall m1 out x1 st1 st2 x8 x9 ptr bc cont x18 x22 x23 x29 x30 x31,
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt psegs POST
      (STF 0x25ea0 m1 x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 DST) x8 x9 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 ptr) (Z_to_bv 64 SRCI)
           (Z_to_bv 64 bc) (Z_to_bv 64 FSE_ZEROFILLED) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) cont
           x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23
           (Z_to_bv 64 64) x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV. open_fh HY.
    pose proof (fd3_loop ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz SRCI ni DT tl fast srci tb HY TBL SRCLEN FAST1
                  (Z.to_nat cap) m1 out x1 st1 st2 0 x8 x9 ptr bc cont x18 x22 x23 x29 x30 x31) as L.
    replace (DST + 0) with DST in L by lia.
    apply L; [lia | exact I | exact S1 | exact S2 | exact BCR | exact PV | lia |].
    intros. eapply (fd2_tprep ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz SRCI ni DT tl fast srci tb HY TBL SRCLEN FAST1); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_25dd0 : forall m1 out x1 st1 st2 x8 x9 ptr bc cont x18 x22 x23 x28 x29 x30 x31,
    FDm out m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt psegs POST
      (STF 0x25e9c m1 x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 DST) x8 x9 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 ptr) (Z_to_bv 64 SRCI)
           (Z_to_bv 64 bc) (Z_to_bv 64 FSE_ZEROFILLED) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) cont
           x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23
           x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV.
    zstep.
    eapply fd3_loop0; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_first : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr ->
    evt psegs POST
      (STF 0x25874 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
           x18 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 (BCR & BOK). open_fh HY. open_fdc I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. rewrite (zx32w_small bc) by lia.
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep.
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply (fd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz SRCI ni DT tl srci tb HY _ out 18446744073709551596);
        [close_fd | lia | left; reflexivity].
    - specialize (BOK ltac:(lia)).
      zstep. zstep. zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep. replace (bc ≫ 3) with (bc / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
        assert (QR : 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (clear - BCR K; Z.div_mod_to_equations; lia).
        remember (bc / 8) as q eqn:EQ.
        zstep.
        lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
        do 5 zstep. zstep. replace (Z.land bc 7) with (bc mod 8) by (symmetry; apply land_7).
        do 5 zstep.
        forget_reg 17.
        zstep. zstep. zstep. zstep. zstep. zstep.
        eapply (fd_f_25dd0 _ out _ st1 st2 _ _ (ptr - q) (bc mod 8)); [close_fd | exact S1 | exact S2 | lia | right; lia].
      + zstep. zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          assert (EP : ptr = SRCI) by lia. subst ptr.
          zstep. zstep. zstep. zstep. zstep. zstep.
          eapply (fd_f_25dd0 _ out _ st1 st2 _ _ SRCI bc); [close_fd | exact S1 | exact S2 | lia | left; lia].
        * (* [comment removed for export] *)
          zstep. replace (bc ≫ 3) with (bc / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
          assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR K; Z.div_mod_to_equations; lia).
          remember (bc / 8) as q eqn:EQ. clear EQ.
          zstep. zstep. if_cases K4; zify_cond K4.
          -- zstep. zstep. replace (q ≪ 3) with (8 * q) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
             zstep.
             rewrite (Z.mod_small q 4294967296) by lia. zstep.
             lbyte SRCB. lbyte SRCB. zstep. rewrite (swrap32_small (bc - 8 * q)) by lia.
             lbyte SRCB. lbyte SRCB. zstep. zstep. lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB.
             do 8 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
             forget_reg 17.
             zstep. zstep. zstep. if_cases K5; zify_cond K5; [|exfalso; lia].
             eapply (fd_f_25dd0 _ out _ st1 st2 _ _ (ptr - q) (bc - 8 * q)); [close_fd | exact S1 | exact S2 | lia | right; lia].
          -- (* [comment removed for export] *)
             zstep.
             assert (DR : 1 <= ptr - SRCI <= 7 /\ 8 <= ni) by (clear - BOK K2 K3 K4 QR; lia).
             zstep. zstep. replace ((ptr - SRCI) ≪ 3) with (8 * (ptr - SRCI)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
             zstep.
             rewrite (Z.mod_small (ptr - SRCI) 4294967296) by lia. zstep.
             replace (ptr - (ptr - SRCI)) with SRCI by lia.
             lbyte SRCB. lbyte SRCB. zstep. rewrite (swrap32_small (bc - 8 * (ptr - SRCI))) by lia.
             lbyte SRCB. lbyte SRCB. zstep. zstep. lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB.
             do 8 zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
             forget_reg 17.
             zstep. zstep. zstep. if_cases K5; zify_cond K5; [|exfalso; lia].
             eapply (fd_f_25dd0 _ out _ st1 st2 _ _ SRCI (bc - 8 * (ptr - SRCI))); [close_fd | exact S1 | exact S2 | lia | left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_init : forall m1 out SRC hn x1 x5 x6 x7 x10 x12 x13 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    FDIm out m1 -> SRCI = SRC + hn -> 4096 <= SRC -> 0 <= hn ->
    evt psegs POST
      (STF 0x254fc m1 x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (ni + hn)) x10 (Z_to_bv 64 (SRC + hn)) x12 x13 (Z_to_bv 64 ni) x15 x16 x17
           (Z_to_bv 64 SRC) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap + -3)) x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I ESRC SRC4K HN0. open_fh HY.
    destruct I as (OUT & OLEN & WKS & SRCB & HDRB & CELB & STK & (fj0 & fmsv & ftlw & F0) & (j2 & FS2) & (j1 & FS1) & (jb & FBD) & FSAV & MI & MU & WM).
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB.
    assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
    eapply evt_cut.
    { eapply (fd_f_bitinit gp tp s8 s9 s10 s11 F fc SPV SRC hn ni srci jb m1); try eassumption; try lia.
      subst SRCI. exact SRCB. }
    intros ms' [PO|PO]; revert ms' PO; post_call psegs m1.
    2:{ (* [comment removed for export] *)
        eapply (fd_epi0 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m SPV lo DST cap WK wksz srci LOS2 _ out _ _ _ _ x14);
          try eassumption; try reflexivity; [lia | left; assumption]. }
    rename x18 into cont. rename x19 into bc. rename x20 into pad. rename PC into FBD. rename PC0 into BC1. rename POST into N1.
    rewrite <- ESRC in FBD.
    zstep. zstep. zstep. zstep.
    assert (BOK0 : fbit_ok SRCI ni bc (bitd_ptr SRCI ni)).
    { unfold fbit_ok, bitd_ptr. split; [lia|]. intros _. destruct (Z.leb_spec 8 ni); [right; lia | left; reflexivity]. }
    eapply evt_cut.
    { eapply (INITDS _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s8 s9 s10 s11 _ _ _ _ F fc _ (SPV + -128) (SPV + -112) SRCI ni DT tl fast bc (bitd_ptr SRCI ni) cont pad srci j1);
        try eassumption; try lia. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv psegs ?mm |- _ => post_call psegs mm end.
    rename x40 into st1. rename x41 into cont1. rename x42 into bc1. rename x43 into ptr1.
    rename PC into FS1. rename PC0 into S1. rename PC1 into FBD. rename PC2 into BOK1. rename POST into BC1'.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s8 s9 s10 s11 _ _ _ _ F fc _ (SPV + -144) (SPV + -112) SRCI ni DT tl fast bc1 ptr1 cont1 pad srci j2);
        try eassumption; try lia. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv psegs ?mm |- _ => post_call psegs mm end.
    subst tbb.
    eapply (fd_f_first _ out st1 x55 x56 x57 pad x58); [| exact S1 | exact PC0 | exact PC2].
    unfold FDC. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [do 3 eexists; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; eassumption.
  Qed.
End INIF.
