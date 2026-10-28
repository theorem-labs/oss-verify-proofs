(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi
     RZ_hft_fdec_l1 RZ_hft_fdec_t1 RZ_hft_fdec_l3 RZ_hft_fdec_t2 RZ_hft_fdec_ini RZ_hft_fdec_bi RZ_fse_decnf_kit RZ_fse_decf_kit fse_kit_dsym fse_kit_reload huf41_kit_reload.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section INIF.
  Hypothesis BINIT : bit_init_stmt_at PFSE_BITINIT.
  Hypothesis INITDS : fse_initds_stmt.
  Hypothesis RELOAD : fse_reload_stmt.
  Hypothesis DSYM : fse_dsym_stmt.
  Hypothesis DSYMF : fse_dsymf_stmt.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis LOSU : lo <= SPV - 192.
  Hypothesis SPA : SPV mod 16 = 0.
  Hypothesis DTA : DT mod 2 = 0.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Hypothesis LOS2 : lo <= SPV - 448.
  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis WKR0 : 0 <= wksz.
  Hypothesis FAST1 : fast = 1.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).
  Notation FDIm := (FDI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DST cap WK wksz SRCI DT tl srci tb).
  Ltac dsp := first [ eassumption | lia | (unfold l3_KT; intros; eapply fd2_tprep; eassumption) | close_fdcu ].

  (* [comment removed for export] *)
  Lemma fd3_loop0 : forall m1 out x1 st1 st2 bc ptr cont pad x21 x22 x23 x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2b680 m1 x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 DST)
         (Z_to_bv 64 64) (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
         (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + cap + -3)) x21 x22 x23 x24 x25 x26 x27
         cont (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4))).
  Proof.
    intros until x27; intros I S1 S2 BCR PV.
    eapply fd3_loop0u; dsp.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_25dd0 : forall m1 out x1 st1 st2 bc ptr cont pad x5 x6 x9 x10 x13 x14 x15 x16 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2b640 m1 x1 x5 x6 (Z_to_bv 64 bc) (Z_to_bv 64 DST) x9 x10 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) x13 x14 x15 x16
         (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + cap)) x19 (Z_to_bv 64 (DST + cap + -3)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV. open_fh HY. pose proof I as I0. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia |].
    zstep. zstep. zstep. zstep. zstep.
    zb_goal.
    eapply fd3_loop0; [exact I0 | exact S1 | exact S2 | exact BCR | exact PV].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_first : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr ->
    evt usegs POST
      (STF 0x2ad48 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17
         (Z_to_bv 64 (DST + cap)) x19 (Z_to_bv 64 (DST + cap + -3)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 (BCR & BOK). open_fh HY. pose proof I as I0. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. first [rewrite sx32w_small by lia | idtac].
    zstep. zstep. if_cases K; zify_cond K.
    - specialize (BOK ltac:(lia)).
      zstep. zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zstep. zstep.
        remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB.
        assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
        eapply evt_cut.
        { eapply (RELOAD _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -144) SRCI ni bc ptr cont pad srci);
            first [eassumption | lia | (unfold bitd_cells; eassumption)]. }
        unfold huf_reload_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
        lazymatch goal with H : rw_cells _ _ (SPV + -144) (bitd_cells _ _ _ _ _) |- _ => unfold bitd_cells in H end.
        subst tbb.
        zstep. first [rewrite sx32w_small by lia | idtac].
        zstep. zstep. zstep. zstep.
        eapply fd_f_25dd0; dsp.
      + zstep. zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          subst ptr. zstep. zstep.
          eapply fd_f_25dd0; [exact I0 | exact S1 | exact S2 | lia | left; reflexivity].
        * (* [comment removed for export] *)
          zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
          assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR K; Z.div_mod_to_equations; lia).
          remember (bc / 8) as q eqn:EQ. clear EQ.
          zstep. zchk.
          zstep. zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. if_cases K4; zify_cond K4.
          -- zstep. zstep. rnorm.
             zstep. zchk.
             zstep. zstep. zstep.
             zstep. zchk.
             zstep. rnorm.
             zstep. rnorm.
             zstep. rewrite swrap32_small by lia.
             zstep. zstep.
             zstep. zchk.
             lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
             zstep. zstep.
             eapply fd_f_25dd0; dsp.
          -- (* [comment removed for export] *)
             zstep. rnorm.
             zstep. zstep. rnorm.
             zstep. zchk.
             zstep. zstep. zstep.
             zstep. zchk.
             zstep. rnorm.
             zstep. rnorm.
             zstep. rewrite swrap32_small by lia.
             zstep. zstep.
             zstep. zchk.
             lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
             zstep. zstep.
             eapply fd_f_25dd0; dsp.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      apply fdcu_fdu in I0.
      eapply fd_epi; try eassumption; first [lia | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_f_init : forall m1 out x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDIm out m1 ->
    evt usegs POST
      (STF 0x2acec m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ni) x13 x14 x15 x16 x17
         (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 SRCI) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I. open_fh HY.
    destruct I as (OUT & OLEN & WKS & SRCB & HDRB & CELB & STK & (fj0 & fmsv & ftlw & F0) & (j2 & FS2) & (j1 & FS1) & (jb & FBD) & FSAV & MI & MU & WM).
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB.
    assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
    eapply evt_cut.
    { eapply (fd_f_bitinit BINIT gp tp (Z_to_bv 64 DST) (Z_to_bv 64 DT) x21 x22 x23 x24 x25 x26 x27 F fc SPV (DST + cap) SRCI ni srci jb m1);
        try eassumption; lia. }
    intros ms' [PO|PO]; revert ms' PO; post_call usegs m1.
    2:{ (* [comment removed for export] *)
        eapply fd_epi0; try eassumption; try reflexivity; first [lia | left; eassumption]. }
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -160) (SPV + -144) SRCI ni DT tl fast);
        first [ eassumption | lia
              | (unfold fbit_ok, bitd_ptr; split; [lia | intros _; destruct (Z.leb_spec 8 ni); [right; lia | left; reflexivity]]) ]. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    zstep. zstep. zstep. zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -176) (SPV + -144) SRCI ni DT tl fast);
        first [ eassumption | lia ]. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    subst tbb. eapply fd_f_first; dsp.
  Qed.
End INIF.
