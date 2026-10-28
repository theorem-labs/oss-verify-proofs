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
     RZ_hft_fdec_l1 RZ_hft_fdec_t1 RZ_fse_decnf_kit fse_kit_dsym fse_kit_reload huf41_kit_reload.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section INI.
  Hypothesis BINIT : bit_init_stmt_at 0x2bd40.
  Hypothesis INITDS : fse_initds_stmt.
  Hypothesis RELOAD : fse_reload_stmt.
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
  Hypothesis DSYM : fse_dsym_stmt.
  Hypothesis DSYMF : fse_dsymf_stmt.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDm := (FDU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).
  Ltac sec_hyps := first [exact HY | exact LOSU | exact SPA | exact DTA | exact TBL | exact SRCLEN | exact LOS2 | exact OFFWK | exact WKR0
                         | exact DSYM | exact DSYMF].

  (* [comment removed for export] *)
  Lemma fd_epi0 : forall m1 out f0 f2 f1 fb r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr usegs m1 DST out -> Z.of_nat (length out) = cap -> stk usegs m1 WK (WK + wksz) -> stk usegs m1 lo (SPV + -192) ->
    rw_cells usegs m1 (SPV + -192) f0 -> cells_size f0 = 16%nat -> rw_cells usegs m1 (SPV + -176) f2 -> cells_size f2 = 16%nat ->
    rw_cells usegs m1 (SPV + -160) f1 -> cells_size f1 = 16%nat -> rw_cells usegs m1 (SPV + -144) fb -> cells_size fb = 40%nat ->
    rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mem_inv usegs m1 -> munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 -> wmono usegs m m1 ->
    0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evt usegs POST (STF 0x2b964 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros OUT OLEN WKS STK F0 SZ0 FS2 SZ2 FS1 SZ1 FBD SZB FSAV MI MU WM RR RES. clear HY TBL SRCLEN DTA.
    do 14 zstep.
    apply stk_of_rw_cells in F0, FS2, FS1, FBD, FSAV. rewrite SZ0 in F0. rewrite SZ2 in FS2. rewrite SZ1 in FS1. rewrite SZB in FBD.
    cbn [cells_size csize Nat.add] in FSAV.
    assert (STK' : stk usegs m1 lo SPV).
    { apply (stk_merge usegs m1 lo (SPV + -192) SPV STK); [|lia].
      apply (stk_merge usegs m1 (SPV + -192) (SPV + -176) SPV); [replace (SPV + -176) with (SPV + -192 + Z.of_nat 16) by lia; exact F0| |lia].
      apply (stk_merge usegs m1 (SPV + -176) (SPV + -160) SPV); [replace (SPV + -160) with (SPV + -176 + Z.of_nat 16) by lia; exact FS2| |lia].
      apply (stk_merge usegs m1 (SPV + -160) (SPV + -144) SPV); [replace (SPV + -144) with (SPV + -160 + Z.of_nat 16) by lia; exact FS1| |lia].
      apply (stk_merge usegs m1 (SPV + -144) (SPV + -104) SPV); [replace (SPV + -104) with (SPV + -144 + Z.of_nat 40) by lia; exact FBD| |lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact FSAV. }
    assert (DSTS : stk usegs m1 DST (DST + cap)).
    { apply rw_cells_of_u8arr in OUT. apply stk_of_rw_cells in OUT. cbn [cells_size csize] in OUT.
      replace (DST + cap) with (DST + Z.of_nat (length out + 0)) by lia. exact OUT. }
    zstep. apply evt_done. unfold fse_dec_post.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact DSTS|]. split; [exact WKS|]. split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Definition FDI (out : list byte) (m1 : fmem) : Prop :=
    u8arr usegs m1 DST out /\ Z.of_nat (length out) = cap
    /\ stk usegs m1 WK (WK + wksz)
    /\ bytes_at usegs m1 SRCI srci
    /\ bytes_at usegs m1 DT (le2 (Z_to_bv 64 tl))
    /\ bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb)
    /\ stk usegs m1 lo (SPV + -192)
    /\ (exists j0 msv tlw, rw_cells usegs m1 (SPV + -192) [CB 8 j0; C4 msv; C4 tlw])
    /\ (exists j2, rw_cells usegs m1 (SPV + -176) [CB 16 j2])
    /\ (exists j1, rw_cells usegs m1 (SPV + -160) [CB 16 j1])
    /\ (exists jb, rw_cells usegs m1 (SPV + -144) [CB 40 jb])
    /\ rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ mem_inv usegs m1 /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 /\ wmono usegs m m1.

  (* [comment removed for export] *)
  Lemma fd1_loop0 : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x17 x21 x23 x24 x25 x26 x27 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2afc0 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4))
           (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SRCI) (Z_to_bv 64 ptr) x17 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) x21
           (Z_to_bv 64 (DST + cap + -3)) x23 x24 x25 x26 x27 (Z_to_bv 64 bc) x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV. open_fh HY. pose proof I as I0. open_fdcu I0.
    do 7 zn.
    eapply fd1_start; try sec_hyps; [exact I | exact S1 | exact S2 | exact BCR | exact PV |].
    intros. eapply fd1_tprep; try sec_hyps; eassumption.
  Qed.

  (* [comment removed for export] *)
  Definition FDC (out : list byte) (st1 st2 : Z) (cont : word) (bc : Z) (pad : list byte) (ptr : Z) (m1 : fmem) : Prop :=
    u8arr usegs m1 DST out /\ Z.of_nat (length out) = cap
    /\ stk usegs m1 WK (WK + wksz)
    /\ bytes_at usegs m1 SRCI srci
    /\ bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb)
    /\ stk usegs m1 lo (SPV + -192)
    /\ (exists j0 msv tlw, rw_cells usegs m1 (SPV + -192) [CB 8 j0; C4 msv; C4 tlw])
    /\ rw_cells usegs m1 (SPV + -176) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells usegs m1 (SPV + -160) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))]
    /\ rw_cells usegs m1 (SPV + -144) (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRCI)
    /\ rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ mem_inv usegs m1 /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 /\ wmono usegs m m1.
  Ltac open_fdc I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & FS2 & FS1 & FBD & FSAV & MI & MU & WM);
                     unfold bitd_cells in FBD.
  Ltac close_fdc := unfold FDC, bitd_cells; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                    split; [eassumption|]; split; [eassumption|]; split; [do 3 eexists; eassumption|]; split; [eassumption|];
                    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

  (* [comment removed for export] *)
  Lemma fd_nf_25970 : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x11 x12 x13 x14 x15 x21 x23 x24 x25 x26 x27 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2afa0 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8)) x11 x12 x13 x14 x15 (Z_to_bv 64 ptr)
           (Z_to_bv 64 SRCI) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) x21 (Z_to_bv 64 (DST + cap + -3))
           x23 x24 x25 x26 x27 (Z_to_bv 64 bc) x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV. open_fh HY. pose proof I as I0. open_fdc I0.
    do 7 zn. zc.
    eapply fd1_loop0; eassumption.
  Qed.

  Lemma fd_nf_ld : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x11 x12 x13 x14 x15 x21 x23 x24 x25 x26 x27 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    SRCI <= ptr -> ptr + 8 <= SRCI + ni -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2af0c m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8)) x11 x12 x13 x14 x15 (Z_to_bv 64 ptr)
           (Z_to_bv 64 SRCI) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) x21 (Z_to_bv 64 (DST + cap + -3))
           x23 x24 x25 x26 x27 (Z_to_bv 64 bc) x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PLO PHI PV. open_fh HY. pose proof I as I0. open_fdc I0.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
    zstep. zstep.
    eapply fd_nf_25970; [close_fdc | exact S1 | exact S2 | exact BCR | exact PV].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_nf_first : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr ->
    evt usegs POST
      (STF 0x2ae78 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + cap)) x19 x20 x21
           (Z_to_bv 64 (DST + cap + -3)) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 (BCR & BOK). open_fh HY. pose proof I as I0. open_fdc I0.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. try rewrite (sx32w_small bc) by lia. try rewrite (zx32w_small bc) by lia. zn.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zn. zn.
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; reflexivity).
      eapply fd_epi; try sec_hyps; [close_fdu | lia | left; reflexivity].
    - specialize (BOK ltac:(lia)).
      do 8 zn.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        zn. zstep.
        remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB in CELB.
        assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
        eapply evt_cut.
        { eapply (RELOAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -144) SRCI ni bc ptr cont pad srci); try eassumption; try lia. }
        unfold huf_reload_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end. unfold bitd_cells in *.
        zstep. try rewrite (sx32w_small (bc mod 8)) by lia. try rewrite (zx32w_small (bc mod 8)) by lia. zn. zn. zn.
        subst tbb. eapply fd_nf_25970; [close_fdc | exact S1 | exact S2 | lia | right; lia].
      + zn. zstep. if_cases K3; zify_cond K3.
        * (* [comment removed for export] *)
          assert (EP : ptr = SRCI) by lia. subst ptr.
          do 6 zn.
          eapply fd1_loop0; [exact I | exact S1 | exact S2 | lia | left; reflexivity].
        * (* [comment removed for export] *)
          zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
          assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR K; Z.div_mod_to_equations; lia).
          remember (bc / 8) as q eqn:EQ. clear EQ.
          zc. zn. zn. zn. zn. zc. zn. zstep. if_cases K4; zify_cond K4.
          -- zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc.
             eapply fd_nf_ld; [close_fdc | exact S1 | exact S2 | lia | lia | lia | right; lia].
          -- (* [comment removed for export] *)
             assert (DR : 1 <= ptr - SRCI <= 7 /\ 8 <= ni) by (clear - BOK K2 K3 K4 QR; lia).
             zn. zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc.
             eapply fd_nf_ld; [close_fdc | exact S1 | exact S2 | lia | lia | lia | left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_nf_init : forall m1 out x1 x5 x6 x7 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDI out m1 ->
    evt usegs POST
      (STF 0x2ae28 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 DT) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 ni) x13 x14 x15 x16 x17
           (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 SRCI) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I. open_fh HY.
    destruct I as (OUT & OLEN & WKS & SRCB & HDRB & CELB & STK & (fj0 & fmsv & ftlw & F0) & (j2 & FS2) & (j1 & FS1) & (jb & FBD) & FSAV & MI & MU & WM).
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB.
    assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
    zc. zn. zc. zn. zn. zn. zc. zn. zn. zstep.
    eapply evt_cut.
    { eapply (BINIT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -144) SRCI ni srci jb); try eassumption; try lia. }
    unfold bit_init_post. post_call usegs m1.
    lazymatch type of POST with (?r0 = _ /\ _) \/ _ => rename r0 into r end.
    zn. zstep.
    destruct POST as [(RN & N1 & cont & bc & pad & BC1 & BC8 & FBD) | (RERR & RLT & bs & FBD)].
    2:{ (* [comment removed for export] *)
        if_cases KE; zify_cond KE; [|exfalso; unfold zd_is_error, ZE_maxCode in RERR; apply Z.ltb_lt in RERR; lia].
        eapply (fd_epi0 _ out _ _ _ _ r); try eassumption; try reflexivity.
        - pose proof RERR as RE2. unfold zd_is_error, ZE_maxCode in RE2. apply Z.ltb_lt in RE2. lia.
        - left; exact RERR. }
    subst r. if_cases KE; zify_cond KE; [exfalso; lia|].
    zn. zn. zn. zstep.
    assert (BOK0 : fbit_ok SRCI ni bc (bitd_ptr SRCI ni)).
    { unfold fbit_ok, bitd_ptr. split; [lia|]. intros _. destruct (Z.leb_spec 8 ni); [right; lia | left; reflexivity]. }
    eapply evt_cut.
    { eapply (INITDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -160) (SPV + -144) SRCI ni DT tl fast bc (bitd_ptr SRCI ni) cont pad srci j1);
        try eassumption; try lia. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    zn. zn. zn. zstep.
    eapply evt_cut.
    { eapply (INITDS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -176) (SPV + -144) SRCI ni DT tl fast _ _ _ pad srci j2);
        try eassumption; try lia. }
    unfold fse_initds_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    subst tbb.
    eapply fd_nf_first; [close_fdc | eassumption | eassumption | eassumption].
  Qed.
End INI.
