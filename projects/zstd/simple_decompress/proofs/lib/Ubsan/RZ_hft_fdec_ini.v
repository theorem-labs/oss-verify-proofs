(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi
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
  Notation STF ip mem w1 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 :=
    (MS (mkR w1 (Z_to_bv 64 (SPV + -192)) gp tp w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31)
        F (Z_to_bv 64 ip) fc None mem (seg_rom usegs)).
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
  Proof using LOSU.
    clear DTA SRCLEN.
    intros * out_arr out_len wk_stk lo_stk c0 c0_sz c2 c2_sz c1 c1_sz cb cb_sz saved mi mu wm r_rng r_ok.
    assert (dst_stk : stk usegs m1 DST (DST + cap)).
    { pose proof (stk_of_rw_cells _ _ _ _ (rw_cells_of_u8arr _ _ _ _ out_arr)) as raw.
      cbn [cells_size csize] in raw. rewrite Nat.add_0_r, out_len in raw. exact raw. }
    assert (grow : forall A B cs, stk usegs m1 lo A -> rw_cells usegs m1 A cs ->
                     B = A + Z.of_nat (cells_size cs) -> lo <= A -> stk usegs m1 lo B).
    { intros A B cs below here B_at lo_le. subst B. exact (stk_release _ _ _ _ _ below here lo_le). }
    assert (frame_free : stk usegs m1 lo SPV).
    { refine (grow (SPV + -104) _ _ (grow (SPV + -144) _ _ (grow (SPV + -160) _ _
                (grow (SPV + -176) _ _ (grow (SPV + -192) _ _ lo_stk c0 _ _) c2 _ _) c1 _ _) cb _ _) saved _ _);
        rewrite ?c0_sz, ?c2_sz, ?c1_sz, ?cb_sz; cbn [cells_size csize Nat.add]; lia. }
    clear grow.
    zn. zn. zn. zn. zn. zn. zn. zn. zn. zn. zn. zn. zn. zn. zstep.
    apply evt_done. unfold fse_dec_post.
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1, r.
    split; [reflexivity |].
    split; [exact mu |]. split; [exact wm |]. split; [exact mi |].
    split; [exact frame_free |]. split; [exact dst_stk |]. split; [exact wk_stk |].
    split; [exact r_rng | exact r_ok].
  Qed.

  (* [comment removed for export] *)
  Definition FDI (out : list byte) (m1 : fmem) : Prop :=
    u8arr usegs m1 DST out /\ zlen out = cap /\ stk usegs m1 WK (WK + wksz) /\
    bytes_at usegs m1 SRCI srci /\ bytes_at usegs m1 DT (le2 (Z_to_bv 64 tl)) /\
    bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb) /\ stk usegs m1 lo (SPV + -192) /\
    (exists (hole : list byte) (msv tlw : word), rw_cells usegs m1 (SPV + -192) [CB 8 hole; C4 msv; C4 tlw]) /\
    (exists sj2 : list byte, rw_cells usegs m1 (SPV + -176) [CB 16 sj2]) /\
    (exists sj1 : list byte, rw_cells usegs m1 (SPV + -160) [CB 16 sj1]) /\
    (exists bj : list byte, rw_cells usegs m1 (SPV + -144) [CB 40 bj]) /\
    rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    mem_inv usegs m1 /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 /\ wmono usegs m m1.

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
    u8arr usegs m1 DST out /\ zlen out = cap /\ stk usegs m1 WK (WK + wksz) /\ bytes_at usegs m1 SRCI srci /\
    bytes_at usegs m1 (DT + 4) (map (Z_to_bv 8) tb) /\ stk usegs m1 lo (SPV + -192) /\
    (exists (hole : list byte) (msv tlw : word), rw_cells usegs m1 (SPV + -192) [CB 8 hole; C4 msv; C4 tlw]) /\
    rw_cells usegs m1 (SPV + -176) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))] /\
    rw_cells usegs m1 (SPV + -160) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] /\
    rw_cells usegs m1 (SPV + -144) (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRCI) /\
    rw_cells usegs m1 (SPV + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
    mem_inv usegs m1 /\ munch [(DST, DST + cap); (WK, WK + wksz); (SPV - 448, SPV)] m m1 /\ wmono usegs m m1.
  Ltac open_fdc I := destruct I as (OUT & OLEN & WKS & SRCB & CELB & STK & (fj0 & fmsv & ftlw & F0) & FS2 & FS1 & FBD & FSAV & MI & MU & WM);
                     unfold bitd_cells in FBD.
  Ltac close_fdc :=
    unfold FDC;
    repeat lazymatch goal with
           | |- _ /\ _ => split
           | |- ex _ => eexists
           end;
    eassumption.

  (* [comment removed for export] *)
  Lemma fd_nf_25970 : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x11 x12 x13 x14 x15 x21 x23 x24 x25 x26 x27 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2afa0 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8)) x11 x12 x13 x14 x15 (Z_to_bv 64 ptr)
           (Z_to_bv 64 SRCI) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) x21 (Z_to_bv 64 (DST + cap + -3))
           x23 x24 x25 x26 x27 (Z_to_bv 64 bc) x29 x30 x31).
  Proof using DSYM HY LOSU OFFWK SPA SRCLEN TBL.
    intros * fdc_now st1_rng st2_rng bc_rng ptr_ok.
    pose proof fdc_now as parts. open_fdc parts. open_fh HY.
    do 7 zn; zc.
    eapply fd1_loop0; [exact fdc_now | exact st1_rng | exact st2_rng | exact bc_rng | exact ptr_ok].
  Qed.

  Lemma fd_nf_ld : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x11 x12 x13 x14 x15 x21 x23 x24 x25 x26 x27 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    SRCI <= ptr -> ptr + 8 <= SRCI + ni -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2af0c m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8)) x11 x12 x13 x14 x15 (Z_to_bv 64 ptr)
           (Z_to_bv 64 SRCI) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) x21 (Z_to_bv 64 (DST + cap + -3))
           x23 x24 x25 x26 x27 (Z_to_bv 64 bc) x29 x30 x31).
  Proof using DSYM DTA HY LOS2 LOSU OFFWK SPA SRCLEN TBL.
    intros * fdc_now st1_rng st2_rng bc_rng ptr_lo ptr_hi ptr_ok.
    pose proof fdc_now as parts. open_fdc parts. open_fh HY.
    assert (cells_len : zlen (map (Z_to_bv 8) tb) = 4 * 2^tl) by (rewrite length_map; apply (proj1 TBL)).
    assert (byte_at : forall k, 0 <= k < 8 -> exists b, ov_read_bytes usegs m1 (wa (ptr + k)) 1 = Some [b]).
    { intros k k_rng. eexists. apply (raw_byte_rd usegs m1 SRCI srci (ptr - SRCI + k)); [exact SRCB | lia | f_equal; lia]. }
    destruct (byte_at 1 ltac:(lia)) as (b1 & rd1). zn. clear rd1.
    destruct (byte_at 2 ltac:(lia)) as (b2 & rd2). zn. clear rd2.
    destruct (byte_at 3 ltac:(lia)) as (b3 & rd3). zn. clear rd3.
    destruct (byte_at 0 ltac:(lia)) as (b0 & rd0). zn. clear rd0.
    do 4 (zn; repeat lazymatch goal with |- context [Some (Z_to_bv 64 (Z.lor ?u ?v))] => let acc := fresh "acc" in generalize (Z_to_bv 64 (Z.lor u v)); intro acc end).
    destruct (byte_at 4 ltac:(lia)) as (b4 & rd4). zn. clear rd4.
    destruct (byte_at 5 ltac:(lia)) as (b5 & rd5). zn. clear rd5.
    zn; repeat lazymatch goal with |- context [Some (Z_to_bv 64 (Z.lor ?u ?v))] => let acc := fresh "acc" in generalize (Z_to_bv 64 (Z.lor u v)); intro acc end.
    destruct (byte_at 6 ltac:(lia)) as (b6 & rd6). zn. clear rd6.
    destruct (byte_at 7 ltac:(lia)) as (b7 & rd7). zn. clear rd7.
    do 9 (zn; repeat lazymatch goal with |- context [Some (Z_to_bv 64 (Z.lor ?u ?v))] => let acc := fresh "acc" in generalize (Z_to_bv 64 (Z.lor u v)); intro acc end).
    zn. zn.
    eapply fd_nf_25970; [close_fdc | exact st1_rng | exact st2_rng | exact bc_rng | exact ptr_ok].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_nf_first : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDC out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr ->
    evt usegs POST
      (STF 0x2ae78 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + cap)) x19 x20 x21
           (Z_to_bv 64 (DST + cap + -3)) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof using DSYM DTA HY LOS2 LOSU OFFWK RELOAD SPA SRCLEN TBL.
    intros * fdc_now st1_rng st2_rng bit_ok.
    destruct bit_ok as (bc_rng & near_src).
    pose proof fdc_now as parts. open_fdc parts. open_fh HY.
    assert (cells_len : zlen (map (Z_to_bv 8) tb) = 4 * 2^tl) by (rewrite length_map; apply (proj1 TBL)).
    zn. rewrite (sx32w_small bc) by lia. zn. zstep.
    if_cases over64; zify_cond over64.
    - zn. zn.
      replace (Z_to_bv 64 (-20)) with (Z_to_bv 64 18446744073709551596) by (apply bv_eq; vm_compute; reflexivity).
      apply (fd_epi0 m1 out [CB 8 fj0; C4 fmsv; C4 ftlw] [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))]
               [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] (bitd_cells cont (Z_to_bv 64 bc) pad ptr SRCI) 18446744073709551596);
        first [assumption | reflexivity | lia | left; vm_compute; reflexivity].
    - specialize (near_src over64).
      assert (q8 : 0 <= bc mod 8 < 8) by (apply Z.mod_pos_bound; lia).
      assert (d8 : 0 <= bc / 8 <= 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
      assert (split8 : bc = 8 * (bc / 8) + bc mod 8) by (apply Z.div_mod; lia).
      zn. zn. zn. zn. zn. zn. zn. zn. zstep.
      if_cases far; zify_cond far.
      + zn. zstep.
        eapply evt_cut.
        { eapply (RELOAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -144) SRCI ni bc ptr cont pad srci);
            first [eassumption | lia]. }
        unfold huf_reload_post. post_call usegs m1. unfold bitd_cells in POST.
        zn. rewrite (sx32w_small (bc mod 8)) by lia. zn. zn. zn.
        eapply fd_nf_25970; [close_fdc | exact st1_rng | exact st2_rng | lia | right; lia].
      + zn. zstep. if_cases at_start; zify_cond at_start.
        * subst ptr. zn. zn. zn. zn. zn. zn.
          eapply fd1_loop0; [exact fdc_now | exact st1_rng | exact st2_rng | lia | left; reflexivity].
        * zn. rewrite (wrap32_small bc), (swrap32_small (bc / 8)) by lia. zc. zn. zn. zn. zn. zc. zn. zstep.
          if_cases enough; zify_cond enough.
          -- zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc.
             rewrite ?Z.div_mul in * by lia.
             eapply fd_nf_ld; [close_fdc | exact st1_rng | exact st2_rng | lia ..].
          -- zn. zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc.
             rewrite ?Z.div_mul in * by lia.
             eapply fd_nf_ld; [close_fdc | exact st1_rng | exact st2_rng | lia ..].
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
