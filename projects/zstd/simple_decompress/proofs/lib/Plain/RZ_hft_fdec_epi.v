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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section EPI.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation FDm := (FD s0 s1 s2 s3 s4 s5 s6 s7 ra m SPV lo DST cap WK wksz SRCI DT srci tb).

  (* [comment removed for export] *)
  Lemma fd_epi : forall m1 out r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31,
    FDm out m1 -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evt psegs POST (STF 0x25610 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 (Z_to_bv 64 r) x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RR RES. open_fh HY. open_fd I.
    do 10 zstep. zstep.
    apply stk_of_rw_cells in F0, FS2, FS1, FBD, FSAV. cbn [cells_size csize Nat.add] in F0, FS2, FS1, FBD, FSAV.
    assert (STK' : stk psegs m1 lo SPV).
    { apply (stk_merge psegs m1 lo (SPV + -160) SPV STK); [|lia].
      apply (stk_merge psegs m1 (SPV + -160) (SPV + -144) SPV); [replace (SPV + -144) with (SPV + -160 + Z.of_nat 16) by lia; exact F0| |lia].
      apply (stk_merge psegs m1 (SPV + -144) (SPV + -128) SPV); [replace (SPV + -128) with (SPV + -144 + Z.of_nat 16) by lia; exact FS2| |lia].
      apply (stk_merge psegs m1 (SPV + -128) (SPV + -112) SPV); [replace (SPV + -112) with (SPV + -128 + Z.of_nat 16) by lia; exact FS1| |lia].
      apply (stk_merge psegs m1 (SPV + -112) (SPV + -72) SPV); [replace (SPV + -72) with (SPV + -112 + Z.of_nat 40) by lia; exact FBD| |lia].
      replace SPV with (SPV + -72 + Z.of_nat 72) at 2 by lia. exact FSAV. }
    assert (DSTS : stk psegs m1 DST (DST + cap)).
    { apply rw_cells_of_u8arr in OUT. apply stk_of_rw_cells in OUT. cbn [cells_size csize] in OUT.
      replace (DST + cap) with (DST + Z.of_nat (length out + 0)) by lia. exact OUT. }
    zstep. apply evt_done. unfold fse_dec_post.
    do 14 eexists. exists m1, r.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact DSTS|]. split; [exact WKS|]. split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  Lemma fd_fin : forall m1 out k x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    FDm out m1 -> 0 <= k <= cap ->
    evt psegs POST (STF 0x26234 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (DST + k)) x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 DST) x20 x21 x22 x23 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HK. open_fh HY.
    zstep. replace (DST + k - DST) with k by lia. zstep.
    eapply fd_epi; [exact I | lia | right; lia].
  Qed.

  Ltac ldsy CELB DT tb st :=
    let a := cur_mem_addr in
    let RDc := fresh "RDc" in
    pose proof (u8ro_znth psegs _ (DT + 4) tb (4 * st + 2) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
    zstep; cbv beta; fold (fc_sy tb st); rewrite (byte_lit (fc_sy tb st)) by lia; clear RDc.

  (* [comment removed for export] *)
  Lemma fd1_finA : forall m1 out st j x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x20 x21 x22 x23 x29 x30 x31,
    FDm out m1 -> 0 <= st < 2^tl -> 0 <= j -> j + 2 <= cap ->
    evt psegs POST (STF 0x261d8 m1 x1 x5 (Z_to_bv 64 st) x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (DT + 4)) x17 x18 (Z_to_bv 64 DST) x20 x21 x22 x23
                        (Z_to_bv 64 (DST + j + 1)) x29 x30 x31).
  Proof.
    intros until x31; intros I ST HJ HJC. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st TBL ltac:(lia) ST) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st ≪ 2) with (DT + 4 + 4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldsy CELB DT tb st. zstep. outst OUT OLEN. zstep.
    replace (DST + j + 2) with (DST + (j + 2)) by lia.
    eapply fd_fin; [close_fd | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_finB : forall m1 out st j x1 x5 x6 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x20 x21 x22 x23 x29 x30 x31,
    FDm out m1 -> 0 <= st < 2^tl -> 0 <= j -> j + 3 <= cap ->
    evt psegs POST (STF 0x26208 m1 x1 x5 x6 (Z_to_bv 64 st) x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DT + 4)) x16 x17 x18 (Z_to_bv 64 DST) x20 x21 x22 x23
                        (Z_to_bv 64 (DST + j + 1)) x29 x30 x31).
  Proof.
    intros until x31; intros I ST HJ HJC. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st TBL ltac:(lia) ST) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st ≪ 2) with (DT + 4 + 4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldsy CELB DT tb st. zstep. outst OUT OLEN. zstep.
    replace (DST + j + 3) with (DST + (j + 3)) by lia.
    eapply fd_fin; [close_fd | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_finA : forall m1 out st j x1 x5 x8 x9 x10 x11 x12 x13 x14 x15 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    FDm out m1 -> 0 <= st < 2^tl -> 0 <= j -> j + 2 <= cap ->
    evt psegs POST (STF 0x261f0 m1 x1 x5 (Z_to_bv 64 st) (Z_to_bv 64 (DST + j + 1)) x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (DT + 4)) x17 x18 (Z_to_bv 64 DST) x20 x21 x22 x23
                        x28 x29 x30 x31).
  Proof.
    intros until x31; intros I ST HJ HJC. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st TBL ltac:(lia) ST) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st ≪ 2) with (DT + 4 + 4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldsy CELB DT tb st. zstep. outst OUT OLEN. zstep.
    replace (DST + j + 2) with (DST + (j + 2)) by lia.
    eapply fd_fin; [close_fd | lia].
  Qed.

  Lemma fd2_finB : forall m1 out st j x1 x6 x8 x9 x10 x11 x12 x13 x14 x16 x17 x18 x20 x21 x22 x23 x28 x29 x30 x31,
    FDm out m1 -> 0 <= st < 2^tl -> 0 <= j -> j + 3 <= cap ->
    evt psegs POST (STF 0x26220 m1 x1 (Z_to_bv 64 st) x6 (Z_to_bv 64 (DST + j + 1)) x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 (DT + 4)) x16 x17 x18 (Z_to_bv 64 DST) x20 x21 x22 x23
                        x28 x29 x30 x31).
  Proof.
    intros until x31; intros I ST HJ HJC. open_fh HY. open_fd I.
    destruct (fd_cell tl fast tb st TBL ltac:(lia) ST) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. replace (DT + 4 + st ≪ 2) with (DT + 4 + 4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    ldsy CELB DT tb st. zstep. outst OUT OLEN.
    replace (DST + j + 3) with (DST + (j + 3)) by lia.
    eapply fd_fin; [close_fd | lia].
  Qed.
End EPI.
