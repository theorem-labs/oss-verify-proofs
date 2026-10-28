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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_fse_decnf_kit fse_kit_dsym.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section EPI.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis LOSU : lo <= SPV - 192.
  Hypothesis SPA : SPV mod 16 = 0.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
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

  (* [comment removed for export] *)
  Lemma fd_epi : forall m1 out r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDm out m1 -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    evt usegs POST (STF 0x2b964 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RR RES. open_fh HY. open_fdu I.
    do 14 zstep.
    apply stk_of_rw_cells in F0, FS2, FS1, FBD, FSAV. cbn [cells_size csize Nat.add] in F0, FS2, FS1, FBD, FSAV.
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
  Lemma fd_fin : forall m1 out k x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDm out m1 -> 0 <= k -> k + 2 <= cap ->
    evt usegs POST (STF 0x2bcf0 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 (Z_to_bv 64 (DST + k)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + k + 1)) x19 x20 x21 x22 x23
                        x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HK HKC. open_fh HY. open_fdu I. pose proof TBL as (TBLEN & TBBY & TBOK).
    zstep. outst OUT OLEN. zstep. replace (DST + k + 2 - DST) with (k + 2) by lia. zstep.
    eapply fd_epi; [close_fdu | lia | right; lia].
  Qed.

  Lemma fd_fin2 : forall m1 out k x1 x5 x6 x7 x9 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDm out m1 -> 0 <= k -> k + 3 <= cap ->
    evt usegs POST (STF 0x2bd1c m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 (Z_to_bv 64 (DST + k)) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + k + 1)) x19 x20 x21 x22 x23
                        x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HK HKC. open_fh HY. open_fdu I. pose proof TBL as (TBLEN & TBBY & TBOK).
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. outst OUT OLEN. zstep. replace (DST + k + 3 - DST) with (k + 3) by lia. zstep.
    eapply fd_epi; [close_fdu | lia | right; lia].
  Qed.

  Ltac fin_pre CELB :=
    pose proof TBL as (TBLEN & TBBY & TBOK);
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]);
    pose proof CELB as CELB0; remember (map (Z_to_bv 8) tb) as tbb eqn:ETBB in CELB;
    assert (TBBL : Z.of_nat (length tbb) = 4 * 2^tl) by (subst tbb; rewrite length_map; exact TBLEN).
  Ltac fin_post := unfold fse_dsym_post; lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.

  (* [comment removed for export] *)
  Lemma fd1_finA : forall m1 out st1 st2 cont bc pad ptr j0 j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st2 < 2^tl -> 0 <= bc <= 4096 -> 0 <= j -> j + 2 <= cap ->
    evt usegs POST (STF 0x2bccc m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j + 1)) x19 x20
                        (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j)) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S2 BCR HJ HJC. open_fh HY. open_fdcu I. fin_pre CELB.
    do 6 zstep.
    eapply evt_cut.
    { eapply (DSYM 0 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -176) (SPV + -144) SRCI DT tl st2 bc FSE_ZEROFILLED cont pad tb);
        try eassumption; try lia; try (intros u U; apply (fse_cell_ok_0 tl fast); apply TBOK; exact U). }
    fin_post.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. sub_norm. replace (DST + j0 - (j0 - j)) with (DST + j) by lia.
    eapply fd_fin; [subst tbb; close_fdu | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_finB : forall m1 out st1 st2 cont bc pad ptr j0 j x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= bc <= 4096 -> 0 <= j -> j + 3 <= cap ->
    evt usegs POST (STF 0x2bd00 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) x9 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j + 1)) x19 x20
                        (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j)) x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 BCR HJ HJC. open_fh HY. open_fdcu I. fin_pre CELB.
    do 6 zstep.
    eapply evt_cut.
    { eapply (DSYM 0 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -160) (SPV + -144) SRCI DT tl st1 bc FSE_ZEROFILLED cont pad tb);
        try eassumption; try lia; try (intros u U; apply (fse_cell_ok_0 tl fast); apply TBOK; exact U). }
    fin_post.
    zstep. sub_norm. replace (DST + j0 - (j0 - j)) with (DST + j) by lia.
    eapply fd_fin2; [subst tbb; close_fdu | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_finA : forall m1 out st1 st2 cont bc pad ptr j0 j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> fast = 1 -> 0 <= st2 < 2^tl -> 0 <= bc <= 4096 -> 0 <= j -> j + 2 <= cap ->
    evt usegs POST (STF 0x2bc84 m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j))
                        x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I FAST S2 BCR HJ HJC. open_fh HY. open_fdcu I. fin_pre CELB. rewrite FAST in TBOK.
    do 6 zstep.
    eapply evt_cut.
    { eapply (DSYMF _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -176) (SPV + -144) SRCI DT tl st2 bc FSE_ZEROFILLED cont pad tb);
        try eassumption; try lia. }
    fin_post.
    zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. sub_norm. replace (DST + j0 - (j0 - j)) with (DST + j) by lia. zstep.
    eapply fd_fin; [subst tbb; close_fdu | lia | lia].
  Qed.

  Lemma fd2_finB : forall m1 out st1 st2 cont bc pad ptr j0 j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> fast = 1 -> 0 <= st1 < 2^tl -> 0 <= bc <= 4096 -> 0 <= j -> j + 3 <= cap ->
    evt usegs POST (STF 0x2bcac m1 x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j))
                        x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I FAST S1 BCR HJ HJC. open_fh HY. open_fdcu I. fin_pre CELB. rewrite FAST in TBOK.
    do 6 zstep.
    eapply evt_cut.
    { eapply (DSYMF _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (SPV + -160) (SPV + -144) SRCI DT tl st1 bc FSE_ZEROFILLED cont pad tb);
        try eassumption; try lia. }
    fin_post.
    zstep. sub_norm. replace (DST + j0 - (j0 - j)) with (DST + j) by lia. zstep.
    eapply fd_fin2; [subst tbb; close_fdu | lia | lia].
  Qed.
End EPI.
