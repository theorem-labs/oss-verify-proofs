(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_blk_iface2 RZ_bst.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma stk_to_u8arr : forall m a (n : nat), stk usegs m a (a + Z.of_nat n) -> exists bs, u8arr usegs m a bs /\ length bs = n.
Proof.
  intros m a n S. destruct (stk_carve usegs m a (a + Z.of_nat n) n S ltac:(lia)) as [_ [j C]].
  replace (a + Z.of_nat n - Z.of_nat n) with a in C by lia.
  exists j. split; [exact (u8arr_of_rw_cells usegs m a n j C)|].
  destruct C as [[Hwf _] _]. exact (proj1 Hwf).
Qed.

Lemma u8arr_to_stk : forall m a bs, u8arr usegs m a bs -> stk usegs m a (a + Z.of_nat (length bs)).
Proof.
  intros m a bs U. apply rw_cells_of_u8arr in U. apply stk_of_rw_cells in U.
  cbn [cells_size csize] in U. rewrite Nat.add_0_r in U. exact U.
Qed.

Lemma bytes_at_agree : forall m A (bs1 bs2 : list byte), bytes_at usegs m A bs1 -> bytes_at usegs m A bs2 ->
  (length bs1 <= length bs2)%nat -> bs1 = firstn (length bs1) bs2.
Proof.
  intros m A bs1 bs2 (_ & _ & H1) (_ & _ & H2) L.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
  - rewrite nth_error_firstn. replace (i <? length bs1)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
    rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs1 i) Hi). symmetry. apply nth_error_None. rewrite firstn_length. lia.
Qed.

Lemma bytes_at_firstn : forall m A (bs : list byte) n, bytes_at usegs m A bs -> bytes_at usegs m A (firstn n bs).
Proof.
  intros m A bs n (H0 & H1 & H). assert (L : (length (firstn n bs) <= length bs)%nat) by (rewrite firstn_length; lia).
  split; [exact H0|]. split; [lia|].
  intros i Hi. rewrite (H i ltac:(lia)). rewrite nth_error_firstn. rewrite firstn_length in Hi.
  replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Notation TSZ k := (8 + 8 * 2^(kind_maxLog k)) (only parsing).

Definition zd_buildseq_stk_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DTS DTP W DFLT : Z) (k : seq_kind) (ty srcSize : Z) (frw oldp : word) (wlen lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r pv,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DTS, DTS + TSZ k); (DTP, DTP + 8); (W, W + wlen); (SPV - 448, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ stk usegs m' DTS (DTS + TSZ k) /\ stk usegs m' W (W + wlen)
    /\ rw_cells usegs m' DTP [C8 pv]
    /\ (forall A bs, bytes_at usegs m A bs ->
          disjoint_from [(DTS, DTS + TSZ k); (DTP, DTP + 8); (W, W + wlen); (SPV - 448, SPV)] A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs)
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true
        \/ (r <= srcSize /\
            ((ty = 0 /\ pv = Z_to_bv 64 DFLT)
             \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\
                 forall bs, bytes_at usegs m DTS bs -> Z.of_nat (length bs) <= TSZ k -> bytes_at usegs m' DTS bs)
             \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 DTS /\
                 exists t, seq_table_ok k t /\ bytes_at usegs m' DTS (map (Z_to_bv 8) (seq_table_bytes t)))))).

Lemma zd_buildseq_stk :
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DTS DTP SRC W DFLT BASE BITS ty wlen : Z) (k : seq_kind)
         (srcb : list Z) (oldp nbw : word),
  stk usegs m DTS (DTS + TSZ k) -> rw_cells usegs m DTP [C8 oldp] -> stk usegs m W (W + wlen) -> 626 <= wlen ->
  bytes_at usegs m SRC (map (Z_to_bv 8) srcb) -> Forall (fun c => 0 <= c < 256) srcb -> Z.of_nat (length srcb) <= 1048576 ->
  bytes_at usegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
  bytes_at usegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
  rw_cells usegs m SPV [C8 nbw; C8 (Z_to_bv 64 W)] ->
  0 <= ty <= 3 ->
  4096 <= DTS -> DTS + TSZ k < 2^47 -> 4096 <= DTP -> DTP + 8 < 2^47 -> 4096 <= W -> W + wlen < 2^47 ->
  4096 <= SRC -> SRC + Z.of_nat (length srcb) < 2^47 -> 4096 <= BASE < 2^47 -> 4096 <= BITS < 2^47 ->
  stk usegs m lo SPV -> lo <= SPV - 448 -> 4096 <= lo -> SPV + 16 < 2^47 ->
  off_stack lo SPV DTS (TSZ k) -> off_stack lo SPV DTP 8 -> off_stack lo SPV W wlen ->
  off_stack lo SPV SRC (Z.of_nat (length srcb)) -> off_stack lo SPV BASE 212 -> off_stack lo SPV BITS 53 ->
  apart DTS (TSZ k) DTP 8 -> apart DTS (TSZ k) W wlen ->
  apart DTS (TSZ k) SRC (Z.of_nat (length srcb)) -> apart DTS (TSZ k) BASE 212 ->
  apart DTS (TSZ k) BITS 53 -> apart DTS (TSZ k) SPV 16 ->
  apart DTP 8 W wlen -> apart DTP 8 SRC (Z.of_nat (length srcb)) -> apart DTP 8 BASE 212 -> apart DTP 8 BITS 53 ->
  apart DTP 8 SPV 16 ->
  apart W wlen SRC (Z.of_nat (length srcb)) -> apart W wlen BASE 212 ->
  apart W wlen BITS 53 -> apart W wlen SPV 16 ->
  DTS mod 4 = 0 -> DTP mod 8 = 0 -> BASE mod 4 = 0 -> W mod 2 = 0 -> SPV mod 16 = 0 -> (t5 <> Z_to_bv 64 0 -> 4096 <= bv_unsigned oldp < 2^47) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DTS -> a1 = Z_to_bv 64 DTP -> a2 = Z_to_bv 64 ty -> a3 = Z_to_bv 64 (kind_max k) -> a4 = Z_to_bv 64 (kind_maxLog k) ->
  a5 = Z_to_bv 64 SRC -> a6 = Z_to_bv 64 (Z.of_nat (length srcb)) -> a7 = Z_to_bv 64 BASE -> t3 = Z_to_bv 64 BITS -> t4 = Z_to_bv 64 DFLT ->
  evt usegs (zd_buildseq_stk_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DTS DTP W DFLT k ty (Z.of_nat (length srcb)) t5 oldp wlen lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_BUILDSEQ) fc None m (seg_rom usegs)).
Proof.
  intros until nbw.
  intros DTK DTPC WK WLEN SRCB FBY SLEN BASEB BITSB ARGS TYR DTSL DTSH DTPL DTPH WL WH SRCL SRCH BASER BITSR STK LOS LO0 SPH
         O1 O2 O3 O4 O5 O6 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 AL1 AL2 AL3 AL4 AL5 OLDP MI E0 E1 E2 E3 E4 E5 E6 E7 E8 E9.
  assert (KM : 8 <= kind_maxLog k <= 9) by (destruct k; cbn; lia).
  assert (P8 : 256 <= 2 ^ kind_maxLog k <= 512) by (destruct k; cbn; lia).
  set (n := Z.to_nat (TSZ k)). assert (EN : Z.of_nat n = TSZ k) by (subst n; lia).
  set (wn := Z.to_nat wlen). assert (EW : Z.of_nat wn = wlen) by (subst wn; lia).
  rewrite <- EN in DTK. rewrite <- EW in WK.
  destruct (stk_to_u8arr m DTS n DTK) as (dt0 & DTA & LD). destruct (stk_to_u8arr m W wn WK) as (wb0 & WA & LW).
  pose proof zd_buildseq_proof as BS. unfold zd_buildseq_stmt in BS.
  eapply evt_mono.
  - eapply (BS ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV lo DTS DTP SRC W DFLT BASE BITS ty k
              dt0 wb0 srcb oldp nbw); try eassumption; try (rewrite ?LD, ?LW, ?EN, ?EW; assumption); try (rewrite ?LD, ?LW, ?EN, ?EW; lia).
  - intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & r & dt' & wb' & pv & -> & MU & WM & MI' & STK' & DTA' & LD' & WA' & LW' & DTPC' & RR & RES).
    unfold zd_buildseq_stk_post. do 14 eexists. exists m', r, pv.
    split; [reflexivity|]. rewrite LD, LW, EN, EW in MU. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [pose proof (u8arr_to_stk m' DTS dt' DTA') as S; rewrite LD', LD, EN in S; exact S|].
    split; [pose proof (u8arr_to_stk m' W wb' WA') as S; rewrite LW', LW, EW in S; exact S|].
    split; [exact DTPC'|].
    split; [intros A bs BA DJ; exact (bytes_at_transport usegs _ m m' A bs BA MU DJ)|].
    split; [exact RR|].
    destruct RES as [ER | (RL & [(T0 & PV & _) | [(T3 & FRN & PV & DE) | (T12 & PV & t & TOK & PRE)]])]; [left; exact ER | right; split; [exact RL|]..].
    + left. auto.
    + right. left. split; [exact T3|]. split; [exact FRN|]. split; [exact PV|]. subst dt'.
      intros bs BA LB. rewrite (bytes_at_agree m DTS bs dt0 BA (proj1 DTA) ltac:(lia)). apply bytes_at_firstn. exact (proj1 DTA').
    + right. right. split; [exact T12|]. split; [exact PV|]. exists t. split; [exact TOK|].
      rewrite <- PRE. apply bytes_at_firstn. exact (proj1 DTA').
Qed.
