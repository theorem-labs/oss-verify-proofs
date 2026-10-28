(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs RZ_hft_x2_sk RZ_hft_x2_w2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section SYMS.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DT WK wksz : Z).
  Hypothesis GEO : x2_geo SPV lo DT WK wksz.
  Variables (ws rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.
  Hypothesis MAXW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Hypothesis MOD : x2_models rank tl T maxW rvl rs0.
  Hypothesis FILLW : huf_fillw_stmt.
  Hypothesis DTA : rsk_al DT 4.
  Variables (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 c16 hdr3 wn wt : word) (r0 : Z).
  Variables (w : Z).
  Hypothesis WR : 1 <= w <= maxW.
  Notation c := (tl + 1 - w).
  Hypothesis CR : tl + 1 - maxW <= c <= T - (tl + 1 - maxW).
  Notation len1 := (2^(T - c)).
  Notation rawmw := (c + (tl + 1 - T)).
  Notation minW := (Z.max 1 rawmw).
  Notation bg := (xs1 rank w).
  Notation en := (xs1 rank (w + 1)).

  Notation FRS k280 := (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK tl T maxW c0 c8 c16 hdr3 r0
                     (Z_to_bv 64 (WK + 52 * c + 4 * minW)) (Z_to_bv 64 (w + 1)) (Z_to_bv 64 rawmw) (Z_to_bv 64 c) (Z_to_bv 64 (2 * tl + 2 - w))
                     (Z_to_bv 64 (WK + 4 * minW)) (Z_to_bv 64 (maxW + 1 - minW)) (Z_to_bv 64 (c + tl + 1 - minW)) (Z_to_bv 64 (4 * minW))
                     (Z_to_bv 64 (c * 65536 + 16777216)) (Z_to_bv 64 (4 * minW)) (Z_to_bv 64 w) (Z_to_bv 64 rawmw) (Z_to_bv 64 minW)
                     (Z_to_bv 64 en) (Z_to_bv 64 len1) k280 wn wt).

  Notation STS pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SPV + -400)) gp tp x5 x6 x7 (Z_to_bv 64 (Z.lxor (WK + 52 * c) 18446744073709551615)) (Z_to_bv 64 T)
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (WK + 736)) x19 x20 x21 (Z_to_bv 64 (52 * c))
             (Z_to_bv 64 (Z.lxor (WK + 676) 18446744073709551615)) x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma x2_sym_cut : forall m1 hdr cw syb cur s st bsym (POSTK : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x27 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz (FRS (Z_to_bv 64 st)) hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> st + rvc rank tl T c minW <= cur ->
    bg <= s < en -> st = rv0 rank tl T w + (s - bg) * len1 -> 0 <= bsym < 256 ->
    (forall m2 cw' cur' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y24 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRS (Z_to_bv 64 st)) hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' -> st + len1 <= cur' ->
       evt usegs POSTK (STS 0x1fad8 m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y24 (Z_to_bv 64 s) y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STS 0x1fa28 m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z_to_bv 64 bsym) x21 x24 (Z_to_bv 64 s)
                         (Z_to_bv 64 (DT + 4 + 4 * st)) x27 x28 x29 x30 x31).
  Proof using GEO OK TT MAXW HIGH MOD FILLW DTA WR CR.
    intros until x31; intros I PR CURL SR EST BSR KONT.
    pose proof I as I0. open_geo GEO. open_x2g I. unfold x2_frame in FR.
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    assert (RS : rv0 rank tl T (w + 1) = rv0 rank tl T w + Znth w rank * len1) by (eapply rv0_step; first [eassumption | lia]).
    assert (R0 : 0 <= rv0 rank tl T w) by (eapply rv0_nonneg; first [eassumption | lia]).
    assert (RM : rv0 rank tl T (w + 1) <= rv0 rank tl T (maxW + 1)) by (eapply rv0_mono; first [eassumption | lia]).
    assert (RT : rv0 rank tl T (maxW + 1) = 2^T) by (eapply rv0_top; first [eassumption | lia]).
    assert (P2C : 0 <= len1) by (apply Z.pow_nonneg; lia).
    assert (STR : 0 <= st) by (rewrite EST; apply Z.add_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; lia]).
    assert (MLE : (s - bg + 1) * len1 <= Znth w rank * len1) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (STH : st + len1 <= 2^T) by lia.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    all: rewrite !signed_lit in KB by lia; try (exfalso; lia).
    zstep. zstep. zstep. zstep.
    eapply (x2_w2_loop gp tp F fc m SPV lo DT WK wksz GEO ws rank tl T maxW rvl rs0 OK TT MAXW HIGH MOD FILLW DTA
              (tl + 1 - w) st bsym CR STR STH BSR (Z.to_nat (maxW + 1 - minW)) m1 _ hdr cw syb cur minW POSTK);
      [reflexivity | exact I0 | exact PR | exact CURL | lia | lia |].
    intros m2 cw' cur' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y27 y28 y29 y30 y31 I2 PR2 CURL2.
    eapply KONT; [exact I2 | exact PR2 | exact CURL2].
  Qed.
End SYMS.
