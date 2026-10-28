(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac nchk K := exfalso;
  repeat match type of K with context [(- ?x - 1) mod 18446744073709551616] =>
    rewrite <- (Z.mod_add (- x - 1) 1 18446744073709551616) in K by lia;
    rewrite (Z.mod_small (- x - 1 + 1 * 18446744073709551616)) in K by lia end;
  repeat (rewrite Z.mod_small in K by lia); lia.
Ltac clw := unfold X2G; repeat (split; [first [eassumption | reflexivity | split; eassumption]|]); first [eassumption | reflexivity].
Ltac kchk K := exfalso; rewrite ?zb_lxor_ones in K by lia; repeat (rewrite Z.mod_small in K by lia); lia.
Ltac chk := let K := fresh "K" in zstep;
  lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K; zify_cond K; [kchk K|]; try clear K | |- _ => idtac end.
Ltac sgn x := lazymatch goal with |- context [Z.lxor x ?k] =>
  replace (Z.lxor x k) with (x + k) by (change k with (2^63); rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity) end.

Section WONE.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DT WK wksz : Z).
  Hypothesis GEO : x2_geo SPV lo DT WK wksz.
  Variables (ws rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.
  Hypothesis MAXW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Hypothesis MOD : x2_models rank tl T maxW rvl rs0.
  Variables (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 c16 hdr3 wn wt : word) (r0 : Z).
  Hypothesis FILLW : huf_fillw_stmt.
  Hypothesis DTA : rsk_al DT 4.

  Notation FRW k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 :=
    (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK tl T maxW c0 c8 c16 hdr3 r0
              k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 wn wt).

  Notation STL pc mm x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SPV + -400)) gp tp x5 x6 x7 x8 (Z_to_bv 64 T) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (DT + 4)) x20 x21 x22 (Z_to_bv 64 (Z.lxor (WK + 676) 18446744073709551615))
             x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma x2_w_one : forall m1 hdr cw syb cur w k136 k176 k184 k192 k200 k208 k216 k240 k248 k272 k280 (POSTK : machine_state -> Prop)
                          x5 x6 x7 x8 x10 x12 x15 x16 x17 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz (FRW k136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w))
                                 (Z_to_bv 64 (2 * tl + 2 - w)) k176 k184 k192 k200 k208 k216 (Z_to_bv 64 w) k240 k248
                                 (Z_to_bv 64 (xs1 rank (w + 1))) k272 k280)
        hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW -> T - (tl + 1 - w) < tl + 1 - maxW ->
    (forall m2 cw' cur' u136 u176 u184 u192 u200 u208 u216 u240 u248 u264 u272 u280
            y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRW u136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w))
                                    (Z_to_bv 64 (2 * tl + 2 - w)) u176 u184 u192 u200 u208 u216 (Z_to_bv 64 w) u240 u248 u264 u272 u280)
           hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' ->
       rv0 rank tl T (w + 1) <= cur' ->
       evt usegs POSTK (STL 0x1f6fc m2 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STL 0x1f798 m1 x5 x6 x7 x8 x10 (Z_to_bv 64 (WK + 4 * w)) x12 (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 (4 * w))
                         x15 x16 x17 x20 x21 x22 x24 (Z_to_bv 64 (xs1 rank w)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PR CURL WR CRT KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR.
    pose proof MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as BG0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ. pose proof (st_rank_nonneg ws rank tl OK w ltac:(lia)) as CNT0.
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    pose proof (rv0_step rank tl T TT w ltac:(lia)) as RV0S.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as RV00.
    pose proof (rv0_mono ws rank tl T OK TT (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)) as RV0M1.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RV0M1.
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    pose proof (rv0_mono ws rank tl T OK TT w (maxW + 1) ltac:(lia) ltac:(lia)) as RVW.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RVW.
    zstep. zstep. if_cases K; zify_cond K.
    { nchk K. }
    lazymatch type of RVA with u32arr ?sg ?mm _ _ => let a := cur_mem_addr in
      pose proof (u32_znth sg mm WK rvl w a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RV0M w WR) in RD.
    zstep. rewrite (zx32w_small (rv0 rank tl T w)) by lia. clear RD.
    remember (rv0 rank tl T w) as rp eqn:ERP.
    zstep. replace (rp ≪ 2) with (4 * rp) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. if_cases K2; zify_cond K2.
    { nchk K2. }
    remember (xs1 rank w) as bg eqn:EBG.
    remember (xs1 rank (w + 1)) as en eqn:EEN.
    zstep. chk.
    zstep. decide_tests. change (Z.b2z false) with 0.
    zstep. sgn bg. decide_tests. change (Z.b2z false) with 0.
    zstep. zstep. chk.
    zstep. zstep. chk.
    zstep. decide_tests. change (Z.b2z false) with 0.
    zstep.
    zstep. sgn en. decide_tests. change (Z.b2z false) with 0.
    zstep. zstep. chk.
    zstep. zstep. zstep. zstep. zstep.
    assert (RV1 : rv0 rank tl T (w + 1) = rp + 2^(T - (tl + 1 - w)) * (en - bg)).
    { rewrite RV0S. replace (en - bg) with (Znth w rank) by lia. ring. }
    assert (N0 : 0 <= 2^(T - (tl + 1 - w)) * (en - bg)) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia | lia]).
    assert (POSH : rp + 2^(T - (tl + 1 - w)) * (en - bg) <= 4096) by lia.
    replace (Z_to_bv 64 (en + (WK + 736))) with (Z_to_bv 64 (WK + 736 + en)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (FILLW (Z_to_bv 64 0x1f804) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -400)
                    lo DT (WK + 736) cw syb rp bg en (tl + 1 - w) T 1 0);
        unfold HUF_DTABLE_BYTES, HUF_FILLW_STACK; try eassumption; try lia.
      pose proof (rsk_al_e DT 4 DTA) as A. Z.div_mod_to_equations. lia. }
    unfold huf_fillw_post, HUF_DTABLE_BYTES, HUF_FILLW_STACK. post_call usegs m1.
    zstep. zstep.
    lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
      pose proof (pref2T_write T cur cw cwn rp (2^(T - (tl + 1 - w)) * (en - bg)) (tl + 1 - w + 256 * 1) PR PO
                    (okwT_val T (tl + 1 - w) 1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
      eapply (KONT mm cwn (Z.max cur (rp + 2^(T - (tl + 1 - w)) * (en - bg)))); [close_x2g | exact PR' | lia] end.
  Qed.
End WONE.
