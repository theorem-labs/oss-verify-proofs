(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs RZ_hft_x2_sym.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac nchk K := exfalso;
  repeat match type of K with context [(- ?x - 1) mod 18446744073709551616] =>
    rewrite <- (Z.mod_add (- x - 1) 1 18446744073709551616) in K by lia;
    rewrite (Z.mod_small (- x - 1 + 1 * 18446744073709551616)) in K by lia end;
  repeat (rewrite Z.mod_small in K by lia); lia.
Ltac clw := unfold X2G; repeat (split; [first [eassumption | reflexivity | split; eassumption]|]); first [eassumption | reflexivity].
Ltac lst_eq := repeat (first [reflexivity | apply f_equal2;
  [first [reflexivity | f_equal; f_equal; lia | lazymatch goal with |- ?g => fail 10 "CELL" g end] |]]).
Ltac e52 := lazymatch goal with |- context [(?a ≪ 32 mod 18446744073709551616 * 223338299392) ≫ 64] =>
  let E := fresh "E52" in
  assert (E : (a ≪ 32 mod 18446744073709551616 * 223338299392) ≫ 64 = 52 * a)
    by (rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by (change (2^32) with 4294967296; lia);
        rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; change (2^64) with 18446744073709551616;
        replace (a * 4294967296 * 223338299392) with (52 * a * 18446744073709551616) by lia; apply Z.div_mul; lia);
  rewrite E; clear E end.

Section WTWO.
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

  Lemma x2_w_two : forall m1 hdr cw syb cur w k136 k176 k184 k192 k200 k208 k216 k240 k248 k272 k280 (POSTK : machine_state -> Prop)
                          x5 x6 x7 x8 x15 x16 x17 x20 x21 x22 x24 x26 x27 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz (FRW k136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w))
                                 (Z_to_bv 64 (2 * tl + 2 - w)) k176 k184 k192 k200 k208 k216 (Z_to_bv 64 w) k240 k248
                                 (Z_to_bv 64 (xs1 rank (w + 1))) k272 k280)
        hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW -> tl + 1 - maxW <= T - (tl + 1 - w) ->
    (forall m2 cw' cur' u136 u176 u184 u192 u200 u208 u216 u240 u248 u264 u272 u280
            y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRW u136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w))
                                    (Z_to_bv 64 (2 * tl + 2 - w)) u176 u184 u192 u200 u208 u216 (Z_to_bv 64 w) u240 u248 u264 u272 u280)
           hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' ->
       rv0 rank tl T (w + 1) <= cur' ->
       evt usegs POSTK (STL 0x1f6fc m2 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STL 0x1f80c m1 x5 x6 x7 x8 (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 (WK + 4 * w))
                         (Z_to_bv 64 (T - (tl + 1 - w))) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 (4 * w)) x15 x16 x17 x20 x21 x22
                         x24 (Z_to_bv 64 (xs1 rank w)) x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PR CURL WR CRT KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
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
    zstep. zstep. if_cases K3; zify_cond K3.
    { assert (CZ : Znth w rank = 0) by lia. rewrite CZ, Z.mul_0_l, Z.add_0_r in RV0S.
      eapply KONT; [clw | exact PR | lia]. }
    zstep. zstep.
    assert (ERAW : bv_swrap 32 (tl + 1 - w + (tl + 1 - T) mod 18446744073709551616) = tl + 1 - w + (tl + 1 - T)).
    { apply swrap32_eqm; [lia|].
      destruct (Z_lt_le_dec (tl + 1 - T) 0) as [NEG|POS0].
      - replace ((tl + 1 - T) mod 18446744073709551616) with (tl + 1 - T + 18446744073709551616)
          by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
        replace (tl + 1 - w + (tl + 1 - T + 18446744073709551616) - (tl + 1 - w + (tl + 1 - T))) with (4294967296 * 4294967296) by lia.
        apply Z.mod_mul. lia.
      - rewrite (Z.mod_small (tl + 1 - T) 18446744073709551616) by lia. rewrite Z.sub_diag. reflexivity. }
    rewrite ERAW. clear ERAW.
    zstep. zstep. zstep. if_cases K4; zify_cond K4.
    1: assert (MW : Z.max 1 (tl + 1 - w + (tl + 1 - T)) = tl + 1 - w + (tl + 1 - T)) by lia.
    2: zstep; zstep; assert (MW : Z.max 1 (tl + 1 - w + (tl + 1 - T)) = 1) by lia.
    all: lazymatch type of MW with _ = ?v =>
      replace (Z_to_bv 64 v) with (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - T)))) by (rewrite MW; reflexivity) end.
    all: lazymatch type of FR with rw_cells ?sg ?mm ?b _ =>
      assert (FR2 : rw_cells sg mm b (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK tl T maxW c0 c8 c16 hdr3 r0
        k136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 (2 * tl + 2 - w))
        k176 k184 k192 k200 k208 k216 (Z_to_bv 64 w) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T)))
        (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 (xs1 rank (w + 1))) k272 k280 wn wt))
        by (unfold x2_frame; rewrite MW; exact FR) end.
    all: clear FR MW; rename FR2 into FR; unfold x2_frame in FR.
    all: zstep; zstep; zstep; e52.
    all: zstep; zstep; if_cases K5; zify_cond K5; [nchk K5|].
    all: zstep; zstep; zstep.
    all: replace (Z.max 1 (tl + 1 - w + (tl + 1 - T)) ≪ 2) with (4 * Z.max 1 (tl + 1 - w + (tl + 1 - T)))
           by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: zstep; zstep.
    all: rewrite (swrap32_small (2 * tl + 2 - w - Z.max 1 (tl + 1 - w + (tl + 1 - T)))) by lia.
    all: zstep; zstep; zstep; zstep; zstep; zstep.
    all: rewrite (sllw_pow2 (T - (tl + 1 - w))) by lia.
    all: zstep; zstep; zstep.
    all: replace ((tl + 1 - w) ≪ 16) with ((tl + 1 - w) * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    all: lazymatch type of RVA with u32arr ?sg ?mm _ _ => let a := cur_mem_addr in
           pose proof (u32_znth sg mm WK rvl w a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
    all: rewrite (RV0M w WR) in RD.
    all: zstep; rewrite (sx32w_small (rv0 rank tl T w)) by lia; clear RD.
    all: zstep; zstep; e52.
    all: zstep; zstep; zstep; zstep; zstep; zstep; zstep; zstep.
    all: replace (Z.max 1 (tl + 1 - w + (tl + 1 - T)) ≪ 2) with (4 * Z.max 1 (tl + 1 - w + (tl + 1 - T)))
           by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: zstep; zstep; zstep; zstep; zstep.
    all: lazymatch type of FR with rw_cells ?sg ?mm ?b _ =>
      assert (FR3 : rw_cells sg mm b (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK tl T maxW c0 c8 c16 hdr3 r0
        (Z_to_bv 64 (WK + 52 * (tl + 1 - w) + 4 * Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 (w + 1))
        (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 (2 * tl + 2 - w))
        (Z_to_bv 64 (WK + 4 * Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 (maxW + 1 - Z.max 1 (tl + 1 - w + (tl + 1 - T))))
        (Z_to_bv 64 (tl + 1 - w + tl + 1 - Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 (4 * Z.max 1 (tl + 1 - w + (tl + 1 - T))))
        (Z_to_bv 64 ((tl + 1 - w) * 65536 + 16777216)) (Z_to_bv 64 (4 * Z.max 1 (tl + 1 - w + (tl + 1 - T)))) (Z_to_bv 64 w)
        (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - T))))
        (Z_to_bv 64 (xs1 rank (w + 1))) (Z_to_bv 64 (2 ^ (T - (tl + 1 - w)))) k280 wn wt));
      [unfold x2_frame; refine (eq_rect _ (fun l => rw_cells sg mm b l) FR _ _); lst_eq|] end.
    all: clear FR; rename FR3 into FR.
    all: eapply x2_sym_loop.
    all: lazymatch goal with
         | |- PREF2T _ _ _ => exact PR
         | |- Z.to_nat _ = _ => reflexivity
         | |- X2G _ _ _ _ _ _ _ _ _ _ _ _ _ _ => clw
         | |- _ => idtac end.
    all: first [eassumption | lia | (rewrite Z.sub_diag; lia)
               | (intros; eapply KONT; [eassumption | eassumption | eassumption])
               | lazymatch goal with |- ?g => fail 10 "G" g end].
  Qed.
End WTWO.
