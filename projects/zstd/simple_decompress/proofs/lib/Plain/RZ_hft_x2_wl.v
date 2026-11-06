(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_l1 RZ_hft_x2_sym.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section WL.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DT WK wksz : Z).
  Hypothesis GEO : x2_geo SPV lo DT WK wksz.
  Variables (ws rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.
  Hypothesis MAXW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Hypothesis MOD : x2_models rank tl T maxW rvl rs0.
  Variables (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 hdr3 hdrw wn wt : word) (r0 : Z).

  Notation FRW v112 v120 v128 v136 v144 :=
    (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK c0 c8 hdr3 r0 hdrw (tl + 1 - T) maxW (tl + 1 - maxW) (tl + 1)
              (C8 v112) (C8 v120) (C8 v128) (C8 v136) (C8 v144) wn wt).

  Notation STL pc mm x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x21 x22 x25 x26 x27 x28 x29 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -272)) gp tp x5 (Z_to_bv 64 (maxW + 1)) x7 x8 x9 x10 x11 x12 x13 x14
             (Z_to_bv 64 (WK + 676)) x16 x17 (Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 8) x21 x22 (Z_to_bv 64 T) (Z_to_bv 64 (WK + 736))
             x25 x26 x27 x28 x29 (Z_to_bv 64 1) (Z_to_bv 64 3))
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x2_w_body : forall m1 hdr cw syb cur w v112 v120 v128 v136 v144 (POSTK : machine_state -> Prop) x1 x5 x7 x8 x9 x11 x12 x13 x14 x16 x17 x21 x22 x26 x27 x28 x29,
    X2G m SPV lo DT WK wksz (FRW v112 v120 v128 v136 v144) hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW ->
    (forall m2 cw' cur' u112 u128 u136 u144 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29,
       X2G m SPV lo DT WK wksz (FRW u112 (Z_to_bv 64 (w + 1)) u128 u136 u144) hdr cw' rvl rank rs0 syb m2 -> PREF2 cur' cw' ->
       rv0 rank tl T (w + 1) <= cur' ->
       evt psegs POSTK (STL 0x1d24c m2 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29)) ->
    evt psegs POSTK (STL 0x1d258 m1 x1 x5 x7 x8 x9 (Z_to_bv 64 w) x11 x12 x13 x14 x16 x17 x21 x22 (Z_to_bv 64 WK) x26 x27 x28 x29).
  Proof.
    intros until x29; intros I PR CURL WR KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
    destruct MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as BG0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ. pose proof (st_rank_nonneg ws rank tl OK w ltac:(lia)) as CNT0.
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    pose proof (rv0_step rank tl T TT w ltac:(lia)) as RV0S.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as RV00.
    pose proof (rv0_mono ws rank tl T OK TT (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)) as RV0M1.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RV0M1.
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    do 6 zstep.
    replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace ((w + 1) ≪ 2) with (4 * (w + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 (WK + 676) rs0 w a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M w ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank w)) by lia. clear RD.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 (WK + 676) rs0 (w + 1) a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M (w + 1) ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank (w + 1))) by lia. clear RD.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 WK rvl w a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RV0M w WR) in RD.
    zstep. rewrite (zx32w_small (rv0 rank tl T w)) by lia. clear RD.
    zstep. zstep. rewrite (swrap32_small (tl + 1 - w)) by lia.
    zstep. rewrite (swrap32_small (T - (tl + 1 - w))) by lia.
    zstep. rewrite (sllw_pow2 (T - (tl + 1 - w))) by lia.
    zstep. zstep. zstep.
    remember (tl + 1 - w) as c eqn:EC.
    remember (xs1 rank w) as bg eqn:EBG. remember (Znth w rank) as cnt eqn:ECNT. remember (rv0 rank tl T w) as pos eqn:EPOS.
    rewrite XSS. replace (T - (tl + 1 - w)) with (T - c) in RV0S by lia.
    remember (2^(T - c)) as len1 eqn:ELEN.
    assert (LENC : (len1 = 1) \/ (len1 = 2) \/ (len1 = 4) \/ (len1 = 8) \/ (exists Q, 2 <= Q <= 512 /\ len1 = 8 * Q)).
    { subst len1. assert (E : T - c = 0 \/ T - c = 1 \/ T - c = 2 \/ T - c = 3 \/ 4 <= T - c <= 11) by lia.
      destruct E as [E|[E|[E|[E|E]]]]; [rewrite E; auto | rewrite E; auto | rewrite E; auto | rewrite E; auto 6|].
      right; right; right; right. exists (2^(T - c - 3)). split.
      - split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia].
      - change 8 with (2^3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (LEN0 : 1 <= len1 <= 4096) by (destruct LENC as [E|[E|[E|[E|(Q & QR & E)]]]]; lia).
    assert (POSH : pos + cnt * len1 <= 4096) by lia.
    assert (KZ : forall mm u112 u128 u136 u144 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29,
               X2G m SPV lo DT WK wksz (FRW u112 (Z_to_bv 64 (w + 1)) u128 u136 u144) hdr cw rvl rank rs0 syb mm -> cnt = 0 ->
               evt psegs POSTK (STL 0x1d24c mm y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29)).
    { intros. eapply KONT; [eassumption | exact PR | lia]. }
    if_cases KL; zify_cond KL.
    2:{ (* [comment removed for export] *)
        zstep. replace (pos ≪ 2) with (4 * pos) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        zstep. zstep. zstep. zstep.
        assert (I1 : X2G m SPV lo DT WK wksz (FRW v112 (Z_to_bv 64 (w + 1)) v128 v136 v144) hdr cw rvl rank rs0 syb m0).
        { unfold X2G. split; [exact HDRC|]. split; [split; [exact CW | exact CWL]|]. split; [exact RVA|]. split; [exact RKA|]. split; [exact RSA|].
          split; [exact SYB|]. split; [exact SYLEN|]. split; [exact SYS|]. split; [exact WKR|]. split; [exact FR|]. split; [reflexivity|].
          split; [exact STK|]. split; [exact MI|]. split; [exact MU | exact WM]. }
        clear ELEN.
        destruct LENC as [L1|[L2|[L4|[L8|(Q & QR & LQ)]]]].
        - (* [comment removed for export] *)
          if_cases K1; zify_lts K1; [exfalso; lia|].
          zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
          zstep. if_cases K3; zify_cond K3; [eapply KZ; [exact I1 | lia]|].
          do 5 zstep.
          replace (c ≪ 16) with (c * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          rewrite (Z.mod_small (c * 65536 + 16777216)) by lia.
          replace ((c * 65536 + 16777216) ≫ 16) with (c + 256) by (rewrite Z.shiftr_div_pow2 by lia; change (2^16) with 65536; Z.div_mod_to_equations; lia).
          replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
          replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + 0))) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
          eapply evt_cut.
          { eapply x2_l1_len1 with (DT := DT) (SYM := WK + 736) (m0 := m0) (cw0 := cw) (pos := pos) (cnt := cnt) (bg := bg) (nb := c) (s := 0)
                                   (j := Z.to_nat (cnt - 0)) (syb := syb); try eassumption; try lia; try reflexivity.
            - apply munch_refl.
            - apply wmono_refl.
            - exact (conj CW CWL).
            - apply cells_written_refl. }
          unfold x2_l1_post. post_call psegs m0.
          lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
            pose proof (pref2_write cur cw cwn pos cnt (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
            eapply (KONT mm cwn (Z.max cur (pos + cnt))); [| exact PR' | lia] end.
          unfold X2G. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [reflexivity|].
          split; [eassumption|]. split; [eassumption|]. split; eassumption.
        - (* [comment removed for export] *)
          if_cases K1; zify_lts K1; [exfalso; lia|].
          zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
          zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
          zstep. if_cases K3; zify_cond K3; [eapply KZ; [exact I1 | lia]|].
          do 4 zstep.
          replace (c ≪ 16) with (c * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
          replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + 2 * 0))) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
          eapply evt_cut.
          { eapply x2_l1_len2 with (DT := DT) (SYM := WK + 736) (m0 := m0) (cw0 := cw) (pos := pos) (cnt := cnt) (bg := bg) (nb := c) (s := 0)
                                   (j := Z.to_nat (cnt - 0)) (syb := syb); try eassumption; try lia; try reflexivity.
            - apply munch_refl.
            - apply wmono_refl.
            - exact (conj CW CWL).
            - replace (2 * 0) with 0 by lia. apply cells_written_refl. }
          unfold x2_l1_post. post_call psegs m0.
          lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
            pose proof (pref2_write cur cw cwn pos (2 * cnt) (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
            eapply (KONT mm cwn (Z.max cur (pos + 2 * cnt))); [| exact PR' | lia] end.
          unfold X2G. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [reflexivity|].
          split; [eassumption|]. split; [eassumption|]. split; eassumption.
        - (* [comment removed for export] *)
          if_cases K1; zify_lts K1; [|exfalso; lia].
          zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
          zstep. if_cases K3; zify_cond K3; [eapply KZ; [exact I1 | lia]|].
          do 4 zstep.
          replace (c ≪ 16) with (c * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
          replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * 0))) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
          eapply evt_cut.
          { eapply x2_l1_len4 with (DT := DT) (SYM := WK + 736) (m0 := m0) (cw0 := cw) (pos := pos) (cnt := cnt) (bg := bg) (nb := c) (s := 0)
                                   (j := Z.to_nat (cnt - 0)) (syb := syb); try eassumption; try lia; try reflexivity.
            - apply munch_refl.
            - apply wmono_refl.
            - exact (conj CW CWL).
            - replace (4 * 0) with 0 by lia. apply cells_written_refl. }
          unfold x2_l1_post. post_call psegs m0.
          lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
            pose proof (pref2_write cur cw cwn pos (4 * cnt) (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
            eapply (KONT mm cwn (Z.max cur (pos + 4 * cnt))); [| exact PR' | lia] end.
          unfold X2G. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [reflexivity|].
          split; [eassumption|]. split; [eassumption|]. split; eassumption.
        - (* [comment removed for export] *)
          if_cases K1; zify_lts K1; [|exfalso; lia].
          zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
          zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
          zstep. if_cases K3; zify_cond K3; [eapply KZ; [exact I1 | lia]|].
          do 4 zstep.
          replace (c ≪ 16) with (c * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
          replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * 0))) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
          eapply evt_cut.
          { eapply x2_l1_len8 with (DT := DT) (SYM := WK + 736) (m0 := m0) (cw0 := cw) (pos := pos) (cnt := cnt) (bg := bg) (nb := c) (s := 0)
                                   (j := Z.to_nat (cnt - 0)) (syb := syb); try eassumption; try lia; try reflexivity.
            - apply munch_refl.
            - apply wmono_refl.
            - exact (conj CW CWL).
            - replace (8 * 0) with 0 by lia. apply cells_written_refl. }
          unfold x2_l1_post. post_call psegs m0.
          lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
            pose proof (pref2_write cur cw cwn pos (8 * cnt) (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
            eapply (KONT mm cwn (Z.max cur (pos + 8 * cnt))); [| exact PR' | lia] end.
          unfold X2G. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [reflexivity|].
          split; [eassumption|]. split; [eassumption|]. split; eassumption.
        - (* [comment removed for export] *)
          if_cases K1; zify_lts K1; [|exfalso; lia].
          zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
          zstep. if_cases K2b; zify_cond K2b; [|exfalso; lia].
          zstep. if_cases K3; zify_cond K3; [eapply KZ; [exact I1 | lia]|].
          do 9 zstep.
          replace (c ≪ 16) with (c * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
          rewrite (Z.mod_small (c * 65536 + 16777216) 18446744073709551616) by lia.
          rewrite (Z.mod_small (c * 65536 + 16777216) 4294967296) by lia.
          rewrite (Z.mod_small len1 4294967296) by lia.
          replace (len1 ≪ 2) with (4 * len1) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
          replace (Z_to_bv 64 (DT + 4 + 4 * pos)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + 0))) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
          replace (Z_to_bv 64 (WK + 736 + (bg + cnt))) with (Z_to_bv 64 (WK + 736 + bg + cnt)) by (f_equal; lia).
          eapply evt_cut.
          { eapply x2_l1_def with (DT := DT) (SYM := WK + 736) (m0 := m0) (cw0 := cw) (pos := pos) (cnt := cnt) (bg := bg) (nb := c) (s := 0) (off := 0)
                                   (len := len1) (Q := Q) (j := Z.to_nat (cnt - 0)) (syb := syb); try eassumption; try lia; try reflexivity.
            - apply munch_refl.
            - apply wmono_refl.
            - exact (conj CW CWL).
            - apply cells_written_refl. }
          unfold x2_l1_post. post_call psegs m0.
          lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
            pose proof (pref2_write cur cw cwn pos (len1 * cnt) (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(apply Z.mul_nonneg_nonneg; lia)) as PR';
            eapply (KONT mm cwn (Z.max cur (pos + len1 * cnt))); [| exact PR' | lia] end.
          unfold X2G. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
          split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [reflexivity|].
          split; [eassumption|]. split; [eassumption|]. split; eassumption. }
    (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    { eapply KZ; [| lia].
      unfold X2G. split; [exact HDRC|]. split; [split; [exact CW | exact CWL]|]. split; [exact RVA|]. split; [exact RKA|]. split; [exact RSA|].
      split; [exact SYB|]. split; [exact SYLEN|]. split; [exact SYS|]. split; [exact WKR|]. split; [exact FR|]. split; [reflexivity|].
      split; [exact STK|]. split; [exact MI|]. split; [exact MU | exact WM]. }
    zstep. zstep.
    assert (ERAW : bv_swrap 32 (c + (tl + 1 - T) mod 18446744073709551616) = c + (tl + 1 - T)).
    { apply swrap32_eqm; [lia|].
      destruct (Z_lt_le_dec (tl + 1 - T) 0) as [NEG|POS0].
      - replace ((tl + 1 - T) mod 18446744073709551616) with (tl + 1 - T + 18446744073709551616)
          by (symmetry; rewrite <- (Z.mod_add _ 1) by lia; apply Z.mod_small; lia).
        replace (c + (tl + 1 - T + 18446744073709551616) - (c + (tl + 1 - T))) with (4294967296 * 4294967296) by lia.
        apply Z.mod_mul. lia.
      - rewrite (Z.mod_small (tl + 1 - T) 18446744073709551616) by lia. replace (c + (tl + 1 - T) - (c + (tl + 1 - T))) with 0 by lia. reflexivity. }
    rewrite ERAW. remember (c + (tl + 1 - T)) as rawmw eqn:ERM.
    zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (CUTM : forall y5 y10, y5 = Z_to_bv 64 (Z.max 1 rawmw) ->
                evt psegs POSTK (STL 0x1d314 mm (Z_to_bv 64 pos) y5 x7 x8 x9 y10 (Z_to_bv 64 len1) (Z_to_bv 64 (tl + 1 - maxW)) x13 (Z_to_bv 64 (WK + 676 + 4 * (w + 1)))
                                     (Z_to_bv 64 c) (Z_to_bv 64 (w + 1)) x21 x22 (Z_to_bv 64 WK) (Z_to_bv 64 (bg + cnt)) (Z_to_bv 64 bg) x28 x29)) end.
    { intros y5 y10 EY5. subst y5.
      zstep. zstep. zstep. zstep.
      assert (E52 : (c ≪ 32 mod 18446744073709551616 * 223338299392) ≫ 64 = 52 * c).
      { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (change (2^32) with 4294967296; lia).
        rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^64) with 18446744073709551616.
        replace (c * 4294967296 * 223338299392) with (52 * c * 18446744073709551616) by lia. apply Z.div_mul. lia. }
      rewrite E52.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K5; zify_lts K5; [|exfalso; lia].
      zstep. zstep. zstep. zstep.
      replace ((1 `max` rawmw) ≪ 2) with (4 * (1 `max` rawmw)) in FR by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (c ≪ 16) with (c * 65536) in FR by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite <- XSS in FR.
      replace (Z_to_bv 64 (c + (tl + 1))) with (Z_to_bv 64 (c + tl + 1)) by (f_equal; lia).
      assert (CRW : tl + 1 - maxW <= c <= T - (tl + 1 - maxW)) by lia.
      assert (IS : X2G m SPV lo DT WK wksz
                     (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK c0 c8 hdr3 r0 hdrw (tl + 1 - T) maxW (tl + 1 - maxW) (tl + 1)
                        (C8 (Z_to_bv 64 (WK + 52 * c + 4 * (1 `max` rawmw)))) (C8 (Z_to_bv 64 (w + 1))) (C8 (Z_to_bv 64 (xs1 rank (w + 1))))
                        (C8 (Z_to_bv 64 (c * 65536 + 16777216))) (C8 (Z_to_bv 64 rawmw)) wn wt) hdr cw rvl rank rs0 syb m0).
      { unfold X2G, x2_frame. split; [exact HDRC|]. split; [split; [exact CW | exact CWL]|]. split; [exact RVA|]. split; [exact RKA|]. split; [exact RSA|].
        split; [exact SYB|]. split; [exact SYLEN|]. split; [exact SYS|]. split; [exact WKR|]. split; [exact FR|]. split; [reflexivity|].
        split; [exact STK|]. split; [exact MI|]. split; [exact MU | exact WM]. }
      clear FR. subst rawmw len1 pos bg c.
      eapply (x2_sym_loop gp tp F fc m SPV lo DT WK wksz GEO ws rank tl T maxW rvl rs0 OK TT MAXW HIGH MOD ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 hdr3 hdrw wn wt r0
                w WR CRW (Z.to_nat (xs1 rank (w + 1) - xs1 rank w)) m0 hdr cw syb cur (xs1 rank w) (rv0 rank tl T w) POSTK);
        try eassumption; try lia.
      intros m2 cw' cur' z1 z5 z8 z9 z10 z12 z13 z14 z17 z21 z22 z25 z26 z27 z28 z29 I2 PR2 CUR2.
      eapply KONT; [exact I2 | exact PR2 | exact CUR2]. }
    if_cases K4; zify_lts K4.
    - eapply CUTM. f_equal. lia.
    - zstep. eapply CUTM. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w_loop : forall j m1 hdr cw syb cur w v112 v120 v128 v136 v144 (POSTK : machine_state -> Prop) x1 x5 x7 x8 x9 x11 x12 x13 x14 x16 x17 x21 x22 x26 x27 x28 x29,
    Z.to_nat (maxW + 1 - w) = j ->
    X2G m SPV lo DT WK wksz (FRW v112 v120 v128 v136 v144) hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW ->
    (forall m2 cw' u112 u120 u128 u136 u144 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29,
       X2G m SPV lo DT WK wksz (FRW u112 u120 u128 u136 u144) hdr cw' rvl rank rs0 syb m2 -> PREF2 (2^T) cw' ->
       evt psegs POSTK (STL 0x1d9a0 m2 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29)) ->
    evt psegs POSTK (STL 0x1d258 m1 x1 x5 x7 x8 x9 (Z_to_bv 64 w) x11 x12 x13 x14 x16 x17 x21 x22 (Z_to_bv 64 WK) x26 x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ I PR CURL WR KEXIT; [exfalso; lia|].
    eapply (x2_w_body m1 hdr cw syb cur w v112 v120 v128 v136 v144 POSTK); try eassumption.
    intros m2 cw' cur' u112 u128 u136 u144 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29 I2 PR2 CUR2.
    pose proof I2 as I2'. open_x2g I2'. unfold x2_frame in FR.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - assert (EW : w = maxW) by lia. subst w.
      eapply KEXIT; [exact I2|].
      rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in CUR2.
      intros i Hi. apply PR2. lia.
    - eapply (IH m2 hdr cw' syb cur' (w + 1)); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  Notation POST := (huf_rd_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo true m).
  Lemma x2_exit : forall m1 hdr cw syb hdw h3 v112 v120 v128 v136 v144 x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x21 x22 x25 x26 x27 x28 x29,
    X2G m SPV lo DT WK wksz (FRW v112 v120 v128 v136 v144) hdr cw rvl rank rs0 syb m1 -> PREF2 (2^T) cw ->
    hdrw = Z_to_bv 64 hdw -> hdr3 = Z_to_bv 64 h3 -> hdw mod 256 = 12 -> 0 <= hdw < 4294967296 -> 0 <= r0 < 2^64 -> 1 <= T ->
    evt psegs POST (STL 0x1d9a0 m1 x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x21 x22 x25 x26 x27 x28 x29).
  Proof.
    intros until x29; intros I PR EHW EH3 HW12 HWR R0R T1. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
    destruct MOD as (RVLEN & RSLEN & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    subst hdrw hdr3.
    assert (HDRL : length hdr = 4%nat) by (destruct HDRC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in HDRC. rewrite <- (bytes_of_unsigned hdr) in HDRC.
    remember (map bv_unsigned hdr) as hz eqn:EHZ.
    assert (HZL : Z.of_nat (length hz) = 4) by (subst hz; rewrite length_map; lia).
    assert (HZB : Forall (fun c => 0 <= c < 256) hz) by (subst hz; apply bytes_unsigned_range).
    clear EHZ.
    zstep. zstep. zstep.
    replace (Z_to_bv 64 DT) with (Z_to_bv 64 (DT + 0)) by (f_equal; lia).
    u8_sok HDRC 0. zstep. u8_store HDRC 0 12; [rewrite HW12; reflexivity|].
    u8_sok HDRC 1. zstep. rewrite <- (le1_lit 1). u8_store HDRC 1 1; [reflexivity|].
    u8_sok HDRC 2. zstep. u8_store HDRC 2 T; [reflexivity|].
    zstep.
    u8_sok HDRC 3. zstep. u8_store HDRC 3 (h3 mod 256); [rewrite Z.mod_mod by lia; reflexivity|].
    zstep. zstep. do 13 zstep. zstep.
    lazymatch type of HDRC with u8arr _ _ _ (map _ ?l) => remember l as hz' eqn:EHZ' end.
    assert (HZ'L : Z.of_nat (length hz') = 4) by (subst hz'; rewrite !Zupd_length; exact HZL).
    assert (HZ'0 : Znth 0 hz' = 12 /\ Znth 1 hz' = 1 /\ Znth 2 hz' = T) by (subst hz'; repeat split; znth_upd; reflexivity).
    clear EHZ'.
    (* [comment removed for export] *)
    assert (DTC : u8arr psegs m1 DT (map (Z_to_bv 8) hz' ++ u16s (map (Z_to_bv 64) cw))).
    { apply (proj2 (u8arr_app psegs m1 DT _ _)). split; [exact HDRC|]. rewrite length_map. replace (DT + Z.of_nat (length hz')) with (DT + 4) by lia. exact CW. }
    (* [comment removed for export] *)
    assert (WKS : stk psegs m1 WK (WK + wksz)).
    { apply u8arr_of_u32arr in RVA, RKA, RSA. apply rw_cells_of_u8arr in RVA, RKA, RSA. apply stk_of_rw_cells in RVA, RKA, RSA.
      cbn [cells_size csize] in RVA, RKA, RSA. rewrite u32s_length, length_map in RVA, RKA, RSA.
      apply (stk_merge psegs m1 WK (WK + 624) (WK + wksz)); [replace (WK + 624) with (WK + Z.of_nat (4 * length rvl + 0)) by lia; exact RVA| |lia].
      apply (stk_merge psegs m1 (WK + 624) (WK + 676) (WK + wksz)); [replace (WK + 676) with (WK + 624 + Z.of_nat (4 * length rank + 0)) by lia; exact RKA| |lia].
      apply (stk_merge psegs m1 (WK + 676) (WK + 736) (WK + wksz)); [replace (WK + 736) with (WK + 676 + Z.of_nat (4 * length rs0 + 0)) by lia; exact RSA| |lia].
      apply (stk_merge psegs m1 (WK + 736) (WK + 992) (WK + wksz)); [exact SYS | exact WKR | lia]. }
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    assert (STK' : stk psegs m1 lo SPV).
    { apply (stk_merge psegs m1 lo (SPV + -272) SPV STK); [|lia]. replace SPV with (SPV + -272 + Z.of_nat 272) at 2 by lia. exact FR. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 14 eexists. exists m1, r0, (map (Z_to_bv 8) hz' ++ u16s (map (Z_to_bv 64) cw)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|]. split; [exact WKS|]. split; [exact DTC|].
    destruct HZ'0 as (H0 & H1 & H2).
    set (dtb' := map (Z_to_bv 8) hz' ++ u16s (map (Z_to_bv 64) cw)).
    assert (NTHH : forall k, 0 <= k < 4 -> nth_error dtb' (Z.to_nat k) = Some (Z_to_bv 8 (Znth k hz'))).
    { intros k Hk. unfold dtb'. rewrite nth_error_app1 by (rewrite length_map; lia). apply nth_error_map_Znth. lia. }
    assert (NTHC : forall k : nat, nth_error dtb' (4 + k) = nth_error (u16s (map (Z_to_bv 64) cw)) k).
    { intros k. unfold dtb'. rewrite nth_error_app2 by (rewrite length_map; lia). f_equal. rewrite length_map. lia. }
    assert (HDROK : huf_hdr_ok dtb').
    { split; [unfold dtb', HUF_DTABLE_BYTES; rewrite length_app, length_map, u16s_length, length_map; lia|].
      rewrite <- H0. exact (NTHH 0 ltac:(lia)). }
    split; [exact HDROK|]. split; [exact R0R|]. intros _.
    assert (P2 : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    split.
    - split; [exact HDROK|]. exists (Z_to_bv 8 1), T.
      split; [rewrite <- H1; exact (NTHH 1 ltac:(lia))|]. split; [rewrite <- H2; exact (NTHH 2 ltac:(lia))|]. split; [lia|].
      split.
      + intros _ i Hi. destruct (PR i Hi) as (_ & LEN). exists (Z_to_bv 8 ((Znth (2 * i + 1) cw / 256) mod 256)). split.
        * replace (Z.to_nat (4 * i + 7)) with (4 + (2 * Z.to_nat (2 * i + 1) + 1))%nat by lia. rewrite NTHC. apply u16s_nth_hi. lia.
        * rewrite byte_lit by (apply Z.mod_pos_bound; lia). exact LEN.
      + change (negb (bv_unsigned (Z_to_bv 8 1) =? 0)) with true. intros i Hi. destruct (PR i Hi) as (NB & _).
        exists (Z_to_bv 8 (Znth (2 * i + 1) cw mod 256)). split.
        * replace (Z.to_nat (4 * i + 6)) with (4 + (2 * Z.to_nat (2 * i + 1)))%nat by lia. rewrite NTHC. apply u16s_nth_lo. lia.
        * rewrite byte_lit by (apply Z.mod_pos_bound; lia). lia.
    - exists (Z_to_bv 8 1). split; [rewrite <- H1; exact (NTHH 1 ltac:(lia))|]. split; [intros _; reflexivity | intros _ E; discriminate E].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_fill : forall m1 hdr cw syb hdw h3 v112 v120 v128 v136 v144 x1 x5 x7 x8 x9 x11 x12 x13 x14 x16 x17 x21 x22 x26 x27 x28 x29,
    X2G m SPV lo DT WK wksz (FRW v112 v120 v128 v136 v144) hdr cw rvl rank rs0 syb m1 ->
    hdrw = Z_to_bv 64 hdw -> hdr3 = Z_to_bv 64 h3 -> hdw mod 256 = 12 -> 0 <= hdw < 4294967296 -> 0 <= r0 < 2^64 ->
    evt psegs POST (STL 0x1d258 m1 x1 x5 x7 x8 x9 (Z_to_bv 64 1) x11 x12 x13 x14 x16 x17 x21 x22 (Z_to_bv 64 WK) x26 x27 x28 x29).
  Proof.
    intros until x29; intros I EHW EH3 HW12 HWR R0R.
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    eapply (x2_w_loop (Z.to_nat (maxW + 1 - 1)) m1 hdr cw syb 0 1 v112 v120 v128 v136 v144 POST); try eassumption; try lia.
    - intros i Hi. lia.
    - rewrite (rv0_1 rank tl T). lia.
    - intros m2 cw' u112 u120 u128 u136 u144 y1 y5 y7 y8 y9 y10 y11 y12 y13 y14 y16 y17 y21 y22 y25 y26 y27 y28 y29 I2 PR2.
      eapply (x2_exit m2 hdr cw' syb hdw h3 u112 u120 u128 u136 u144); try eassumption; lia.
  Qed.
End WL.
