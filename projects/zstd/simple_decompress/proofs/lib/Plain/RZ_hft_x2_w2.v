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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_l2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section W2.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DT WK wksz : Z).
  Hypothesis GEO : x2_geo SPV lo DT WK wksz.
  Variables (ws rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.
  Hypothesis MAXW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Hypothesis MOD : x2_models rank tl T maxW rvl rs0.

  (* [comment removed for export] *)
  Variables (c st bsym : Z).
  Hypothesis CR : tl + 1 - maxW <= c <= T - (tl + 1 - maxW).
  Hypothesis STR : 0 <= st.  Hypothesis STH : st + 2^(T - c) <= 2^T.
  Hypothesis BSR : 0 <= bsym < 256.

  Notation STW pc mm x1 x5 x8 x9 x10 x11 x13 x14 x17 x21 x22 x25 x26 x27 x28 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -272)) gp tp x5 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (WK + 52 * c)) x8 x9 x10 x11 (Z_to_bv 64 (bsym + 33554432)) x13 x14
             (Z_to_bv 64 (WK + 676)) (Z_to_bv 64 (c + tl + 1)) x17 (Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 8) x21 x22 (Z_to_bv 64 T) (Z_to_bv 64 (WK + 736))
             x25 x26 x27 x28 (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 1) (Z_to_bv 64 3))
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x2_w2_body : forall m1 fr hdr cw syb cur w2 (POSTK : machine_state -> Prop) x1 x5 x8 x9 x10 x11 x13 x14 x17 x21 x25 x26 x27 x28,
    X2G m SPV lo DT WK wksz fr hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> st + rvc rank tl T c w2 <= cur ->
    1 <= w2 <= maxW -> c <= T - (tl + 1 - w2) ->
    (forall m2 cw' cur' y5 y8 y9 y10 y14 y17 y21 y25 y26 y28,
       X2G m SPV lo DT WK wksz fr hdr cw' rvl rank rs0 syb m2 -> PREF2 cur' cw' -> st + rvc rank tl T c (w2 + 1) <= cur' ->
       evt psegs POSTK (STW 0x1d610 m2 x1 y5 y8 y9 y10 x11 x13 y14 y17 y21 (Z_to_bv 64 (w2 + 1)) y25 y26 x27 y28)) ->
    evt psegs POSTK (STW 0x1d614 m1 x1 x5 x8 x9 x10 x11 x13 x14 x17 x21 (Z_to_bv 64 w2) x25 x26 x27 x28).
  Proof.
    intros until x28; intros I PR CURL W2R CDIV KONT. open_geo GEO. open_x2g I.
    destruct MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    pose proof (rvc_nonneg ws rank tl T OK TT c w2 ltac:(lia) ltac:(lia)) as RVC0.
    pose proof (rvc_step rank tl T TT c w2 ltac:(lia) ltac:(lia) CDIV) as RVCS.
    pose proof (rvc_mono ws rank tl T OK TT c (w2 + 1) (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as RVCM1.
    rewrite (rvc_top ws rank tl T OK TT c maxW ltac:(lia) MAXW HIGH) in RVCM1.
    pose proof (xs1_step rank w2 ltac:(lia)) as XSS.
    pose proof (xs1_nonneg ws rank tl OK w2 ltac:(lia)) as XS0.
    pose proof (xs1_mono ws rank tl OK (w2 + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK w2 ltac:(lia)) as CNT0. pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ.
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (P2C : 1 <= 2^(T - c)) by (pose proof (Z.pow_pos_nonneg 2 (T - c) ltac:(lia) ltac:(lia)); lia).
    remember (c + tl + 1 - w2) as tb eqn:ETB.
    rewrite (swrap32_small tb) by lia.
    replace (w2 ≪ 2) with (4 * w2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace ((w2 + 1) ≪ 2) with (4 * (w2 + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 WK rvl (13 * c + w2) a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RVCM c w2 CR W2R) in RD.
    zstep. rewrite (zx32w_small (rvc rank tl T c w2)) by lia. clear RD.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 (WK + 676) rs0 w2 a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M w2 ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank w2)) by lia. clear RD.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 (WK + 676) rs0 (w2 + 1) a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M (w2 + 1) ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank (w2 + 1))) by lia. clear RD.
    zstep. rewrite (swrap32_small (T - tb)) by lia.
    zstep. rewrite (sllw_pow2 (T - tb)) by lia.
    zstep. zstep. zstep.
    replace (rvc rank tl T c w2 ≪ 2) with (4 * rvc rank tl T c w2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (T - (tl + 1 - w2) - c) with (T - tb) in RVCS by lia.
    remember (rvc rank tl T c w2) as rp eqn:ERP. remember (xs1 rank w2) as bg eqn:EBG. remember (Znth w2 rank) as cnt eqn:ECNT.
    rewrite XSS.
    remember (2^(T - tb)) as len2 eqn:ELEN.
    assert (LENC : (len2 = 1) \/ (len2 = 2) \/ (len2 = 4) \/ (len2 = 8) \/ (exists Q, 2 <= Q <= 256 /\ len2 = 8 * Q)).
    { subst len2. assert (E : T - tb = 0 \/ T - tb = 1 \/ T - tb = 2 \/ T - tb = 3 \/ 4 <= T - tb <= 11) by lia.
      destruct E as [E|[E|[E|[E|E]]]]; [rewrite E; auto | rewrite E; auto | rewrite E; auto | rewrite E; auto 6|].
      right; right; right; right. exists (2^(T - tb - 3)). split.
      - split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia].
      - change 8 with (2^3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (LEN0 : 1 <= len2 <= 2048) by (destruct LENC as [E|[E|[E|[E|(Q & QR & E)]]]]; lia).
    assert (POSH : st + rp + cnt * len2 <= 4096) by lia.
    assert (KZ : forall y5 y8 y9 y10 y14 y17 y21 y25 y26 y28, cnt = 0 ->
               evt psegs POSTK (STW 0x1d610 m1 x1 y5 y8 y9 y10 x11 x13 y14 y17 y21 (Z_to_bv 64 (w2 + 1)) y25 y26 x27 y28)).
    { intros. eapply KONT; [close_x2g | exact PR | lia]. }
    clear ELEN. zstep.
    destruct LENC as [L1|[L2|[L4|[L8|(Q & QR & LQ)]]]].
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [exfalso; lia|].
      zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. if_cases K3; zify_cond K3; [eapply KZ; lia|].
      do 3 zstep.
      replace (tb ≪ 16) with (tb * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      replace (Z_to_bv 64 (tb * 65536 + (bsym + 33554432))) with (Z_to_bv 64 (tb * 65536 + bsym + 33554432)) by (f_equal; lia).
      replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp + 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
      eapply evt_cut.
      { eapply x2_l2_len1 with (m0 := m1) (cw0 := cw) (pos := st + rp) (cnt := cnt) (bg := bg) (s := 0) (j := Z.to_nat (cnt - 0)) (syb := syb) (SYM := WK + 736);
          try eassumption; try lia; try reflexivity.
        - apply munch_refl.
        - apply wmono_refl.
        - apply cells_written_refl. }
      unfold x2_l2_post. post_call psegs m1.
      lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
        pose proof (pref2_write cur cw cwn (st + rp) cnt (tb + 512) PR PO (okw_val tb 2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
        eapply (KONT mm cwn (Z.max cur (st + rp + cnt))); [close_x2g | exact PR' | lia] end.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [exfalso; lia|].
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
      zstep. if_cases K3; zify_cond K3; [eapply KZ; lia|].
      do 3 zstep.
      replace (tb ≪ 16) with (tb * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      replace (Z_to_bv 64 (tb * 65536 + (bsym + 33554432))) with (Z_to_bv 64 (tb * 65536 + bsym + 33554432)) by (f_equal; lia).
      replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp + 2 * 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
      eapply evt_cut.
      { eapply x2_l2_len2 with (m0 := m1) (cw0 := cw) (pos := st + rp) (cnt := cnt) (bg := bg) (s := 0) (j := Z.to_nat (cnt - 0)) (syb := syb) (SYM := WK + 736);
          try eassumption; try lia; try reflexivity.
        - apply munch_refl.
        - apply wmono_refl.
        - replace (2 * 0) with 0 by lia. apply cells_written_refl. }
      unfold x2_l2_post. post_call psegs m1.
      lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
        pose proof (pref2_write cur cw cwn (st + rp) (2 * cnt) (tb + 512) PR PO (okw_val tb 2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
        eapply (KONT mm cwn (Z.max cur (st + rp + 2 * cnt))); [close_x2g | exact PR' | lia] end.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. if_cases K3; zify_cond K3; [eapply KZ; lia|].
      do 3 zstep.
      replace (tb ≪ 16) with (tb * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      replace (Z_to_bv 64 (tb * 65536 + (bsym + 33554432))) with (Z_to_bv 64 (tb * 65536 + bsym + 33554432)) by (f_equal; lia).
      replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp + 4 * 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
      eapply evt_cut.
      { eapply x2_l2_len4 with (m0 := m1) (cw0 := cw) (pos := st + rp) (cnt := cnt) (bg := bg) (s := 0) (j := Z.to_nat (cnt - 0)) (syb := syb) (SYM := WK + 736);
          try eassumption; try lia; try reflexivity.
        - apply munch_refl.
        - apply wmono_refl.
        - replace (4 * 0) with 0 by lia. apply cells_written_refl. }
      unfold x2_l2_post. post_call psegs m1.
      lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
        pose proof (pref2_write cur cw cwn (st + rp) (4 * cnt) (tb + 512) PR PO (okw_val tb 2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
        eapply (KONT mm cwn (Z.max cur (st + rp + 4 * cnt))); [close_x2g | exact PR' | lia] end.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
      zstep. if_cases K3; zify_cond K3; [eapply KZ; lia|].
      do 3 zstep.
      replace (tb ≪ 16) with (tb * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      replace (Z_to_bv 64 (tb * 65536 + (bsym + 33554432))) with (Z_to_bv 64 (tb * 65536 + bsym + 33554432)) by (f_equal; lia).
      replace (Z_to_bv 64 (bg + cnt - bg)) with (Z_to_bv 64 (cnt - 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp + 8 * 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
      eapply evt_cut.
      { eapply x2_l2_len8 with (m0 := m1) (cw0 := cw) (pos := st + rp) (cnt := cnt) (bg := bg) (s := 0) (j := Z.to_nat (cnt - 0)) (syb := syb) (SYM := WK + 736);
          try eassumption; try lia; try reflexivity.
        - apply munch_refl.
        - apply wmono_refl.
        - replace (8 * 0) with 0 by lia. apply cells_written_refl. }
      unfold x2_l2_post. post_call psegs m1.
      lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
        pose proof (pref2_write cur cw cwn (st + rp) (8 * cnt) (tb + 512) PR PO (okw_val tb 2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
        eapply (KONT mm cwn (Z.max cur (st + rp + 8 * cnt))); [close_x2g | exact PR' | lia] end.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. if_cases K2b; zify_cond K2b; [|exfalso; lia].
      zstep. if_cases K3; zify_cond K3; [eapply KZ; lia|].
      do 8 zstep.
      replace (tb ≪ 16) with (tb * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      rewrite (Z.mod_small (tb * 65536 + (bsym + 33554432)) 18446744073709551616) by lia.
      rewrite (Z.mod_small (tb * 65536 + (bsym + 33554432)) 4294967296) by lia.
      rewrite (Z.mod_small len2 4294967296) by lia.
      replace (len2 ≪ 2) with (4 * len2) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
      replace (Z_to_bv 64 (tb * 65536 + (bsym + 33554432))) with (Z_to_bv 64 (tb * 65536 + bsym + 33554432)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp + 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + bg)) with (Z_to_bv 64 (WK + 736 + bg + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 736 + (bg + cnt))) with (Z_to_bv 64 (WK + 736 + bg + cnt)) by (f_equal; lia).
      eapply evt_cut.
      { eapply x2_l2_def with (m0 := m1) (cw0 := cw) (pos := st + rp) (cnt := cnt) (bg := bg) (s := 0) (off := 0) (len := len2) (Q := Q)
                              (j := Z.to_nat (cnt - 0)) (syb := syb) (SYM := WK + 736);
          try eassumption; try lia; try reflexivity.
        - apply munch_refl.
        - apply wmono_refl.
        - apply cells_written_refl. }
      unfold x2_l2_post. post_call psegs m1.
      lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
        pose proof (pref2_write cur cw cwn (st + rp) (len2 * cnt) (tb + 512) PR PO (okw_val tb 2 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(nia)) as PR';
        eapply (KONT mm cwn (Z.max cur (st + rp + len2 * cnt))); [close_x2g | exact PR' | lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w2_loop : forall j m1 fr hdr cw syb cur w2 (POSTK : machine_state -> Prop) x1 x5 x8 x9 x10 x11 x13 x14 x17 x21 x25 x26 x27 x28,
    Z.to_nat (maxW + 1 - w2) = j ->
    X2G m SPV lo DT WK wksz fr hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> st + rvc rank tl T c w2 <= cur ->
    1 <= w2 <= maxW -> c <= T - (tl + 1 - w2) ->
    (forall m2 cw' cur' y5 y8 y9 y10 y14 y17 y21 y25 y26 y28,
       X2G m SPV lo DT WK wksz fr hdr cw' rvl rank rs0 syb m2 -> PREF2 cur' cw' -> st + 2^(T - c) <= cur' ->
       evt psegs POSTK (STW 0x1d4f0 m2 x1 y5 y8 y9 y10 x11 x13 y14 y17 y21 (Z_to_bv 64 (maxW + 1)) y25 y26 x27 y28)) ->
    evt psegs POSTK (STW 0x1d614 m1 x1 x5 x8 x9 x10 x11 x13 x14 x17 x21 (Z_to_bv 64 w2) x25 x26 x27 x28).
  Proof.
    induction j as [|j IH]; intros until x28; intros EJ I PR CURL W2R CDIV KONT; [exfalso; lia|].
    eapply (x2_w2_body m1 fr hdr cw syb cur w2 POSTK); try eassumption.
    intros m2 cw' cur' y5 y8 y9 y10 y14 y17 y21 y25 y26 y28 I2 PR2 CURL2.
    zstep. if_cases KB; zify_cond KB.
    - assert (EW : w2 = maxW) by lia. subst w2.
      eapply KONT; [exact I2 | exact PR2 |].
      assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
      rewrite (rvc_top ws rank tl T OK TT c maxW ltac:(lia) MAXW HIGH) in CURL2. exact CURL2.
    - eapply (IH m2 fr hdr cw' syb cur' (w2 + 1) POSTK); try eassumption; lia.
  Qed.
End W2.
