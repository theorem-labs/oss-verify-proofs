(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs RZ_hft_x2_sk RZ_hft_x2_w2 huf42_4_kit_scut.
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
  (* [comment removed for export] *)
  Variables (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 c16 hdr3 wn wt : word) (r0 : Z).
  (* [comment removed for export] *)
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
  Ltac chk := zstep; let K := fresh "K" in if_cases K; zify_cond K; [exfalso; rewrite ?signed_lit, ?zb_lxor_ones in K by lia; lia | clear K].
  Ltac sdec := repeat match goal with
    | |- context [Z.lxor ?a 9223372036854775808] =>
        change 9223372036854775808 with (2^63); rewrite (zb_lxor_sign a) by lia; rewrite (Z.mod_small (a + 2^63)) by lia
    | |- context [Z.ltb ?a ?b] => first [rewrite (proj2 (Z.ltb_ge a b)) by lia | rewrite (proj2 (Z.ltb_lt a b)) by lia]
    | |- context [Z.b2z false] => change (Z.b2z false) with 0
    | |- context [Z.b2z true] => change (Z.b2z true) with 1 end; zsimp.
  Ltac cl := unfold X2G, x2_cells; repeat (split; [first [eassumption | reflexivity | split; eassumption]|]); first [eassumption | reflexivity].

  (* [comment removed for export] *)
  Lemma x2_sym_body : forall m1 hdr cw syb cur s st k280 (POSTK : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz (FRS k280) hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> st <= cur ->
    bg <= s < en -> st = rv0 rank tl T w + (s - bg) * len1 ->
    (forall m2 cw' cur' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y24 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRS (Z_to_bv 64 st)) hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' -> st + len1 <= cur' ->
       evt usegs POSTK (STS 0x1fad8 m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y24 (Z_to_bv 64 s) y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STS 0x1f8c4 m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 st) x17 (Z_to_bv 64 (DT + 4)) x20 x21 x24 (Z_to_bv 64 s)
                         x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PR CURL SR EST KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
    destruct MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as BG0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ.
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    pose proof (rv0_step rank tl T TT w ltac:(lia)) as RV0S.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as RV00.
    pose proof (rv0_mono ws rank tl T OK TT (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)) as RV0M1.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RV0M1.
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (LEN1R : 2 <= len1 <= 2048) by (split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (STR : 0 <= st /\ st + len1 <= 2^T).
    { assert (A : (s - bg + 1) * len1 <= Znth w rank * len1) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (B : 0 <= (s - bg) * len1) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite EST. split; lia. }
    zstep. replace (st ≪ 2) with (4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. chk.
    zstep. zstep. zstep. zstep. sdec.
    chk.
    zstep. chk.
    zstep. zstep. zstep. zstep. sdec.
    chk.
    zstep.
    lbyte SYB.
    lazymatch goal with |- context [bv_unsigned (nth ?k syb ?d)] =>
      assert (BSR : 0 <= bv_unsigned (nth k syb d) < 256) by (pose proof (bv_unsigned_in_range 8 (nth k syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth k syb d)) as bsym eqn:EBS; clear EBS end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mS end.
    assert (CUT : forall mm cwm curm y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y27 y28 y29 y30 y31,
              X2G m SPV lo DT WK wksz (FRS (Z_to_bv 64 st)) hdr cwm rvl rank rs0 syb mm -> PREF2T T curm cwm -> st + rvc rank tl T c minW <= curm ->
              evt usegs POSTK (STS 0x1fa28 mm y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 (Z_to_bv 64 bsym) y21 y24 (Z_to_bv 64 s)
                                   (Z_to_bv 64 (DT + 4 + 4 * st)) y27 y28 y29 y30 y31)).
    { intros mm cwm curm y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y27 y28 y29 y30 y31 IM PRM CURM.
      eapply x2_sym_cut. all: try exact IM. all: try exact KONT. all: try eassumption. all: lia. }
    zstep. zstep.
    zstep. if_cases KA; zify_lts KA.
    - (* [comment removed for export] *)
      assert (EMW : minW = 1) by lia.
      eapply CUT; [cl | exact PR |].
      rewrite EMW. rewrite (rvc_1 rank tl T c ltac:(lia)). lia.
    - assert (EMW : minW = rawmw) by lia.
      zstep. chk.
      zstep. zstep. zstep. zstep.
      replace (c * 65536 + 16777216) with ((c + 256) * 65536) by lia.
      destruct (x2_X_val (c + 256) bsym ltac:(lia) ltac:(lia)) as (EX & XH & XR). rewrite EX.
      remember ((c + 256) * 65536 + bsym) as X eqn:EXV.
      rewrite (Z.mod_small X 4294967296) by lia.
      zstep.
      pose proof (x2_D_words X XR) as (DR & W1 & W3). cbv zeta in DR, W1, W3. rewrite XH in W1, W3.
      remember (Z.lor ((X ≪ 32) mod 18446744073709551616) X) as D eqn:ED. clear ED.
      assert (HW1 : hidden ((D ≫ 16) mod 2^16 = c + 256)) by exact W1.
      assert (HW3 : hidden ((D ≫ 48) mod 2^16 = c + 256)) by exact W3.
      clear W1 W3.
      do 5 zstep.
      pose proof (rvc_nonneg ws rank tl T OK TT c minW ltac:(lia) ltac:(lia)) as SK0.
      pose proof (rvc_mono ws rank tl T OK TT c minW (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as SKH.
      rewrite (rvc_top ws rank tl T OK TT c maxW ltac:(lia) MAXW HIGH) in SKH.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply evt_cut.
        { eapply x2_sk_len2 with (DT := DT) (m0 := mS) (cw0 := cw) (pos := st) (nb := c) (D := D); try eassumption; try lia; try reflexivity.
          all: first [apply munch_refl | apply wmono_refl | split; eassumption]. }
        unfold x2_sk_post. post_call usegs mS.
        lazymatch goal with PO : cells_written cw ?cwn _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (pref2T_write T cur cw cwn st 2 (c + 256) PR PO (okwT_val T c 1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
          eapply (CUT mm cwn (Z.max cur (st + 2))); [cl | exact PR' | lia] end.
      + zstep. zstep. if_cases K4; zify_cond K4.
        2:{ (* [comment removed for export] *)
            eapply evt_cut.
            { eapply x2_sk_len4 with (DT := DT) (m0 := mS) (cw0 := cw) (pos := st) (nb := c) (D := D); try eassumption; try lia; try reflexivity.
              all: first [apply munch_refl | apply wmono_refl | split; eassumption]. }
            unfold x2_sk_post. post_call usegs mS.
            lazymatch goal with PO : cells_written cw ?cwn _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
              pose proof (pref2T_write T cur cw cwn st 4 (c + 256) PR PO (okwT_val T c 1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
              eapply (CUT mm cwn (Z.max cur (st + 4))); [cl | exact PR' | lia] end. }
        (* [comment removed for export] *)
        zstep.
        lazymatch goal with |- _ => let a := cur_mem_addr in
          pose proof (u32_znth usegs mS WK rvl (13 * c + minW) a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
        rewrite (RVCM c minW CR ltac:(lia)) in RD.
        zstep. rewrite (sx32w_small (rvc rank tl T c minW)) by lia. clear RD.
        remember (rvc rank tl T c minW) as sk eqn:ESK.
        zstep. if_cases K5; zify_lts K5.
        { (* [comment removed for export] *)
          eapply (CUT mS cw cur); [cl | exact PR | lia]. }
        do 4 zstep.
        assert (L8 : exists Q, 1 <= Q <= 256 /\ len1 = 8 * Q).
        { assert (E : 3 <= T - c <= 11) by (split; [|lia]; destruct (Z.le_gt_cases 3 (T - c)) as [G|G]; [exact G|]; exfalso;
            assert (C : T - c = 1 \/ T - c = 2) by lia; destruct C as [C|C]; rewrite C in K2, K4; cbn in K2, K4; lia).
          exists (2^(T - c - 3)). split.
          - split; [pose proof (Z.pow_pos_nonneg 2 (T - c - 3) ltac:(lia) ltac:(lia)); lia | change 256 with (2^8); apply Z.pow_le_mono_r; lia].
          - change 8 with (2^3). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        destruct L8 as (Q & QR & L8).
        remember ((sk - 1) / 8) as nq eqn:ENQ.
        assert (NQR : 0 <= nq /\ 8 * nq <= sk - 1 < 8 * nq + 8) by (subst nq; Z.div_mod_to_equations; lia).
        assert (NQH : 8 * (nq + 1) <= len1) by (rewrite L8 in *; lia).
        replace (Z_to_bv 64 (DT + 4 + 4 * st)) with (Z_to_bv 64 (DT + 4 + 4 * (st + 8 * 0))) by (f_equal; lia).
        setreg 15 (Z_to_bv 64 (DT + 20 + 4 * (st + 8 * 0))) ltac:(f_equal; lia).
        eapply evt_cut.
        { eapply x2_sk_loop with (DT := DT) (m0 := mS) (cw0 := cw) (pos := st) (nb := c) (D := D) (q := 0) (NQ := nq + 1) (j := Z.to_nat (nq + 1 - 0));
            try eassumption; try lia; try reflexivity.
          all: first [apply munch_refl | apply wmono_refl | apply cells_written_refl | split; eassumption | f_equal; lia]. }
        unfold x2_sk_post. post_call usegs mS.
        replace (Z_to_bv 64 (DT + 4 + 4 * (st + 8 * 0))) with (Z_to_bv 64 (DT + 4 + 4 * st)) by (f_equal; lia).
        lazymatch goal with PO : cells_written cw ?cwn _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (pref2T_write T cur cw cwn st (8 * (nq + 1)) (c + 256) PR PO (okwT_val T c 1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
          eapply (CUT mm cwn (Z.max cur (st + 8 * (nq + 1)))); [cl | exact PR' | lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sym_loop : forall j m1 hdr cw syb cur s st k280 (POSTK : machine_state -> Prop) x5 x6 x7 x10 x11 x12 x13 x14 x15 x17 x20 x21 x24 x26 x27 x28 x29 x30 x31,
    Z.to_nat (en - s) = j ->
    X2G m SPV lo DT WK wksz (FRS k280) hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> st <= cur ->
    bg <= s < en -> st = rv0 rank tl T w + (s - bg) * len1 ->
    (forall m2 cw' cur' u280 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y24 y25 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRS u280) hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' -> rv0 rank tl T (w + 1) <= cur' ->
       evt usegs POSTK (STS 0x1f6fc m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (DT + 4)) y20 y21 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STS 0x1f8c4 m1 x5 x6 x7 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 st) x17 (Z_to_bv 64 (DT + 4)) x20 x21 x24 (Z_to_bv 64 s)
                         x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I PR CURL SR EST KONT; [exfalso; lia|].
    eapply (x2_sym_body m1 hdr cw syb cur s st k280 POSTK); try eassumption.
    intros m2 cw' cur' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y24 y26 y27 y28 y29 y30 y31 I2 PR2 CUR2.
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as BG0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ.
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    pose proof (rv0_step rank tl T TT w ltac:(lia)) as RV0S.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as RV00.
    pose proof (rv0_mono ws rank tl T OK TT (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)) as RV0M1.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RV0M1.
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (LEN1R : 2 <= len1 <= 2048) by (split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 2048 with (2^11); apply Z.pow_le_mono_r; lia]).
    assert (STR : 0 <= st /\ st + len1 <= 2^T).
    { assert (A : (s - bg + 1) * len1 <= Znth w rank * len1) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (B : 0 <= (s - bg) * len1) by (apply Z.mul_nonneg_nonneg; lia).
      rewrite EST. split; lia. }
    open_x2g I2. unfold x2_frame in FR.
    zstep. zstep.
    repeat match goal with |- context [bv_swrap 32 ?z] => rewrite (swrap32_small z) by lia end.
    zstep.
    if_cases K; [exfalso; unfold bv_lts in K; rewrite !signed_lit in K by lia; zify_cond K; lia | clear K].
    zstep. zstep. zstep.
    repeat match goal with |- context [bv_swrap 32 ?z] => rewrite (swrap32_small z) by lia end.
    zstep. zstep. zstep. zstep.
    if_cases KB; zify_cond KB; repeat (rewrite Z.mod_small in KB by lia).
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1f8c4) _ _ _ _) =>
        eapply (IH m2 hdr cw' syb cur' (s + 1) (st + len1) (Z_to_bv 64 st) POSTK); try eassumption; try lia;
        close_x2g
    | |- _ =>
        (* [comment removed for export] *)
        zstep;
        eapply (KONT m2 cw' cur' (Z_to_bv 64 st)); [close_x2g | exact PR2 |];
        rewrite RV0S; assert (E : Znth w rank = s - bg + 1) by lia; rewrite E; lia
    end.
  Qed.
End SYMS.
