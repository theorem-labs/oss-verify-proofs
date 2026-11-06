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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_sk RZ_hft_x2_w2.
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
  (* [comment removed for export] *)
  Variables (ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 c0 c8 hdr3 hdrw wn wt : word) (r0 : Z).
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

  Notation FRS := (x2_frame ra0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK c0 c8 hdr3 r0 hdrw (tl + 1 - T) maxW (tl + 1 - maxW) (tl + 1)
                     (C8 (Z_to_bv 64 (WK + 52 * c + 4 * minW))) (C8 (Z_to_bv 64 (w + 1))) (C8 (Z_to_bv 64 en))
                     (C8 (Z_to_bv 64 (c * 65536 + 16777216))) (C8 (Z_to_bv 64 rawmw)) wn wt).

  Notation STS pc mm x1 x5 x8 x9 x10 x12 x13 x14 x17 x21 x22 x25 x26 x27 x28 x29 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -272)) gp tp x5 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (WK + 52 * c)) x8 x9 x10 (Z_to_bv 64 len1) x12 x13 x14
             (Z_to_bv 64 (WK + 676)) (Z_to_bv 64 (c + tl + 1)) x17 (Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 8) x21 x22 (Z_to_bv 64 T) (Z_to_bv 64 (WK + 736))
             x25 x26 x27 x28 x29 (Z_to_bv 64 1) (Z_to_bv 64 3))
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x2_sym_body : forall m1 hdr cw syb cur s st (POSTK : machine_state -> Prop) x8 x9 x10 x12 x13 x14 x17 x21 x22 x25 x26 x28 x29,
    X2G m SPV lo DT WK wksz FRS hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> st <= cur ->
    bg <= s < en -> st = rv0 rank tl T w + (s - bg) * len1 ->
    (forall m2 cw' cur' y5 y8 y9 y10 y12 y14 y17 y21 y22 y25 y26 y28 y29,
       X2G m SPV lo DT WK wksz FRS hdr cw' rvl rank rs0 syb m2 -> PREF2 cur' cw' -> st + len1 <= cur' ->
       evt psegs POSTK (STS 0x1d4f0 m2 (Z_to_bv 64 st) y5 y8 y9 y10 y12 (Z_to_bv 64 minW) y14 y17 y21 y22 y25 y26 (Z_to_bv 64 s) y28 y29)) ->
    evt psegs POSTK (STS 0x1d508 m1 (Z_to_bv 64 st) (Z_to_bv 64 minW) x8 x9 x10 x12 x13 x14 x17 x21 x22 x25 x26 (Z_to_bv 64 s) x28 x29).
  Proof.
    intros until x29; intros I PR CURL SR EST KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR.
    destruct MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    zstep.
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
    lbyte SYB.
    lazymatch goal with |- context [bv_unsigned (nth ?k syb ?d)] =>
      assert (BSR : 0 <= bv_unsigned (nth k syb d) < 256) by (pose proof (bv_unsigned_in_range 8 (nth k syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth k syb d)) as bsym eqn:EBS; clear EBS end.
    zstep. rewrite (swrap32_small (st + 0)) by lia. replace (st + 0) with st by lia.
    zstep. zstep. zstep. zstep.
    replace (st ≪ 2) with (4 * st) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (CUT2 : forall mm cwm curm y8 y9 y10 y12 y13 y17 y21 y22 y28,
              X2G m SPV lo DT WK wksz FRS hdr cwm rvl rank rs0 syb mm -> PREF2 curm cwm -> st + rvc rank tl T c minW <= curm ->
              evt psegs POSTK (STS 0x1d5fc mm (Z_to_bv 64 st) (Z_to_bv 64 minW) y8 y9 y10 y12 y13 (Z_to_bv 64 bsym) y17 y21 y22 x25 x26 (Z_to_bv 64 s) y28 (Z_to_bv 64 (DT + 4 + 4 * st)))).
    { intros mm cwm curm y8 y9 y10 y12 y13 y17 y21 y22 y28 IM PRM CURM.
      zstep. zstep.
      replace (Z.lor bsym 33554432) with (bsym + 33554432)
        by (rewrite Z.lor_comm; change 33554432 with (512 * 2^16); rewrite lor_disj_add by (try lia; change (2^16) with 65536; lia); lia).
      zstep. zstep. zstep.
      eapply (x2_w2_loop gp tp F fc m SPV lo DT WK wksz GEO ws rank tl T maxW rvl rs0 OK TT MAXW HIGH MOD c st bsym CR ltac:(lia) ltac:(lia) ltac:(lia)
                (Z.to_nat (maxW + 1 - minW)) mm FRS hdr cwm syb curm minW POSTK); try eassumption; try lia.
      intros m2 cw' cur' y5' y8' y9' y10' y14' y17' y21' y25' y26' y28' I2 PR2 CUR2.
      eapply KONT; eassumption. }
    zstep.
    if_cases KA; zify_lts KA.
    - (* [comment removed for export] *)
      assert (EMW : minW = 1) by lia.
      eapply (CUT2 m1 cw cur); [close_x2g | exact PR |].
      rewrite EMW. rewrite (rvc_1 rank tl T c ltac:(lia)). lia.
    - assert (EMW : minW = rawmw) by lia.
      zstep.
      zstep. zstep. zstep. zstep.
      replace (c * 65536 + 16777216) with ((c + 256) * 65536) by lia.
      destruct (x2_X_val (c + 256) bsym ltac:(lia) ltac:(lia)) as (EX & XH & XR). rewrite EX.
      remember ((c + 256) * 65536 + bsym) as X eqn:EXV.
      rewrite (Z.mod_small X 4294967296) by lia.
      pose proof (x2_D_words X XR) as (DR & W1 & W3). cbv zeta in DR, W1, W3. rewrite XH in W1, W3.
      remember (Z.lor ((X ≪ 32) mod 18446744073709551616) X) as D eqn:ED. clear ED.
      assert (HW1 : hidden ((D ≫ 16) mod 2^16 = c + 256)) by exact W1.
      assert (HW3 : hidden ((D ≫ 48) mod 2^16 = c + 256)) by exact W3.
      clear W1 W3.
      zstep. zstep. zstep.
      pose proof (rvc_nonneg ws rank tl T OK TT c minW ltac:(lia) ltac:(lia)) as SK0.
      pose proof (rvc_mono ws rank tl T OK TT c minW (maxW + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as SKH.
      rewrite (rvc_top ws rank tl T OK TT c maxW ltac:(lia) MAXW HIGH) in SKH.
      zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply evt_cut.
        { eapply x2_sk_len2 with (DT := DT) (m0 := m1) (cw0 := cw) (pos := st) (nb := c) (D := D); try eassumption; try lia; try reflexivity.
          - apply munch_refl.
          - apply wmono_refl. }
        unfold x2_sk_post. post_call psegs m1.
        lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
          pose proof (pref2_write cur cw cwn st 2 (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
          eapply (CUT2 mm cwn (Z.max cur (st + 2))); [close_x2g | exact PR' | lia] end.
      + zstep. if_cases K4; zify_cond K4.
        2:{ (* [comment removed for export] *)
            eapply evt_cut.
            { eapply x2_sk_len4 with (DT := DT) (m0 := m1) (cw0 := cw) (pos := st) (nb := c) (D := D); try eassumption; try lia; try reflexivity.
              - apply munch_refl.
              - apply wmono_refl. }
            unfold x2_sk_post. post_call psegs m1.
            lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
              pose proof (pref2_write cur cw cwn st 4 (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
              eapply (CUT2 mm cwn (Z.max cur (st + 4))); [close_x2g | exact PR' | lia] end. }
        (* [comment removed for export] *)
        zstep.
        lazymatch goal with |- _ => let a := cur_mem_addr in
          pose proof (u32_znth psegs m1 WK rvl (13 * c + minW) a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
        rewrite (RVCM c minW CR ltac:(lia)) in RD.
        zstep. rewrite (sx32w_small (rvc rank tl T c minW)) by lia. clear RD.
        remember (rvc rank tl T c minW) as sk eqn:ESK.
        zstep. if_cases K5; zify_lts K5.
        { (* [comment removed for export] *)
          eapply (CUT2 m1 cw cur); [close_x2g | exact PR | lia]. }
        do 7 zstep.
        assert (LM : Z.land ((sk ≪ 2 + -4) mod 18446744073709551616) 18446744073709551584 = 32 * ((sk - 1) / 8)).
        { assert (SKR : 1 <= sk <= 2048) by lia. clear - SKR.
          assert (B : forallb (fun q => Z.land ((q ≪ 2 + -4) mod 18446744073709551616) 18446744073709551584 =? 32 * ((q - 1) / 8))
                        (map Z.of_nat (seq 1 2048)) = true) by (vm_compute; reflexivity).
          rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat sk). split; [lia|]. apply in_seq. lia. }
        rewrite LM.
        zstep.
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
        replace (Z_to_bv 64 (DT + 20 + 4 * st)) with (Z_to_bv 64 (DT + 20 + 4 * (st + 8 * 0))) by (f_equal; lia).
        replace (Z_to_bv 64 (DT + 52 + 4 * st + 32 * nq)) with (Z_to_bv 64 (DT + 20 + 4 * (st + 8 * (nq + 1)))) by (f_equal; lia).
        eapply evt_cut.
        { eapply x2_sk_loop with (DT := DT) (m0 := m1) (cw0 := cw) (pos := st) (nb := c) (D := D) (q := 0) (NQ := nq + 1) (j := Z.to_nat (nq + 1 - 0));
            try eassumption; try lia; try reflexivity.
          - apply munch_refl.
          - apply wmono_refl.
          - apply cells_written_refl. }
        unfold x2_sk_post. post_call psegs m1.
        lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
          pose proof (pref2_write cur cw cwn st (8 * (nq + 1)) (c + 256) PR PO (okw_val c 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
          eapply (CUT2 mm cwn (Z.max cur (st + 8 * (nq + 1)))); [close_x2g | exact PR' | lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_sym_loop : forall j m1 hdr cw syb cur s st (POSTK : machine_state -> Prop) x8 x9 x10 x12 x13 x14 x17 x21 x22 x25 x26 x28 x29,
    Z.to_nat (en - s) = j ->
    X2G m SPV lo DT WK wksz FRS hdr cw rvl rank rs0 syb m1 -> PREF2 cur cw -> st <= cur ->
    bg <= s < en -> st = rv0 rank tl T w + (s - bg) * len1 ->
    (forall m2 cw' cur' y1 y5 y8 y9 y10 y12 y13 y14 y17 y21 y22 y25 y26 y27 y28 y29,
       X2G m SPV lo DT WK wksz FRS hdr cw' rvl rank rs0 syb m2 -> PREF2 cur' cw' -> rv0 rank tl T (w + 1) <= cur' ->
       evt psegs POSTK (STS 0x1d24c m2 y1 y5 y8 y9 y10 y12 y13 y14 y17 y21 y22 y25 y26 y27 y28 y29)) ->
    evt psegs POSTK (STS 0x1d508 m1 (Z_to_bv 64 st) (Z_to_bv 64 minW) x8 x9 x10 x12 x13 x14 x17 x21 x22 x25 x26 (Z_to_bv 64 s) x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ I PR CURL SR EST KONT; [exfalso; lia|].
    eapply (x2_sym_body m1 hdr cw syb cur s st POSTK); try eassumption.
    intros m2 cw' cur' y5 y8 y9 y10 y12 y14 y17 y21 y22 y25 y26 y28 y29 I2 PR2 CUR2.
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
    zstep. rewrite (swrap32_small (s + 1)) by lia.
    zstep. zstep. zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      eapply KONT; [close_x2g | exact PR2 |].
      rewrite RV0S. replace (T - (tl + 1 - w)) with (T - c) by lia.
      assert (E : Znth w rank = s - bg + 1) by lia. rewrite E. lia.
    - eapply (IH m2 hdr cw' syb cur' (s + 1) (st + len1) POSTK); try eassumption; try lia.
      close_x2g.
  Qed.
End SYMS.
