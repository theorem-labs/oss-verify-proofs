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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs.
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
  Hypothesis FILLW : huf_fillw_stmt.
  Hypothesis DTA : rsk_al DT 4.

  (* [comment removed for export] *)
  Variables (c st bsym : Z).
  Hypothesis CR : tl + 1 - maxW <= c <= T - (tl + 1 - maxW).
  Hypothesis STR : 0 <= st.  Hypothesis STH : st + 2^(T - c) <= 2^T.
  Hypothesis BSR : 0 <= bsym < 256.

  Notation STW pc mm x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x24 x25 x27 x28 x29 x30 x31 :=
    (MS (mkR (Z_to_bv 64 T) (Z_to_bv 64 (SPV + -400)) gp tp x5 x6 x7 (Z_to_bv 64 (Z.lxor (WK + 52 * c) 18446744073709551615)) (Z_to_bv 64 T)
             x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (WK + 736)) x19 (Z_to_bv 64 bsym) x21 (Z_to_bv 64 (52 * c))
             (Z_to_bv 64 (Z.lxor (WK + 676) 18446744073709551615)) x24 x25 (Z_to_bv 64 (DT + 4 + 4 * st)) x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Ltac kchk K := exfalso; rewrite ?zb_lxor_ones in K by lia; repeat (rewrite Z.mod_small in K by lia); lia.
  Ltac chk := let K := fresh "K" in zstep;
    lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases K; zify_cond K; [kchk K|]; try clear K | |- _ => idtac end.
  Ltac sgn x := lazymatch goal with |- context [Z.lxor x ?k] =>
    replace (Z.lxor x k) with (x + k) by (change k with (2^63); rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity) end.

  (* [comment removed for export] *)
  Lemma x2_w2_body : forall m1 fr hdr cw syb cur w2 (POSTK : machine_state -> Prop) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz fr hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> st + rvc rank tl T c w2 <= cur ->
    1 <= w2 <= maxW -> c <= T - (tl + 1 - w2) ->
    (forall m2 cw' cur' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz fr hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' -> st + rvc rank tl T c (w2 + 1) <= cur' ->
       evt usegs POSTK (STW 0x1fad4 m2 y5 y6 y7 (Z_to_bv 64 (4 * (w2 + 1))) y11 y12 y13 y14 y15 y16 y17 y19
                         (Z_to_bv 64 (c + tl + 1 - (w2 + 1))) (Z_to_bv 64 (WK + 4 * (w2 + 1))) x25 (Z_to_bv 64 (maxW + 1 - (w2 + 1))) y28 y29 y30 y31)) ->
    evt usegs POSTK (STW 0x1fa44 m1 x5 x6 x7 (Z_to_bv 64 (4 * w2)) x11 x12 x13 x14 x15 x16 x17 x19
                      (Z_to_bv 64 (c + tl + 1 - w2)) (Z_to_bv 64 (WK + 4 * w2)) x25 (Z_to_bv 64 (maxW + 1 - w2)) x28 x29 x30 x31).
  Proof using GEO OK TT MAXW HIGH MOD FILLW DTA CR STR STH BSR.
    intros until x31; intros I PR CURL W2R CDIV KONT. open_geo GEO. open_x2g I.
    destruct MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
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
    (* [comment removed for export] *)
    chk. zstep. chk. chk. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 WK rvl (13 * c + w2) a RVA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RVCM c w2 CR W2R) in RD.
    zstep. rewrite (zx32w_small (rvc rank tl T c w2)) by lia. clear RD.
    pose proof (rvc_mono ws rank tl T OK TT c w2 (w2 + 1) ltac:(lia) ltac:(lia) ltac:(lia)) as RVCW.
    remember (rvc rank tl T c w2) as rp eqn:ERP.
    zstep. replace (rp ≪ 2) with (4 * rp) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. chk. chk.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 (WK + 676) rs0 w2 a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M w2 ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank w2)) by lia. clear RD.
    remember (xs1 rank w2) as bg eqn:EBG.
    zstep. chk.
    zstep. decide_tests. change (Z.b2z false) with 0.
    zstep. sgn bg. decide_tests. change (Z.b2z false) with 0.
    zstep. zstep. chk.
    (* [comment removed for export] *)
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 (WK + 676) rs0 (w2 + 1) a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (RS0M (w2 + 1) ltac:(lia)) in RD.
    zstep. rewrite (sx32w_small (xs1 rank (w2 + 1))) by lia. clear RD.
    remember (xs1 rank (w2 + 1)) as en eqn:EEN.
    zstep. chk.
    zstep. decide_tests. change (Z.b2z false) with 0.
    zstep. sgn en. decide_tests. change (Z.b2z false) with 0.
    zstep. zstep. chk.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (RV1 : rvc rank tl T c (w2 + 1) = rp + 2^(T - tb) * (en - bg)).
    { rewrite RVCS. replace (T - (tl + 1 - w2) - c) with (T - tb) by lia. replace (en - bg) with (Znth w2 rank) by lia. rewrite ERP. ring. }
    assert (N0 : 0 <= 2^(T - tb) * (en - bg)) by (apply Z.mul_nonneg_nonneg; [apply Z.pow_nonneg; lia | lia]).
    assert (POSH : st + rp + 2^(T - tb) * (en - bg) <= 4096) by lia.
    replace (Z_to_bv 64 (DT + 4 + 4 * st + 4 * rp)) with (Z_to_bv 64 (DT + 4 + 4 * (st + rp))) by (f_equal; lia).
    replace (Z_to_bv 64 (en + (WK + 736))) with (Z_to_bv 64 (WK + 736 + en)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (FILLW (Z_to_bv 64 0x1fac0) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -400)
                    lo DT (WK + 736) cw syb (st + rp) bg en tb T 2 bsym);
        unfold HUF_DTABLE_BYTES, HUF_FILLW_STACK; try eassumption; try lia.
      pose proof (rsk_al_e DT 4 DTA) as A. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    unfold huf_fillw_post, HUF_DTABLE_BYTES, HUF_FILLW_STACK. post_call usegs m1.
    zstep. zstep. zstep. zstep. zstep.
    rewrite (swrap32_small (tb + -1)) by lia.
    replace (Z_to_bv 64 (tb + -1)) with (Z_to_bv 64 (c + tl + 1 - (w2 + 1))) by (f_equal; lia).
    replace (Z_to_bv 64 (WK + 4 * w2 + 4)) with (Z_to_bv 64 (WK + 4 * (w2 + 1))) by (f_equal; lia).
    replace (Z_to_bv 64 (maxW + 1 - w2 + -1)) with (Z_to_bv 64 (maxW + 1 - (w2 + 1))) by (f_equal; lia).
    replace (Z_to_bv 64 (4 * w2 + 4)) with (Z_to_bv 64 (4 * (w2 + 1))) by (f_equal; lia).
    (* [comment removed for export] *)
    lazymatch goal with PC : x2_cells ?mm DT ?cwn, PO : cells_written cw ?cwn _ _ _ |- _ =>
      pose proof (pref2T_write T cur cw cwn (st + rp) (2^(T - tb) * (en - bg)) (tb + 256 * 2) PR PO
                    (okwT_val T tb 2 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as PR';
      eapply (KONT mm cwn (Z.max cur (st + rp + 2^(T - tb) * (en - bg)))); [close_x2g | exact PR' | lia] end.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w2_loop : forall j m1 fr hdr cw syb cur w2 (POSTK : machine_state -> Prop) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x25 x28 x29 x30 x31,
    Z.to_nat (maxW + 1 - w2) = j ->
    X2G m SPV lo DT WK wksz fr hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> st + rvc rank tl T c w2 <= cur ->
    1 <= w2 <= maxW -> c <= T - (tl + 1 - w2) ->
    (forall m2 cw' cur' y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz fr hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' -> st + 2^(T - c) <= cur' ->
       evt usegs POSTK (STW 0x1fad8 m2 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y21 y24 x25 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STW 0x1fa44 m1 x5 x6 x7 (Z_to_bv 64 (4 * w2)) x11 x12 x13 x14 x15 x16 x17 x19
                      (Z_to_bv 64 (c + tl + 1 - w2)) (Z_to_bv 64 (WK + 4 * w2)) x25 (Z_to_bv 64 (maxW + 1 - w2)) x28 x29 x30 x31).
  Proof using GEO OK TT MAXW HIGH MOD FILLW DTA CR STR STH BSR.
    induction j as [|j IH]; intros until x31; intros EJ I PR CURL W2R CDIV KONT; [exfalso; lia|].
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    eapply (x2_w2_body m1 fr hdr cw syb cur w2 POSTK); try eassumption.
    intros m2 cw' cur' y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 I2 PR2 CURL2.
    zstep. if_cases KB; zify_cond KB; (destruct (Z.eq_dec w2 maxW) as [EW|NW]; [subst w2|]); try (exfalso; lia).
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fad8) _ _ _ _) =>
        eapply KONT; [exact I2 | exact PR2 |];
        rewrite (rvc_top ws rank tl T OK TT c maxW ltac:(lia) MAXW HIGH) in CURL2; exact CURL2
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1fa44) _ _ _ _) =>
        eapply (IH m2 fr hdr cw' syb cur' (w2 + 1) POSTK); try eassumption; lia
    end.
  Qed.
End W2.
