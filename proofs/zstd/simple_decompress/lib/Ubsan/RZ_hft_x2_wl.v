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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs huf421_kit_fill huf411_kit_rs RZ_hft_x2_sym huf42_4_kit_wtwo huf42_4_kit_wone.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac close_x2gr := unfold X2G; repeat (split; [first [eassumption | reflexivity]|]); first [eassumption | reflexivity].

Section WL.
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

  (* [comment removed for export] *)
  Lemma x2_w_body : forall m1 hdr cw syb cur w k136 k144 k152 k160 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 (POSTK : machine_state -> Prop)
                           x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30,
    X2G m SPV lo DT WK wksz (FRW k136 k144 k152 k160 (Z_to_bv 64 (2 * tl + 2 - w)) k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280)
        hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW ->
    (forall m2 cw' cur' u136 u176 u184 u192 u200 u208 u216 u240 u248 u264 u272 u280
            y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRW u136 (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 (tl + 1 - w))
                                    (Z_to_bv 64 (2 * tl + 2 - w)) u176 u184 u192 u200 u208 u216 (Z_to_bv 64 w) u240 u248 u264 u272 u280)
           hdr cw' rvl rank rs0 syb m2 -> PREF2T T cur' cw' ->
       rv0 rank tl T (w + 1) <= cur' ->
       evt usegs POSTK (STL 0x1f6fc m2 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STL 0x1f728 m1 x5 x6 x7 x8 x10 (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 w) x13 x14 x15 x16 x17 x20 x21 x22
                         x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (tl + 1 - w))).
  Proof.
    intros until x30; intros I PR CURL WR KONT. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
    pose proof MOD as (RVLEN & RSLEN & RV0M & RVCM & RS0M).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as BG0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XSM. pose proof (xs1_top ws rank tl OK) as XST.
    pose proof (st_rank_nonneg ws rank tl OK 0 ltac:(lia)) as CNTZ. pose proof (st_rank_nonneg ws rank tl OK w ltac:(lia)) as CNT0.
    pose proof (xs1_step rank w ltac:(lia)) as XSS.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    if_cases K0; zify_cond K0.
    1: assert (MW : Z.max 1 (tl + 1 - w + (tl + 1 - T)) = tl + 1 - w + (tl + 1 - T)) by lia.
    2: zstep; assert (MW : Z.max 1 (tl + 1 - w + (tl + 1 - T)) = 1) by lia.
    all: lazymatch type of MW with _ = ?v =>
      replace (Z_to_bv 64 v) with (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - T)))) by (rewrite MW; reflexivity) end.
    all: clear MW.
    (* [comment removed for export] *)
    all: zstep; zstep.
    all: replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: zstep; if_cases KC1; zify_cond KC1;
         [exfalso; rewrite ?zb_lxor_ones in KC1 by lia; repeat (rewrite Z.mod_small in KC1 by lia); lia|].
    (* [comment removed for export] *)
    all: zstep; zstep; zstep; zstep.
    all: replace ((w + 1) ≪ 2) with (4 * (w + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    all: zstep; if_cases KC2; zify_cond KC2;
         [exfalso; rewrite ?zb_lxor_ones in KC2 by lia; repeat (rewrite Z.mod_small in KC2 by lia); lia|].
    (* [comment removed for export] *)
    all: zstep; zstep; zstep.
    all: lazymatch type of RSA with u32arr ?sg ?mm _ _ => let a := cur_mem_addr in
           pose proof (u32_znth sg mm (WK + 676) rs0 w a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    all: rewrite (RS0M w ltac:(lia)) in RD.
    all: zstep; rewrite (sx32w_small (xs1 rank w)) by lia; clear RD.
    all: lazymatch type of RSA with u32arr ?sg ?mm _ _ => let a := cur_mem_addr in
           pose proof (u32_znth sg mm (WK + 676) rs0 (w + 1) a RSA ltac:(lia) ltac:(addr_tac)) as RD end.
    all: rewrite (RS0M (w + 1) ltac:(lia)) in RD.
    all: zstep; rewrite (sx32w_small (xs1 rank (w + 1))) by lia; clear RD.
    (* [comment removed for export] *)
    all: zstep.
    all: zstep; zstep; zstep; rewrite (swrap32_small (tl + 1 - w)) by lia.
    all: zstep; rewrite (swrap32_small (T - (tl + 1 - w))) by lia.
    all: zstep; zstep; zstep; zstep.
    (* [comment removed for export] *)
    all: if_cases KC3; zify_cond KC3; repeat (rewrite Z.mod_small in KC3 by lia); [eapply x2_w_two | eapply x2_w_one].
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- PREF2T _ _ _ => exact PR
         | |- X2G _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
             unfold X2G; repeat (split; [first [eassumption | reflexivity | split; eassumption]|]); first [eassumption | reflexivity]
         | |- _ => idtac end.
    all: first [eassumption | exact KONT | lia | lazymatch goal with |- ?g => fail 10 "G" g end].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_w_loop : forall j m1 hdr cw syb cur w k136 k144 k152 k160 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 (POSTK : machine_state -> Prop)
                           x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30,
    Z.to_nat (maxW + 1 - w) = j ->
    X2G m SPV lo DT WK wksz (FRW k136 k144 k152 k160 (Z_to_bv 64 (2 * tl + 2 - w)) k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280)
        hdr cw rvl rank rs0 syb m1 -> PREF2T T cur cw -> rv0 rank tl T w <= cur ->
    1 <= w <= maxW ->
    (forall m2 cw' u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u240 u248 u264 u272 u280
            y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31,
       X2G m SPV lo DT WK wksz (FRW u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u240 u248 u264 u272 u280)
           hdr cw' rvl rank rs0 syb m2 -> PREF2T T (2^T) cw' ->
       evt usegs POSTK (STL 0x1fb04 m2 y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POSTK (STL 0x1f728 m1 x5 x6 x7 x8 x10 (Z_to_bv 64 (tl + 1 - w + (tl + 1 - T))) (Z_to_bv 64 w) x13 x14 x15 x16 x17 x20 x21 x22
                         x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (tl + 1 - w))).
  Proof.
    induction j as [|j IH]; intros until x30; intros EJ I PR CURL WR KEXIT; [exfalso; lia|].
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    pose proof MOD as (RVLEN & RSLEN & _).
    eapply (x2_w_body m1 hdr cw syb cur w); try eassumption.
    intros m2 cw' cur' u136 u176 u184 u192 u200 u208 u216 u240 u248 u264 u272 u280
           y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 I2 PR2 CUR2.
    open_geo GEO. destruct I2 as (HDRC & (CW & CWL) & RVA & RKA & RSA & SYB & SYLEN & SYS & WKR & FR & FRSZ & STK & MI & MU & WM).
    unfold x2_frame in FR.
    do 11 zstep.
    lazymatch goal with |- context [bv_swrap 32 (?A mod ?M + -1)] =>
      assert (ESW : bv_swrap 32 (A mod M + -1) = tl + 1 - (w + 1) + (tl + 1 - T)) by (apply swrap32_eqm; [lia | Z.div_mod_to_equations; lia]);
      rewrite ESW; clear ESW end.
    lazymatch type of CW with u8arr _ ?mm _ _ => assert (CWS : x2_cells mm DT cw') by (split; assumption) end.
    clear CW CWL.
    if_cases KB; zify_cond KB; repeat (rewrite Z.mod_small in KB by lia).
    - assert (EW : w = maxW) by lia. subst w.
      rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in CUR2.
      eapply KEXIT; [close_x2gr|]. exact (pref2T_mono T (2^T) cur' cw' PR2 CUR2).
    - replace (Z_to_bv 64 (2 * tl + 2 - w + -1)) with (Z_to_bv 64 (2 * tl + 2 - (w + 1))) in FR by (f_equal; lia).
      replace (Z_to_bv 64 (tl + 1 - w + -1)) with (Z_to_bv 64 (tl + 1 - (w + 1))) by (f_equal; lia).
      eapply (IH _ hdr cw' syb cur' (w + 1)); [lia | close_x2gr | exact PR2 | exact CUR2 | lia | exact KEXIT].
  Qed.

  (* [comment removed for export] *)
  Notation POST := (huf_rd_post ra0 gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo true m).
  Lemma x2_exit : forall m1 hdr cw syb h3 k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280
                         x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    X2G m SPV lo DT WK wksz (FRW k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280)
        hdr cw rvl rank rs0 syb m1 -> PREF2T T (2^T) cw ->
    hdr3 = Z_to_bv 64 (h3 * 16777216) -> 0 <= h3 < 256 -> 0 <= r0 < 2^64 ->
    evt usegs POST (STL 0x1fb04 m1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PR EH3 H3R R0R. open_geo GEO. open_x2g I. unfold x2_frame in FR. destruct CWS as (CW & CWL).
    destruct MOD as (RVLEN & RSLEN & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct OK as (_ & _ & _ & L & _); exact L).
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    subst hdr3.
    assert (HDRL : length hdr = 4%nat) by (destruct HDRC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; exact LJ).
    apply u8arr_of_rw_cells in HDRC.
    do 7 zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8arr_storen_ok usegs m1 DT hdr 0 4 a HDRC ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SOK end.
    zstep.
    lazymatch goal with |- context [Z.lor (Z.lor (Z.lor ?a ?b) 12) 256] =>
      assert (EV : Z.lor (Z.lor (Z.lor a b) 12) 256 = 268 + 65536 * T + 16777216 * h3) end.
    { rewrite <- Z.lor_assoc. change (Z.lor 12 256) with 268.
      rewrite Z.shiftl_mul_pow2 by lia. change (2^16) with 65536. rewrite Z.mod_small by lia.
      rewrite (Z.lor_comm (T * 65536) (h3 * 16777216)).
      replace (h3 * 16777216) with (h3 * 2^24) by reflexivity.
      rewrite (lor_disj_add h3 (T * 65536) 24) by (try change (2^24) with 16777216; lia).
      replace (h3 * 2^24 + T * 65536) with ((h3 * 256 + T) * 2^16) by (change (2^24) with 16777216; change (2^16) with 65536; ring).
      rewrite (lor_disj_add (h3 * 256 + T) 268 16) by (try change (2^16) with 65536; lia).
      change (2^16) with 65536. ring. }
    rewrite EV.
    pose proof (u8arr_writen usegs m1 DT hdr 0 (le4 (Z_to_bv 64 (268 + 65536 * T + 16777216 * h3))) HDRC ltac:(lia) ltac:(rewrite length_le4; lia)) as HD'.
    replace (write_to_mem m1 (Z_to_bv 64 DT)) with (write_to_mem m1 (wa (DT + 0))) by (f_equal; unfold wa; f_equal; lia).
    clear HDRC EV. store_done.
    rewrite (le4_Z (268 + 65536 * T + 16777216 * h3) (268 + 65536 * T + 16777216 * h3)) in HD' by reflexivity.
    assert (EZ : ZdSeqTable.zle4 (268 + 65536 * T + 16777216 * h3) = [12; 1; T; h3]).
    { unfold ZdSeqTable.zle4. f_equal; [|f_equal; [|f_equal; [|f_equal]]]; Z.div_mod_to_equations; lia. }
    rewrite EZ in HD'.
    assert (UB : upd_bytes hdr (Z.to_nat 0) (map (Z_to_bv 8) [12; 1; T; h3]) = map (Z_to_bv 8) [12; 1; T; h3]).
    { unfold upd_bytes. change (Z.to_nat 0) with O. rewrite firstn_O. rewrite skipn_all2 by (cbn [length map]; lia).
      rewrite app_nil_r. reflexivity. }
    rewrite UB in HD'. clear UB EZ.
    do 15 zstep.
    (* [comment removed for export] *)
    assert (DTC : u8arr usegs m0 DT (map (Z_to_bv 8) [12; 1; T; h3] ++ u16s (map (Z_to_bv 64) cw))).
    { apply (proj2 (u8arr_app usegs m0 DT _ _)). split; [exact HD'|]. rewrite length_map. cbn [length]. replace (DT + Z.of_nat 4) with (DT + 4) by lia. exact CW. }
    (* [comment removed for export] *)
    assert (WKS : stk usegs m0 WK (WK + wksz)).
    { apply u8arr_of_u32arr in RVA, RKA, RSA. apply rw_cells_of_u8arr in RVA, RKA, RSA. apply stk_of_rw_cells in RVA, RKA, RSA.
      cbn [cells_size csize] in RVA, RKA, RSA. rewrite u32s_length, length_map in RVA, RKA, RSA.
      apply (stk_merge usegs m0 WK (WK + 624) (WK + wksz)); [replace (WK + 624) with (WK + Z.of_nat (4 * length rvl + 0)) by lia; exact RVA| |lia].
      apply (stk_merge usegs m0 (WK + 624) (WK + 676) (WK + wksz)); [replace (WK + 676) with (WK + 624 + Z.of_nat (4 * length rank + 0)) by lia; exact RKA| |lia].
      apply (stk_merge usegs m0 (WK + 676) (WK + 736) (WK + wksz)); [replace (WK + 736) with (WK + 676 + Z.of_nat (4 * length rs0 + 0)) by lia; exact RSA| |lia].
      apply (stk_merge usegs m0 (WK + 736) (WK + 992) (WK + wksz)); [exact SYS | exact WKR | lia]. }
    apply stk_of_rw_cells in FR. cbn [cells_size csize Nat.add] in FR.
    assert (STK' : stk usegs m0 lo SPV).
    { apply (stk_merge usegs m0 lo (SPV + -400) SPV STK); [|lia]. replace SPV with (SPV + -400 + Z.of_nat 400) at 2 by lia. exact FR. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 15 eexists. exists r0, (map (Z_to_bv 8) [12; 1; T; h3] ++ u16s (map (Z_to_bv 64) cw)).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|]. split; [exact WKS|]. split; [exact DTC|].
    set (dtb' := map (Z_to_bv 8) [12; 1; T; h3] ++ u16s (map (Z_to_bv 64) cw)).
    assert (NTHC : forall k : nat, nth_error dtb' (4 + k) = nth_error (u16s (map (Z_to_bv 64) cw)) k) by (intros k; reflexivity).
    assert (HDROK : huf_hdr_ok dtb').
    { split; [unfold dtb', HUF_DTABLE_BYTES; rewrite length_app, length_map, u16s_length, length_map; cbn [length]; lia|].
      reflexivity. }
    split; [exact HDROK|]. split; [exact R0R|]. intros _.
    assert (P2 : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    split.
    - split; [exact HDROK|]. exists (Z_to_bv 8 1), T.
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
      split.
      + intros _ i Hi. destruct (PR i Hi) as (_ & LEN). exists (Z_to_bv 8 ((Znth (2 * i + 1) cw / 256) mod 256)). split.
        * replace (Z.to_nat (4 * i + 7)) with (4 + (2 * Z.to_nat (2 * i + 1) + 1))%nat by lia. rewrite NTHC. apply u16s_nth_hi. lia.
        * rewrite byte_lit by (apply Z.mod_pos_bound; lia). exact LEN.
      + change (negb (bv_unsigned (Z_to_bv 8 1) =? 0)) with true. intros i Hi. destruct (PR i Hi) as (NB & _).
        exists (Z_to_bv 8 (Znth (2 * i + 1) cw mod 256)). split.
        * replace (Z.to_nat (4 * i + 6)) with (4 + (2 * Z.to_nat (2 * i + 1)))%nat by lia. rewrite NTHC. apply u16s_nth_lo. lia.
        * rewrite byte_lit by (apply Z.mod_pos_bound; lia). lia.
    - exists (Z_to_bv 8 1). split; [reflexivity|]. split; [intros _; reflexivity | intros _ E; discriminate E].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_fill : forall m1 hdr cw syb h3 k136 k144 k152 k160 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280
                         x5 x6 x7 x8 x10 x13 x14 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30,
    X2G m SPV lo DT WK wksz (FRW k136 k144 k152 k160 (Z_to_bv 64 (2 * tl + 1)) k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280)
        hdr cw rvl rank rs0 syb m1 ->
    hdr3 = Z_to_bv 64 (h3 * 16777216) -> 0 <= h3 < 256 -> 0 <= r0 < 2^64 ->
    evt usegs POST (STL 0x1f728 m1 x5 x6 x7 x8 x10 (Z_to_bv 64 (2 * tl + 1 - T)) (Z_to_bv 64 1) x13 x14 x15 x16 x17 x20 x21 x22
                        x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 tl)).
  Proof.
    intros until x30; intros I EH3 H3R R0R.
    assert (TLR : 1 <= tl <= 12) by (destruct OK as (H & _); exact H).
    replace (Z_to_bv 64 (2 * tl + 1 - T)) with (Z_to_bv 64 (tl + 1 - 1 + (tl + 1 - T))) by (f_equal; lia).
    replace (Z_to_bv 64 tl) with (Z_to_bv 64 (tl + 1 - 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (2 * tl + 1)) with (Z_to_bv 64 (2 * tl + 2 - 1)) in I by (f_equal; lia).
    eapply (x2_w_loop (Z.to_nat (maxW + 1 - 1)) m1 hdr cw syb 0 1); try eassumption; try lia.
    - apply pref2T_0.
    - rewrite (rv0_1 rank tl T). lia.
    - intros m2 cw' u136 u144 u152 u160 u168 u176 u184 u192 u200 u208 u216 u224 u240 u248 u264 u272 u280
             y5 y6 y7 y8 y10 y11 y12 y13 y14 y15 y16 y17 y20 y21 y22 y24 y25 y26 y27 y28 y29 y30 y31 I2 PR2.
      eapply x2_exit; eassumption.
  Qed.
End WL.
