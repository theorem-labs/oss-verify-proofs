(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_pre RZ_hft_x2_wl huf421_kit_fill huf411_kit_rs huf42_4_kit_sbc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X2S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n < 2^32.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis HDR : huf_hdr_ok dtb.  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis DTSRC : DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT.  Hypothesis WKSRC : WK + wksz <= SRC \/ SRC + n <= WK.
  Hypothesis DTA : rsk_al DT 4.  Hypothesis FILLW : huf_fillw_stmt.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo true m).
  Notation MUNCH := [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -400)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma x2_exit_err : forall m1 dtb' r x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr usegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk usegs m1 WK (WK + wksz) -> stk usegs m1 lo (SPV + -400) ->
    stk usegs m1 (SPV + -400) (SPV + -104) -> rw_cells usegs m1 (SPV + -104) SAVED ->
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 -> 0 <= r < 2^64 -> zd_is_error r = true ->
    evt usegs POST (STF 0x1fb28 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC HDR' WKS STK STF0 FSAV MI MU WM RR RE. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    do 13 zstep. zstep.
    apply stk_of_rw_cells in FSAV. cbn [cells_size csize Nat.add] in FSAV.
    assert (STK' : stk usegs m1 lo SPV).
    { apply (stk_merge usegs m1 lo (SPV + -400) SPV STK); [|lia].
      apply (stk_merge usegs m1 (SPV + -400) (SPV + -104) SPV STF0); [|lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact FSAV. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 14 eexists. exists m1, r, dtb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [exact DTC|]. split; [exact HDR'|]. split; [exact RR|]. intros E. rewrite RE in E. discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_maxw_loop : forall j mm (ws rank : list Z) tl T v x1 x5 x6 x7 x9 x13 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat v = j -> huf_stats_ok ws rank tl -> tl <= T <= 12 -> mem_inv usegs mm ->
    u32arr usegs mm (WK + 624) (map (Z_to_bv 64) rank) -> 0 <= v <= tl -> (forall u, v < u <= tl -> Znth u rank = 0) ->
    (forall maxW y15, 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
       evt usegs POST (STF 0x1f4bc mm x1 x5 x6 x7 (Z_to_bv 64 maxW) x9 (Z_to_bv 64 (Z.lxor (WK + 624) 18446744073709551615)) (Z_to_bv 64 (tl - maxW))
                           (Z_to_bv 64 (1 + 2 * (tl - maxW))) x13 (Z_to_bv 64 13) y15 x16 x17 x18 x19 x20 (Z_to_bv 64 (WK + 624)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt usegs POST (STF 0x1f494 mm x1 x5 x6 x7 (Z_to_bv 64 v) x9 (Z_to_bv 64 (Z.lxor (WK + 624) 18446744073709551615)) (Z_to_bv 64 (tl - v))
                        (Z_to_bv 64 (1 + 2 * (tl - v))) x13 (Z_to_bv 64 13) x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (WK + 624)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ SOK TT MI RK VR ZR KONT.
    { exfalso. assert (v = 0) by lia. subst v. apply (some_weight ws rank tl T SOK TT). intros u Hu. apply ZR. lia. }
    assert (TLR : 1 <= tl <= 12) by (destruct SOK as (H & _); exact H).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    zstep. replace (v ≪ 2) with (4 * v) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. if_cases KC; zify_cond KC.
    { exfalso. rewrite zb_lxor_ones in KC by lia. rewrite ?Z.shiftl_mul_pow2 in KC by lia. repeat (rewrite Z.mod_small in KC by lia). lia. }
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs mm (WK + 624) rank v a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep.
    pose proof (st_rank_nonneg ws rank tl SOK v ltac:(lia)) as C0.
    assert (CH : Znth v rank <= 256).
    { destruct SOK as (_ & (_ & LEN) & _ & _ & CNT & _). rewrite (CNT v ltac:(lia)). unfold hcount.
      pose proof (count_occ_bound Z.eq_dec v ws). unfold FseNCount.Zlength in LEN. lia. }
    rewrite (sx32w_small (Znth v rank)) by lia. clear RD.
    zstep. if_cases KB; zify_cond KB.
    - eapply (KONT v); [lia |].
      intros u Hu. destruct (Z_le_gt_dec u tl) as [LE|GT]; [apply ZR; lia | apply (st_rank_high ws rank tl SOK u); lia].
    - zstep. rewrite (swrap32_small (v + -1)) by lia.
      zstep. zstep. zstep. if_cases KL; zify_cond KL; [|exfalso; lia].
      replace (Z_to_bv 64 (tl - v + 1)) with (Z_to_bv 64 (tl - (v + -1))) by (f_equal; lia).
      replace (Z_to_bv 64 (1 + 2 * (tl - v) + 2)) with (Z_to_bv 64 (1 + 2 * (tl - (v + -1)))) by (f_equal; lia).
      eapply (IH mm ws rank tl T (v + -1)); try eassumption; try lia.
      intros u Hu. destruct (Z.eq_dec u v) as [->|NE]; [exact KB | apply ZR; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_setup : forall m1 (dt hw rank rs00 : list Z) (tl T maxW nbs r0 h3 : Z) flags fj16 j40 j88 j112 j136
      x5 x6 x7 x9 x10 x12 x14 x15 x16 x17 x18 x21 x24 x25 x26 x27 x28 x29 x30,
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    u8arr usegs m1 DT (map (Z_to_bv 8) dt) -> Z.of_nat (length dt) = 16388 -> Forall (fun c => 0 <= c < 256) dt -> Znth 0 dt = 12 ->
    0 <= h3 < 256 ->
    stk usegs m1 WK (WK + 624) -> u32arr usegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) rs00) -> Z.of_nat (length rs00) = 15 ->
    stk usegs m1 (WK + 736) (WK + 992) ->
    u8arr usegs m1 (WK + 992) (map (Z_to_bv 8) hw) -> Z.of_nat (length hw) = 256 -> Forall (fun c => 0 <= c < 256) hw ->
    stk usegs m1 (WK + 1248) (WK + 1248 + 876) -> stk usegs m1 (WK + 2124) (WK + wksz) -> 2124 <= wksz ->
    rw_cells usegs m1 (SPV + -400)
      [C8 (Z_to_bv 64 876); C8 flags; CB 8 fj16; C8 (Z_to_bv 64 (h3 * 16777216)); C8 (Z_to_bv 64 r0); CB 40 j40; C8 (Z_to_bv 64 12);
       CB 16 j88; C8 (Z_to_bv 64 (tl + 1)); CB 16 j112; C8 (Z_to_bv 64 (WK + 676)); CB 152 j136] ->
    rw_cells usegs m1 (SPV + -112) [C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SPV + -104) SAVED -> stk usegs m1 lo (SPV + -400) ->
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 -> 1 <= r0 <= n ->
    tl <= T <= 12 -> 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
    evt usegs POST (STF 0x1f4bc m1 (Z_to_bv 64 T) x5 x6 x7 (Z_to_bv 64 maxW) x9 x10 (Z_to_bv 64 (tl - maxW)) x12 (Z_to_bv 64 (WK + 680)) x14
                        x15 x16 x17 x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (WK + 992)) x21 (Z_to_bv 64 DT) (Z_to_bv 64 WK) x24 x25 x26 x27
                        x28 x29 x30 (Z_to_bv 64 tl)).
  Proof.
    intros until x30; intros MI MU WM DTC DTL' DTBY DTZ0 H3R RVS RK RS0A RS00L SYS HWC HWLEN HWBY CWK' WKR WK2124 F0 NSC FSAV STK' SOK NBR R0N TT MAXW HIGH.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof SOK as (TLR & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    zstep.
    zstep. lazymatch goal with |- context [bv_swrap 32 ?z] =>
      replace (bv_swrap 32 z) with (maxW + 1) by (rewrite (swrap32_small z) by (first [lia | Z.div_mod_to_equations; lia]); first [lia | Z.div_mod_to_equations; lia]) end.
    zstep. zstep.
    zstep. if_cases K; zify_cond K; [exfalso; repeat (rewrite Z.mod_small in K by lia); lia|]. try clear K.
    zstep. zstep. zstep. rewrite (zext32_sh30 (maxW + 1)) by lia.
    zstep.
    replace (Z_to_bv 64 (WK + 684)) with (Z_to_bv 64 (WK + 680 + 4 * 1)) by (f_equal; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (xs1 rank 1)) by (rewrite (xs1_1 rank); reflexivity).
    eapply evt_cut.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply x2_p2_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rs0 := rs00) (rs := rs00) (w := 1)
                               (j := Z.to_nat (maxW + 1 - 1)); try eassumption; try lia; try reflexivity end.
      all: first [apply munch_refl | apply wmono_refl | intros; lia]. }
    unfold x2_p2_post. post_call usegs m1.
    rename POST into RS2M. rename PC into RSA. rename PC0 into RSL.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    eapply x2_setup_bc with (n := n) (dt := dt) (hw := hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (nbs := nbs) (r0 := r0) (h3 := h3)
                            (flags := flags) (fj16 := fj16) (j40 := j40) (j88 := j88) (j112 := j112) (j136 := j136); try eassumption; try lia.
  Qed.

End X2S.
