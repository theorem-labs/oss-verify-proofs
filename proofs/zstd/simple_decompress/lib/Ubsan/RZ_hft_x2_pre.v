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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac u32w RK s x v :=
  lazymatch type of RK with u32arr ?segs ?mx ?Wb (map (Z_to_bv 64) ?l) =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok segs mx Wb _ s a RK ltac:(rewrite length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx ?a2 ?bs) _) =>
      replace (write_to_mem mx a2 bs) with (write_to_mem mx (wa (Wb + 4 * s)) bs) by (f_equal; unfold wa; f_equal; lia) end;
    let S2 := fresh "RK" in
    pose proof (u32arr_write segs mx Wb _ s (Z_to_bv 64 x) RK ltac:(rewrite length_map, ?Zupd_length; lia)) as S2;
    clear RK; store_done;
    apply (u32arr_upd_Z segs _ Wb l (Z.to_nat s) x v) in S2; [| first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity | lia ]];
    change (upd_nat (Z.to_nat s) v l) with (Zupd s v l) in S2;
    rename S2 into RK
  end.
Ltac kchk K := exfalso; rewrite ?zb_lxor_ones in K by lia; repeat (rewrite Z.mod_small in K by lia); lia.

Section PRE.
  Variables (gp tp x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (SPF WK : Z) (m0 : fmem).
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKH : WK + 2124 < 2^47.
  Variables (ws rank : list Z) (tl T maxW : Z).
  Hypothesis OK : huf_stats_ok ws rank tl.
  Hypothesis TT : tl <= T <= 12.
  Hypothesis MAXW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.

  Let TLR : 1 <= tl <= 12. Proof. destruct OK as (H & _). exact H. Qed.
  Let RKLEN : Z.of_nat (length rank) = 13. Proof. destruct OK as (_ & _ & _ & L & _). exact L. Qed.
  Lemma pre_cnt : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct OK as (_ & (_ & LEN) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v ws). unfold FseNCount.Zlength in LEN. lia.
  Qed.

  (* [comment removed for export] *)
  Definition x2_p2_post (rs0 : list Z) : machine_state -> Prop :=
    fun ms' => exists y5 y6 y16 m' rs0',
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 y6 (Z_to_bv 64 (xs1 rank (maxW + 1))) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1f508) fc None m' (seg_rom usegs)
      /\ munch [(WK + 676, WK + 736)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ u32arr usegs m' (WK + 676) (map (Z_to_bv 64) rs0') /\ Z.of_nat (length rs0') = 15
      /\ forall w, 1 <= w <= maxW -> Znth (w + 1) rs0' = xs1 rank w.

  Lemma x2_p2_loop : forall j m rs0 rs w y7,
    x14 = Z_to_bv 64 (Z.lxor (WK + 680) 18446744073709551615) -> x17 = Z_to_bv 64 (4 * (maxW + 1)) ->
    Z.to_nat (maxW + 1 - w) = j -> 1 <= w <= maxW ->
    mem_inv usegs m -> munch [(WK + 676, WK + 736)] m0 m -> wmono usegs m0 m ->
    u32arr usegs m (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m (WK + 676) (map (Z_to_bv 64) rs) -> Z.of_nat (length rs) = 15 ->
    (forall v, 1 <= v < w -> Znth (v + 1) rs = xs1 rank v) ->
    evt usegs (x2_p2_post rs0)
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp (Z_to_bv 64 (4 * w)) (Z_to_bv 64 (xs1 rank w)) y7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 (WK + 680 + 4 * w)) x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1f4e0) fc None m (seg_rom usegs)).
  Proof.
    induction j as [|j IH]; intros until y7; intros EX14 EX17 EJ WR MI MU WM RK RS RSL INV; [exfalso; lia|]. rewrite EX14, EX17.
    pose proof (pre_cnt w ltac:(lia)) as CW.
    pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)) as X0.
    pose proof (xs1_mono ws rank tl OK (w + 1) 13 ltac:(lia) ltac:(lia)) as XM. pose proof (xs1_top ws rank tl OK) as XT.
    pose proof (xs1_step rank w ltac:(lia)) as XS. pose proof (pre_cnt 0 ltac:(lia)) as C0.
    assert (WSL : FseNCount.Zlength ws <= 256) by (destruct OK as (_ & (_ & H) & _); exact H).
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m (WK + 624) rank w a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx32w_small (Znth w rank)) by lia. clear RD.
    u32w RS (w + 1) (xs1 rank w) (xs1 rank w).
    zstep. zstep. zstep. zstep.
    assert (INV' : forall v, 1 <= v < w + 1 -> Znth (v + 1) (Zupd (w + 1) (xs1 rank w) rs) = xs1 rank v).
    { intros v Hv. destruct (Z.eq_dec v w) as [->|NE]; [apply Znth_Zupd_same; unfold FseNCount.Zlength; lia|].
      rewrite Znth_Zupd_other by lia. apply INV. lia. }
    assert (RSL' : Z.of_nat (length (Zupd (w + 1) (xs1 rank w) rs)) = 15) by (rewrite Zupd_length; exact RSL).
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (4 * w + 4)) with (Z_to_bv 64 (4 * (w + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 680 + 4 * w + 4)) with (Z_to_bv 64 (WK + 680 + 4 * (w + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (Znth w rank + xs1 rank w)) with (Z_to_bv 64 (xs1 rank (w + 1))) by (f_equal; lia).
      rewrite <- EX14, <- EX17. eapply (IH _ rs0 _ (w + 1)); try eassumption; try lia.
    - assert (EW : w = maxW) by lia. subst w.
      zstep. apply evt_done. unfold x2_p2_post. do 5 eexists.
      split; [rewrite EX14, EX17; replace (Znth maxW rank + xs1 rank maxW) with (xs1 rank (maxW + 1)) by lia; reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact RS|]. split; [exact RSL'|].
      intros v Hv. apply INV'. lia.
  Qed.

  (* [comment removed for export] *)
  Variables (hw : list Z) (nbs : Z).
  Hypothesis EWS : ws = firstn (Z.to_nat nbs) hw.
  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis HWBY : Forall (fun c => 0 <= c < 256) hw.  Hypothesis NBR : 2 <= nbs <= 256.
  Definition psort (w : Z) : Z := if w =? 0 then xs1 rank (maxW + 1) else xs1 rank w.

  Definition x2_p3_post : machine_state -> Prop :=
    fun ms' => exists y16 y28 y29 y30 m' rs' syb',
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 y16 x17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 x31)
               F (Z_to_bv 64 0x1f57c) fc None m' (seg_rom usegs)
      /\ munch [(WK + 676, WK + 992)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ u32arr usegs m' (WK + 676) (map (Z_to_bv 64) rs') /\ Z.of_nat (length rs') = 15
      /\ u8arr usegs m' (WK + 736) syb' /\ Z.of_nat (length syb') = 256
      /\ forall w, 0 <= w <= maxW -> Znth (w + 1) rs' = psort w + Znth w rank.

  Lemma ws_len' : FseNCount.Zlength ws = nbs.
  Proof. rewrite EWS. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth' : forall i, 0 <= i < nbs -> Znth i ws = Znth i hw.
  Proof.
    intros i Hi. rewrite EWS. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.

  Lemma x2_p3_loop : forall j m rs syb i y28 y29 y30,
    x5 = Z_to_bv 64 (Z.lxor (WK + 736) 18446744073709551615) -> x6 = Z_to_bv 64 256 -> x7 = Z_to_bv 64 255 ->
    x13 = Z_to_bv 64 (WK + 680) -> x14 = Z_to_bv 64 (Z.lxor (WK + 680) 18446744073709551615) -> x15 = Z_to_bv 64 nbs ->
    x17 = Z_to_bv 64 (Z.lxor (WK + 992) 18446744073709551615) -> x18 = Z_to_bv 64 (WK + 736) -> x20 = Z_to_bv 64 (WK + 992) ->
    Z.to_nat (nbs - i) = j -> 0 <= i < nbs ->
    mem_inv usegs m -> munch [(WK + 676, WK + 992)] m0 m -> wmono usegs m0 m ->
    u8arr usegs m (WK + 992) (map (Z_to_bv 8) hw) ->
    u32arr usegs m (WK + 676) (map (Z_to_bv 64) rs) -> Z.of_nat (length rs) = 15 ->
    u8arr usegs m (WK + 736) syb -> Z.of_nat (length syb) = 256 ->
    (forall w, 0 <= w <= maxW -> Znth (w + 1) rs = psort w + hcount (firstn (Z.to_nat i) ws) w) ->
    evt usegs x2_p3_post
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 (Z_to_bv 64 i) x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 x31)
          F (Z_to_bv 64 0x1f53c) fc None m (seg_rom usegs)).
  Proof.
    induction j as [|j IH]; intros until y30; intros EX5 EX6 EX7 EX13 EX14 EX15 EX17 EX18 EX20 EJ IR MI MU WM HWC RS RSL SYC SYL INV; [exfalso; lia|].
    rewrite EX5, EX6, EX7, EX13, EX14, EX15, EX17, EX18, EX20.
    pose proof ws_len' as WSL. pose proof (ws_nth' i IR) as WNTH.
    pose proof (hcount_firstn_lt ws i ltac:(lia)) as HLT. pose proof (hcount_firstn_step ws i) as HST.
    pose proof (hcount_nonneg (firstn (Z.to_nat i) ws) (Znth i ws)) as H0.
    destruct OK as (_ & _ & FA & _ & CNT & _).
    pose proof (hForall_Znth _ ws i FA ltac:(lia)) as WR0. cbv beta in WR0.
    rewrite WNTH in *. remember (Znth i hw) as w eqn:EW.
    rewrite <- (CNT w ltac:(lia)) in HLT.
    assert (WM1 : w <= maxW) by (destruct (Z_le_gt_dec w maxW) as [L|G]; [exact L | exfalso; rewrite (HIGH w ltac:(lia)) in HLT; lia]).
    pose proof (INV w ltac:(lia)) as RV.
    assert (SLOT : 0 <= Znth (w + 1) rs /\ Znth (w + 1) rs + 1 <= nbs).
    { rewrite RV. unfold psort. pose proof (xs1_total ws rank tl OK maxW ltac:(lia) HIGH) as XT. rewrite WSL in XT.
      destruct (Z.eqb_spec w 0) as [E0|N0].
      - subst w. pose proof (xs1_nonneg ws rank tl OK (maxW + 1) ltac:(lia)). rewrite E0 in *. lia.
      - pose proof (xs1_nonneg ws rank tl OK w ltac:(lia)). pose proof (xs1_step rank w ltac:(lia)) as XS.
        pose proof (xs1_mono ws rank tl OK (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)). pose proof (pre_cnt 0 ltac:(lia)). lia. }
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs m (WK + 992) hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite <- EW in RD.
    zstep. cbv beta. rewrite (byte_lit w) by lia. clear RD.
    zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m (WK + 676) rs (w + 1) a RS ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx32w_small (Znth (w + 1) rs)) by lia. clear RD.
    zstep.
    u32w RS (w + 1) (Znth (w + 1) rs + 1) (Znth (w + 1) rs + 1).
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep.
    outst SYC SYL.
    zstep.
    remember (Zupd (w + 1) (Znth (w + 1) rs + 1) rs) as rs' eqn:ERS'.
    assert (RSL' : Z.of_nat (length rs') = 15) by (subst rs'; rewrite Zupd_length; exact RSL).
    assert (INV' : forall v, 0 <= v <= maxW -> Znth (v + 1) rs' = psort v + hcount (firstn (Z.to_nat (i + 1)) ws) v).
    { intros v Hv. rewrite (HST v ltac:(lia)). subst rs'. destruct (Z.eq_dec w v) as [->|NE].
      - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite (INV v Hv). lia.
      - rewrite Znth_Zupd_other by lia. rewrite (INV v Hv). lia. }
    clear ERS'.
    zstep. if_cases KB; zify_cond KB.
    - rewrite <- EX5, <- EX6, <- EX7, <- EX13, <- EX14, <- EX15, <- EX17, <- EX18, <- EX20.
      eapply (IH _ rs' _ (i + 1)); try eassumption; try lia.
    - assert (EI : i + 1 = nbs) by lia.
      apply evt_done. unfold x2_p3_post. do 4 eexists. do 3 eexists.
      split; [rewrite EX5, EX6, EX7, EX13, EX14, EX15, EX17, EX18, EX20; reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact RS|]. split; [exact RSL'|].
      split; [eassumption|]. split; [eassumption|].
      intros v Hv. rewrite (INV' v Hv). rewrite EI. rewrite <- WSL. rewrite hcount_firstn_all. rewrite (CNT v ltac:(lia)). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition x2_p4_post : machine_state -> Prop :=
    fun ms' => exists y5 y11 y12 y15 y17 m' rvl',
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 x6 x7 x8 x9 x10 y11 y12 x13 x14 y15 x16 y17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1f5dc) fc None m' (seg_rom usegs)
      /\ munch [(WK, WK + 624)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ u32arr usegs m' WK (map (Z_to_bv 64) rvl') /\ Z.of_nat (length rvl') = 156
      /\ forall w, 1 <= w <= maxW -> Znth w rvl' = rv0 rank tl T w.

  Lemma x2_p4_loop : forall j m rvl w y5,
    x7 = Z_to_bv 64 (Z.lxor WK 18446744073709551615) -> x13 = Z_to_bv 64 (4 * (maxW + 1)) -> x16 = Z_to_bv 64 32 ->
    Z.to_nat (maxW + 1 - w) = j -> 1 <= w <= maxW ->
    mem_inv usegs m -> munch [(WK, WK + 624)] m0 m -> wmono usegs m0 m ->
    u32arr usegs m (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m WK (map (Z_to_bv 64) rvl) -> Z.of_nat (length rvl) = 156 ->
    (forall v, 1 <= v < w -> Znth v rvl = rv0 rank tl T v) ->
    evt usegs x2_p4_post
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 x6 x7 x8 x9 x10 (Z_to_bv 64 (T - tl + (w - 1))) (Z_to_bv 64 (WK + 624 + 4 * w)) x13 x14
               (Z_to_bv 64 (4 * w)) x16 (Z_to_bv 64 (rv0 rank tl T w)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1f5b4) fc None m (seg_rom usegs)).
  Proof.
    induction j as [|j IH]; intros until y5; intros EX7 EX13 EX16 EJ WR MI MU WM RK RV RVL INV; [exfalso; lia|]. rewrite EX7, EX13, EX16.
    pose proof (pre_cnt w ltac:(lia)) as CW.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as R0.
    pose proof (rv0_step rank tl T TT w ltac:(lia)) as RS.
    pose proof (rv0_mono ws rank tl T OK TT (w + 1) (maxW + 1) ltac:(lia) ltac:(lia)) as RM.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in RM.
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    replace (T - (tl + 1 - w)) with (T - tl + (w - 1)) in RS by lia.
    assert (PE : 1 <= 2^(T - tl + (w - 1)) <= 4096).
    { split; [pose proof (Z.pow_pos_nonneg 2 (T - tl + (w - 1)) ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]. }
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m (WK + 624) rank w a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx32w_small (Znth w rank)) by lia. clear RD.
    u32w RV w (rv0 rank tl T w) (rv0 rank tl T w).
    zstep.
    rewrite (shiftl_mod32 (Znth w rank) (T - tl + (w - 1))) by lia.
    assert (PRD : 0 <= Znth w rank * 2^(T - tl + (w - 1)) <= 4096) by (split; [apply Z.mul_nonneg_nonneg; lia | lia]).
    rewrite (swrap32_small (Znth w rank * 2 ^ (T - tl + (w - 1)))) by lia.
    zstep. rewrite (swrap32_small (T - tl + (w - 1) + 1)) by lia.
    zstep. zstep. zstep.
    remember (Zupd w (rv0 rank tl T w) rvl) as rvl' eqn:ERVL'.
    assert (RVL' : Z.of_nat (length rvl') = 156) by (subst rvl'; rewrite Zupd_length; exact RVL).
    assert (INV' : forall v, 1 <= v < w + 1 -> Znth v rvl' = rv0 rank tl T v).
    { intros v Hv. subst rvl'. destruct (Z.eq_dec v w) as [->|NE]; [apply Znth_Zupd_same; unfold FseNCount.Zlength; lia|].
      rewrite Znth_Zupd_other by lia. apply INV. lia. }
    clear ERVL'.
    zstep. if_cases KB; zify_cond KB.
    - rewrite <- EX7, <- EX13, <- EX16.
      replace (Z_to_bv 64 (4 * w + 4)) with (Z_to_bv 64 (4 * (w + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 624 + 4 * w + 4)) with (Z_to_bv 64 (WK + 624 + 4 * (w + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (T - tl + (w - 1) + 1)) with (Z_to_bv 64 (T - tl + (w + 1 - 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (Znth w rank * 2 ^ (T - tl + (w - 1)) + rv0 rank tl T w)) with (Z_to_bv 64 (rv0 rank tl T (w + 1))) by (f_equal; lia).
      eapply (IH _ rvl' (w + 1)); try eassumption; try lia.
    - apply evt_done. unfold x2_p4_post. do 7 eexists.
      split; [rewrite EX7, EX13, EX16; reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact RV|]. split; [exact RVL'|].
      intros v Hv. apply INV'. lia.
  Qed.

  (* [comment removed for export] *)
  Notation cmin := (tl + 1 - maxW).
  Notation cmax := (T - (tl + 1 - maxW)).
  Definition rows_inv (c w : Z) (rvl : list Z) : Prop :=
    Z.of_nat (length rvl) = 156 /\ (forall v, 1 <= v <= maxW -> Znth v rvl = rv0 rank tl T v) /\
    (forall c' v, cmin <= c' < c -> 1 <= v <= maxW -> Znth (13 * c' + v) rvl = rvc rank tl T c' v) /\
    (forall v, 1 <= v < w -> Znth (13 * c + v) rvl = rvc rank tl T c v).

  Definition x2_p5_post : machine_state -> Prop :=
    fun ms' => exists y5 y6 y13 y15 y16 y17 m' rvl',
      ms' = MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 y6 x7 x8 x9 x10 x11 x12 y13 x14 y15 y16 y17
                    x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
               F (Z_to_bv 64 0x1f698) fc None m' (seg_rom usegs)
      /\ munch [(WK, WK + 624)] m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
      /\ u32arr usegs m' WK (map (Z_to_bv 64) rvl') /\ rows_inv (cmax + 1) 1 rvl'.

  (* [comment removed for export] *)
  Lemma x2_p5_inner : forall j m rvl c w y5 y6,
    x7 = Z_to_bv 64 (Z.lxor WK 18446744073709551615) -> x8 = Z_to_bv 64 maxW -> x23 = Z_to_bv 64 WK ->
    Z.to_nat (maxW + 1 - w) = j -> 1 <= w <= maxW -> cmin <= c <= cmax ->
    mem_inv usegs m -> munch [(WK, WK + 624)] m0 m -> wmono usegs m0 m ->
    u32arr usegs m WK (map (Z_to_bv 64) rvl) -> rows_inv c w rvl ->
    (forall m' rvl' z5 z6 z15 z16 z17, mem_inv usegs m' -> munch [(WK, WK + 624)] m0 m' -> wmono usegs m0 m' ->
       u32arr usegs m' WK (map (Z_to_bv 64) rvl') -> rows_inv (c + 1) 1 rvl' ->
       evt usegs x2_p5_post
         (MS (mkR x1 (Z_to_bv 64 SPF) gp tp z5 z6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 z15 z16 z17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (Z_to_bv 64 0x1f640) fc None m' (seg_rom usegs))) ->
    evt usegs x2_p5_post
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 y6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 (Z_to_bv 64 (WK + 52 * c))
               (Z_to_bv 64 (Z.lxor (WK + 52 * c) 18446744073709551615)) (Z_to_bv 64 w)
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1f60c) fc None m (seg_rom usegs)).
  Proof.
    induction j as [|j IH]; intros until y6; intros EX7 EX8 EX23 EJ WR CRR MI MU WM RV (RVL & R0 & RC & RW) KROW; [exfalso; lia|]. rewrite EX7, EX8, EX23.
    pose proof (rv0_nonneg ws rank tl T OK TT w ltac:(lia)) as V0.
    pose proof (rv0_mono ws rank tl T OK TT w (maxW + 1) ltac:(lia) ltac:(lia)) as VM.
    rewrite (rv0_top ws rank tl T OK TT maxW MAXW HIGH) in VM.
    assert (P2T : 2^T <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    zstep. zstep. rewrite (zext32_sh30 w) by lia.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. rewrite (Z.mod_small w) by lia.
    zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m WK rvl w a RV ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite (R0 w WR) in RD.
    zstep. rewrite (sx32w_small (rv0 rank tl T w)) by lia. clear RD.
    zstep. zstep.
    assert (ESR : bv_swrap 32 (bv_wrap 32 (rv0 rank tl T w) ≫ (c mod 32)) = rvc rank tl T c w).
    { rewrite wrap32_small by lia. rewrite (Z.mod_small c 32) by lia. unfold rvc. rewrite Z.shiftr_div_pow2 by lia.
      apply swrap32_small. assert (0 < 2^c) by (apply Z.pow_pos_nonneg; lia).
      assert (0 <= rv0 rank tl T w / 2^c <= rv0 rank tl T w) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]). lia. }
    rewrite ESR.
    zstep. rewrite (swrap32_small (w + 1)) by lia.
    u32w RV (13 * c + w) (rvc rank tl T c w) (rvc rank tl T c w).
    remember (Zupd (13 * c + w) (rvc rank tl T c w) rvl) as rvl' eqn:ERVL'.
    assert (RI' : rows_inv c (w + 1) rvl').
    { subst rvl'. split; [rewrite Zupd_length; exact RVL|]. split; [|split].
      - intros v Hv. rewrite Znth_Zupd_other by lia. apply R0. exact Hv.
      - intros c' v Hc Hv. rewrite Znth_Zupd_other by lia. apply RC; assumption.
      - intros v Hv. destruct (Z.eq_dec v w) as [->|NE]; [apply Znth_Zupd_same; unfold FseNCount.Zlength; lia|].
        rewrite Znth_Zupd_other by lia. apply RW. lia. }
    clear ERVL'.
    zstep. if_cases KB; zify_cond KB.
    - rewrite <- EX7, <- EX8, <- EX23.
      eapply (IH _ rvl' c (w + 1)); try eassumption; try lia.
    - assert (EW : w = maxW) by lia. subst w.
      rewrite <- EX7, <- EX8, <- EX23.
      eapply KROW; try eassumption.
      destruct RI' as (L' & R0' & RC' & RW'). split; [exact L'|]. split; [exact R0'|]. split; [|intros v Hv; lia].
      intros c' v Hc Hv. destruct (Z.eq_dec c' c) as [->|NE]; [apply RW'; lia | apply RC'; lia].
  Qed.

  Lemma x2_p5_loop : forall j m rvl c y5 y6 y15 y16 y17,
    x7 = Z_to_bv 64 (Z.lxor WK 18446744073709551615) -> x8 = Z_to_bv 64 maxW -> x11 = Z_to_bv 64 12 -> x12 = Z_to_bv 64 52 ->
    x14 = Z_to_bv 64 (cmax + 1) -> x23 = Z_to_bv 64 WK ->
    Z.to_nat (cmax + 1 - c) = j -> cmin <= c <= cmax ->
    mem_inv usegs m -> munch [(WK, WK + 624)] m0 m -> wmono usegs m0 m ->
    u32arr usegs m WK (map (Z_to_bv 64) rvl) -> rows_inv c 1 rvl ->
    evt usegs x2_p5_post
      (MS (mkR x1 (Z_to_bv 64 SPF) gp tp y5 y6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 c) x14 y15 y16 y17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1f5f4) fc None m (seg_rom usegs)).
  Proof.
    induction j as [|j IH]; intros until y17; intros EX7 EX8 EX11 EX12 EX14 EX23 EJ CRR MI MU WM RV RI; [exfalso; lia|].
    rewrite EX7, EX11, EX12, EX23.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep.
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. replace (Z_to_bv 64 (WK + c * 52)) with (Z_to_bv 64 (WK + 52 * c)) by (f_equal; lia).
    zstep. zstep.
    rewrite <- EX7, <- EX11, <- EX12, <- EX23.
    eapply (x2_p5_inner (Z.to_nat (maxW + 1 - 1)) m rvl c 1); try eassumption; try lia.
    intros m' rvl' z5 z6 z15 z16 z17 MI' MU' WM' RV' RI'.
    zstep. rewrite (swrap32_small (c + 1)) by lia.
    zstep. zstep. if_cases KB; rewrite EX14 in KB; zify_cond KB.
    - eapply (IH m' rvl' (c + 1)); try eassumption; try lia.
    - assert (EC : c = cmax) by lia.
      zstep. apply evt_done. unfold x2_p5_post. do 8 eexists.
      split; [reflexivity|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact RV'|]. rewrite <- EC. exact RI'.
  Qed.
End PRE.
