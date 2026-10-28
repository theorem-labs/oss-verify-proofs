(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst Step.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_top.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation -deprecated".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rk_c4_bytes : forall ws, cells_bytes (map C4 ws) = u32s ws.
Proof. induction ws as [|w ws IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma rk_c4_size : forall ws, Z.of_nat (cells_size (map C4 ws)) = 4 * Z.of_nat (length ws).
Proof. induction ws as [|w ws IH]; cbn [map cells_size csize length]; lia. Qed.
Lemma rk_c4_wf : forall ws, cells_wf (map C4 ws).
Proof. induction ws as [|w ws IH]; cbn; auto. Qed.

Lemma rk_u32arr_cells : forall m A ws, u32arr usegs m A ws -> rw_cells usegs m A (map C4 ws).
Proof.
  intros m A ws [B Wr]. unfold rw_cells, cells_at. rewrite rk_c4_bytes, rk_c4_size. split; [split; [apply rk_c4_wf | exact B] | exact Wr].
Qed.

Lemma rk_cells_u32arr : forall m A ws, rw_cells usegs m A (map C4 ws) -> u32arr usegs m A ws.
Proof.
  intros m A ws [[_ B] Wr]. unfold u32arr. rewrite rk_c4_bytes in B. rewrite rk_c4_size in Wr. split; [exact B | exact Wr].
Qed.

Lemma rk_list13 : forall (l : list Z), length l = 13%nat ->
  l = [nth 0 l 0; nth 1 l 0; nth 2 l 0; nth 3 l 0; nth 4 l 0; nth 5 l 0; nth 6 l 0; nth 7 l 0; nth 8 l 0; nth 9 l 0;
       nth 10 l 0; nth 11 l 0; nth 12 l 0].
Proof.
  intros l H.
  do 13 (destruct l as [|? l]; [discriminate H|]). destruct l; [reflexivity | discriminate H].
Qed.

Fixpoint rk_psum (j : nat) (l : list Z) : Z := match j with O => 0 | S j' => nth j' l 0 + rk_psum j' l end.

Lemma rk_nth_bound : forall (l : list Z) j, Forall (fun v => 0 <= v <= 256) l -> 0 <= nth j l 0 <= 256.
Proof.
  induction l as [|a l IH]; intros j H; destruct j as [|j]; cbn; try lia.
  - inversion H; subst; assumption.
  - inversion H; subst; apply IH; assumption.
Qed.

Lemma rk_psum_bound : forall l j, Forall (fun v => 0 <= v <= 256) l -> 0 <= rk_psum j l <= 256 * Z.of_nat j.
Proof. intros l j H. induction j as [|j IH]; cbn [rk_psum]; [lia|]. pose proof (rk_nth_bound l j H). lia. Qed.

Lemma rk_load_ok : forall l n, (n < length l)%nat -> load l (Z.of_nat n) = Ok (nth n l 0).
Proof.
  intros l n H. unfold load, FseNCount.Zlength, FseNCount.Znth. rewrite Nat2Z.id.
  replace ((0 <=? Z.of_nat n) && (Z.of_nat n <? Z.of_nat (length l))) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
Qed.

Lemma rk_store_ok : forall l n v, (n < length l)%nat -> store l (Z.of_nat n) v = Ok (upd_nat n v l).
Proof.
  intros l n v H. unfold store, FseNCount.Zlength, FseNCount.Zupd. rewrite Nat2Z.id.
  replace ((0 <=? Z.of_nat n) && (Z.of_nat n <? Z.of_nat (length l))) with true
    by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). reflexivity.
Qed.

Lemma rk_rsl_spec : forall rank, length rank = 13%nat -> Forall (fun v => 0 <= v <= 256) rank ->
  forall f n rs, (n + f <= 13)%nat -> length rs = 13%nat ->
  exists r, rank_start_loop f (Z.of_nat n) (rk_psum n rank) rank rs = Ok r /\ length r = 13%nat /\
    (forall i, (i < n)%nat -> nth i r 0 = nth i rs 0) /\ (forall i, (n <= i < n + f)%nat -> nth i r 0 = rk_psum i rank).
Proof.
  intros rank LR RR. induction f as [|f IH]; intros n rs Hn Lrs.
  - exists rs. split; [reflexivity|]. split; [exact Lrs|]. split; intros; [reflexivity | lia].
  - cbn [rank_start_loop]. rewrite (rk_load_ok rank n) by lia. cbn [bind].
    rewrite (rk_store_ok rs n (rk_psum n rank)) by lia. cbn [bind].
    replace (u32 (rk_psum n rank + nth n rank 0)) with (rk_psum (S n) rank)
      by (unfold u32; cbn [rk_psum]; pose proof (rk_psum_bound rank n RR); pose proof (rk_nth_bound rank n RR); rewrite Z.mod_small; lia).
    replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
    destruct (IH (S n) (upd_nat n (rk_psum n rank) rs) ltac:(lia) ltac:(rewrite upd_nat_length; exact Lrs)) as (r & R & LRr & BEL & ABV).
    exists r. split; [exact R|]. split; [exact LRr|]. split.
    + intros i Hi. rewrite BEL by lia. apply nth_upd_nat_other; lia.
    + intros i Hi. destruct (Nat.eq_dec i n) as [->|Hne].
      * rewrite BEL by lia. apply nth_upd_nat_same; lia.
      * apply ABV; lia.
Qed.

Lemma rk_rsl0 : forall rank tl, length rank = 13%nat -> Forall (fun v => 0 <= v <= 256) rank -> 0 <= tl <= 12 ->
  exists rs, rank_start_loop (Z.to_nat (tl + 1)) 0 0 rank (repeat 0 13) = Ok rs /\
    forall i, (i < Z.to_nat (tl + 1))%nat -> nth i rs 0 = rk_psum i rank.
Proof.
  intros rank tl LR RR TL.
  destruct (rk_rsl_spec rank LR RR (Z.to_nat (tl + 1)) 0 (repeat 0 13) ltac:(lia) (repeat_length _ _)) as (r & R & _ & _ & A).
  exists r. split; [exact R | intros i Hi; apply A; lia].
Qed.

Lemma rk_rs_u32 : forall m A cs ws n bs, cs = map C4 ws ++ [CB n bs] -> rw_cells usegs m A cs -> (n mod 4 = 0)%nat ->
  exists jw, length jw = (n / 4)%nat /\ u32arr usegs m A (ws ++ jw).
Proof.
  intros m A cs ws n bs -> [[WF B] Wr] N4.
  apply cells_wf_app in WF. destruct WF as [_ [LB _]]. cbn in LB.
  destruct (u32s_of_bytes (n / 4) bs ltac:(rewrite LB; pose proof (Nat.div_mod_eq n 4); lia)) as (jw & LJ & UJ).
  exists jw. split; [exact LJ|]. unfold u32arr. rewrite u32s_app. split.
  - rewrite cells_bytes_app, rk_c4_bytes in B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, <- UJ in B. exact B.
  - rewrite cells_size_app in Wr. cbn [cells_size csize] in Wr.
    replace (4 * Z.of_nat (length (ws ++ jw))) with (Z.of_nat (cells_size (map C4 ws) + (n + 0))); [exact Wr|].
    rewrite app_length. pose proof (rk_c4_size ws). pose proof (Nat.div_mod_eq n 4). lia.
Qed.

Lemma rk_rs_u32' : forall m A cs ws, cs = map C4 ws -> rw_cells usegs m A cs -> u32arr usegs m A ws.
Proof. intros m A cs ws -> H. apply rk_cells_u32arr; exact H. Qed.

Ltac rk_c4ws cs := lazymatch cs with
  | C4 ?v :: ?r => let t := rk_c4ws r in constr:(v :: t)
  | _ => constr:(@nil word) end.
Ltac rk_lastcb cs := lazymatch cs with
  | [CB ?n ?bs] => constr:((n, bs))
  | _ :: ?r => rk_lastcb r end.
Ltac rk_nenum j := lazymatch goal with
  | H : (j < O)%nat |- _ => exfalso; lia
  | H : (j < S ?k)%nat |- _ => destruct j as [|j]; [clear H | assert ((j < k)%nat) by lia; clear H; rk_nenum j] end.
Ltac rk_zenum x := lazymatch goal with H : ?lo <= x <= ?hi |- _ =>
  let d := eval vm_compute in (lo <=? hi) in lazymatch d with
  | false => exfalso; lia
  | true => let lo' := eval vm_compute in (lo + 1) in
      let Ex := fresh "Ex" in let Nx := fresh "Nx" in let H' := fresh "Hr" in
      destruct (Z.eq_dec x lo) as [Ex | Nx]; [ rewrite Ex; clear H | assert (H' : lo' <= x <= hi) by lia; clear H Nx; rk_zenum x ] end end.

Section CANSEC. Context {rc : runConstT}.
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].
  Hypothesis X1012 : forall m1 h ws rank tl rs rsw jrest jdt jsy j8 j16a j16b j16c j24 (c1 c2 x1 x6 x7 x11 x12 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    tl <= mtl + 1 ->
    rank_start_loop (Z.to_nat (tl + 1)) 0 0 rank (repeat 0 13) = Ok rs ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 0x01000001 + tl * 65536))] ->
    u8arr usegs m1 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    u8arr usegs m1 (W + 1236) (map (Z_to_bv 8) ws ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 W (map (Z_to_bv 64) rank) ->
    u32arr usegs m1 (W + 52) rsw -> length rsw = 13%nat -> (forall i, 0 <= i <= tl -> nth_error rsw (Z.to_nat i) = Some (Z_to_bv 64 (Znth i rs))) ->
    u8arr usegs m1 (W + 980) jsy -> zlen jsy = 256 ->
    rw_cells usegs m1 (SP + -240) [C8 c1; C8 c2; CB 8 j8; C8 (Z_to_bv 64 (hs_ret h)); CB 16 j16a; C8 (Z_to_bv 64 DT);
                                   CB 16 j16b; C8 (Z_to_bv 64 (tl + 1)); CB 16 j16c; C8 (Z_to_bv 64 W); CB 24 j24] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -240) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp (Z_to_bv 64 (18446744073709551615 - (W + 52))) x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 W)
                            x11 x12 (Z_to_bv 64 (W + 980)) (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 tl)
                            (Z_to_bv 64 (W + 52)) (Z_to_bv 64 (hs_nbSymbols h + -4)) (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4))
                            (Z_to_bv 64 W) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (mtl * 0x01000001)) x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 1012)) fc None m1 (seg_rom usegs)).

  Lemma x1_396 : forall m1 h ws rank tl jrest jdt jrs jsy j80 j24 (c1 c2 tv x1 x5 x6 x7 x11 x12 x13 x16 x17 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 0x01000001))] ->
    u8arr usegs m1 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    u8arr usegs m1 (W + 1236) (map (Z_to_bv 8) ws ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 W (map (Z_to_bv 64) rank) ->
    u8arr usegs m1 (W + 52) jrs -> zlen jrs = 52 ->
    u8arr usegs m1 (W + 980) jsy -> zlen jsy = 256 ->
    rw_cells usegs m1 (SP + -240) [C8 c1; C8 c2; CB 80 j80; C8 (Z_to_bv 64 W); CB 24 j24] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 tv] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -240) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 (hs_ret h))
                            x11 x12 x13 (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 tl) x16 x17 (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 W) s5 s6 s7 s8 s9 s10 s11
                            (Z_to_bv 64 (mtl * 0x01000001)) x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 396)) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros m1 h ws rank tl jrest jdt jrs jsy j80 j24 c1 c2 tv x1 x5 x6 x7 x11 x12 x13 x16 x17 x29 x30 x31
      RS SOK RET1 SRCB MTL DT0 DTA DTL W0 WA WL LOS SPB SPA DJ RDT RDJ LJD RSC HWr LJR RKr RSa LRS SYa LSY FRa NSr TLr FRb ST MU WM MI.
    pose proof SOK as (TL1 & LWS & NBS & WSR & LRK1 & RKC & KS).
    unfold HufPure_HufStats.HUF_TABLELOG_MAX, HufPure_HufStats.HUF_SYMBOLVALUE_MAX in TL1, NBS, LRK1, RKC.
    unfold FseNCount.Zlength in LWS, LRK1.
    unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in MU. unfold hk in DJ.
    unfold PHUF_RDT_X1. pose proof (mtl_byte mtl MTL) as MTB.
    assert (DTA4 : Z.land DT 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; Z.div_mod_to_equations; lia).
    assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    destruct (rescale_spec _ _ _ _ (Z.min (mtl + 1) 11) (WF_of_stats h SOK) ltac:(lia)) as (ws' & rank' & tl' & RSC' & WF' & TLM).
    rewrite RSC in RSC'. injection RSC' as <- <- <-.
    pose proof WF' as (TLW & LWS' & NBS' & WSR' & LRK' & RKC' & KS'). unfold FseNCount.Zlength in LWS', LRK'.
    pose proof (wf_rank_bounds _ _ _ _ WF') as RB.
    pose proof (fun i => proj1 (Forall_nth (fun v => 0 <= v <= 256) rank) RB i 0) as RBn. assert (LR13 : length rank = 13%nat) by lia. rewrite LR13 in RBn.
    pose proof (RBn 0%nat ltac:(lia)) as R0. pose proof (RBn 1%nat ltac:(lia)) as R1. pose proof (RBn 2%nat ltac:(lia)) as R2.
    pose proof (RBn 3%nat ltac:(lia)) as R3. pose proof (RBn 4%nat ltac:(lia)) as R4. pose proof (RBn 5%nat ltac:(lia)) as R5.
    pose proof (RBn 6%nat ltac:(lia)) as R6. pose proof (RBn 7%nat ltac:(lia)) as R7. pose proof (RBn 8%nat ltac:(lia)) as R8.
    pose proof (RBn 9%nat ltac:(lia)) as R9. pose proof (RBn 10%nat ltac:(lia)) as R10. pose proof (RBn 11%nat ltac:(lia)) as R11.
    pose proof (RBn 12%nat ltac:(lia)) as R12. clear RBn RB.
    apply rk_u32arr_cells in RKr. rewrite (rk_list13 rank ltac:(lia)) in RKr. cbn [map] in RKr.
    apply (rw_cells_of_u8arr usegs) in RSa. replace (length jrs) with 52%nat in RSa by lia.
    pose proof (wf_rank_bounds _ _ _ _ WF') as RBf.
    assert (TLB : 2 <= tl <= 12) by lia.
    clear TLM.
    destruct (rk_rsl0 rank tl ltac:(lia) RBf ltac:(lia)) as (rs & RSL & RSV).
    x1w_walk. x1w_zbr. x1w_norm. rewrite ?MTB. x1w_br Q1.
    - x1w_zto 2996.
      pose proof (stk_of_rw_cells usegs _ _ _ FRa) as S1. cbn [cells_size csize Nat.add] in S1.
      pose proof (stk_of_rw_cells usegs _ _ _ NSr) as S2. cbn [cells_size csize Nat.add] in S2.
      pose proof (stk_of_rw_cells usegs _ _ _ TLr) as S3. cbn [cells_size csize Nat.add] in S3.
      replace (bv_unsigned sp + -240 + Z.of_nat 128) with (bv_unsigned sp + -112) in S1 by lia.
      replace (bv_unsigned sp + -112 + Z.of_nat 4) with (bv_unsigned sp + -108) in S2 by lia.
      replace (bv_unsigned sp + -108 + Z.of_nat 4) with (bv_unsigned sp + -104) in S3 by lia.
      pose proof (stk_merge usegs _ _ _ _ ST S1 ltac:(lia)) as S4.
      pose proof (stk_merge usegs _ _ _ _ S4 S2 ltac:(lia)) as S5.
      pose proof (stk_merge usegs _ _ _ _ S5 S3 ltac:(lia)) as S6.
      replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 (2^64 - 44)) by (apply Z_to_bv_eqm; reflexivity).
      eapply x1_epi; [lia | lia | exact FRb | exact S6 | lia | eassumption | eassumption | eassumption | lia | intros; lia].
    - x1w_walkd. x1w_zbr. x1w_norm.
      lazymatch goal with H : rw_cells _ _ DT [C4 (Z_to_bv 64 ?e)] |- _ =>
        assert (E : e = mtl * 0x01000001 + tl * 65536)
          by (clear - MTL TLB; revert MTL TLB; revert tl; intros b Ha Hb; rk_zenum mtl; rk_zenum b; vm_compute; reflexivity);
        rewrite E in H; clear E end.
      repeat (lazymatch goal with
        | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
            let d := eval vm_compute in (z =? PHUF_RDT_X1 + 1012) in lazymatch d with true => fail | false => zstep end
        | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
            x1w_norm; first [x1w_dec_if | x1w_ck | x1w_decl | let U := fresh "TK" in x1w_br U] end).
      all: match goal with H : rw_cells _ _ (W + 52) ?cs |- _ =>
        let wsl := rk_c4ws cs in let n := eval cbn [length] in (length wsl) in
        let k := eval vm_compute in (Z.of_nat n - 1) in
        assert (TLk : tl = k) by lia; subst tl end.
      all: repeat (match goal with H : context [bv_swrap 32 _] |- _ => rewrite swrap32_small in H by lia end).
      all: x1w_norm.
      all: match goal with H : rw_cells _ ?mm W _ |- _ =>
        assert (RKw : u32arr usegs mm W (map (Z_to_bv 64) rank)) by (rewrite (rk_list13 rank LR13); apply rk_cells_u32arr; exact H) end.
      all: match goal with H : rw_cells _ _ (W + 52) ?cs |- _ =>
        let wsl := rk_c4ws cs in let n0 := eval cbn [length] in (length wsl) in
        let k := eval vm_compute in (Z.of_nat n0 - 1) in
        first [ let p := rk_lastcb cs in lazymatch p with (?n, ?bs) =>
                  destruct (rk_rs_u32 _ _ cs wsl n bs eq_refl H eq_refl) as (jw & LJW & RSW);
                  eapply (X1012 _ h ws rank k rs (wsl ++ jw)) end
              | pose proof (rk_rs_u32' _ _ cs wsl eq_refl H) as RSW;
                eapply (X1012 _ h ws rank k rs wsl) ] end.
      all: try first [ eassumption | (unfold hk; lia) | lia | reflexivity ].
      all: try (intros i Hi; rk_zenum i;
        repeat (match goal with |- context [Z.to_nat ?z] => lazymatch z with Z0 => idtac | Zpos _ => idtac end;
                  let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v end);
        cbn [nth_error app]; unfold FseNCount.Znth;
        repeat (match goal with |- context [Z.to_nat ?z] => lazymatch z with Z0 => idtac | Zpos _ => idtac end;
                  let v := eval vm_compute in (Z.to_nat z) in change (Z.to_nat z) with v end);
        rewrite RSV by lia; cbn [rk_psum]; do 2 f_equal; lia).
      all: rewrite length_app, LJW; reflexivity.
  Qed.
End TOP.
End CANSEC.
(* [comment removed for export] *)
