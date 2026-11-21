(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffFib HuffHeap HuffBuild HuffBuild2 HuffGen.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Definition isum (f : Z -> Z) (n : Z) : Z := zsum (map f (ziota 1 (Z.to_nat n))).

Lemma isum_snoc : forall f n, 0 <= n -> isum f (n + 1) = isum f n + f (n + 1).
Proof.
  intros f n Hn. unfold isum. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite ziota_S_r, map_app, zsum_app. cbn. replace (1 + Z.of_nat (Z.to_nat n)) with (n + 1) by lia. lia.
Qed.
Lemma isum_0 : forall f, isum f 0 = 0.
Proof. reflexivity. Qed.
Lemma isum_ext : forall f g n, (forall i, 1 <= i <= n -> f i = g i) -> isum f n = isum g n.
Proof. intros. unfold isum. apply zsum_map_ext. intros i Hi. apply in_ziota in Hi. apply H. lia. Qed.
Lemma isum_add : forall f g n, isum (fun i => f i + g i) n = isum f n + isum g n.
Proof. intros. unfold isum. apply zsum_map_add. Qed.
Lemma isum_mul : forall c f n, isum (fun i => c * f i) n = c * isum f n.
Proof. intros. unfold isum. apply zsum_map_mul. Qed.

Lemma regroup : forall (l : list Z) (m g : Z -> Z) (M : Z), 0 <= M ->
  (forall j, In j l -> 1 <= m j <= M) ->
  zsum (map (fun j => g (m j)) l) = isum (fun b => zsum (map (fun j => if m j =? b then 1 else 0) l) * g b) M.
Proof.
  intros l m g M HM Hm. induction l as [|j l IH].
  - cbn [map zsum]. unfold isum. symmetry.
    etransitivity; [apply zsum_map_ext; intros; cbn [map zsum]; apply Z.mul_0_l|].
    generalize (ziota 1 (Z.to_nat M)). clear. induction l; cbn; lia.
  - cbn [map zsum]. rewrite IH by (intros; apply Hm; now right).
    pose proof (Hm j (or_introl eq_refl)) as Hj.
    transitivity (isum (fun b => (if m j =? b then 1 else 0) * g b + zsum (map (fun j0 : Z => if m j0 =? b then 1 else 0) l) * g b) M).
    + rewrite isum_add. f_equal.
      unfold isum. rewrite <- (Z2Nat.id M) in Hj by lia.
      generalize (Z.to_nat M) Hj. clear. intros n. revert j.
      assert (G : forall a n, (forall j, a <= m j < a + Z.of_nat n -> g (m j) = zsum (map (fun b : Z => (if m j =? b then 1 else 0) * g b) (ziota a n)))
                /\ (forall j, ~ (a <= m j < a + Z.of_nat n) -> 0 = zsum (map (fun b : Z => (if m j =? b then 1 else 0) * g b) (ziota a n)))).
      { clear n. intros a n. revert a. induction n as [|n IH]; intros a.
        - split; intros; cbn in *; lia.
        - rewrite Nat2Z.inj_succ. split; intros; cbn [ziota map zsum].
          + destruct (Z.eqb_spec (m j) a).
            * rewrite <- (proj2 (IH (a + 1)) j) by lia. rewrite e. lia.
            * rewrite <- (proj1 (IH (a + 1)) j) by lia. lia.
          + destruct (Z.eqb_spec (m j) a); [lia|]. rewrite <- (proj2 (IH (a + 1)) j) by lia. lia. }
      intros j Hj. apply (proj1 (G 1 n) j). lia.
    + apply isum_ext. intros b Hb. lia.
Qed.

Lemma isum_nonneg : forall f n, (forall i, 1 <= i <= n -> 0 <= f i) -> 0 <= isum f n.
Proof.
  intros f n H. unfold isum. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (i & <- & Hi).
  apply in_ziota in Hi. apply H. lia.
Qed.

Lemma isum_le1 : forall f n i0, 0 <= n -> 1 <= i0 <= n -> (forall i, 1 <= i <= n -> 0 <= f i) -> f i0 <= isum f n.
Proof.
  intros f n i0 Hn Hi0 H.
  rewrite (isum_ext f (fun i => (if i =? i0 then f i0 else 0) + (if i =? i0 then 0 else f i)) n) by (intros; destruct (Z.eqb_spec i i0); subst; lia).
  rewrite isum_add.
  assert (isum (fun i => if i =? i0 then f i0 else 0) n = f i0).
  { unfold isum. rewrite <- (Z2Nat.id n) in Hi0 by lia. revert Hi0. generalize (Z.to_nat n). clear.
    assert (G : forall q a, (a <= i0 < a + Z.of_nat q -> zsum (map (fun i : Z => if i =? i0 then f i0 else 0) (ziota a q)) = f i0)
                        /\ (~ (a <= i0 < a + Z.of_nat q) -> zsum (map (fun i : Z => if i =? i0 then f i0 else 0) (ziota a q)) = 0)).
    { induction q as [|q IH]; intros a; [cbn; split; intros; lia|]. rewrite Nat2Z.inj_succ. cbn [ziota map zsum].
      destruct (IH (a + 1)) as [A B]. split; intros; destruct (Z.eqb_spec a i0); first [rewrite B; lia | rewrite A; lia | lia]. }
    intros q Hq. apply (proj1 (G q 1)). lia. }
  pose proof (isum_nonneg (fun i => if i =? i0 then 0 else f i) n ltac:(intros; cbn beta; destruct (Z.eqb_spec i i0); [lia| apply H; lia])) as NN0. lia.
Qed.


Section Gen2.
Variables (s : deflate_state) (t : tree_id) (FC0 : arr) (BC : arr) (OL SL : Z).
Variables (FC DL HP DP : arr) (sub : Z -> htree).

Local Set Warnings "-notation-for-abbreviation".
Local Notation elems := (sd_elems t).
Local Notation UPl := (UP FC0 t).
Local Notation FPf := (FP FC0 t).
Local Notation uu := (u t FC0).
Local Notation MCv := (MCP FC0 t).
Local Notation ML := (sd_max_length t).
Local Notation hm := (hm t FC0).
Local Notation HP7 := (HP7 t FC0 HP).
Local Notation nd := (nd DL HP).
Local Notation leafp := (leafp t FC0 HP).
Local Notation SUM := (SUM t FC0).
Local Notation rng := (rng t FC0).
Local Notation xb := (xbits t).

Hypothesis INV : Inv4 t FC0 (uu - 1) FC DL HP 1 hm DP sub.

Let U2 := u_ge2 t FC0.
Let RV := root_val t FC0 FC DL HP DP sub INV.
Let H7v := HP7v t FC0 FC DL HP DP sub INV.
Let H7hi := HP7_hi t FC0 FC DL HP DP sub INV.
Let H7root := HP7_root t FC0 FC DL HP DP sub INV.
Let H7inj := HP7_inj t FC0 FC DL HP DP sub INV.
Let PPOS := parent_pos t FC0 FC DL HP DP sub INV.
Let IDR := ids_range t FC0 FC DL HP DP sub INV.
Let RINT := root_internal t FC0 FC DL HP DP sub INV.
Let NDS := nd_step t FC0 FC DL HP DP sub INV.
Let NDNN := nd_nonneg t FC0 FC DL HP DP sub INV.
Let MCF := MC_facts t FC0 FC DL HP DP sub INV.
Let LPOS := leaf_positions t FC0 FC DL HP DP sub INV.
Let NDSUB := nd_sub t FC0 FC DL HP DP sub INV.
Let SUML := SUM_leaves t FC0 FC DL HP DP sub INV.
Let MLR := ML_range t FC0 FC DL HP DP sub INV.

Let k : Z := uu - 1.
Let y (i : Z) : Z := elems + i - 1.


Definition phi (d : Z) : Z := 2 ^ (ML - Z.min d ML).

Lemma phi_succ : forall d, 0 <= d -> 2 * phi (d + 1) = phi d + (if ML <=? d then 1 else 0).
Proof.
  intros d Hd. unfold phi. pose proof MLR. destruct (Z.leb_spec ML d).
  - rewrite !Z.min_r by lia. rewrite Z.sub_diag. cbn. lia.
  - rewrite !Z.min_l by lia. replace (ML - d) with (1 + (ML - (d + 1))) by lia.
    rewrite Z.pow_add_r by lia. cbn. lia.
Qed.

Lemma SUM_pairs : forall f n, 0 <= n -> SUM f (hm + 2 * n) = zsum (map (fun m => f (hm + 2 * m) + f (hm + 2 * m + 1)) (ziota 0 (Z.to_nat n))).
Proof.
  intros f n Hn. rewrite <- (Z2Nat.id n) at 1 by lia. induction (Z.to_nat n) as [|m IH].
  - cbn. rewrite Z.add_0_r. apply SUM_hm.
  - rewrite ziota_S_r, map_app, zsum_app. cbn [map zsum]. rewrite <- IH.
    rewrite Nat2Z.inj_succ. replace (hm + 2 * Z.succ (Z.of_nat m)) with (hm + 2 * Z.of_nat m + 1 + 1) by lia.
    rewrite !SUM_snoc by (pose proof U2; lia). replace (0 + Z.of_nat m) with (Z.of_nat m) by lia. lia.
Qed.

Lemma hm_k : hm = 573 - 2 * k /\ 1 <= k <= 285 /\ 19 <= elems <= 286 /\ k + 1 <= elems.
Proof. pose proof U2. subst k. unfold HuffGen.hm in *. lia. Qed.

Lemma child_depth : forall m, 0 <= m < k ->
  nd (arr_get HP7 (hm + 2 * m)) = nd (y (k - m)) + 1 /\ nd (arr_get HP7 (hm + 2 * m + 1)) = nd (y (k - m)) + 1.
Proof.
  intros m Hm. pose proof hm_k as (E & K & EL & _). pose proof INV as [? ? ? ? ? ? ? i_dad].
  split; rewrite NDS by lia; rewrite H7hi by lia; rewrite i_dad by lia; subst y; f_equal; f_equal; lia.
Qed.

Lemma y_pos : forall i, 1 <= i <= k -> exists h, hm - 1 <= h <= 572 /\ arr_get HP7 h = y i /\ (i < k -> hm <= h).
Proof.
  intros i Hi. pose proof hm_k as (E & K & EL & _). pose proof INV as [? ? ? ? ? ? i_int].
  destruct (i_int i ltac:(subst k; lia)) as (p & Hp & Ep). subst y.
  destruct Hp as [Hp|Hp].
  - assert (p = 1) by lia. subst p. exists (hm - 1). rewrite H7root.
    unfold root. split; [lia|]. split; [exact Ep|]. intros.
    pose proof RV as RV'. unfold root in RV'. subst k. lia.
  - exists p. rewrite H7hi by lia. split; [lia|]. split; [exact Ep| lia].
Qed.

Lemma nd_y_nonneg : forall i, 1 <= i <= k -> 0 <= nd (y i).
Proof.
  intros i Hi. destruct (y_pos i Hi) as (h & Hh & Eh & _). rewrite <- Eh. apply NDNN. lia.
Qed.

Lemma y_root : y k = root HP /\ nd (y k) = 0.
Proof.
  pose proof RV as RV'. subst y k.
  split; [lia|]. replace (elems + (uu - 1) - 1) with (root HP) by lia. apply nd_root.
Qed.

Lemma internal_positions :
  Permutation (map (arr_get HP7) (filter (fun h => negb (leafp h)) (rng 573))) (map y (ziota 1 (Z.to_nat (k - 1)))).
Proof.
  pose proof hm_k as (E & K & EL & _). pose proof MCF as [MCr LF].
  apply NoDup_Permutation.
  - apply NoDup_map_on; [apply NoDup_filter; apply NoDup_ziota|].
    intros a b Ha Hb Eq. apply filter_In in Ha. apply filter_In in Hb. destruct Ha as [Ha _], Hb as [Hb _].
    unfold HuffGen.rng in Ha, Hb. apply in_ziota in Ha. apply in_ziota in Hb.
    apply H7inj; lia.
  - apply NoDup_map_on; [apply NoDup_ziota|]. intros a b _ _ Eq. subst y. cbn beta in Eq. lia.
  - intros x. rewrite !in_map_iff. split.
    + intros (h & <- & Hh). apply filter_In in Hh. destruct Hh as [Hh NL]. unfold HuffGen.rng in Hh. apply in_ziota in Hh.
      pose proof (IDR h ltac:(lia)) as [R1 R2].
      assert (~ arr_get HP7 h < elems).
      { intros Hl. apply (proj2 (LF h ltac:(lia))) in Hl. rewrite Hl in NL. discriminate. }
      assert (arr_get HP7 h <> root HP).
      { rewrite <- H7root. intros Eq. apply H7inj in Eq; lia. }
      pose proof RV.
      exists (arr_get HP7 h - elems + 1). split; [subst y; cbn beta; lia|]. apply in_ziota. subst k. lia.
    + intros (i & <- & Hi). apply in_ziota in Hi. destruct (y_pos i ltac:(lia)) as (h & Hh & Eh & Hh2).
      exists h. split; [exact Eh|]. apply filter_In. split; [unfold HuffGen.rng; apply in_ziota; lia|].
      destruct (leafp h) eqn:EQ; [|reflexivity]. exfalso. apply (proj1 (LF h ltac:(lia))) in EQ. rewrite Eh in EQ. subst y. cbn beta in EQ. lia.
Qed.

Definition N : Z := isum (fun i => if ML <=? nd (y i) then 1 else 0) k.
Definition K0 : Z := zsum (map (fun j => phi (nd j)) UPl).

Theorem excess_identity : K0 = 2 ^ ML + N /\ SUM (ovff t FC0 DL HP) 573 = 2 * N /\ 0 <= N.
Proof.
  pose proof hm_k as (E & K & EL & _). pose proof MCF as [MCr LF].
  assert (S1 : SUM (fun h => phi (nd (arr_get HP7 h))) 573 = isum (fun i => 2 * phi (nd (y i) + 1)) k).
  { replace 573 with (hm + 2 * k) by lia. rewrite SUM_pairs by lia.
    unfold isum.
    assert (G : forall n, (n <= Z.to_nat k)%nat ->
      zsum (map (fun m : Z => phi (nd (arr_get HP7 (hm + 2 * m))) + phi (nd (arr_get HP7 (hm + 2 * m + 1)))) (ziota 0 n))
      = zsum (map (fun i : Z => 2 * phi (nd (y i) + 1)) (ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n + 1) n))).
    { induction n as [|n IH]; intros Hn; [reflexivity|].
      rewrite ziota_S_r, map_app, zsum_app. cbn [map zsum]. rewrite IH by lia.
      rewrite Nat2Z.inj_succ.
      replace (Z.of_nat (Z.to_nat k) - Z.succ (Z.of_nat n) + 1) with (Z.of_nat (Z.to_nat k) - Z.of_nat n) by lia.
      change (ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n) (S n)) with ((Z.of_nat (Z.to_nat k) - Z.of_nat n) :: ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n + 1) n).
      cbn [map zsum]. destruct (child_depth (Z.of_nat n) ltac:(lia)) as [C1 C2]. rewrite Z.add_0_l, C1, C2.
      replace (k - Z.of_nat n) with (Z.of_nat (Z.to_nat k) - Z.of_nat n) by lia. lia. }
    rewrite (G (Z.to_nat k)) by lia. f_equal. f_equal. f_equal; lia. }
  assert (S2 : SUM (fun h => phi (nd (arr_get HP7 h))) 573 = K0 + isum (fun i => phi (nd (y i))) (k - 1)).
  { unfold HuffGen.SUM.
    transitivity (zsum (map (fun h => (if leafp h then phi (nd (arr_get HP7 h)) else 0) + (if negb (leafp h) then phi (nd (arr_get HP7 h)) else 0)) (rng 573))).
    { apply zsum_map_ext. intros h _. destruct (leafp h); cbn; lia. }
    rewrite zsum_map_add. f_equal.
    - rewrite zsum_filter_map. unfold K0. rewrite <- (zsum_map_perm _ _ _ LPOS). rewrite map_map. reflexivity.
    - rewrite zsum_filter_map. unfold isum.
      transitivity (zsum (map (fun x => phi (nd x)) (map y (ziota 1 (Z.to_nat (k - 1)))))); [| rewrite map_map; reflexivity].
      rewrite <- (zsum_map_perm _ _ _ internal_positions). rewrite map_map. reflexivity. }
  assert (S3 : isum (fun i => 2 * phi (nd (y i) + 1)) k = isum (fun i => phi (nd (y i))) k + N).
  { unfold N. rewrite <- isum_add. apply isum_ext. intros i Hi. apply phi_succ. apply nd_y_nonneg. lia. }
  assert (S4 : isum (fun i => phi (nd (y i))) k = isum (fun i => phi (nd (y i))) (k - 1) + 2 ^ ML).
  { replace k with (k - 1 + 1) at 1 by lia. rewrite isum_snoc by lia. replace (k - 1 + 1) with k by lia.
    destruct y_root as [_ ->]. unfold phi. pose proof MLR. rewrite Z.min_l, Z.sub_0_r by lia. reflexivity. }
  assert (NN : 0 <= N).
  { unfold N, isum. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (i & <- & _). destruct (ML <=? _); lia. }
  split; [lia|]. split; [|exact NN].
  replace 573 with (hm + 2 * k) by lia. rewrite SUM_pairs by lia. unfold N, isum.
  assert (G : forall n, (n <= Z.to_nat k)%nat ->
    zsum (map (fun m : Z => ovff t FC0 DL HP (hm + 2 * m) + ovff t FC0 DL HP (hm + 2 * m + 1)) (ziota 0 n))
    = 2 * zsum (map (fun i : Z => if ML <=? nd (y i) then 1 else 0) (ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n + 1) n))).
  { induction n as [|n IH]; intros Hn; [reflexivity|].
    rewrite ziota_S_r, map_app, zsum_app. cbn [map zsum]. rewrite IH by lia.
    rewrite Nat2Z.inj_succ.
    replace (Z.of_nat (Z.to_nat k) - Z.succ (Z.of_nat n) + 1) with (Z.of_nat (Z.to_nat k) - Z.of_nat n) by lia.
    change (ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n) (S n)) with ((Z.of_nat (Z.to_nat k) - Z.of_nat n) :: ziota (Z.of_nat (Z.to_nat k) - Z.of_nat n + 1) n).
    cbn [map zsum]. unfold ovff. destruct (child_depth (Z.of_nat n) ltac:(lia)) as [C1 C2]. rewrite Z.add_0_l, C1, C2.
    replace (k - Z.of_nat n) with (Z.of_nat (Z.to_nat k) - Z.of_nat n) by lia.
    destruct (Z.ltb_spec ML (nd (y (Z.of_nat (Z.to_nat k) - Z.of_nat n)) + 1)), (Z.leb_spec ML (nd (y (Z.of_nat (Z.to_nat k) - Z.of_nat n)))); lia. }
  rewrite (G (Z.to_nat k)) by lia. f_equal. f_equal. f_equal. f_equal; lia.
Qed.



Definition KB (B : Z -> Z) : Z := isum (fun b => B b * 2 ^ (ML - b)) ML.
Definition SlowB (B : Z -> Z) : Z := isum (fun b => B b * 2 ^ (ML - b)) (ML - 1).
Definition cntB (B : Z -> Z) : Z := isum B ML.

Record LI (BCx : arr) (rex : Z) : Prop := LIc {
  li_len : arr_len BCx = 16;
  li_nn : forall b, 0 <= b <= 15 -> 0 <= arr_get BCx b;
  li_out : forall b, 0 <= b <= 15 -> (b < 1 \/ ML < b) -> arr_get BCx b = 0;
  li_cnt : cntB (arr_get BCx) = uu;
  li_K : KB (arr_get BCx) = 2 ^ ML + rex;
  li_rex : 0 <= rex;
  li_low : SlowB (arr_get BCx) <= 2 ^ ML }.

Lemma u_small : uu < 2 ^ ML /\ uu <= 286.
Proof.
  pose proof U2 as U. pose proof (UP_len_elems t FC0) as V. clear -U V.
  destruct t; cbn in *; unfold MAX_BITS, MAX_BL_BITS, L_CODES, D_CODES, BL_CODES in *; cbn; lia.
Qed.

Lemma find_spec2 : forall DLx f BCx b,
  (exists b0, b - Z.of_nat f < b0 <= b /\ arr_get BCx b0 <> 0) ->
  let r := gen_bitlen_find f (bt_upd s t FC DLx HP7 1 (hm - 1) DP BCx 0 0 0) b in
  b - Z.of_nat f < r <= b /\ arr_get BCx r <> 0 /\ forall j, r < j <= b -> arr_get BCx j = 0.
Proof.
  intros DLx. induction f as [|f IH]; intros BCx b (b0 & Hb0 & Nz); [cbn in Hb0; lia|].
  cbn [gen_bitlen_find]. unfold bl_count_get. autorewrite with btupd. rewrite Nat2Z.inj_succ in *.
  destruct (Z.eqb_spec (arr_get BCx b) 0).
  - destruct (IH BCx (b - 1)) as (A1 & A2 & A3).
    { exists b0. split; [|exact Nz]. destruct (Z.eq_dec b0 b); [subst; congruence| lia]. }
    cbv zeta. split; [lia|]. split; [exact A2|]. intros j Hj. destruct (Z.eq_dec j b); [subst; exact e| apply A3; lia].
  - cbv zeta. split; [lia|]. split; [exact n|]. intros; lia.
Qed.

Local Notation X6 DLc BCc OLc SLc := (bt_upd s t FC DLc HP7 1 (hm - 1) DP BCc OLc SLc MCv).

Lemma loop2_trip : forall DLx BCx rex, LI BCx rex -> 1 <= rex ->
  let r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DLx HP7 1 (hm - 1) DP BCx 0 0 0) (ML - 1) in
  LI (bl_adj ML BCx r) (rex - 1).
Proof.
  intros DLx BCx rex [LEN NN OUT CNT K REX LOW] Hrex. pose proof MLR as MR. pose proof u_small as US.
  set (B := arr_get BCx) in *.
  assert (EX : exists b0, ML - 1 - Z.of_nat (Z.to_nat ML) < b0 <= ML - 1 /\ B b0 <> 0).
  { destruct (Z_le_gt_dec (SlowB B) 0) as [Z0|POS].
    - exfalso. unfold KB in K. unfold SlowB in Z0.
      replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia. replace (ML - 1 + 1) with ML in K by lia.
      rewrite Z.sub_diag, Z.pow_0_r in K.
      pose proof (isum_le1 B ML ML ltac:(lia) ltac:(lia) ltac:(intros; apply NN; lia)) as LE. unfold cntB in CNT. rewrite CNT in LE.
      pose proof (isum_nonneg (fun b => B b * 2 ^ (ML - b)) (ML - 1) ltac:(intros; apply Z.mul_nonneg_nonneg; [apply NN; lia| apply Z.pow_nonneg; lia])). lia.
    -
      assert (EXb : exists b0, 1 <= b0 <= ML - 1 /\ B b0 <> 0).
      { unfold SlowB, isum in POS.
        destruct (Exists_dec (fun x => x <> 0) (map (fun b => B b * 2 ^ (ML - b)) (ziota 1 (Z.to_nat (ML - 1))))) as [E|NE].
        { intros x. destruct (Z.eq_dec x 0); [right; lia| left; lia]. }
        - apply Exists_exists in E. destruct E as (x & Hx & Nx). apply in_map_iff in Hx. destruct Hx as (b0 & <- & Hb0).
          apply in_ziota in Hb0. exists b0. split; [lia|]. intros E0. apply Nx. rewrite E0. lia.
        - exfalso. apply Forall_Exists_neg in NE.
          assert (zsum (map (fun b : Z => B b * 2 ^ (ML - b)) (ziota 1 (Z.to_nat (ML - 1)))) = 0); [|lia].
          revert NE. generalize (map (fun b : Z => B b * 2 ^ (ML - b)) (ziota 1 (Z.to_nat (ML - 1)))). clear.
          induction l; intros NE; [reflexivity|]. inversion NE; subst. cbn. rewrite IHl by assumption. lia. }
      destruct EXb as (b0 & Hb0 & Nb0). exists b0. split; [lia| exact Nb0]. }
  pose proof (find_spec2 DLx (Z.to_nat ML) BCx (ML - 1) EX) as FS. cbv zeta in FS. fold B in FS.
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DLx HP7 1 (hm - 1) DP BCx 0 0 0) (ML - 1)) in *.
  destruct FS as (Hr & Br & Zr).
  assert (Hr1 : 1 <= r <= ML - 1).
  { split; [|lia]. destruct (Z_le_gt_dec 1 r); [assumption|]. exfalso. apply Br. apply OUT; lia. }
  pose proof (NN r ltac:(lia)) as NNr.
  assert (LEu : forall b, 1 <= b <= ML -> B b <= uu).
  { intros b Hb. rewrite <- CNT. unfold cntB. apply isum_le1; [lia| lia| intros; apply NN; lia]. }
  assert (BML : rex <= B ML).
  { unfold KB in K. unfold SlowB in LOW. replace ML with (ML - 1 + 1) in K at 1 by lia. rewrite isum_snoc in K by lia.
    replace (ML - 1 + 1) with ML in K by lia. rewrite Z.sub_diag, Z.pow_0_r in K. lia. }
  assert (ADJ : forall b, arr_get (bl_adj ML BCx r) b =
            if b =? ML then (if r + 1 =? ML then B (r + 1) + 2 else B ML) - 1
            else if b =? r + 1 then B (r + 1) + 2
            else if b =? r then B r - 1 else B b).
  { intros b. unfold bl_adj. rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set, LEN. fold B.
    pose proof (LEu r ltac:(lia)). pose proof (LEu (r + 1) ltac:(lia)). pose proof (LEu ML ltac:(lia)). pose proof (NN (r + 1) ltac:(lia)). pose proof (NN ML ltac:(lia)).
    replace ((0 <=? ML) && (ML <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    replace ((0 <=? r + 1) && (r + 1 <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    replace ((0 <=? r) && (r <? 16)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    rewrite !Bool.andb_true_r.
    replace (r =? r + 1) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (r =? ML) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (Z.eqb_sym ML b), (Z.eqb_sym (r + 1) b), (Z.eqb_sym r b).
    destruct (Z.eqb_spec b ML); destruct (Z.eqb_spec (r + 1) ML); destruct (Z.eqb_spec b (r + 1)); destruct (Z.eqb_spec b r);
      subst; try lia; rewrite ?(wrap16_id (B (r + 1) + 2)) by lia; rewrite ?(wrap16_id (B r - 1)) by lia; rewrite ?wrap16_id by lia; try reflexivity; lia. }
  assert (DSUM : forall (w : Z -> Z) n, 0 <= n -> r <= n -> n <= ML ->
            isum (fun b => arr_get (bl_adj ML BCx r) b * w b) n
            = isum (fun b => B b * w b) n - w r + (if r + 1 <=? n then 2 * w (r + 1) else 0) - (if n =? ML then w ML else 0)).
  { intros w n Hn Hrn HnM.
    rewrite (isum_ext (fun b => arr_get (bl_adj ML BCx r) b * w b)
              (fun b => B b * w b + ((if b =? r then - w r else 0) + ((if b =? r + 1 then 2 * w (r + 1) else 0) + (if b =? ML then - w ML else 0)))) n).
    2:{ intros b Hb. rewrite ADJ.
        destruct (Z.eqb_spec (r + 1) ML) as [EQ|NE].
        - rewrite <- EQ. destruct (Z.eqb_spec b (r + 1)); [subst b; destruct (Z.eqb_spec (r + 1) r); [lia|]; lia|].
          destruct (Z.eqb_spec b r); [subst b; lia| lia].
        - destruct (Z.eqb_spec b ML); [subst b; destruct (Z.eqb_spec ML (r + 1)); [lia|]; destruct (Z.eqb_spec ML r); [lia|]; lia|].
          destruct (Z.eqb_spec b (r + 1)); [subst b; destruct (Z.eqb_spec (r + 1) r); [lia|]; lia|].
          destruct (Z.eqb_spec b r); [subst b; lia| lia]. }
    rewrite !isum_add.
    assert (IND : forall c (v : Z) n', 0 <= n' -> isum (fun b => if b =? c then v else 0) n' = if (1 <=? c) && (c <=? n') then v else 0).
    { clear. intros c v n' Hn'. unfold isum. rewrite <- (Z2Nat.id n') at 2 by lia. generalize (Z.to_nat n') as q. clear n' Hn'. intros q.
      assert (G : forall a, zsum (map (fun b : Z => if b =? c then v else 0) (ziota a q)) = (if (a <=? c) && (c <=? a + Z.of_nat q - 1) then v else 0)).
      { induction q as [|q IH]; intros a; cbn [ziota map zsum].
        - change (Z.of_nat 0) with 0. destruct (Z.leb_spec a c), (Z.leb_spec c (a + 0 - 1)); cbn [andb]; lia.
        - rewrite IH. rewrite Nat2Z.inj_succ.
          destruct (Z.eqb_spec a c), (Z.leb_spec a c), (Z.leb_spec (a + 1) c), (Z.leb_spec c (a + 1 + Z.of_nat q - 1)), (Z.leb_spec c (a + Z.succ (Z.of_nat q) - 1)); cbn [andb]; lia. }
      rewrite G. destruct (Z.leb_spec 1 c), (Z.leb_spec c (1 + Z.of_nat q - 1)), (Z.leb_spec c (Z.of_nat q)); cbn [andb]; lia. }
    rewrite !IND by lia.
    replace ((1 <=? r) && (r <=? n)) with true by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
    replace (1 <=? r + 1) with true by (symmetry; rewrite Z.leb_le; lia). cbn [andb].
    destruct (Z.eqb_spec n ML).
    - subst n. replace ((1 <=? ML) && (ML <=? ML)) with true by (symmetry; rewrite Bool.andb_true_iff, !Z.leb_le; lia).
      destruct (Z.leb_spec (r + 1) ML); lia.
    - replace ((1 <=? ML) && (ML <=? n)) with false by (symmetry; rewrite Bool.andb_false_iff, !Z.leb_gt; lia).
      destruct (Z.leb_spec (r + 1) n); lia. }
  split.
  - unfold bl_adj. rewrite !arr_len_set. exact LEN.
  - intros b Hb. rewrite ADJ. pose proof (NN b Hb). pose proof (NN (r + 1) ltac:(lia)). pose proof (NN ML ltac:(lia)).
    destruct (Z.eqb_spec b ML); [destruct (Z.eqb_spec (r + 1) ML); lia|].
    destruct (Z.eqb_spec b (r + 1)); [lia|]. destruct (Z.eqb_spec b r); lia.
  - intros b Hb Hout. rewrite ADJ. destruct (Z.eqb_spec b ML); [lia|]. destruct (Z.eqb_spec b (r + 1)); [lia|].
    destruct (Z.eqb_spec b r); [lia|]. apply OUT; assumption.
  - unfold cntB. rewrite <- (isum_ext (fun b => arr_get (bl_adj ML BCx r) b * 1)) by (intros; lia).
    rewrite DSUM by lia. rewrite Z.eqb_refl. replace (r + 1 <=? ML) with true by (symmetry; apply Z.leb_le; lia). unfold cntB in CNT. rewrite <- CNT.
    rewrite <- (isum_ext (fun b => B b * 1) B) by (intros; lia). lia.
  - unfold KB. rewrite DSUM by lia. rewrite Z.eqb_refl. replace (r + 1 <=? ML) with true by (symmetry; apply Z.leb_le; lia). unfold KB in K. rewrite K.
    rewrite Z.sub_diag, Z.pow_0_r. replace (ML - r) with (1 + (ML - (r + 1))) by lia. rewrite Z.pow_add_r by lia. replace (2 ^ 1) with 2 by reflexivity. lia.
  - lia.
  - unfold SlowB. rewrite DSUM by lia. unfold SlowB in LOW.
    destruct (Z.eqb_spec (ML - 1) ML); [lia|].
    replace (ML - r) with (1 + (ML - (r + 1))) by lia. rewrite Z.pow_add_r by lia. replace (2 ^ 1) with 2 by reflexivity.
    pose proof (Z.pow_nonneg 2 (ML - (r + 1)) ltac:(lia)). destruct (Z.leb_spec (r + 1) (ML - 1)); lia.
Qed.

Lemma gb_loop2 : forall DLx OLx SLx f BCx rex, LI BCx rex -> 1 <= rex -> (Z.to_nat rex <= f)%nat ->
  exists BCf, gen_bitlen_loop2 f (X6 DLx BCx OLx SLx) ML (2 * rex) = X6 DLx BCf OLx SLx /\ LI BCf 0.
Proof.
  intros DLx OLx SLx. induction f as [|f IH]; intros BCx rex L Hrex Hf; [lia|].
  pose proof (GL2_step t ML f s FC DLx HP7 1 (hm - 1) DP BCx OLx SLx MCv (2 * rex)) as E. cbv zeta in E. rewrite E. clear E.
  rewrite (find_flat t (Z.to_nat ML) s FC DLx HP7 1 (hm - 1) DP BCx OLx SLx MCv).
  pose proof (loop2_trip DLx BCx rex L Hrex) as L1. cbv zeta in L1.
  destruct (Z.ltb_spec 0 (2 * rex - 2)).
  - replace (2 * rex - 2) with (2 * (rex - 1)) by lia. apply IH; [exact L1| lia| lia].
  - eexists. split; [reflexivity|]. replace (rex - 1) with 0 in L1 by lia. exact L1.
Qed.



Definition ind (h : Z) : Z := if leafp h then 1 else 0.

Lemma SUM_ext : forall f g h, (forall q, hm <= q < h -> f q = g q) -> SUM f h = SUM g h.
Proof.
  intros f g h E. unfold HuffGen.SUM. apply zsum_map_ext. intros q Hq. unfold HuffGen.rng in Hq. apply in_ziota in Hq. apply E. lia.
Qed.

Definition RS (f : Z -> Z) (a b : Z) : Z := SUM f b - SUM f a.

Lemma RS_snoc : forall f a b, hm <= a <= b -> RS f a (b + 1) = RS f a b + f b.
Proof. intros. unfold RS. rewrite SUM_snoc by lia. lia. Qed.
Lemma RS_nil : forall f a, RS f a a = 0.
Proof. intros. unfold RS. lia. Qed.
Lemma RS_ind : forall f a b (P : Z -> Prop),
  hm <= a <= b -> P 0 -> (forall q acc, a <= q < b -> P acc -> P (acc + f q)) -> P (RS f a b).
Proof.
  intros f a b P Hab H0 Hs. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  assert (G : forall n, (n <= Z.to_nat (b - a))%nat -> P (RS f a (a + Z.of_nat n))).
  { induction n as [|n IH]; intros Hn; [rewrite Z.add_0_r, RS_nil; exact H0|].
    rewrite Nat2Z.inj_succ. replace (a + Z.succ (Z.of_nat n)) with (a + Z.of_nat n + 1) by lia.
    rewrite RS_snoc by lia. apply Hs; [lia|]. apply IH. lia. }
  apply G. lia.
Qed.
Lemma RS_ext : forall f g a b, hm <= a <= b -> (forall q, a <= q < b -> f q = g q) -> RS f a b = RS g a b.
Proof.
  intros f g a b Hab E. replace b with (a + Z.of_nat (Z.to_nat (b - a))) in * by lia.
  induction (Z.to_nat (b - a)) as [|n IH]; [rewrite Z.add_0_r, !RS_nil; reflexivity|].
  rewrite Nat2Z.inj_succ in *. replace (a + Z.succ (Z.of_nat n)) with (a + Z.of_nat n + 1) in * by lia.
  rewrite !RS_snoc by lia. rewrite IH, E by (intros; try apply E; lia). reflexivity.
Qed.
Lemma RS_nonneg : forall f a b, hm <= a <= b -> (forall q, a <= q < b -> 0 <= f q) -> 0 <= RS f a b.
Proof. intros f a b Hab Hf. apply RS_ind; [lia| lia|]. intros q acc Hq Hacc. specialize (Hf q Hq). lia. Qed.
Lemma RS_scale : forall (c : Z) a b, hm <= a <= b -> RS (fun q => if leafp q then c else 0) a b = c * RS ind a b.
Proof.
  intros c a b Hab. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  induction (Z.to_nat (b - a)) as [|n IH]; [rewrite Z.add_0_r, !RS_nil; lia|].
  rewrite Nat2Z.inj_succ. replace (a + Z.succ (Z.of_nat n)) with (a + Z.of_nat n + 1) by lia.
  rewrite !RS_snoc by lia. rewrite IH. unfold ind. destruct (leafp (a + Z.of_nat n)); lia.
Qed.
Lemma RS_app : forall f a b c, RS f a b + RS f b c = RS f a c.
Proof. intros. unfold RS. lia. Qed.

Lemma ind_01 : forall q, 0 <= ind q <= 1.
Proof. intros. unfold ind. destruct (leafp q); lia. Qed.

Lemma gb_loop3i : forall BCx SLx f bits n h DLx OLx,
  hm <= h <= 573 -> 0 <= n <= RS ind hm h -> (Z.to_nat (h - hm) < f)%nat ->
  arr_len DLx = tsize t -> 1 <= bits <= ML -> 0 <= OLx < 2 ^ 64 ->
  exists h' DLx' OLx',
    gen_bitlen_loop3i f (X6 DLx BCx OLx SLx) t MCv bits n h = (X6 DLx' BCx OLx' SLx, h')
    /\ hm <= h' <= h /\ RS ind h' h = n /\ (0 < n -> leafp h' = true) /\ (n = 0 -> h' = h)
    /\ arr_len DLx' = tsize t /\ 0 <= OLx' < 2 ^ 64
    /\ (forall q, h' <= q < h -> leafp q = true -> arr_get DLx' (arr_get HP7 q) = bits)
    /\ (forall q, hm - 1 <= q <= 572 -> (q < h' \/ h <= q \/ leafp q = false) -> arr_get DLx' (arr_get HP7 q) = arr_get DLx (arr_get HP7 q))
    /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLx' j = arr_get DLx j)
    /\ OLx' = wrap64 (OLx + RS (fun q => if leafp q then (bits - arr_get DLx (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) h' h).
Proof.
  intros BCx SLx. induction f as [|f IH]; intros bits n h DLx OLx Hh Hn Hf LDLx Hbits HOL; [lia|].
  pose proof MCF as [MCr LF]. pose proof MLR as MR. pose proof (elems_tsize t) as ET.
  rewrite GL3i_step. destruct (Z.eqb_spec n 0) as [N0|N0]; cbn [negb].
  { subst n. exists h, DLx, OLx. split; [reflexivity|]. split; [lia|]. split; [rewrite RS_nil; reflexivity|]. split; [intros; lia|].
    split; [intros; reflexivity|]. split; [exact LDLx|]. split; [exact HOL|]. split; [intros; lia|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    rewrite RS_nil, Z.add_0_r. symmetry. apply wrap64_id. exact HOL. }
  assert (Hh1 : hm < h).
  { destruct (Z.eq_dec h hm); [|lia]. subst h. rewrite RS_nil in Hn. lia. }
  pose proof (GB3i_flat t MCv s FC DLx HP7 1 (hm - 1) DP BCx OLx SLx bits n h) as E. cbv zeta in E. rewrite E. clear E.
  assert (RSh : RS ind hm h = RS ind hm (h - 1) + ind (h - 1)).
  { replace h with (h - 1 + 1) at 1 by lia. rewrite RS_snoc by lia. reflexivity. }
  destruct (Z.ltb_spec MCv (arr_get HP7 (h - 1))) as [INT|LEAF].
  -
    assert (NL : leafp (h - 1) = false) by (unfold HuffGen.leafp; apply Bool.negb_false_iff; apply Z.ltb_lt; exact INT).
    assert (I0 : ind (h - 1) = 0) by (unfold ind; rewrite NL; reflexivity).
    destruct (IH bits n (h - 1) DLx OLx ltac:(lia) ltac:(lia) ltac:(lia) LDLx Hbits HOL) as (h' & DLx' & OLx' & E1 & R1 & C1 & LP & Z0 & L1 & O1 & A1 & U1 & Z1 & S1).
    exists h', DLx', OLx'. split; [exact E1|]. split; [lia|].
    split; [replace h with (h - 1 + 1) by lia; rewrite RS_snoc by lia; replace (h - 1 + 1 - 1) with (h - 1) by lia; lia|].
    split; [exact LP|]. split; [intros; lia|]. split; [exact L1|]. split; [exact O1|].
    split; [intros q Hq Lq; destruct (Z.eq_dec q (h - 1)); [subst; congruence| apply A1; lia || exact Lq]|].
    split; [intros q Hq Hc; apply U1; [lia|]; destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; lia| right; right; exact Hc]|]. split; [exact Z1|].
    rewrite S1. replace h with (h - 1 + 1) at 2 by lia. rewrite RS_snoc by lia. replace (h - 1 + 1 - 1) with (h - 1) by lia. rewrite NL. f_equal. lia.
  -
    assert (YL : leafp (h - 1) = true) by (unfold HuffGen.leafp; apply Bool.negb_true_iff; apply Z.ltb_ge; exact LEAF).
    assert (I1 : ind (h - 1) = 1) by (unfold ind; rewrite YL; reflexivity).
    set (m := arr_get HP7 (h - 1)) in *.
    pose proof (IDR (h - 1) ltac:(lia)) as [Rm Lm]. fold m in Rm, Lm.
    set (DL1 := if arr_get DLx m =? bits then DLx else arr_set DLx m (wrap16 bits)).
    set (OL1 := if arr_get DLx m =? bits then OLx else wrap64 (OLx + (bits - arr_get DLx m) * arr_get FC m)).
    replace (if arr_get DLx m =? bits then (X6 DLx BCx OLx SLx, n - 1, h - 1) else (X6 (arr_set DLx m (wrap16 bits)) BCx (wrap64 (OLx + (bits - arr_get DLx m) * arr_get FC m)) SLx, n - 1, h - 1))
      with (X6 DL1 BCx OL1 SLx, n - 1, h - 1) by (subst DL1 OL1; destruct (arr_get DLx m =? bits); reflexivity).
    assert (LDL1 : arr_len DL1 = tsize t) by (subst DL1; destruct (arr_get DLx m =? bits); [exact LDLx| rewrite arr_len_set; exact LDLx]).
    assert (DL1v : forall x, arr_get DL1 x = if x =? m then bits else arr_get DLx x).
    { intros x. subst DL1. destruct (Z.eqb_spec (arr_get DLx m) bits).
      - destruct (Z.eqb_spec x m); [subst; auto| reflexivity].
      - rewrite arr_get_set, (Z.eqb_sym m x). destruct (Z.eqb_spec x m); cbn [andb]; [|reflexivity].
        rewrite inb_true by lia. apply wrap16_id. lia. }
    assert (OL1v : OL1 = wrap64 (OLx + (bits - arr_get DLx m) * arr_get FC m)).
    { subst OL1. destruct (Z.eqb_spec (arr_get DLx m) bits); [|reflexivity]. rewrite e, Z.sub_diag, Z.mul_0_l, Z.add_0_r. symmetry. apply wrap64_id. exact HOL. }
    assert (HOL1 : 0 <= OL1 < 2 ^ 64) by (rewrite OL1v; apply wrap64_range).
    clearbody DL1 OL1.
    destruct (IH bits (n - 1) (h - 1) DL1 OL1 ltac:(lia) ltac:(lia) ltac:(lia) LDL1 Hbits HOL1) as (h' & DLx' & OLx' & E1 & R1 & C1 & LP & Z0 & L1 & O1 & A1 & U1 & Z1 & S1).
    exists h', DLx', OLx'. split; [exact E1|]. split; [lia|].
    split; [replace h with (h - 1 + 1) by lia; rewrite RS_snoc by lia; replace (h - 1 + 1 - 1) with (h - 1) by lia; lia|].
    split; [intros; destruct (Z.eq_dec n 1); [rewrite Z0 by lia; exact YL|apply LP; lia]|].
    split; [intros; lia|].
    split; [exact L1|]. split; [exact O1|].
    split.
    { intros q Hq Lq. destruct (Z.eq_dec q (h - 1)).
      - subst q. rewrite U1; [| lia| right; left; lia]. fold m. rewrite DL1v, Z.eqb_refl. reflexivity.
      - rewrite A1 by (lia || exact Lq). reflexivity. }
    split.
    { intros q Hq Hc. rewrite U1; [| lia | destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; lia| right; right; exact Hc]]. rewrite DL1v.
      destruct (Z.eqb_spec (arr_get HP7 q) m); [|reflexivity]. exfalso. subst m. apply H7inj in e; try lia.
      subst q. destruct Hc as [Hc|[Hc|Hc]]; [lia| lia| congruence]. }
    split.
    { intros j Hj Hnj. rewrite Z1 by assumption. rewrite DL1v. destruct (Z.eqb_spec j m); [|reflexivity].
      exfalso. apply Hnj. subst j. apply (proj1 Lm). apply (proj1 (LF (h - 1) ltac:(lia))). exact YL. }
    rewrite S1, OL1v. rewrite BuildTreeModel.wrap64_add_l. f_equal.
    set (g := fun q : Z => if leafp q then (bits - arr_get DLx (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0).
    rewrite <- (RS_app g h' (h - 1) h).
    pose proof (RS_snoc g (h - 1) (h - 1) ltac:(lia)) as RR1. rewrite RS_nil in RR1. replace (h - 1 + 1) with h in RR1 by lia. rewrite RR1.
    replace (g (h - 1)) with ((bits - arr_get DLx m) * arr_get FC m) by (subst g m; cbn beta; rewrite YL; reflexivity).
    rewrite (RS_ext (fun q => if leafp q then (bits - arr_get DL1 (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) g); [lia| lia|].
    intros q Hq. subst g. cbn beta. rewrite DL1v. destruct (Z.eqb_spec (arr_get HP7 q) m); [|reflexivity].
    exfalso. subst m. apply H7inj in e; lia.
Qed.


Lemma leaves_count : SUM ind 573 = uu.
Proof.
  rewrite (SUML (fun _ => 1) ind).
  - unfold u. generalize UPl. clear. induction l; [reflexivity|]. cbn [map zsum]. rewrite IHl, zlen_cons. lia.
  - intros h Hh Lh. unfold ind. rewrite Lh. reflexivity.
  - intros h Hh Lh. unfold ind. rewrite Lh. reflexivity.
Qed.

Section Outer.
Variables (DLc BCf : arr) (OLc SLx : Z).
Hypothesis LIf : LI BCf 0.
Hypothesis OLcr : 0 <= OLc < 2 ^ 64.
Let B := arr_get BCf.

Record OI (bits h : Z) (DLx : arr) (OLx : Z) : Prop := OIc {
  oi_len : arr_len DLx = tsize t;
  oi_h : hm <= h <= 573;
  oi_done : RS ind h 573 = isum B ML - isum B bits;
  oi_rng : forall q, h <= q <= 572 -> leafp q = true -> bits + 1 <= arr_get DLx (arr_get HP7 q) <= ML;
  oi_mono : forall q1 q2, h <= q1 <= q2 -> q2 <= 572 -> leafp q1 = true -> leafp q2 = true ->
              arr_get DLx (arr_get HP7 q1) <= arr_get DLx (arr_get HP7 q2);
  oi_sum : forall g, RS (fun q => if leafp q then g (arr_get DLx (arr_get HP7 q)) else 0) h 573
             = isum (fun b => B b * g b) ML - isum (fun b => B b * g b) bits;
  oi_low : forall q, hm - 1 <= q <= 572 -> (q < h \/ leafp q = false) -> arr_get DLx (arr_get HP7 q) = arr_get DLc (arr_get HP7 q);
  oi_zero : forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLx j = arr_get DLc j;
  oi_olx : OLx = wrap64 (OLc + RS (fun q => if leafp q then (arr_get DLx (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) h 573) }.

Lemma OI_start : arr_len DLc = tsize t -> OI ML 573 DLc OLc.
Proof.
  intros L. pose proof U2. split.
  - exact L. - unfold HuffGen.hm in *; lia. - rewrite RS_nil. lia.
  - intros; lia. - intros; lia. - intros g. rewrite RS_nil. lia.
  - intros; reflexivity. - intros; reflexivity.
  - rewrite RS_nil, Z.add_0_r. symmetry. apply wrap64_id. exact OLcr.
Qed.

Lemma gb_loop3 : forall f bits h DLx OLx, 0 <= bits <= ML -> (Z.to_nat bits <= f)%nat -> OI bits h DLx OLx ->
  exists DLf OLf hf, gen_bitlen_loop3 f (X6 DLx BCf OLx SLx) t MCv bits h = X6 DLf BCf OLf SLx /\ OI 0 hf DLf OLf.
Proof.
  induction f as [|f IH]; intros bits h DLx OLx Hbits Hf O.
  { assert (bits = 0) by lia. subst bits. exists DLx, OLx, h. split; [reflexivity| exact O]. }
  rewrite GL3_step. destruct (Z.eqb_spec bits 0) as [->|NZ]; cbn [negb].
  { exists DLx, OLx, h. split; [reflexivity| exact O]. }
  unfold bl_count_get. autorewrite with btupd. fold (B bits).
  destruct O as [LEN Hh DONE RNG MONO SUMg LOW ZERO OLX].
  destruct LIf as [LBC NN OUT CNT KK _ _]. fold B in NN, OUT, CNT, KK. pose proof MLR as MR. pose proof U2 as UU.
  pose proof leaves_count as LC.
  assert (HOLx : 0 <= OLx < 2 ^ 64) by (rewrite OLX; apply wrap64_range).
  assert (REM : RS ind hm h = isum B bits).
  { pose proof (RS_app ind hm h 573) as A. unfold RS in A, DONE |- *. rewrite SUM_hm in *. unfold cntB in CNT. lia. }
  assert (Bb : 0 <= B bits <= isum B bits).
  { split; [apply NN; lia|]. apply isum_le1; [lia| lia| intros; apply NN; lia]. }
  destruct (gb_loop3i BCf SLx 574 bits (B bits) h DLx OLx ltac:(lia) ltac:(lia) ltac:(unfold HuffGen.hm in *; lia) LEN ltac:(lia) HOLx)
    as (h' & DLx' & OLx' & E1 & R1 & C1 & LP & Z0 & L1 & O1 & A1 & U1 & Z1 & S1).
  rewrite E1.
  destruct (IH (bits - 1) h' DLx' OLx' ltac:(lia) ltac:(lia)) as (DLf & OLf & hf & E2 & O2).
  2:{ exists DLf, OLf, hf. split; [exact E2| exact O2]. }
  assert (ISS : forall w, isum (fun b => B b * w b) bits = isum (fun b => B b * w b) (bits - 1) + B bits * w bits).
  { intros w. replace bits with (bits - 1 + 1) at 1 by lia. rewrite isum_snoc by lia. replace (bits - 1 + 1) with bits by lia. reflexivity. }
  split.
  - exact L1.
  - lia.
  - rewrite <- (RS_app ind h' h 573), C1, DONE.
    pose proof (ISS (fun _ => 1)) as I1. cbn beta in I1.
    rewrite (isum_ext (fun b => B b * 1) B) in I1 by (intros; lia). rewrite (isum_ext (fun b => B b * 1) B) in I1 by (intros; lia). lia.
  - intros q Hq Lq. destruct (Z_lt_le_dec q h).
    + rewrite A1 by (lia || exact Lq). lia.
    + rewrite U1 by (lia || (right; left; lia)). specialize (RNG q ltac:(lia) Lq). lia.
  - intros q1 q2 Hq Hq2 L1q L2q. destruct (Z_lt_le_dec q2 h).
    + rewrite !A1 by (lia || assumption). lia.
    + rewrite (U1 q2) by (lia || (right; left; lia)). destruct (Z_lt_le_dec q1 h).
      * rewrite A1 by (lia || assumption). specialize (RNG q2 ltac:(lia) L2q). lia.
      * rewrite (U1 q1) by (lia || (right; left; lia)). apply MONO; try lia; assumption.
  - intros g. rewrite <- (RS_app _ h' h 573).
    rewrite (RS_ext (fun q => if leafp q then g (arr_get DLx' (arr_get HP7 q)) else 0) (fun q => if leafp q then g bits else 0) h' h); [|lia|].
    2:{ intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. rewrite A1 by (lia || exact Lq). reflexivity. }
    rewrite RS_scale, C1 by lia.
    rewrite (RS_ext (fun q => if leafp q then g (arr_get DLx' (arr_get HP7 q)) else 0) (fun q => if leafp q then g (arr_get DLx (arr_get HP7 q)) else 0) h 573); [|lia|].
    2:{ intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. rewrite U1 by (lia || (right; left; lia)). reflexivity. }
    rewrite SUMg, (ISS g). lia.
  - intros q Hq Hc. rewrite U1; [| lia| destruct Hc; [left; lia| right; right; assumption]]. apply LOW; [lia|]. destruct Hc; [left; lia| right; assumption].
  - intros j Hj Hnj. rewrite Z1 by assumption. apply ZERO; assumption.
  - rewrite S1, OLX. rewrite BuildTreeModel.wrap64_add_l. f_equal.
    rewrite <- (RS_app (fun q => if leafp q then (arr_get DLx' (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) h' h 573).
    rewrite (RS_ext (fun q => if leafp q then (arr_get DLx' (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0)
                    (fun q => if leafp q then (bits - arr_get DLx (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) h' h); [|lia|].
    2:{ intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. rewrite A1 by (lia || exact Lq). rewrite <- (LOW q) by (lia || (left; lia)). reflexivity. }
    rewrite (RS_ext (fun q => if leafp q then (arr_get DLx' (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0)
                    (fun q => if leafp q then (arr_get DLx (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) h 573); [lia|lia|].
    intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. rewrite U1 by (lia || (right; left; lia)). reflexivity.
Qed.

Lemma OI_final : forall hf DLf OLf, OI 0 hf DLf OLf ->
  (forall q, hm <= q <= 572 -> leafp q = true -> hf <= q)
  /\ (forall q, hm <= q <= 572 -> leafp q = true -> 1 <= arr_get DLf (arr_get HP7 q) <= ML)
  /\ (forall q1 q2, hm <= q1 <= q2 -> q2 <= 572 -> leafp q1 = true -> leafp q2 = true -> arr_get DLf (arr_get HP7 q1) <= arr_get DLf (arr_get HP7 q2))
  /\ (forall g, SUM (fun q => if leafp q then g (arr_get DLf (arr_get HP7 q)) else 0) 573 = isum (fun b => B b * g b) ML)
  /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLf j = arr_get DLc j)
  /\ OLf = wrap64 (OLc + SUM (fun q => if leafp q then (arr_get DLf (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) 573)
  /\ arr_len DLf = tsize t.
Proof.
  intros hf DLf OLf [LEN Hh DONE RNG MONO SUMg LOW ZERO OLX].
  destruct LIf as [LBC NN OUT CNT KK _ _]. fold B in NN, OUT, CNT, KK. pose proof U2 as UU. pose proof leaves_count as LC.
  rewrite isum_0, Z.sub_0_r in DONE. unfold cntB in CNT. rewrite CNT in DONE.
  assert (NOLEAF : RS ind hm hf = 0).
  { pose proof (RS_app ind hm hf 573) as A. unfold RS in A, DONE |- *. rewrite SUM_hm in *. lia. }
  assert (ALL : forall q, hm <= q <= 572 -> leafp q = true -> hf <= q).
  { intros q Hq Lq. destruct (Z_lt_le_dec q hf); [|assumption]. exfalso.
    pose proof (RS_app ind hm q hf) as A. pose proof (RS_nonneg ind hm q ltac:(lia) ltac:(intros; apply ind_01)).
    pose proof (RS_snoc ind q q ltac:(lia)) as Sq. rewrite RS_nil in Sq. pose proof (RS_app ind q (q + 1) hf).
    pose proof (RS_nonneg ind (q + 1) hf ltac:(lia) ltac:(intros; apply ind_01)). unfold ind in Sq at 2. rewrite Lq in Sq. lia. }
  split; [exact ALL|].
  split; [intros q Hq Lq; specialize (RNG q ltac:(specialize (ALL q Hq Lq); lia) Lq); lia|].
  split; [intros q1 q2 Hq Hq2 L1q L2q; apply MONO; try assumption; specialize (ALL q1 ltac:(lia) L1q); lia|].
  split.
  { intros g. specialize (SUMg g). rewrite isum_0, Z.sub_0_r in SUMg. rewrite <- SUMg. unfold RS.
    rewrite <- (Z.sub_0_r (SUM _ 573)) at 1. f_equal. symmetry.
    pose proof (RS_app (fun q => if leafp q then g (arr_get DLf (arr_get HP7 q)) else 0) hm hf hf) as A.
    unfold RS in A |- *. rewrite SUM_hm in *.
    enough (Z0 : SUM (fun q : Z => if leafp q then g (arr_get DLf (arr_get HP7 q)) else 0) hf = SUM (fun _ => 0) hf).
    { rewrite Z0. clear. unfold HuffGen.SUM. generalize (HuffGen.rng t FC0 hf). induction l; cbn; lia. }
    apply SUM_ext. intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. exfalso. specialize (ALL q ltac:(lia) Lq). lia. }
  split; [exact ZERO|]. split; [|exact LEN].
  rewrite OLX. f_equal. f_equal. unfold RS.
  enough (Z0 : SUM (fun q : Z => if leafp q then (arr_get DLf (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0) hf = SUM (fun _ => 0) hf).
  { rewrite Z0. replace (SUM (fun _ => 0) hf) with 0; [lia|]. clear. unfold HuffGen.SUM. generalize (HuffGen.rng t FC0 hf). induction l; cbn; lia. }
  apply SUM_ext. intros q Hq. destruct (leafp q) eqn:Lq; [|reflexivity]. exfalso. specialize (ALL q ltac:(lia) Lq). lia.
Qed.
End Outer.



Lemma weight_order : forall q1 q2, hm <= q1 <= q2 -> q2 <= 572 ->
  arr_get FC (arr_get HP7 q2) <= arr_get FC (arr_get HP7 q1).
Proof.
  intros q1 q2 Hq Hq2. pose proof INV as [? ? ? ? ? ? ? ? ? ? i_word].
  replace q2 with (q1 + Z.of_nat (Z.to_nat (q2 - q1))) in * by lia.
  induction (Z.to_nat (q2 - q1)) as [|n IH]; [rewrite Z.add_0_r; lia|].
  rewrite Nat2Z.inj_succ in *. replace (q1 + Z.succ (Z.of_nat n)) with (q1 + Z.of_nat n + 1) in * by lia.
  rewrite !H7hi in * by lia. specialize (IH ltac:(lia) ltac:(lia)). specialize (i_word (q1 + Z.of_nat n) ltac:(lia)). lia.
Qed.

Lemma LI_start : forall BCc, arr_len BCc = 16 ->
  (forall b, 0 <= b <= 15 -> arr_get BCc b = zsum (map (fun j => if Z.min (nd j) ML =? b then 1 else 0) UPl)) ->
  LI BCc N.
Proof.
  intros BCc LBC HBC. pose proof MLR as MR. pose proof excess_identity as (EK & EO & NN).
  destruct (leaf_depths t FC0 FC DL HP DP sub INV) as [PD PW].
  assert (ND1 : forall j, In j UPl -> 1 <= nd j).
  { intros j Hj. assert (Hin : In (j, nd j) (map (fun e => (ea e, ed e)) (hprof 0 (T HP sub)))).
    { apply (Permutation_in _ (Permutation_sym PD)). apply in_map_iff. exists j. auto. }
    apply in_map_iff in Hin. destruct Hin as (e & Ee & He). injection Ee as E1 E2. rewrite <- E2.
    destruct (T_prof t FC0 FC DL HP DP sub INV e He) as (_ & _ & ?). assumption. }
  assert (MIN : forall j, In j UPl -> 1 <= Z.min (nd j) ML <= ML) by (intros j Hj; specialize (ND1 j Hj); lia).
  assert (RG : forall g, isum (fun b => arr_get BCc b * g b) ML = zsum (map (fun j => g (Z.min (nd j) ML)) UPl)).
  { intros g. rewrite (regroup UPl (fun j => Z.min (nd j) ML) g ML ltac:(lia) MIN). apply isum_ext. intros b Hb. rewrite HBC by lia. reflexivity. }
  split.
  - exact LBC.
  - intros b Hb. rewrite HBC by lia. apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & _). destruct (_ =? b); lia.
  - intros b Hb Ho. rewrite HBC by lia. etransitivity; [apply zsum_map_ext|].
    + intros j Hj. specialize (MIN j Hj). destruct (Z.eqb_spec (Z.min (nd j) ML) b); [lia|]. reflexivity.
    + generalize UPl. clear. induction l; cbn; lia.
  - unfold cntB. rewrite <- (isum_ext (fun b => arr_get BCc b * 1)) by (intros; lia). rewrite RG.
    unfold u. generalize UPl. clear. induction l; [reflexivity|]. cbn [map zsum]. rewrite IHl, zlen_cons. lia.
  - unfold KB. rewrite RG. fold phi. unfold K0 in EK. exact EK.
  - exact NN.
  - unfold SlowB.
    assert (EQ1 : isum (fun b => arr_get BCc b * 2 ^ (ML - b)) (ML - 1) = isum (fun b => arr_get BCc b * (if b <=? ML - 1 then 2 ^ (ML - b) else 0)) ML).
    { pose proof (isum_snoc (fun b => arr_get BCc b * (if b <=? ML - 1 then 2 ^ (ML - b) else 0)) (ML - 1) ltac:(lia)) as IS.
      replace (ML - 1 + 1) with ML in IS by lia. rewrite IS. cbn beta.
      replace (ML <=? ML - 1) with false by (symmetry; apply Z.leb_gt; lia). rewrite Z.mul_0_r, Z.add_0_r.
      apply isum_ext. intros b Hb. replace (b <=? ML - 1) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
    rewrite EQ1, RG.
    transitivity (zsum (map (fun p : Z * Z => if snd p <=? ML - 1 then 2 ^ (ML - snd p) else 0) (map (fun j => (j, nd j)) UPl))).
    { rewrite map_map. apply Z.eq_le_incl. apply zsum_map_ext. intros j Hj. cbn [snd]. specialize (MIN j Hj).
      destruct (Z.leb_spec (Z.min (nd j) ML) (ML - 1)), (Z.leb_spec (nd j) (ML - 1)); try lia. rewrite Z.min_l by lia. reflexivity. }
    rewrite <- (zsum_map_perm _ _ _ PD). rewrite map_map. cbn [snd].
    set (TT := T HP sub). destruct (tree_code_complete TT) as [DT KT].
    set (Hs := hheight TT + ML).
    pose proof (kraft_hprof Hs 0 TT ltac:(lia) ltac:(subst Hs; lia)) as K. rewrite Z.sub_0_r in K.
    unfold kraft in K.
    assert (SPLIT : zsum (map (fun e => 2 ^ (Hs - ed e)) (hprof 0 TT))
       = zsum (map (fun e => if ed e <=? ML - 1 then 2 ^ (Hs - ed e) else 0) (hprof 0 TT))
         + zsum (map (fun e => if ed e <=? ML - 1 then 0 else 2 ^ (Hs - ed e)) (hprof 0 TT))).
    { rewrite <- zsum_map_add. apply zsum_map_ext. intros e _. destruct (ed e <=? ML - 1); lia. }
    assert (NN2 : 0 <= zsum (map (fun e => if ed e <=? ML - 1 then 0 else 2 ^ (Hs - ed e)) (hprof 0 TT))).
    { apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (e & <- & He).
      destruct (ed e <=? ML - 1); [lia|]. apply Z.pow_nonneg. lia. }
    assert (SC : zsum (map (fun e => if ed e <=? ML - 1 then 2 ^ (Hs - ed e) else 0) (hprof 0 TT))
       = 2 ^ (Hs - ML) * zsum (map (fun x : ent => if ed x <=? ML - 1 then 2 ^ (ML - ed x) else 0) (hprof 0 TT))).
    { rewrite <- zsum_map_mul. apply zsum_map_ext. intros e He. destruct (Z.leb_spec (ed e) (ML - 1)); [|lia].
      rewrite <- Z.pow_add_r by (subst Hs; pose proof (hheight_nonneg TT); lia). f_equal. lia. }
    assert (P2 : 2 ^ Hs = 2 ^ (Hs - ML) * 2 ^ ML) by (rewrite <- Z.pow_add_r by (subst Hs; pose proof (hheight_nonneg TT); lia); f_equal; lia).
    pose proof (Z.pow_pos_nonneg 2 (Hs - ML) ltac:(lia) ltac:(subst Hs; pose proof (hheight_nonneg TT); lia)). nia.
Qed.

Theorem gen_bitlen_overflow : forall DLc BCc OLc SLc ovc,
  arr_len BC = 16 -> 0 <= OL < 2 ^ 64 -> 0 <= SL < 2 ^ 64 ->
  GI t FC0 OL SL FC DL HP 573 DLc BCc OLc SLc ovc -> ovc <> 0 ->
  exists DLf BCf OLf,
    gen_bitlen_loop3 (Z.to_nat ML) (gen_bitlen_loop2 573 (X6 DLc BCc OLc SLc) ML ovc) t MCv ML HEAP_SIZE = X6 DLf BCf OLf SLc
    /\ arr_len DLf = tsize t /\ arr_len BCf = 16
    /\ (forall j, In j UPl -> 1 <= arr_get DLf j <= ML)
    /\ (forall j, 0 <= j < elems -> ~ In j UPl -> arr_get DLf j = 0)
    /\ (forall g, zsum (map (fun j => g (arr_get DLf j)) UPl) = isum (fun b => arr_get BCf b * g b) ML)
    /\ KB (arr_get BCf) = 2 ^ ML
    /\ (forall b, 0 <= b <= 15 -> (b < 1 \/ ML < b) -> arr_get BCf b = 0)
    /\ (forall b, 0 <= b <= 15 -> 0 <= arr_get BCf b)
    /\ OLf = wrap64 (OL + zsum (map (fun j => FPf j * (arr_get DLf j + xb j)) UPl))
    /\ (forall i j, In i UPl -> In j UPl -> FPf i < FPf j -> arr_get DLf j <= arr_get DLf i).
Proof.
  intros DLc BCc OLc SLc ovc LBC OLr SLr G Hov.
  pose proof (pass1_summary t FC0 OL SL FC DL HP DP sub INV OLr SLr DLc BCc OLc SLc ovc G) as (SDL & SZ & SBC & SOL & SSL & SOV & LDLc & LBCc).
  pose proof excess_identity as (EK & EO & NN). pose proof MLR as MR. pose proof hm_k as (E & K & EL & _).
  pose proof MCF as [MCr LF].
  destruct G as [GL GD GT GZ GB GO GS GV].
  assert (OV : ovc = 2 * N) by (rewrite GV; exact EO).
  assert (N1 : 1 <= N) by lia.
  assert (Nk : N <= k).
  { unfold N, isum.
    assert (Gb : forall l, zsum (map (fun i : Z => if ML <=? nd (y i) then 1 else 0) l) <= zlen l).
    { induction l; [change (0 <= zlen (@nil Z)); unfold zlen; cbn [length]; lia|]. cbn [map zsum]. rewrite zlen_cons. destruct (ML <=? _); lia. }
    etransitivity; [apply Gb|]. unfold zlen. rewrite ziota_length. lia. }
  pose proof (LI_start BCc LBCc SBC) as L0.
  destruct (gb_loop2 DLc OLc SLc 573 BCc N L0 N1 ltac:(lia)) as (BCf & E2 & LIf).
  rewrite OV, E2.
  assert (OLcr : 0 <= OLc < 2 ^ 64) by (rewrite GO; apply wrap64_range).
  destruct (gb_loop3 DLc BCf OLc SLc LIf OLcr (Z.to_nat ML) ML 573 DLc OLc ltac:(lia) ltac:(lia) (OI_start DLc BCf OLc SLc OLcr LDLc))
    as (DLf & OLf & hf & E3 & O3).
  unfold HEAP_SIZE. rewrite E3.
  destruct (OI_final DLc BCf OLc LIf OLcr hf DLf OLf O3) as (ALL & RNG & MONO & SUMg & ZERO & OLF & LDLf).
  destruct LIf as [LBCf NNf OUTf CNTf KKf _ _].
  assert (POS : forall j, In j UPl -> exists q, hm <= q <= 572 /\ leafp q = true /\ arr_get HP7 q = j).
  { intros j Hj. pose proof (Permutation_in j (Permutation_sym LPOS) Hj) as Hin.
    apply in_map_iff in Hin. destruct Hin as (q & Eq & Hq). apply filter_In in Hq. destruct Hq as [Hq Lq].
    unfold HuffGen.rng in Hq. apply in_ziota in Hq. exists q. split; [lia|]. split; assumption. }
  exists DLf, BCf, OLf. split; [reflexivity|]. split; [exact LDLf|]. split; [exact LBCf|].
  split. { intros j Hj. destruct (POS j Hj) as (q & Hq & Lq & <-). apply RNG; assumption. }
  split. { intros j Hj Hnj. rewrite ZERO by assumption. apply SZ; assumption. }
  split.
  { intros g. rewrite <- SUMg. symmetry. apply SUML.
    - intros h Hh Lh. rewrite Lh. reflexivity.
    - intros h Hh Lh. rewrite Lh. reflexivity. }
  split; [rewrite KKf; lia|]. split; [exact OUTf|]. split; [exact NNf|].
  split.
  { rewrite OLF, GO. rewrite BuildTreeModel.wrap64_add_l. f_equal. rewrite <- Z.add_assoc. f_equal.
    rewrite (SUML (fun j => FPf j * (Z.min (nd j) ML + xb j)) (olf t FC0 FC DL HP)).
    2:{ intros h Hh Lh. unfold olf. rewrite Lh. unfold Ld. pose proof INV as [? ? ? ? ? ? ? ? i_fc]. rewrite i_fc; [reflexivity|].
        apply (proj1 (LF h ltac:(lia))) in Lh. pose proof (IDR h ltac:(lia)). lia. }
    2:{ intros h Hh Lh. unfold olf. rewrite Lh. reflexivity. }
    rewrite (SUML (fun j => (arr_get DLf j - Z.min (nd j) ML) * FPf j) (fun q => if leafp q then (arr_get DLf (arr_get HP7 q) - arr_get DLc (arr_get HP7 q)) * arr_get FC (arr_get HP7 q) else 0)).
    2:{ intros h Hh Lh. rewrite Lh. pose proof INV as [? ? ? ? ? ? ? ? i_fc].
        pose proof (proj1 (LF h ltac:(lia)) Lh) as Lt. pose proof (IDR h ltac:(lia)) as [R1 R2].
        rewrite i_fc by lia. rewrite SDL by (apply (proj1 R2); exact Lt). reflexivity. }
    2:{ intros h Hh Lh. rewrite Lh. reflexivity. }
    rewrite <- zsum_map_add. apply zsum_map_ext. intros; lia. }
  intros i j Hi Hj Fij.
  destruct (POS i Hi) as (qi & Hqi & Lqi & Ei). destruct (POS j Hj) as (qj & Hqj & Lqj & Ej).
  pose proof INV as [? ? ? ? ? ? ? ? i_fc].
  pose proof (IDR qi ltac:(lia)) as [Ri1 Ri2]. pose proof (IDR qj ltac:(lia)) as [Rj1 Rj2].
  pose proof (proj1 (LF qi ltac:(lia)) Lqi) as Lti. pose proof (proj1 (LF qj ltac:(lia)) Lqj) as Ltj.
  assert (Wi : FPf i = arr_get FC (arr_get HP7 qi)) by (rewrite i_fc by lia; rewrite Ei; reflexivity).
  assert (Wj : FPf j = arr_get FC (arr_get HP7 qj)) by (rewrite i_fc by lia; rewrite Ej; reflexivity).
  destruct (Z_le_gt_dec qi qj).
  - pose proof (weight_order qi qj ltac:(lia) ltac:(lia)). lia.
  - rewrite <- Ei, <- Ej. apply MONO; try assumption; lia.
Qed.

End Gen2.
