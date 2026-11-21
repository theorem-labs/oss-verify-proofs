(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees HuffTree HuffFib HuffHeap HuffBuild HuffBuild2 HuffGen HuffGen2 HuffSpec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import TreeModel BuildTreeModel GenBitlenModel ScanModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition bsum (b : arr) : Z := zsum (map (arr_get b) (ziota 0 19)).

Lemma zsum_map_ziota_upd : forall (g g' : Z -> Z) a n i,
  (forall j, j <> i -> g' j = g j) ->
  zsum (map g' (ziota a n)) = zsum (map g (ziota a n)) + (if (a <=? i) && (i <? a + Z.of_nat n) then g' i - g i else 0).
Proof.
  intros g g' a n i E. revert a. induction n as [|n IH]; intros a; cbn [ziota map zsum].
  - change (Z.of_nat 0) with 0. destruct (Z.leb_spec a i), (Z.ltb_spec i (a + 0)); cbn [andb]; lia.
  - rewrite IH. rewrite Nat2Z.inj_succ.
    destruct (Z.eq_dec a i).
    + subst a. replace ((i + 1 <=? i) && (i <? i + 1 + Z.of_nat n)) with false by (symmetry; rewrite Bool.andb_false_iff, Z.leb_gt; lia).
      replace ((i <=? i) && (i <? i + Z.succ (Z.of_nat n))) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia). lia.
    + rewrite (E a) by lia.
      destruct (Z.leb_spec (a + 1) i), (Z.ltb_spec i (a + 1 + Z.of_nat n)), (Z.leb_spec a i), (Z.ltb_spec i (a + Z.succ (Z.of_nat n))); cbn [andb]; lia.
Qed.

Lemma bsum_set : forall b i v, arr_len b = 39 -> 0 <= i ->
  bsum (arr_set b i v) = bsum b + (if i <? 19 then v - arr_get b i else 0).
Proof.
  intros b i v L Hi. unfold bsum.
  rewrite (zsum_map_ziota_upd (arr_get b) (arr_get (arr_set b i v)) 0 19 i) by (intros j Hj; apply arr_get_set_other; lia).
  f_equal. destruct (Z.ltb_spec i 19).
  - replace ((0 <=? i) && (i <? 0 + Z.of_nat 19)) with true by (symmetry; rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt; lia).
    rewrite arr_get_set_same by lia. reflexivity.
  - replace ((0 <=? i) && (i <? 0 + Z.of_nat 19)) with false by (symmetry; rewrite Bool.andb_false_iff, Z.ltb_ge; lia). reflexivity.
Qed.

Definition bnn (b : arr) : Prop := forall i, 0 <= i < 39 -> 0 <= arr_get b i.

Lemma bsum_ge : forall b i, bnn b -> 0 <= i < 19 -> arr_get b i <= bsum b.
Proof.
  intros b i NN Hi. unfold bsum.
  assert (G : forall a n, (a <= i < a + Z.of_nat n) -> 0 <= a -> a + Z.of_nat n <= 39 -> arr_get b i <= zsum (map (arr_get b) (ziota a n))).
  { intros a n. revert a. induction n as [|n IH]; intros a H Ha Hn; [lia|]. cbn [ziota map zsum]. rewrite Nat2Z.inj_succ in H, Hn.
    assert (0 <= zsum (map (arr_get b) (ziota (a + 1) n))).
    { apply zsum_nonneg. intros x Hx. apply in_map_iff in Hx. destruct Hx as (j & <- & Hj). apply in_ziota in Hj. apply NN. lia. }
    destruct (Z.eq_dec a i); [subst; lia|]. specialize (IH (a + 1) ltac:(lia) ltac:(lia)). pose proof (NN a ltac:(lia)). lia. }
  apply G; lia.
Qed.

Lemma bump_ok : forall b i k, arr_len b = 39 -> bnn b -> 0 <= k -> 0 <= i < 19 -> bsum b + k < 65536 ->
  let b' := arr_set b i (wrap16 (arr_get b i + k)) in
  arr_len b' = 39 /\ bnn b' /\ bsum b' = bsum b + k /\ (forall j, arr_get b j <= arr_get b' j).
Proof.
  intros b i k L NN Hk Hi Hs. cbv zeta. split; [rewrite arr_len_set; exact L|].
  pose proof (NN i ltac:(lia)) as NNi. pose proof (bsum_ge b i NN ltac:(lia)). rewrite (wrap16_id (arr_get b i + k)) by lia.
  assert (VAL : forall j, arr_get (arr_set b i (arr_get b i + k)) j = if j =? i then arr_get b i + k else arr_get b j).
  { intros j. rewrite arr_get_set, (Z.eqb_sym i j). destruct (Z.eqb_spec j i); cbn [andb]; [|reflexivity]. rewrite inb_true by lia. reflexivity. }
  split; [intros j Hj; rewrite VAL; destruct (Z.eqb_spec j i); [lia| apply NN; exact Hj]|].
  split; [rewrite bsum_set by lia; rewrite (proj2 (Z.ltb_lt _ _)) by lia; lia|].
  intros j. rewrite VAL. destruct (Z.eqb_spec j i); [subst; lia| lia].
Qed.

Lemma st_upd_ok : forall mn b curlen prevlen count,
  arr_len b = 39 -> bnn b -> 0 <= curlen <= 15 -> (mn = 3 \/ mn = 4) -> 1 <= count -> bsum b + count < 65536 ->
  let b' := st_upd mn b curlen prevlen count in
  arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum b + count /\ (forall j, arr_get b j <= arr_get b' j).
Proof.
  intros mn b curlen prevlen count L NN Hc Hmn Hk Hs. unfold st_upd.
  destruct (Z.ltb_spec count mn).
  { destruct (bump_ok b curlen count L NN ltac:(lia) ltac:(lia) Hs) as (A & B & C & D). cbv zeta. repeat split; auto. lia. }
  unfold REP_3_6, REPZ_3_10, REPZ_11_138.
  destruct (Z.eqb_spec curlen 0); cbn [negb].
  - destruct (Z.leb_spec count 10).
    + destruct (bump_ok b 17 1 L NN ltac:(lia) ltac:(lia) ltac:(lia)) as (A & B & C & D). cbv zeta. repeat split; auto. lia.
    + destruct (bump_ok b 18 1 L NN ltac:(lia) ltac:(lia) ltac:(lia)) as (A & B & C & D). cbv zeta. repeat split; auto. lia.
  - destruct (Z.eqb_spec curlen prevlen); cbn [negb].
    + destruct (bump_ok b 16 1 L NN ltac:(lia) ltac:(lia) ltac:(lia)) as (A & B & C & D). cbv zeta. repeat split; auto. lia.
    + destruct (bump_ok b curlen 1 L NN ltac:(lia) ltac:(lia) ltac:(lia)) as (A & B & C & D).
      destruct (bump_ok (arr_set b curlen (wrap16 (arr_get b curlen + 1))) 16 1 A B ltac:(lia) ltac:(lia) ltac:(lia)) as (A2 & B2 & C2 & D2).
      cbv zeta. split; [exact A2|]. split; [exact B2|]. split; [lia|]. intros j. specialize (D j). specialize (D2 j). lia.
Qed.

Lemma scan_loop_sum : forall f s0 b t mc n prevlen nextlen count mx mn,
  arr_len b = 39 -> bnn b -> 0 <= count -> 0 <= n -> (mn = 3 \/ mn = 4) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s0 t i <= 15) ->
  (n <= mc -> nextlen = Len s0 t n) ->
  bsum b + count + (mc + 1 - n) < 65536 ->
  exists b', scan_tree_loop f (set_bl_tree_fc s0 b) t mc n prevlen nextlen count mx mn = set_bl_tree_fc s0 b'
    /\ arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum b + count + Z.max 0 (mc + 1 - n) /\ (forall j, arr_get b j <= arr_get b' j).
Proof.
  induction f as [|f IH]; intros s0 b t mc n prevlen nextlen count mx mn L NN Hc Hn Hmn HL Hnext Hs.
  - exists b. rewrite scan_loop_0. repeat split; auto; try lia; try (intros; lia).
  - rewrite scan_loop_S. destruct (Z.leb_spec n mc); [| exists b; repeat split; auto; try lia; try (intros; lia)]. cbv zeta.
    specialize (Hnext ltac:(lia)). pose proof (HL n ltac:(lia)) as HLn.
    destruct ((count + 1 <? mx) && (nextlen =? Len s0 t (n + 1))).
    + destruct (IH s0 b t mc (n + 1) prevlen (Len s0 t (n + 1)) (count + 1) mx mn L NN ltac:(lia) ltac:(lia) Hmn HL ltac:(intros; reflexivity) ltac:(lia))
        as (b' & E & L' & NN' & S' & M'). exists b'. repeat split; auto. lia.
    + destruct (tree_counts nextlen (Len s0 t (n + 1))) as [mx' mn'] eqn:TC.
      pose proof (tree_counts_range _ _ _ _ TC) as [_ Hmn'].
      destruct (st_upd_ok mn b nextlen prevlen (count + 1) L NN ltac:(subst nextlen; lia) Hmn ltac:(lia) ltac:(lia)) as (L1 & NN1 & S1 & M1).
      destruct (IH s0 (st_upd mn b nextlen prevlen (count + 1)) t mc (n + 1) nextlen (Len s0 t (n + 1)) 0 mx' mn' L1 NN1 ltac:(lia) ltac:(lia) Hmn' HL ltac:(intros; reflexivity) ltac:(lia))
        as (b' & E & L' & NN' & S' & M'). exists b'. split; [exact E|]. split; [exact L'|]. split; [exact NN'|].
      split; [lia|]. intros j. specialize (M1 j). specialize (M' j). lia.
Qed.

Theorem scan_sum : forall s t mc, tree_lens s -> bnn (ds_bl_tree_fc s) -> -1 <= mc -> mc + 1 < arr_len (tree_dl s t) ->
  (forall i, 0 <= i <= mc -> 0 <= Len s t i <= 15) ->
  bsum (ds_bl_tree_fc s) + (mc + 1) < 65536 ->
  exists b', scan_tree s t mc = set_bl_tree_fc (set_Len s t (mc + 1) 65535) b'
    /\ arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum (ds_bl_tree_fc s) + (mc + 1)
    /\ (forall j, arr_get (ds_bl_tree_fc s) j <= arr_get b' j).
Proof.
  intros s t mc TL NN Hmc Hmc1 HL Hs. unfold scan_tree.
  set (s1 := set_Len s t (mc + 1) 65535).
  assert (L1 : forall i, 0 <= i <= mc -> Len s1 t i = Len s t i).
  { intros i Hi. subst s1. rewrite Len_set_Len by lia. destruct (Z.eqb_spec (mc + 1) i); [lia| reflexivity]. }
  assert (B1 : ds_bl_tree_fc s1 = ds_bl_tree_fc s).
  { subst s1. unfold set_Len, set_Dad. destruct t; reflexivity. }
  assert (LB : arr_len (ds_bl_tree_fc s) = 39) by (unfold tree_lens in TL; tauto).
  assert (E1 : set_bl_tree_fc s1 (ds_bl_tree_fc s) = s1) by (rewrite <- B1; apply sbf_self).
  assert (G : forall mx mn, (mn = 3 \/ mn = 4) ->
    exists b', scan_tree_loop (Z.to_nat (mc + 1)) (set_bl_tree_fc s1 (ds_bl_tree_fc s)) t mc 0 (-1) (Len s t 0) 0 mx mn = set_bl_tree_fc s1 b'
      /\ arr_len b' = 39 /\ bnn b' /\ bsum b' <= bsum (ds_bl_tree_fc s) + (mc + 1) /\ (forall j, arr_get (ds_bl_tree_fc s) j <= arr_get b' j)).
  { intros mx mn Hmn.
    destruct (scan_loop_sum (Z.to_nat (mc + 1)) s1 (ds_bl_tree_fc s) t mc 0 (-1) (Len s t 0) 0 mx mn LB NN ltac:(lia) ltac:(lia) Hmn
                ltac:(intros i Hi; rewrite L1 by lia; apply HL; lia) ltac:(intros; rewrite L1 by lia; reflexivity) ltac:(lia))
       as (b' & E & L' & NN' & S' & M'). exists b'. split; [exact E|]. repeat split; auto. lia. }
  destruct (Len s t 0 =? 0).
  - destruct (G 138 3 ltac:(lia)) as (b' & E & R). rewrite E1 in E. exists b'. split; [exact E| exact R].
  - destruct (G 7 4 ltac:(lia)) as (b' & E & R). rewrite E1 in E. exists b'. split; [exact E| exact R].
Qed.


Lemma Len_set_Len_other : forall s t i v t' n, t <> t' -> Len (set_Len s t i v) t' n = Len s t' n.
Proof. intros s [| |] i v [| |] n H; try congruence; reflexivity. Qed.

Lemma bt_max_code_other : forall s t t' FC DL HP HL HM DP BC OL SL MC, t' <> t ->
  max_code (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' = max_code s t'.
Proof. intros s [| |] [| |]; intros; try congruence; reflexivity. Qed.

Lemma Len_bt_other : forall s t t' FC DL HP HL HM DP BC OL SL MC n, t' <> t ->
  Len (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' n = Len s t' n.
Proof. intros s [| |] [| |]; intros; try congruence; reflexivity. Qed.

Lemma max_code_set_Len : forall s t i v t', max_code (set_Len s t i v) t' = max_code s t'.
Proof. intros s [| |] i v [| |]; reflexivity. Qed.
Lemma max_code_sbf : forall s b t', max_code (set_bl_tree_fc s b) t' = max_code s t'.
Proof. intros s b [| |]; reflexivity. Qed.
Lemma opt_len_sbf : forall s b, ds_opt_len (set_bl_tree_fc s b) = ds_opt_len s.
Proof. reflexivity. Qed.
Lemma static_len_sbf : forall s b, ds_static_len (set_bl_tree_fc s b) = ds_static_len s.
Proof. reflexivity. Qed.
Lemma d_max_code_sbf_setLen : forall s b t i v, ds_d_max_code (set_bl_tree_fc (set_Len s t i v) b) = ds_d_max_code s.
Proof. intros s b [| |] i v; reflexivity. Qed.
Lemma opt_len_set_Len : forall s t i v, ds_opt_len (set_Len s t i v) = ds_opt_len s.
Proof. intros s [| |] i v; reflexivity. Qed.
Lemma static_len_set_Len : forall s t i v, ds_static_len (set_Len s t i v) = ds_static_len s.
Proof. intros s [| |] i v; reflexivity. Qed.
Lemma tree_lens_set_Len : forall s t i v, tree_lens s -> tree_lens (set_Len s t i v).
Proof.
  intros s t i v H. unfold set_Len, set_Dad. apply tree_lens_set_dl; [exact H|]. rewrite arr_len_set. apply tree_lens_dl. exact H.
Qed.
Lemma tree_lens_sbf : forall s b, tree_lens s -> arr_len b = 39 -> tree_lens (set_bl_tree_fc s b).
Proof. intros s b H L. change (set_bl_tree_fc s b) with (set_tree_fc s TB b). apply tree_lens_set_fc; [exact H| exact L]. Qed.

Lemma wrap64_sub_add : forall a b c, wrap64 (wrap64 a - b + c) = wrap64 (a - b + c).
Proof. intros. replace (wrap64 a - b + c) with (wrap64 a + (c - b)) by lia. rewrite BuildTreeModel.wrap64_add_l. f_equal. lia. Qed.

Lemma wrap64_inner4 : forall a k1 k2 k3 k4, wrap64 (wrap64 a - k1 + k2 - k3 + k4) = wrap64 (a - k1 + k2 - k3 + k4).
Proof. intros. replace (wrap64 a - k1 + k2 - k3 + k4) with (wrap64 a + (k4 - k3 + k2 - k1)) by lia. rewrite BuildTreeModel.wrap64_add_l. f_equal. lia. Qed.

Lemma bt_same : forall s s' t, tree_fc s' t = tree_fc s t ->
  bt_U s' t = bt_U s t /\ bt_F s' t = bt_F s t /\ bt_mc s' t = bt_mc s t /\ bt_npad s' t = bt_npad s t
  /\ bt_slpad s' t = bt_slpad s t /\ bt_Ftot s' t = bt_Ftot s t.
Proof. intros s s' t E. unfold bt_U, bt_F, bt_mc, bt_npad, bt_slpad, bt_Ftot. rewrite E. repeat split; reflexivity. Qed.

Lemma zsum_filter_le : forall (p : Z -> bool) (g : Z -> Z) l, (forall x, In x l -> 0 <= g x) ->
  zsum (map g (filter p l)) <= zsum (map g l).
Proof.
  induction l as [|x l IH]; intros H; cbn; [lia|].
  specialize (IH ltac:(intros; apply H; now right)). pose proof (H x (or_introl eq_refl)). destruct (p x); cbn; lia.
Qed.

Lemma Ftot_TB_le : forall s, bnn (ds_bl_tree_fc s) -> bt_Ftot s TB <= bsum (ds_bl_tree_fc s) + 2.
Proof.
  intros s NN. rewrite bt_Ftot_eq. pose proof (bt_U_facts s TB) as (_ & _ & _ & _ & _ & _ & NP & _).
  enough (zsum (map (Freq s TB) (Ulist (tree_fc s TB) TB)) <= bsum (ds_bl_tree_fc s)) by lia.
  unfold Ulist, Ul, bsum. cbn [sd_elems]. unfold BL_CODES. change (Z.to_nat 19) with 19%nat.
  etransitivity; [apply zsum_filter_le; intros x Hx; apply NN; apply in_ziota in Hx; lia|]. apply Z.le_refl.
Qed.


Record flush_pre (s : deflate_state) : Prop := FLUSH_PRE {
  fp_lens : tree_lens s;
  fp_fl : forall j, 0 <= j < 286 -> 0 <= Freq s TL j;
  fp_fd : forall j, 0 <= j < 30 -> 0 <= Freq s TD j;
  fp_fb : bnn (ds_bl_tree_fc s);
  fp_totl : bt_Ftot s TL < 2 ^ 16;
  fp_totd : bt_Ftot s TD < 2 ^ 16;
  fp_totb : bsum (ds_bl_tree_fc s) + 320 < 2 ^ 16;
  fp_ol : 0 <= ds_opt_len s < 2 ^ 64;
  fp_sl : 0 <= ds_static_len s < 2 ^ 64 }.

Definition bt_post (s : deflate_state) (t : tree_id) (s' : deflate_state) (L Lz : Z -> Z) : Prop :=
  let U := bt_U s t in let F := bt_F s t in let ML := sd_max_length t in
    (exists T, hbuild (map (fun j => HL (F j) j) U) T
               /\ Permutation (map (fun e => (ea e, ed e)) (hprof 0 T)) (map (fun j => (j, L j)) U)
               /\ Permutation (map (fun e => (ea e, ew e)) (hprof 0 T)) (map (fun j => (j, F j)) U)
               /\ hw T = bt_Ftot s t)
    /\ (forall j, In j U -> 1 <= L j)
    /\ (bt_Ftot s t < fibZ (ML + 3) -> forall j, In j U -> L j <= ML)
    /\ (forall H c, dep_ok H c -> kraft H c <= 2 ^ H -> (forall e, In e c -> 0 <= ew e) ->
          Permutation (map ew c) (map F U) -> zsum (map (fun j => F j * L j) U) <= ccost c)
    /\ (forall i j, In i U -> In j U -> F i < F j -> L j <= L i)
    /\ ((forall j, In j U -> L j <= ML) -> forall j, In j U -> Lz j = L j)
    /\ (forall j, In j U -> Len s' t j = Lz j /\ 1 <= Lz j <= ML)
    /\ (forall j, 0 <= j < sd_elems t -> ~ In j U -> Len s' t j = 0)
    /\ zsum (map (fun j => 2 ^ (ML - Lz j)) U) = 2 ^ ML
    /\ (forall i j, In i U -> In j U -> F i < F j -> Lz j <= Lz i)
    /\ ds_opt_len s' = wrap64 (ds_opt_len s - bt_npad s t + zsum (map (fun j => F j * (Lz j + xbits t j)) U))
    /\ ds_static_len s' = (if stree_has t
                           then wrap64 (ds_static_len s - bt_slpad s t + zsum (map (fun j => F j * (stree_Len t j + xbits t j)) U))
                           else ds_static_len s)
    /\ max_code s' t = bt_mc s t
    /\ (forall b, 0 <= b <= 15 -> bl_count_get s' b = zsum (map (fun j => if Lz j =? b then 1 else 0) U))
    /\ bt_pen U F ML L Lz (bl_count_get s')
    /\ (exists FC' DL' HP' DP' BC', s' = bt_upd s t FC' DL' HP' 1 (575 - 2 * zlen U - 1) DP' BC' (ds_opt_len s') (ds_static_len s') (bt_mc s t)
           /\ arr_len FC' = tsize t /\ arr_len DL' = tsize t /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16).

Lemma bt_post_intro : forall s t, bt_pre s t -> exists L Lz, bt_post s t (build_tree s t) L Lz.
Proof. intros s t P. destruct (build_tree_lengths s t P) as (L & Lz & H). exists L, Lz. exact H. Qed.

Section Flush.
Variable s0 : deflate_state.
Hypothesis PRE : flush_pre s0.

Variables Y1 Y2 Y3 Y4 Y5 : deflate_state.
Hypothesis EY1 : Y1 = build_tree s0 TL.
Hypothesis EY2 : Y2 = build_tree Y1 TD.
Hypothesis EY3 : Y3 = scan_tree Y2 TL (ds_l_max_code Y2).
Hypothesis EY4 : Y4 = scan_tree Y3 TD (ds_d_max_code Y3).
Hypothesis EY5 : Y5 = build_tree Y4 TB.

Theorem flush_trees :
  exists LL LzL LD LzD LB LzB b3 b4,
       bt_post s0 TL Y1 LL LzL
    /\ bt_post Y1 TD Y2 LD LzD /\ tree_fc Y1 TD = tree_fc s0 TD /\ ds_bl_tree_fc Y2 = ds_bl_tree_fc s0
    /\ bt_post Y4 TB Y5 LB LzB /\ tree_fc Y4 TB = b4
    /\ Y3 = set_bl_tree_fc (set_Len Y2 TL (bt_mc s0 TL + 1) 65535) b3
    /\ Y4 = set_bl_tree_fc (set_Len Y3 TD (bt_mc s0 TD + 1) 65535) b4
    /\ bnn b3 /\ bnn b4 /\ arr_len b4 = 39
    /\ (forall j, arr_get (ds_bl_tree_fc s0) j <= arr_get b3 j <= arr_get b4 j)
    /\ bsum b4 <= bsum (ds_bl_tree_fc s0) + (bt_mc s0 TL + 1) + (bt_mc s0 TD + 1)
    /\ (forall j, In j (bt_U s0 TL) -> Len Y5 TL j = LzL j)
    /\ (forall j, 0 <= j <= bt_mc s0 TL -> ~ In j (bt_U s0 TL) -> Len Y5 TL j = 0) /\ Len Y5 TL (bt_mc s0 TL + 1) = 65535
    /\ (forall j, In j (bt_U s0 TD) -> Len Y5 TD j = LzD j)
    /\ (forall j, 0 <= j <= bt_mc s0 TD -> ~ In j (bt_U s0 TD) -> Len Y5 TD j = 0) /\ Len Y5 TD (bt_mc s0 TD + 1) = 65535
    /\ ds_l_max_code Y5 = bt_mc s0 TL /\ ds_d_max_code Y5 = bt_mc s0 TD /\ ds_bl_max_code Y5 = bt_mc Y4 TB
    /\ ds_opt_len Y5 = wrap64 (ds_opt_len s0
         - bt_npad s0 TL + zsum (map (fun j => bt_F s0 TL j * (LzL j + xbits TL j)) (bt_U s0 TL))
         - bt_npad s0 TD + zsum (map (fun j => bt_F s0 TD j * (LzD j + xbits TD j)) (bt_U s0 TD))
         - bt_npad Y4 TB + zsum (map (fun j => bt_F Y4 TB j * (LzB j + xbits TB j)) (bt_U Y4 TB)))
    /\ ds_static_len Y5 = wrap64 (ds_static_len s0
         - bt_slpad s0 TL + zsum (map (fun j => bt_F s0 TL j * (stree_Len TL j + xbits TL j)) (bt_U s0 TL))
         - bt_slpad s0 TD + zsum (map (fun j => bt_F s0 TD j * (stree_Len TD j + xbits TD j)) (bt_U s0 TD)))
    /\ tree_lens Y5
    /\ tree_lens Y2 /\ tree_lens Y3 /\ tree_lens Y4
    /\ ds_l_max_code Y2 = bt_mc s0 TL /\ ds_d_max_code Y3 = bt_mc s0 TD
    /\ (forall i, 0 <= i <= bt_mc s0 TL -> Len Y2 TL i = Len Y5 TL i)
    /\ (forall i, 0 <= i <= bt_mc s0 TD -> Len Y3 TD i = Len Y5 TD i)
    /\ (forall y, 0 <= y < 19 -> ~ In y (bt_U Y4 TB) -> Len Y5 TB y = 0)
    /\ bt_pre s0 TL /\ bt_pre Y1 TD /\ bt_pre Y4 TB.
Proof.
  destruct PRE as [TL0 FL FD FB TOTL TOTD TOTB OL0 SL0].
  pose proof (bt_U_facts s0 TL) as (NDL & RNGL & MCL & U2L & _ & _ & NPL & _).
  pose proof (bt_U_facts s0 TD) as (NDD & RNGD & MCD & U2D & _ & _ & NPD & _).
  assert (RL : 0 <= bt_mc s0 TL < 286) by (pose proof (RNGL _ MCL) as X; cbn [sd_elems] in X; unfold L_CODES in X; lia).
  assert (RD : 0 <= bt_mc s0 TD < 30) by (pose proof (RNGD _ MCD) as X; cbn [sd_elems] in X; unfold D_CODES in X; lia).
  assert (RLj : forall j, In j (bt_U s0 TL) -> 0 <= j <= bt_mc s0 TL) by (intros j Hj; pose proof (RNGL j Hj); lia).
  assert (RDj : forall j, In j (bt_U s0 TD) -> 0 <= j <= bt_mc s0 TD) by (intros j Hj; pose proof (RNGD j Hj); lia).
  assert (P1 : bt_pre s0 TL) by (split; auto).
  destruct (bt_post_intro s0 TL P1) as (LL & LzL & B1). rewrite <- EY1 in B1.
  pose proof B1 as (_ & _ & _ & _ & _ & _ & LenL & ZL & _ & _ & OL1 & SL1 & MC1 & _ & _ & (FC1 & DL1 & HP1 & DP1 & BC1 & E1 & LFC1 & LDL1 & LHP1 & LDP1 & LBC1)).
  assert (TL1 : tree_lens Y1).
  { rewrite E1. apply bt_tree_lens; auto. }
  assert (FR1 : tree_fc Y1 TD = tree_fc s0 TD /\ tree_fc Y1 TB = tree_fc s0 TB /\ tree_dl Y1 TD = tree_dl s0 TD /\ ds_bl_tree_fc Y1 = ds_bl_tree_fc s0).
  { rewrite E1. repeat split; try (apply bt_tree_fc_other; discriminate); try (apply bt_tree_dl_other; discriminate); reflexivity. }
  destruct FR1 as (FC1D & FC1B & DL1D & BL1).
  destruct (bt_same s0 Y1 TD FC1D) as (UD & FDq & MCDq & NPDq & SPDq & FTDq).
  assert (P2 : bt_pre Y1 TD).
  { split; [exact TL1| | rewrite FTDq; exact TOTD| rewrite OL1; apply wrap64_range| rewrite SL1; cbn [stree_has]; apply wrap64_range].
    intros j Hj. unfold Freq. rewrite FC1D. apply FD. exact Hj. }
  destruct (bt_post_intro Y1 TD P2) as (LD & LzD & B2). rewrite <- EY2 in B2.
  pose proof B2 as (_ & _ & _ & _ & _ & _ & LenD & ZD & _ & _ & OL2 & SL2 & MC2 & _ & _ & (FC2 & DL2 & HP2 & DP2 & BC2 & E2 & LFC2 & LDL2 & LHP2 & LDP2 & LBC2)).
  rewrite UD in LenD, ZD. rewrite MCDq in MC2, E2. rewrite UD, FDq, NPDq in OL2. rewrite UD, FDq, SPDq in SL2. rewrite UD in E2.
  assert (TL2 : tree_lens Y2) by (rewrite E2; apply bt_tree_lens; auto).
  assert (FR2 : tree_dl Y2 TL = tree_dl Y1 TL /\ ds_bl_tree_fc Y2 = ds_bl_tree_fc s0 /\ ds_l_max_code Y2 = bt_mc s0 TL /\ ds_d_max_code Y2 = bt_mc s0 TD
                /\ ds_opt_len Y2 = ds_opt_len Y2 /\ tree_fc Y2 TB = tree_fc s0 TB).
  { rewrite E2. split; [apply bt_tree_dl_other; discriminate|]. split; [rewrite <- BL1; reflexivity|].
    split; [rewrite <- MC1; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. rewrite <- FC1B. apply bt_tree_fc_other; discriminate. }
  destruct FR2 as (DL2L & BL2 & MCL2 & MCD2 & _ & FC2B).
  assert (LENL15 : forall i, 0 <= i <= bt_mc s0 TL -> 0 <= Len Y2 TL i <= 15).
  { intros i Hi. rewrite E2, Len_bt_other by discriminate.
    destruct (in_dec Z.eq_dec i (bt_U s0 TL)) as [IN|NIN].
    - destruct (LenL i IN) as [-> R]. cbn [sd_max_length] in R. unfold MAX_BITS in R. lia.
    - rewrite ZL; [lia| cbn [sd_elems]; unfold L_CODES; lia |exact NIN]. }
  destruct (scan_sum Y2 TL (bt_mc s0 TL) TL2 ltac:(rewrite BL2; exact FB) ltac:(lia)
              ltac:(rewrite (tree_lens_dl Y2 TL TL2); cbn [tsize]; lia) LENL15 ltac:(rewrite BL2; lia))
    as (b3 & E3 & Lb3 & NN3 & S3 & M3).
  rewrite <- MCL2 in E3. rewrite <- EY3 in E3. rewrite MCL2 in E3. rewrite BL2 in S3, M3.
  assert (TL3 : tree_lens Y3) by (rewrite E3; apply tree_lens_sbf; [apply tree_lens_set_Len; exact TL2| exact Lb3]).
  assert (MCD3 : ds_d_max_code Y3 = bt_mc s0 TD) by (rewrite E3, d_max_code_sbf_setLen; exact MCD2).
  assert (LEND15 : forall i, 0 <= i <= bt_mc s0 TD -> 0 <= Len Y3 TD i <= 15).
  { intros i Hi. rewrite E3, sbf_Len, Len_set_Len_other by discriminate.
    destruct (in_dec Z.eq_dec i (bt_U s0 TD)) as [IN|NIN].
    - destruct (LenD i IN) as [-> R]. cbn [sd_max_length] in R. unfold MAX_BITS in R. lia.
    - rewrite ZD; [lia| cbn [sd_elems]; unfold D_CODES; lia |exact NIN]. }
  assert (BL3 : ds_bl_tree_fc Y3 = b3) by (rewrite E3; reflexivity).
  destruct (scan_sum Y3 TD (bt_mc s0 TD) TL3 ltac:(rewrite BL3; exact NN3) ltac:(lia)
              ltac:(rewrite (tree_lens_dl Y3 TD TL3); cbn [tsize]; lia) LEND15 ltac:(rewrite BL3; lia))
    as (b4 & E4 & Lb4 & NN4 & S4 & M4).
  rewrite <- MCD3 in E4. rewrite <- EY4 in E4. rewrite MCD3 in E4. rewrite BL3 in S4, M4.
  assert (TL4 : tree_lens Y4) by (rewrite E4; apply tree_lens_sbf; [apply tree_lens_set_Len; exact TL3| exact Lb4]).
  assert (FC4B : tree_fc Y4 TB = b4) by (rewrite E4; reflexivity).
  assert (P5 : bt_pre Y4 TB).
  { split; [exact TL4| | | |].
    - intros j Hj. unfold Freq. rewrite FC4B. apply NN4. cbn in Hj. unfold BL_CODES in Hj. lia.
    - assert (BL4 : ds_bl_tree_fc Y4 = b4) by (rewrite E4; reflexivity).
      pose proof (Ftot_TB_le Y4 ltac:(rewrite BL4; exact NN4)) as FT. rewrite BL4 in FT. lia.
    - rewrite E4, opt_len_sbf, opt_len_set_Len, E3, opt_len_sbf, opt_len_set_Len, OL2. apply wrap64_range.
    - rewrite E4, static_len_sbf, static_len_set_Len, E3, static_len_sbf, static_len_set_Len, SL2. cbn [stree_has]. apply wrap64_range. }
  destruct (bt_post_intro Y4 TB P5) as (LB & LzB & B5). rewrite <- EY5 in B5.
  pose proof B5 as (_ & _ & _ & _ & _ & _ & LenB & ZB & _ & _ & OL5 & SL5 & MC5 & _ & _ & (FC5 & DL5 & HP5 & DP5 & BC5 & E5 & LFC5 & LDL5 & LHP5 & LDP5 & LBC5)).
  assert (TL5 : tree_lens Y5) by (rewrite E5; apply bt_tree_lens; auto).
  assert (LenX5L : forall j, Len Y5 TL j = if bt_mc s0 TL + 1 =? j then wrap16 65535 else Len Y1 TL j).
  { intros j. rewrite E5, Len_bt_other by discriminate.
    rewrite E4, sbf_Len, Len_set_Len_other by discriminate. rewrite E3, sbf_Len.
    rewrite Len_set_Len by (rewrite (tree_lens_dl Y2 TL TL2); cbn [tsize]; lia).
    rewrite E2, Len_bt_other by discriminate. exact eq_refl. }
  assert (LenX5D : forall j, Len Y5 TD j = if bt_mc s0 TD + 1 =? j then wrap16 65535 else Len Y2 TD j).
  { intros j. rewrite E5, Len_bt_other by discriminate.
    rewrite E4, sbf_Len. rewrite Len_set_Len by (rewrite (tree_lens_dl Y3 TD TL3); cbn [tsize]; lia).
    rewrite E3, sbf_Len, Len_set_Len_other by discriminate. exact eq_refl. }
  exists LL, LzL, LD, LzD, LB, LzB, b3, b4.
  split; [exact B1|]. split; [exact B2|]. split; [exact FC1D|]. split; [exact BL2|]. split; [exact B5|]. split; [exact FC4B|].
  split; [exact E3|]. split; [exact E4|]. split; [exact NN3|]. split; [exact NN4|]. split; [exact Lb4|].
  split; [intros j; split; [apply M3| apply M4]|]. split; [lia|].
  split; [intros j Hj; rewrite LenX5L; destruct (Z.eqb_spec (bt_mc s0 TL + 1) j); [pose proof (RLj j Hj); lia|]; apply (proj1 (LenL j Hj))|].
  split; [intros j Hj Hnj; rewrite LenX5L; destruct (Z.eqb_spec (bt_mc s0 TL + 1) j); [lia|]; apply ZL; [cbn [sd_elems]; unfold L_CODES; lia| exact Hnj]|].
  split; [rewrite LenX5L, Z.eqb_refl; reflexivity|].
  split; [intros j Hj; rewrite LenX5D; destruct (Z.eqb_spec (bt_mc s0 TD + 1) j); [pose proof (RDj j Hj); lia|]; apply (proj1 (LenD j Hj))|].
  split; [intros j Hj Hnj; rewrite LenX5D; destruct (Z.eqb_spec (bt_mc s0 TD + 1) j); [lia|]; apply ZD; [cbn [sd_elems]; unfold D_CODES; lia| exact Hnj]|].
  split; [rewrite LenX5D, Z.eqb_refl; reflexivity|].
  split.
  { change (ds_l_max_code Y5) with (max_code Y5 TL). rewrite E5, bt_max_code_other by discriminate.
    rewrite E4, max_code_sbf, max_code_set_Len, E3, max_code_sbf, max_code_set_Len. exact MCL2. }
  split.
  { change (ds_d_max_code Y5) with (max_code Y5 TD). rewrite E5, bt_max_code_other by discriminate.
    rewrite E4, max_code_sbf, max_code_set_Len. exact MCD3. }
  split; [exact MC5|].
  split.
  { rewrite OL5. replace (ds_opt_len Y4) with (ds_opt_len Y2) by (rewrite E4, opt_len_sbf, opt_len_set_Len, E3, opt_len_sbf, opt_len_set_Len; reflexivity).
    rewrite OL2, OL1. rewrite wrap64_sub_add, wrap64_inner4. apply (f_equal wrap64). exact eq_refl. }
  split.
  { rewrite SL5. cbn [stree_has]. replace (ds_static_len Y4) with (ds_static_len Y2) by (rewrite E4, static_len_sbf, static_len_set_Len, E3, static_len_sbf, static_len_set_Len; reflexivity).
    rewrite SL2, SL1. cbn [stree_has]. rewrite !wrap64_sub_add. apply (f_equal wrap64). exact eq_refl. }
  split; [exact TL5|]. split; [exact TL2|]. split; [exact TL3|]. split; [exact TL4|]. split; [exact MCL2|]. split; [exact MCD3|].
  split. { intros i Hi. rewrite LenX5L. destruct (Z.eqb_spec (bt_mc s0 TL + 1) i); [lia|]. rewrite E2, Len_bt_other by discriminate. reflexivity. }
  split. { intros i Hi. rewrite LenX5D. destruct (Z.eqb_spec (bt_mc s0 TD + 1) i); [lia|]. rewrite E3, sbf_Len, Len_set_Len_other by discriminate. reflexivity. }
  split. { intros y Hy Hny. apply ZB; [cbn [sd_elems]; unfold BL_CODES; lia| exact Hny]. }
  split; [exact P1|]. split; [exact P2| exact P5].
Qed.
End Flush.
