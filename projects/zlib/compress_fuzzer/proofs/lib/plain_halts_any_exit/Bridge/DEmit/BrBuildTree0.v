(** * Bridge.DEmit.BrBuildTree0 — kit for pair D26 ([build_tree]): the per-tree relation and [pqdownheap].

    S5's [build_tree] works on the whole [deflate_state]; S5's own
    [BuildTreeModel.bt_upd s0 t FC DL HP HL HM DP BC OL SL MC] writes the
    tree fields of tree [t] into a base state [s0], and its [btupd] rewrite
    database turns every step of the build into a [bt_upd] again.  RT's
    [build_tree] carries the same data as locals (a [Tree], a heap, a depth
    array, [bl_count], ...).  [brel] relates S5's five arrays to RT's on
    their live ranges (and records S5's array lengths, since a store past an
    S5 array's end is dropped).

    This file: [brel] and its update/read kit, [smaller] on both sides, and
    [pqdownheap] (S5 fuel 32, RT fuel 12: both run out only after the sift
    position passes [heap_len < 573], see [pq_down_rel]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  The relation                                                          *)
(* ------------------------------------------------------------------------- *)

Record brel (t : DS.tree_id) (FC DL HP DP BC : arr) (T : RT.Tree) (hp dep blc : Base.zarr) : Prop := mkBrel {
  b_fc : arr_rel FC (RT.tr_fc T) 0 (TM.tsize t);
  b_dl : arr_rel DL (RT.tr_dl T) 0 (TM.tsize t);
  b_hp : arr_rel HP hp 0 573;
  b_dp : arr_rel DP dep 0 573;
  b_bc : arr_rel BC blc 0 16;
  b_lfc : arr_len FC = TM.tsize t;
  b_ldl : arr_len DL = TM.tsize t;
  b_lhp : arr_len HP = 573;
  b_ldp : arr_len DP = 573;
  b_lbc : arr_len BC = 16 }.

Lemma tsize_le : forall t, 39 <= TM.tsize t <= 573.
Proof. intros []; cbn; lia. Qed.

Lemma brel_fc_set : forall t FC DL HP DP BC T hp dep blc i v,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < TM.tsize t ->
  brel t (arr_set FC i (wrap16 v)) DL HP DP BC (RT.t_setfreq T i v) hp dep blc.
Proof.
  intros t FC DL HP DP BC T hp dep blc i v H Hi. destruct H.
  constructor; try assumption; rewrite ?arr_len_set; try assumption.
  unfold RT.t_setfreq. cbn [RT.tr_fc]. rewrite BrBits.wrap16_u16.
  apply arr_rel_set; [assumption | intros; lia].
Qed.

Lemma brel_dl_set : forall t FC DL HP DP BC T hp dep blc i v,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < TM.tsize t ->
  brel t FC (arr_set DL i (wrap16 v)) HP DP BC (RT.t_setlen T i v) hp dep blc.
Proof.
  intros t FC DL HP DP BC T hp dep blc i v H Hi. destruct H.
  constructor; try assumption; rewrite ?arr_len_set; try assumption.
  unfold RT.t_setlen. cbn [RT.tr_dl]. rewrite BrBits.wrap16_u16.
  apply arr_rel_set; [assumption | intros; lia].
Qed.

Lemma t_setdad_setlen : forall T i v, RT.t_setdad T i v = RT.t_setlen T i v.
Proof. reflexivity. Qed.
Lemma t_setcode_setfreq : forall T i v, RT.t_setcode T i v = RT.t_setfreq T i v.
Proof. reflexivity. Qed.

Lemma brel_hp_set : forall t FC DL HP DP BC T hp dep blc i v,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 573 ->
  brel t FC DL (arr_set HP i v) DP BC T (Base.zset hp i v) dep blc.
Proof.
  intros t FC DL HP DP BC T hp dep blc i v H Hi. destruct H.
  constructor; try assumption; rewrite ?arr_len_set; try assumption.
  apply arr_rel_set; [assumption | intros; lia].
Qed.

Lemma brel_dp_set : forall t FC DL HP DP BC T hp dep blc i v,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 573 ->
  brel t FC DL HP (arr_set DP i (wrap8 v)) BC T hp (Base.zset dep i (Base.u8 v)) blc.
Proof.
  intros t FC DL HP DP BC T hp dep blc i v H Hi. destruct H.
  constructor; try assumption; rewrite ?arr_len_set; try assumption.
  rewrite BrBits.wrap8_u8. apply arr_rel_set; [assumption | intros; lia].
Qed.

Lemma brel_bc_set : forall t FC DL HP DP BC T hp dep blc i v,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 16 ->
  brel t FC DL HP DP (arr_set BC i (wrap16 v)) T hp dep (Base.zset blc i (Base.u16 v)).
Proof.
  intros t FC DL HP DP BC T hp dep blc i v H Hi. destruct H.
  constructor; try assumption; rewrite ?arr_len_set; try assumption.
  rewrite BrBits.wrap16_u16. apply arr_rel_set; [assumption | intros; lia].
Qed.

Lemma brel_fc_get : forall t FC DL HP DP BC T hp dep blc i,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < TM.tsize t -> arr_get FC i = RT.tr_fc T i.
Proof. intros. apply (b_fc _ _ _ _ _ _ _ _ _ _ H). exact H0. Qed.
Lemma brel_dl_get : forall t FC DL HP DP BC T hp dep blc i,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < TM.tsize t -> arr_get DL i = RT.tr_dl T i.
Proof. intros. apply (b_dl _ _ _ _ _ _ _ _ _ _ H). exact H0. Qed.
Lemma brel_hp_get : forall t FC DL HP DP BC T hp dep blc i,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 573 -> arr_get HP i = hp i.
Proof. intros. apply (b_hp _ _ _ _ _ _ _ _ _ _ H). exact H0. Qed.
Lemma brel_dp_get : forall t FC DL HP DP BC T hp dep blc i,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 573 -> arr_get DP i = dep i.
Proof. intros. apply (b_dp _ _ _ _ _ _ _ _ _ _ H). exact H0. Qed.
Lemma brel_bc_get : forall t FC DL HP DP BC T hp dep blc i,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= i < 16 -> arr_get BC i = blc i.
Proof. intros. apply (b_bc _ _ _ _ _ _ _ _ _ _ H). exact H0. Qed.

(** A changed RT tree whose fc half is unchanged. *)
Lemma brel_T_fc : forall t FC DL HP DP BC T T' hp dep blc,
  brel t FC DL HP DP BC T hp dep blc -> RT.tr_fc T' = RT.tr_fc T -> RT.tr_dl T' = RT.tr_dl T ->
  brel t FC DL HP DP BC T' hp dep blc.
Proof. intros t FC DL HP DP BC T T' hp dep blc H E1 E2. destruct H. constructor; rewrite ?E1, ?E2; assumption. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  [smaller]                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma smaller_rel : forall s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc n m,
  brel t FC DL HP DP BC T hp dep blc -> 0 <= n < TM.tsize t -> 0 <= m < TM.tsize t ->
  DT.smaller (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t n m = RT.smaller T dep n m.
Proof.
  intros s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc n m H Hn Hm.
  pose proof (tsize_le t).
  unfold DT.smaller, RT.smaller, RT.t_freq. autorewrite with btupd.
  rewrite !(brel_fc_get _ _ _ _ _ _ _ _ _ _ _ H) by lia.
  rewrite !(brel_dp_get _ _ _ _ _ _ _ _ _ _ _ H) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  [pqdownheap]                                                          *)
(* ------------------------------------------------------------------------- *)

Definition pqr (t : DS.tree_id) (HP : arr) (HL : Z) : Prop :=
  forall i, 1 <= i <= HL -> 0 <= arr_get HP i < TM.tsize t.

Lemma pqr_set : forall t HP HL k v, pqr t HP HL -> 0 <= v < TM.tsize t -> pqr t (arr_set HP k v) HL.
Proof.
  intros t HP HL k v H Hv i Hi. rewrite arr_get_set.
  destruct (_ && _); [exact Hv | apply H; exact Hi].
Qed.

Lemma pow2_S : forall f : nat, 2 ^ Z.of_nat (S f) = 2 * 2 ^ Z.of_nat f.
Proof. intros f. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

Lemma pow2_pos : forall f : nat, 1 <= 2 ^ Z.of_nat f.
Proof. intros f. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat f) ltac:(lia) ltac:(lia)). lia. Qed.

Lemma pq_down_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc v k,
  brel t FC DL HP DP BC T hp dep blc -> HL < 573 -> 1 <= k <= HL ->
  pqr t HP HL -> 0 <= v < TM.tsize t ->
  HL < k * 2 ^ Z.of_nat f -> HL < k * 2 ^ Z.of_nat g ->
  let r := DT.pqdownheap_loop f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t v k (Z.shiftl k 1) in
  exists HP', DT.heap_set (fst r) (snd r) v = bt_upd s0 t FC DL HP' HL HM DP BC OL SL MC
    /\ brel t FC DL HP' DP BC T (RT.pq_down g T dep hp HL v k) dep blc
    /\ pqr t HP' HL.
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc v k H HL573 Hk Hpq Hv Hf Hg r.
  - cbn [Z.of_nat] in Hf. rewrite Z.pow_0_r in Hf. lia.
  - destruct g as [|g]; [cbn [Z.of_nat] in Hg; rewrite Z.pow_0_r in Hg; lia|].
    pose proof (tsize_le t) as Ht.
    rewrite pow2_S in Hf, Hg.
    subst r. cbn [DT.pqdownheap_loop RT.pq_down]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. replace (k * 2) with (2 * k) by lia.
    destruct (Z.leb_spec (2 * k) HL) as [Hj|Hj].
    + assert (Hj1 : 1 <= 2 * k <= HL) by lia.
      rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ (2 * k) H) by lia.
      set (j' := if (2 * k <? HL) && DT.smaller (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t
                                       (arr_get HP (2 * k + 1)) (arr_get HP (2 * k))
                 then 2 * k + 1 else 2 * k).
      assert (Ej : (if (2 * k <? HL) && RT.smaller T dep (hp (2 * k + 1)) (arr_get HP (2 * k)) then 2 * k + 1 else 2 * k) = j').
      { subst j'. destruct (Z.ltb_spec (2 * k) HL); cbn [andb]; [|reflexivity].
        rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ (2 * k + 1) H) by lia.
        rewrite (smaller_rel s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc) by (first [exact H | apply Hpq; lia | lia]).
        reflexivity. }
      rewrite Ej.
      assert (Hj' : 2 * k <= j' <= HL /\ j' <= 2 * k + 1).
      { subst j'. destruct (Z.ltb_spec (2 * k) HL); cbn [andb]; [destruct (DT.smaller _ _ _ _)|]; lia. }
      rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ j' H) by lia.
      rewrite (smaller_rel s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc) by (first [exact H | apply Hpq; lia | lia]).
      destruct (RT.smaller T dep v (arr_get HP j')).
      * cbn [fst snd]. autorewrite with btupd. exists (arr_set HP k v). split; [reflexivity|].
        split; [apply brel_hp_set; [exact H | lia] | apply pqr_set; assumption].
      * autorewrite with btupd.
        destruct (IH g s0 t FC DL (arr_set HP k (arr_get HP j')) HL HM DP BC OL SL MC T
                     (Base.zset hp k (arr_get HP j')) dep blc v j') as (HP' & E1 & E2 & E3).
        { apply brel_hp_set; [exact H | lia]. }
        { exact HL573. } { lia. }
        { apply pqr_set; [exact Hpq | apply Hpq; lia]. }
        { exact Hv. }
        { pose proof (pow2_pos f). nia. }
        { pose proof (pow2_pos g). nia. }
        replace (Z.shiftl j' 1) with (j' * 2 ^ 1) by (rewrite Z.shiftl_mul_pow2; lia).
        exists HP'. split; [|split; [|exact E3]].
        -- rewrite Z.shiftl_mul_pow2 in E1 by lia. exact E1.
        -- rewrite (brel_hp_get _ _ _ _ _ _ _ _ _ _ j' H) in E2 by lia.
           rewrite (brel_hp_get _ _ _ _ _ _ _ _ _ _ j' H) by lia. exact E2.
    + cbn [fst snd]. autorewrite with btupd. exists (arr_set HP k v). split; [reflexivity|].
      split; [apply brel_hp_set; [exact H | lia] | apply pqr_set; assumption].
Qed.

Lemma pqdownheap_rel : forall s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc k,
  brel t FC DL HP DP BC T hp dep blc -> HL < 573 -> 1 <= k <= HL -> pqr t HP HL ->
  exists HP', DT.pqdownheap (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t k
              = bt_upd s0 t FC DL HP' HL HM DP BC OL SL MC
    /\ brel t FC DL HP' DP BC T (RT.pqdownheap T dep hp HL k) dep blc
    /\ pqr t HP' HL.
Proof.
  intros s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc k H HL573 Hk Hpq.
  unfold DT.pqdownheap, RT.pqdownheap. autorewrite with btupd.
  pose proof (pq_down_rel 32 12 s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc (arr_get HP k) k H HL573 Hk Hpq
                ltac:(apply Hpq; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as (HP' & E1 & E2 & E3).
  cbv zeta in E1.
  destruct (DT.pqdownheap_loop 32 _ t (arr_get HP k) k (Z.shiftl k 1)) as [s1 k1].
  cbn [fst snd] in E1. exists HP'. split; [exact E1|]. split; [|exact E3].
  rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ k H) by lia. exact E2.
Qed.
