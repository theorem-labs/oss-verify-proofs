(** * Bridge.DEmit.BrBuildTree1 — pair D26, first phases: the initial heap, the forced codes, heapify.

    S5's [build_tree_loop1] / [build_tree_loop2] / [build_tree_loop3] against
    RT's [bt_init] / [bt_force2] / [bt_heapify], each on [bt_upd] states
    ([BrBuildTree0]).  S5's fuels are exact (elems, 2, heap_len/2); RT's are
    static over-estimates; both stop on the same loop condition. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrBuildTree0.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrTally.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma elems_range : forall t, 19 <= DS.sd_elems t <= 286 /\ TM.tsize t = 2 * DS.sd_elems t + 1.
Proof. intros []; cbn [DS.sd_elems TM.tsize]; unfold DS.L_CODES, DS.D_CODES, DS.BL_CODES; lia. Qed.

Lemma sd_elems_tk : forall t, RT.sd_elems (tk_of t) = DS.sd_elems t.
Proof. intros []; reflexivity. Qed.

Lemma wrap64_u64 : forall v, wrap64 v = RT.u64 v.
Proof. intros v. rewrite wrap64_mod. reflexivity. Qed.

Ltac csplit := repeat match goal with |- _ /\ _ => split end.

(** Heap entries below a bound. *)
Definition pqb (B : Z) (HP : arr) (HL : Z) : Prop := forall i, 1 <= i <= HL -> 0 <= arr_get HP i < B.

(* ------------------------------------------------------------------------- *)
(* 1.  [build_tree_loop1] vs [bt_init]                                       *)
(* ------------------------------------------------------------------------- *)

Lemma loop1_rel : forall f g n s0 t FC DL HP HL HM DP BC OL SL MC mc T hp dep blc,
  brel t FC DL HP DP BC T hp dep blc ->
  f = Z.to_nat (DS.sd_elems t - n) -> (Z.to_nat (DS.sd_elems t - n) < g)%nat ->
  0 <= n <= DS.sd_elems t -> 0 <= HL -> HL + (DS.sd_elems t - n) <= DS.sd_elems t ->
  pqb (DS.sd_elems t) HP HL -> -1 <= mc < DS.sd_elems t ->
  let r := DT.build_tree_loop1 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t (DS.sd_elems t) n mc in
  match RT.bt_init g n (DS.sd_elems t) T hp dep HL mc with
  | (T', hp', dep', hl', mc') =>
    exists DL' HP' DP', fst r = bt_upd s0 t FC DL' HP' hl' HM DP' BC OL SL MC
      /\ snd r = mc' /\ brel t FC DL' HP' DP' BC T' hp' dep' blc
      /\ HL <= hl' <= DS.sd_elems t /\ pqb (DS.sd_elems t) HP' hl' /\ -1 <= mc' < DS.sd_elems t
  end.
Proof.
  induction f as [|f IH]; intros g n s0 t FC DL HP HL HM DP BC OL SL MC mc T hp dep blc H Hf Hg Hn HL0 HLE Hpq Hmc r;
    destruct (elems_range t) as [HE Hts]; subst r.
  - assert (n = DS.sd_elems t) by lia. subst n.
    destruct g as [|g]; [lia|]. cbn [DT.build_tree_loop1 RT.bt_init fst snd].
    rewrite Z.leb_refl. exists DL, HP, DP. csplit; first [assumption | reflexivity | lia].
  - destruct g as [|g]; [lia|].
    assert (Hn' : n < DS.sd_elems t) by lia.
    cbn [DT.build_tree_loop1 RT.bt_init]. cbv zeta. autorewrite with btupd.
    replace (n <? DS.sd_elems t) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (DS.sd_elems t <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    unfold RT.t_freq. rewrite <- (brel_fc_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
    destruct (Z.eqb_spec (arr_get FC n) 0) as [E0|E0]; cbn [negb].
    + autorewrite with btupd.
      pose proof (IH g (n + 1) s0 t FC (arr_set DL n (wrap16 0)) HP HL HM DP BC OL SL MC mc (RT.t_setlen T n 0) hp dep blc
                    ltac:(apply brel_dl_set; [exact H | lia]) ltac:(lia) ltac:(lia) ltac:(lia) HL0 ltac:(lia) Hpq Hmc) as IH'.
      cbv zeta in IH'. exact IH'.
    + autorewrite with btupd.
      change (Base.zset dep n 0) with (Base.zset dep n (Base.u8 0)).
      pose proof (IH g (n + 1) s0 t FC DL (arr_set HP (HL + 1) n) (HL + 1) HM (arr_set DP n (wrap8 0)) BC OL SL MC n T
                    (Base.zset hp (HL + 1) n) (Base.zset dep n (Base.u8 0)) blc) as IH'.
      cbv zeta in IH'.
      destruct (RT.bt_init g (n + 1) (DS.sd_elems t) T (Base.zset hp (HL + 1) n) (Base.zset dep n (Base.u8 0)) (HL + 1) n)
        as [[[[T' hp'] dep'] hl'] mc'].
      destruct IH' as (DL' & HP' & DP' & E1 & E2 & E3 & E4 & E5 & E6).
      { apply brel_dp_set; [apply brel_hp_set; [exact H | lia] | lia]. }
      { lia. } { lia. } { lia. } { lia. } { lia. }
      { intros i Hi. rewrite arr_get_set. destruct (_ && _) eqn:Ei; [lia|].
        destruct (Z.eq_dec i (HL + 1)) as [->|Ne].
        - exfalso. rewrite Z.eqb_refl in Ei. cbn [andb] in Ei. rewrite (proj2 (arr_inb_spec HP (HL + 1))) in Ei
            by (rewrite (b_lhp _ _ _ _ _ _ _ _ _ _ H); lia). discriminate.
        - apply Hpq. lia. }
      { lia. }
      exists DL', HP', DP'. csplit; first [assumption | reflexivity | lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  [build_tree_loop2] vs [bt_force2]                                     *)
(* ------------------------------------------------------------------------- *)

Lemma stree_agree : forall t node, 0 <= node <= 2 ->
  match RT.sd_stree (tk_of t) with
  | None => DS.stree_has t = false
  | Some st => DS.stree_has t = true /\ DS.stree_Len t node = RT.t_len st node
  end.
Proof.
  intros [] node Hn; cbn [RT.sd_stree tk_of DS.stree_has DS.stree_Len]; try reflexivity;
    (split; [reflexivity|]); unfold RT.t_len; cbn [RT.tr_dl RT.static_ltree RT.static_dtree];
    unfold DS.static_ltree_dl, DS.static_dtree_dl; rewrite BrTally.arr_of_list_zlist by lia; reflexivity.
Qed.

Lemma loop2_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC mc T hp dep blc,
  brel t FC DL HP DP BC T hp dep blc ->
  0 <= HL <= DS.sd_elems t -> pqb (DS.sd_elems t) HP HL -> -1 <= mc < DS.sd_elems t ->
  (Z.to_nat (2 - HL) <= f)%nat -> (Z.to_nat (2 - HL) < g)%nat ->
  let r := DT.build_tree_loop2 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t mc in
  match RT.bt_force2 g (RT.sd_stree (tk_of t)) T hp dep HL mc OL SL with
  | (T', hp', dep', hl', mc', ol', sl') =>
    exists FC' HP' DP', fst r = bt_upd s0 t FC' DL HP' hl' HM DP' BC ol' sl' MC
      /\ snd r = mc' /\ brel t FC' DL HP' DP' BC T' hp' dep' blc
      /\ 2 <= hl' <= DS.sd_elems t /\ pqb (DS.sd_elems t) HP' hl' /\ -1 <= mc' < DS.sd_elems t
  end.
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC mc T hp dep blc H HL0 Hpq Hmc Hf Hg r;
    destruct (elems_range t) as [HE Hts]; subst r.
  - destruct g as [|g]; [lia|]. cbn [DT.build_tree_loop2 RT.bt_force2 fst snd].
    replace (2 <=? HL) with true by (symmetry; apply Z.leb_le; lia).
    exists FC, HP, DP. csplit; first [assumption | reflexivity | lia].
  - destruct g as [|g]; [lia|].
    cbn [DT.build_tree_loop2 RT.bt_force2]. autorewrite with btupd.
    destruct (Z.leb_spec 2 HL) as [H2|H2].
    + replace (HL <? 2) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
      exists FC, HP, DP. csplit; first [assumption | reflexivity | lia].
    + replace (HL <? 2) with true by (symmetry; apply Z.ltb_lt; lia).
      set (node := if mc <? 2 then mc + 1 else 0).
      set (mc' := if mc <? 2 then mc + 1 else mc).
      assert (Hnode : 0 <= node <= 2 /\ -1 <= mc' < DS.sd_elems t)
        by (subst node mc'; destruct (Z.ltb_spec mc 2); lia).
      replace (if mc <? 2 then (mc + 1, mc + 1) else (0, mc)) with (node, mc')
        by (subst node mc'; destruct (mc <? 2); reflexivity).
      cbv zeta. autorewrite with btupd.
      pose proof (stree_agree t node ltac:(lia)) as ST.
      set (SL' := if DS.stree_has t then wrap64 (SL - DS.stree_Len t node) else SL).
      set (sl' := match RT.sd_stree (tk_of t) with None => SL | Some st => RT.u64 (SL - RT.t_len st node) end).
      assert (ESL : SL' = sl').
      { subst SL' sl'. destruct (RT.sd_stree (tk_of t)) as [st|]; [destruct ST as [-> ->]; apply wrap64_u64 | rewrite ST; reflexivity]. }
      assert (EX : (if DS.stree_has t
                    then bt_upd s0 t (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node)
                           (HL + 1) HM (arr_set DP node (wrap8 0)) BC (wrap64 (OL - 1))
                           (wrap64 (SL - DS.stree_Len t node)) MC
                    else bt_upd s0 t (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node)
                                (HL + 1) HM (arr_set DP node (wrap8 0)) BC (wrap64 (OL - 1)) SL MC)
                   = bt_upd s0 t (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node)
                            (HL + 1) HM (arr_set DP node (wrap8 0)) BC (wrap64 (OL - 1)) SL' MC).
      { subst SL'. destruct (DS.stree_has t); reflexivity. }
      rewrite EX. clear EX. rewrite <- ESL.
      change (Base.zset dep node 0) with (Base.zset dep node (Base.u8 0)).
      rewrite <- wrap64_u64.
      pose proof (IH g s0 t (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM
                    (arr_set DP node (wrap8 0)) BC (wrap64 (OL - 1)) SL' MC mc' (RT.t_setfreq T node 1)
                    (Base.zset hp (HL + 1) node) (Base.zset dep node (Base.u8 0)) blc) as IH'.
      cbv zeta in IH'.
      destruct (RT.bt_force2 g (RT.sd_stree (tk_of t)) (RT.t_setfreq T node 1) (Base.zset hp (HL + 1) node)
                  (Base.zset dep node (Base.u8 0)) (HL + 1) mc' (wrap64 (OL - 1)) SL')
        as [[[[[[T' hp'] dep'] hl'] mc''] ol'] sl''].
      destruct IH' as (FC' & HP' & DP' & E1 & E2 & E3 & E4 & E5 & E6).
      { apply brel_dp_set; [apply brel_hp_set; [apply brel_fc_set; [exact H | lia] | lia] | lia]. }
      { lia. }
      { intros i Hi. rewrite arr_get_set. destruct (_ && _) eqn:Ei; [lia|].
        destruct (Z.eq_dec i (HL + 1)) as [->|Ne].
        - exfalso. rewrite Z.eqb_refl in Ei. cbn [andb] in Ei. rewrite (proj2 (arr_inb_spec HP (HL + 1))) in Ei
            by (rewrite (b_lhp _ _ _ _ _ _ _ _ _ _ H); lia). discriminate.
        - apply Hpq. lia. }
      { lia. } { lia. } { lia. }
      exists FC', HP', DP'. csplit; first [assumption | reflexivity | lia].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  [build_tree_loop3] vs [bt_heapify]                                    *)
(* ------------------------------------------------------------------------- *)

Lemma pqb_pqr : forall t HP HL, pqb (DS.sd_elems t) HP HL -> pqr t HP HL.
Proof. intros t HP HL H i Hi. destruct (elems_range t). specialize (H i Hi). lia. Qed.

Lemma loop3_rel : forall f g n s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc,
  brel t FC DL HP DP BC T hp dep blc -> HL < 573 -> n <= HL -> pqr t HP HL ->
  (Z.to_nat n <= f)%nat -> (Z.to_nat n < g)%nat ->
  exists HP', DT.build_tree_loop3 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t n
              = bt_upd s0 t FC DL HP' HL HM DP BC OL SL MC
    /\ brel t FC DL HP' DP BC T (RT.bt_heapify g T dep hp HL n) dep blc /\ pqr t HP' HL.
Proof.
  induction f as [|f IH]; intros g n s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc H HL573 Hn Hpq Hf Hg.
  - destruct g as [|g]; [lia|]. cbn [DT.build_tree_loop3 RT.bt_heapify].
    replace (n <? 1) with true by (symmetry; apply Z.ltb_lt; lia).
    exists HP. csplit; first [assumption | reflexivity].
  - destruct g as [|g]; [lia|]. cbn [DT.build_tree_loop3 RT.bt_heapify].
    destruct (Z.leb_spec 1 n) as [H1|H1].
    + replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
      destruct (pqdownheap_rel s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc n H HL573 ltac:(lia) Hpq)
        as (HP1 & E1 & E2 & E3).
      rewrite E1.
      apply (IH g (n - 1) s0 t FC DL HP1 HL HM DP BC OL SL MC T (RT.pqdownheap T dep hp HL n) dep blc E2 HL573);
        [lia | exact E3 | lia | lia].
    + replace (n <? 1) with true by (symmetry; apply Z.ltb_lt; lia).
      exists HP. csplit; first [assumption | reflexivity].
Qed.
