(** * Bridge.DEmit.BrBuildTree2 — pair D26, the combine loop.

    S5's [build_tree_loop4] (fuel 573) against RT's [bt_loop] (fuel
    HEAP_SIZE = 573) over [bt_step]: one trip removes the two smallest
    nodes [n], [m], stores them at the top of the heap array, and inserts
    their parent [node].  Each trip shrinks [heap_len] by one and the loop
    stops at 1, so both fuels are generous ([heap_len <= 286]).

    The invariant also bounds the indices the trip writes: [node] stays
    below the tree size ([node + heap_len - 2 < tsize]) and the two top
    stores stay inside the heap array ([heap_max - 2 heap_len >= 1]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrBuildTree0 BrBuildTree1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition bst (T : RT.Tree) (hp dep : Base.zarr) (hl hm node : Z) : RT.BtSt :=
  {| RT.b_tree := T; RT.b_heap := hp; RT.b_dep := dep; RT.b_hlen := hl; RT.b_hmax := hm; RT.b_node := node |}.

Lemma loop4_rel : forall f g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc node,
  brel t FC DL HP DP BC T hp dep blc -> 2 <= HL < 573 -> 1 <= HM - 2 * HL -> HM <= 573 ->
  0 <= node -> node + HL - 2 < TM.tsize t -> pqr t HP HL ->
  (Z.to_nat HL <= f)%nat -> (Z.to_nat HL <= g)%nat ->
  exists FC' DL' HP' HL' HM' DP' stf,
    DT.build_tree_loop4 f (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t node
      = bt_upd s0 t FC' DL' HP' HL' HM' DP' BC OL SL MC
    /\ RT.bt_loop g (bst T hp dep HL HM node) = Some stf
    /\ brel t FC' DL' HP' DP' BC (RT.b_tree stf) (RT.b_heap stf) (RT.b_dep stf) blc
    /\ HL' = RT.b_hlen stf /\ HM' = RT.b_hmax stf
    /\ HL' = 1 /\ 1 <= HM' - 2 * HL' /\ HM' <= 573 /\ pqr t HP' HL'.
Proof.
  induction f as [|f IH]; intros g s0 t FC DL HP HL HM DP BC OL SL MC T hp dep blc node H HL2 HM2 HM573 Hn0 Hnode Hpq Hf Hg;
    [lia|].
  destruct g as [|g]; [lia|].
  pose proof (tsize_le t) as Ht.
  assert (P1 : 0 <= arr_get HP 1 < TM.tsize t) by (apply Hpq; lia).
  assert (PL : 0 <= arr_get HP HL < TM.tsize t) by (apply Hpq; lia).
  cbn [DT.build_tree_loop4 RT.bt_loop]. unfold DS.SMALLEST. cbv zeta. autorewrite with btupd.
  (* the first pqdownheap *)
  destruct (pqdownheap_rel s0 t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC T
              (Base.zset hp 1 (arr_get HP HL)) dep blc 1) as (HP3 & E3 & B3 & Q3).
  { apply brel_hp_set; [exact H | lia]. } { lia. } { lia. }
  { apply pqr_set; [intros i Hi; apply Hpq; lia | exact PL]. }
  rewrite E3. autorewrite with btupd.
  assert (P3 : 0 <= arr_get HP3 1 < TM.tsize t) by (apply Q3; lia).
  set (n := arr_get HP 1) in *. set (m := arr_get HP3 1) in *.
  set (v := (if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m) + 1).
  (* the second pqdownheap *)
  set (FC8 := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m))).
  set (DL11 := arr_set (arr_set DL m (wrap16 node)) n (wrap16 node)).
  set (DP9 := arr_set DP node (wrap8 v)).
  set (HP12 := arr_set (arr_set (arr_set HP3 (HM - 1) n) (HM - 1 - 1) m) 1 node).
  set (T2 := RT.t_setlen (RT.t_setlen (RT.t_setfreq T node (RT.t_freq T n + RT.t_freq T m)) m node) n node).
  set (dep1 := Base.zset dep node (Base.u8 ((if dep m <=? dep n then dep n else dep m) + 1))).
  set (hp5 := Base.zset (Base.zset (Base.zset (RT.pqdownheap T dep (Base.zset hp 1 (arr_get HP HL)) (HL - 1) 1)
                                                (HM - 1) n) (HM - 1 - 1) m) 1 node).
  assert (B12 : brel t FC8 DL11 HP12 DP9 BC T2 hp5 dep1 blc).
  { subst FC8 DL11 HP12 DP9 T2 dep1 hp5 v.
    unfold RT.t_freq. rewrite <- (brel_fc_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
    rewrite <- (brel_fc_get _ _ _ _ _ _ _ _ _ _ m H) by lia.
    rewrite <- (brel_dp_get _ _ _ _ _ _ _ _ _ _ n H) by lia.
    rewrite <- (brel_dp_get _ _ _ _ _ _ _ _ _ _ m H) by lia.
    apply brel_hp_set; [|lia]. apply brel_hp_set; [|lia]. apply brel_hp_set; [|lia].
    apply brel_dl_set; [|lia]. apply brel_dl_set; [|lia].
    apply brel_dp_set; [|lia]. apply brel_fc_set; [|lia].
    destruct B3. constructor; assumption. }
  destruct (pqdownheap_rel s0 t FC8 DL11 HP12 (HL - 1) (HM - 1 - 1) DP9 BC OL SL MC T2 hp5 dep1 blc 1 B12)
    as (HP13 & E13 & B13 & Q13); [lia | lia | |].
  { subst HP12. apply pqr_set; [|lia]. apply pqr_set; [|lia]. apply pqr_set; [exact Q3 | lia]. }
  (* the RT trip, in the same names *)
  assert (EST : RT.bt_step (bst T hp dep HL HM node)
                = if 2 <=? HL - 1 then RT.BtCont (bst T2 (RT.pqdownheap T2 dep1 hp5 (HL - 1) 1) dep1 (HL - 1) (HM - 1 - 1) (node + 1))
                  else RT.BtDone (bst T2 (RT.pqdownheap T2 dep1 hp5 (HL - 1) 1) dep1 (HL - 1) (HM - 1 - 1) (node + 1))).
  { unfold RT.bt_step, bst. cbn [RT.b_heap RT.b_hlen RT.b_tree RT.b_dep RT.b_hmax RT.b_node]. unfold RT.SMALLEST.
    subst T2 dep1 hp5 m n.
    rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ 1 H) by lia.
    rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ HL H) by lia.
    rewrite <- (brel_hp_get _ _ _ _ _ _ _ _ _ _ 1 B3) by lia.
    reflexivity. }
  rewrite EST.
  replace (DS.ds_heap_len (bt_upd s0 t FC8 DL11 HP13 (HL - 1) (HM - 1 - 1) DP9 BC OL SL MC)) with (HL - 1)
    by (autorewrite with btupd; reflexivity).
  rewrite E13. autorewrite with btupd.
  destruct (Z.leb_spec 2 (HL - 1)) as [C|C].
  - destruct (IH g s0 t FC8 DL11 HP13 (HL - 1) (HM - 1 - 1) DP9 BC OL SL MC T2
               (RT.pqdownheap T2 dep1 hp5 (HL - 1) 1) dep1 blc (node + 1) B13)
      as (FC' & DL' & HP' & HL' & HM' & DP' & stf & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9);
      [lia | lia | lia | lia | lia | exact Q13 | lia | lia |].
    exists FC', DL', HP', HL', HM', DP', stf.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|]. split; [exact F7|]. split; [exact F8 | exact F9].
  - exists FC8, DL11, HP13, (HL - 1), (HM - 1 - 1), DP9,
      (bst T2 (RT.pqdownheap T2 dep1 hp5 (HL - 1) 1) dep1 (HL - 1) (HM - 1 - 1) (node + 1)).
    split; [reflexivity|]. split; [reflexivity|].
    cbn [bst RT.b_tree RT.b_heap RT.b_dep RT.b_hlen RT.b_hmax].
    split; [exact B13|]. split; [reflexivity|]. split; [reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia | exact Q13].
Qed.
