(** * Bridge.DEmit.BrBuildTree — pairs D26-D28 composed: [build_tree].

    S5's [build_tree] and RT's run the same phases; the phase lemmas are in
    [BrBuildTree0]-[BrBuildTree4]:
    - heap setup ([loop1_rel], [loop2_rel]), max code, heapify
      ([loop3_rel]), the combine loop ([loop4_rel]), the root store;
    - [gen_bitlen] ([gen_bitlen_rel]);
    - [gen_codes] ([gen_codes_rel]).
    S5's [bt_safe] is unfolded alongside the S5 run, so each of its facts
    is read at the state the phase lemma needs it. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs
  BrBuildTree0 BrBuildTree1 BrBuildTree2 BrBuildTree3 BrBuildTree4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** The [btupd] rewrites below run on terms holding S5's loops at fuel 573;
    keyed matching keeps the matcher from unfolding them. *)
Local Set Keyed Unification.

(* ------------------------------------------------------------------------- *)
(* 1.  [trel] and [brel]                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma brel_of_trel : forall s ts t, trel s ts -> TM.tree_lens s ->
  brel t (DS.tree_fc s t) (DS.tree_dl s t) (DS.ds_heap s) (DS.ds_depth s) (DS.ds_bl_count s)
       (RT.ts_trees ts (tk_of t)) (RT.ts_heap ts) (RT.ts_depth ts) (RT.ts_blcount ts).
Proof.
  intros s ts t HT HL. unfold trel in HT. cbv zeta in HT. unfold TM.tree_lens in HL.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & _).
  destruct HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
  destruct t; constructor; cbn [DS.tree_fc DS.tree_dl tk_of TM.tsize]; assumption.
Qed.

Ltac tkne := unfold RT.TK_L, RT.TK_D, RT.TK_BL; lia.

Lemma trel_upd : forall s0 ts ts' t FC DL HP HL HM DP BC OL SL MC,
  trel s0 ts ->
  brel t FC DL HP DP BC (RT.ts_trees ts' (tk_of t)) (RT.ts_heap ts') (RT.ts_depth ts') (RT.ts_blcount ts') ->
  (forall j, j <> tk_of t -> RT.ts_trees ts' j = RT.ts_trees ts j) ->
  (forall j, j <> tk_of t -> RT.ts_maxcode ts' j = RT.ts_maxcode ts j) ->
  HL = RT.ts_heaplen ts' -> HM = RT.ts_heapmax ts' -> OL = RT.ts_optlen ts' -> SL = RT.ts_statlen ts' ->
  MC = RT.ts_maxcode ts' (tk_of t) -> RT.ts_matches ts' = RT.ts_matches ts ->
  trel (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) ts'.
Proof.
  intros s0 ts ts' t FC DL HP HL HM DP BC OL SL MC HT B Eo Em EHL EHM EOL ESL EMC Emt.
  destruct B as [Bfc Bdl Bhp Bdp Bbc _ _ _ _ _].
  unfold trel in *. cbv zeta in *.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17).
  destruct t; cbn [tk_of TM.tsize] in *;
    cbn [bt_upd DS.ds_dyn_ltree_fc DS.ds_dyn_ltree_dl DS.ds_dyn_dtree_fc DS.ds_dyn_dtree_dl DS.ds_bl_tree_fc
         DS.ds_bl_tree_dl DS.ds_bl_count DS.ds_heap DS.ds_depth DS.ds_l_max_code DS.ds_d_max_code DS.ds_bl_max_code
         DS.ds_heap_len DS.ds_heap_max DS.ds_opt_len DS.ds_static_len DS.ds_matches];
    csplit;
    first [ exact Bfc | exact Bdl | exact Bhp | exact Bdp | exact Bbc | assumption
          | (rewrite Eo by tkne; assumption) | (rewrite Em by tkne; assumption) | (rewrite Emt; assumption) ].
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's installs                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma rt_bt_install : forall k T hp dep hl hm mc ol sl (ts ts' : RT.TSt),
  ts' = RT.set_statlen sl (RT.set_optlen ol (RT.set_heapmax hm (RT.set_heaplen hl
          (RT.set_depth dep (RT.set_heap hp (RT.set_max k mc (RT.set_tree k T ts))))))) ->
  RT.ts_trees ts' k = T /\ RT.ts_heap ts' = hp /\ RT.ts_depth ts' = dep /\ RT.ts_blcount ts' = RT.ts_blcount ts
  /\ RT.ts_heaplen ts' = hl /\ RT.ts_heapmax ts' = hm /\ RT.ts_maxcode ts' k = mc
  /\ RT.ts_optlen ts' = ol /\ RT.ts_statlen ts' = sl
  /\ (forall j, j <> k -> RT.ts_trees ts' j = RT.ts_trees ts j)
  /\ (forall j, j <> k -> RT.ts_maxcode ts' j = RT.ts_maxcode ts j)
  /\ RT.ts_matches ts' = RT.ts_matches ts.
Proof.
  intros k T hp dep hl hm mc ol sl ts ts' ->. cbn. rewrite !Z.eqb_refl.
  csplit; try reflexivity; intros j Hj; replace (j =? k) with false by (symmetry; apply Z.eqb_neq; exact Hj);
    reflexivity.
Qed.

Lemma rt_set_tree_proj : forall k T (ts : RT.TSt),
  RT.ts_trees (RT.set_tree k T ts) k = T /\ RT.ts_heap (RT.set_tree k T ts) = RT.ts_heap ts
  /\ RT.ts_depth (RT.set_tree k T ts) = RT.ts_depth ts /\ RT.ts_blcount (RT.set_tree k T ts) = RT.ts_blcount ts
  /\ RT.ts_heaplen (RT.set_tree k T ts) = RT.ts_heaplen ts /\ RT.ts_heapmax (RT.set_tree k T ts) = RT.ts_heapmax ts
  /\ RT.ts_maxcode (RT.set_tree k T ts) = RT.ts_maxcode ts
  /\ RT.ts_optlen (RT.set_tree k T ts) = RT.ts_optlen ts /\ RT.ts_statlen (RT.set_tree k T ts) = RT.ts_statlen ts
  /\ (forall j, j <> k -> RT.ts_trees (RT.set_tree k T ts) j = RT.ts_trees ts j)
  /\ RT.ts_symbuf (RT.set_tree k T ts) = RT.ts_symbuf ts /\ RT.ts_symnext (RT.set_tree k T ts) = RT.ts_symnext ts
  /\ RT.ts_matches (RT.set_tree k T ts) = RT.ts_matches ts /\ RT.ts_bw (RT.set_tree k T ts) = RT.ts_bw ts.
Proof.
  intros k T ts. cbn. rewrite Z.eqb_refl.
  csplit; try reflexivity; intros j Hj; replace (j =? k) with false by (symmetry; apply Z.eqb_neq; exact Hj);
    reflexivity.
Qed.

Lemma rt_gen_bitlen_frame : forall k ts,
  RT.ts_symbuf (RT.gen_bitlen k ts) = RT.ts_symbuf ts /\ RT.ts_symnext (RT.gen_bitlen k ts) = RT.ts_symnext ts
  /\ RT.ts_matches (RT.gen_bitlen k ts) = RT.ts_matches ts /\ RT.ts_bw (RT.gen_bitlen k ts) = RT.ts_bw ts.
Proof.
  intros k ts. unfold RT.gen_bitlen. cbv zeta.
  destruct (RT.gb_pass1 _ _ _ _ _ _ _ _ _ _ _ _ _ _) as [[[[T2 blc1] ol1] sl1] ov].
  destruct (ov =? 0); [cbn; csplit; reflexivity|].
  destruct (RT.gb_pass2 _ _ _ _ _ _ _ _ _) as [T3 ol2]. cbn; csplit; reflexivity.
Qed.

(** [RT.build_tree] only touches the tree fields. *)
Lemma rt_build_tree_frame : forall k ts,
  let ts' := RT.build_tree k ts in
  RT.ts_symbuf ts' = RT.ts_symbuf ts /\ RT.ts_symnext ts' = RT.ts_symnext ts
  /\ RT.ts_matches ts' = RT.ts_matches ts /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof.
  intros k ts ts'. subst ts'. unfold RT.build_tree. cbv zeta.
  destruct (RT.bt_init _ _ _ _ _ _ _ _) as [[[[t0 hp0] dep0] hlen0] maxc0].
  destruct (RT.bt_force2 _ _ _ _ _ _ _ _ _) as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1].
  destruct (RT.bt_loop _ _) as [stf|]; [|csplit; reflexivity].
  match goal with |- context [RT.set_tree k ?X (RT.gen_bitlen k ?S)] =>
    destruct (rt_set_tree_proj k X (RT.gen_bitlen k S)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4);
    destruct (rt_gen_bitlen_frame k S) as (F1 & F2 & F3 & F4) end.
  rewrite J1, J2, J3, J4, F1, F2, F3, F4. cbn. csplit; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  [build_tree]                                                          *)
(* ------------------------------------------------------------------------- *)

Lemma br_build_tree_upd : forall s0 ts t FC DL HP HL HM DP BC OL SL MC,
  trel s0 ts ->
  brel t FC DL HP DP BC (RT.ts_trees ts (tk_of t)) (RT.ts_heap ts) (RT.ts_depth ts) (RT.ts_blcount ts) ->
  OL = RT.ts_optlen ts -> SL = RT.ts_statlen ts ->
  GBM.bt_safe (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t ->
  trel (DT.build_tree (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t) (RT.build_tree (tk_of t) ts)
  /\ -1 <= RT.ts_maxcode (RT.build_tree (tk_of t) ts) (tk_of t) < DS.sd_elems t
  /\ (TM.tree_lens s0 -> TM.tree_lens (DT.build_tree (bt_upd s0 t FC DL HP HL HM DP BC OL SL MC) t)).
Proof.
  intros s0 ts t FC DL HP HL HM DP BC OL SL MC HT B0 EOL ESL HS.
  pose proof (tsize_le t) as Ht. destruct (elems_range t) as [HE Hts]. pose proof (ml_range t) as Hml.
  unfold GBM.bt_safe in HS. cbv zeta in HS. destruct HS as (_ & _ & _ & HS). revert HS.
  unfold DT.build_tree, RT.build_tree. cbv zeta.
  autorewrite with btupd.
  rewrite sd_elems_tk, <- EOL, <- ESL.
  change DS.HEAP_SIZE with 573. change RT.HEAP_SIZE with 573.
  (* heap setup *)
  pose proof (loop1_rel (Z.to_nat (DS.sd_elems t)) (Z.to_nat RT.L_CODES + 2) 0 s0 t FC DL HP 0 573 DP BC OL SL MC (-1)
                (RT.ts_trees ts (tk_of t)) (RT.ts_heap ts) (RT.ts_depth ts) (RT.ts_blcount ts) B0
                ltac:(f_equal; lia) ltac:(unfold RT.L_CODES; lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros i Hi; lia) ltac:(lia)) as P1.
  cbv zeta in P1. revert P1.
  destruct (RT.bt_init (Z.to_nat RT.L_CODES + 2) 0 (DS.sd_elems t) (RT.ts_trees ts (tk_of t)) (RT.ts_heap ts)
              (RT.ts_depth ts) 0 (-1)) as [[[[T0 hp0] dep0] hl0] mc0].
  destruct (DT.build_tree_loop1 (Z.to_nat (DS.sd_elems t)) (bt_upd s0 t FC DL HP 0 573 DP BC OL SL MC) t
              (DS.sd_elems t) 0 (-1)) as [X1 m1].
  intros P1. cbv beta iota in P1.
  destruct P1 as (DL1 & HP1 & DP1 & E1 & E2 & B1 & Hhl0 & Hpq0 & Hmc0). cbn [fst snd] in E1, E2. subst X1 m1.
  cbv beta iota.
  pose proof (loop2_rel 2 3 s0 t FC DL1 HP1 hl0 573 DP1 BC OL SL MC mc0 T0 hp0 dep0 (RT.ts_blcount ts) B1
                ltac:(lia) Hpq0 Hmc0 ltac:(lia) ltac:(lia)) as P2.
  cbv zeta in P2. revert P2.
  destruct (RT.bt_force2 3 (RT.sd_stree (tk_of t)) T0 hp0 dep0 hl0 mc0 OL SL)
    as [[[[[[T1 hp1] dep1] hl1] mc1] ol1] sl1].
  destruct (DT.build_tree_loop2 2 (bt_upd s0 t FC DL1 HP1 hl0 573 DP1 BC OL SL MC) t mc0) as [X2 m2].
  intros P2. cbv beta iota in P2.
  destruct P2 as (FC2 & HP2 & DP2 & E1 & E2 & B2 & Hhl1 & Hpq1 & Hmc1). cbn [fst snd] in E1, E2. subst X2 m2.
  cbv beta iota.
  autorewrite with btupd.
  (* heapify *)
  pose proof (loop3_rel (Z.to_nat (hl1 / 2)) (Z.to_nat 573) (hl1 / 2) s0 t FC2 DL1 HP2 hl1 573 DP2 BC ol1 sl1 mc1
                T1 hp1 dep1 (RT.ts_blcount ts) B2 ltac:(lia) ltac:(lia) (pqb_pqr _ _ _ Hpq1) ltac:(lia) ltac:(lia))
    as P3.
  destruct P3 as (HP3 & E3 & B3 & Q3).
  rewrite E3.
  (* the combine loop *)
  pose proof (loop4_rel 573 (Z.to_nat 573) s0 t FC2 DL1 HP3 hl1 573 DP2 BC ol1 sl1 mc1 T1
                (RT.bt_heapify (Z.to_nat 573) T1 dep1 hp1 hl1 (hl1 / 2)) dep1 (RT.ts_blcount ts) (DS.sd_elems t) B3
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q3 ltac:(lia) ltac:(lia))
    as P4.
  destruct P4 as (FC4 & DL4 & HP4 & HL4 & HM4 & DP4 & stf & E4 & F2 & B4 & EH4 & EM4 & H41 & H42 & H43 & Q4).
  rewrite E4.
  unfold bst in F2. rewrite F2. cbv beta iota.
  autorewrite with btupd.
  intros HS.
  (* the root store, then [gen_bitlen] *)
  match goal with |- context [RT.gen_bitlen (tk_of t) ?S] => remember S as S1 eqn:ES1 end.
  destruct (rt_bt_install _ _ _ _ _ _ _ _ _ _ _ ES1) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
  destruct HS as (_ & _ & _ & Htop & Hdl & Hg1 & Hg2 & Hlen).
  set (HP7 := arr_set HP4 (HM4 - 1) (arr_get HP4 DS.SMALLEST)) in *.
  assert (LHP4 : arr_len HP4 = 573) by exact (b_lhp _ _ _ _ _ _ _ _ _ _ B4).
  assert (B7 : brel t FC4 DL4 HP7 DP4 BC (RT.ts_trees S1 (tk_of t)) (RT.ts_heap S1) (RT.ts_depth S1)
                 (RT.ts_blcount S1)).
  { rewrite I1, I2, I3, I4. rewrite <- EM4. subst HP7. unfold DS.SMALLEST, RT.SMALLEST.
    rewrite (brel_hp_get _ _ _ _ _ _ _ _ _ _ 1 B4) by lia.
    apply brel_hp_set; [exact B4 | lia]. }
  assert (Hroot : 0 <= arr_get HP7 (HM4 - 1) < TM.tsize t).
  { subst HP7. rewrite arr_get_set_same by lia. unfold DS.SMALLEST. apply Q4. lia. }
  assert (Htop' : forall h, HM4 - 1 + 1 <= h < 573 -> 0 <= arr_get HP7 h < TM.tsize t).
  { intros h Hh. specialize (Htop h Hh). autorewrite with btupd in Htop. exact Htop. }
  pose proof (gen_bitlen_rel s0 t FC4 DL4 HP7 HL4 (HM4 - 1) DP4 BC ol1 sl1 mc1 S1 B7
                ltac:(rewrite I6, <- EM4; reflexivity) ltac:(rewrite I7; reflexivity)
                ltac:(rewrite I8; reflexivity) ltac:(rewrite I9; reflexivity)
                ltac:(lia) ltac:(lia) Hroot Htop' Hdl Hg1 Hg2) as P5.
  destruct P5 as (DL5 & BC5 & OL5 & SL5 & E5 & B5 & EO5 & ES5 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  rewrite E5 in Hlen |- *.
  (* [gen_codes] *)
  pose proof (gen_codes_rel s0 t FC4 DL5 HP7 HL4 (HM4 - 1) DP4 BC5 OL5 SL5 mc1 _ _ _ _ mc1 B5 ltac:(lia)
                ltac:(intros i Hi; specialize (Hlen i Hi); autorewrite with btupd in Hlen; exact Hlen)) as P6.
  destruct P6 as (FC6 & E6 & B6).
  rewrite E6.
  match goal with |- trel _ (RT.set_tree _ ?X ?S) /\ _ =>
    destruct (rt_set_tree_proj (tk_of t) X S)
      as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14) end.
  split.
  - apply (trel_upd s0 ts).
    + exact HT.
    + rewrite J1, J2, J3, J4. exact B6.
    + intros j Hj. rewrite J10 by exact Hj. rewrite G6 by exact Hj. apply I10, Hj.
    + intros j Hj. rewrite J7, G5. apply I11, Hj.
    + rewrite J5, G3, I5. exact EH4.
    + rewrite J6, G4, I6. lia.
    + rewrite J8. exact EO5.
    + rewrite J9. exact ES5.
    + rewrite J7, G5, I7. reflexivity.
    + rewrite J13, G9, I12. reflexivity.
  - split; [rewrite J7, G5, I7; exact Hmc1|].
    intros HL0. destruct B6 as [_ _ _ _ _ Lfc Ldl Lhp Ldp Lbc]. unfold TM.tree_lens in *.
    destruct t; cbn [bt_upd TM.tsize DS.ds_dyn_ltree_fc DS.ds_dyn_ltree_dl DS.ds_dyn_dtree_fc DS.ds_dyn_dtree_dl
                     DS.ds_bl_tree_fc DS.ds_bl_tree_dl DS.ds_bl_count DS.ds_heap DS.ds_depth] in *; tauto.
Qed.

Theorem br_build_tree : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t ->
  trel (DT.build_tree s t) (RT.build_tree (tk_of t) ts).
Proof.
  intros s ts t HT HL HS.
  pose proof (brel_of_trel s ts t HT HL) as B0.
  assert (EOL : DS.ds_opt_len s = RT.ts_optlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  assert (ESL : DS.ds_static_len s = RT.ts_statlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  rewrite <- (bt_upd_self s t) in HS |- *.
  exact (proj1 (br_build_tree_upd _ _ _ _ _ _ _ _ _ _ _ _ _ HT B0 EOL ESL HS)).
Qed.

(** The max code [build_tree] records is below the tree's element count
    (so [scan_tree]/[send_tree] stay within RT's [L_CODES + 3] steps). *)
Theorem br_build_tree_mc : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t ->
  -1 <= DS.max_code (DT.build_tree s t) t < DS.sd_elems t.
Proof.
  intros s ts t HT HL HS.
  pose proof (brel_of_trel s ts t HT HL) as B0.
  assert (EOL : DS.ds_opt_len s = RT.ts_optlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  assert (ESL : DS.ds_static_len s = RT.ts_statlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  rewrite <- (bt_upd_self s t) in HS |- *.
  destruct (br_build_tree_upd _ _ _ _ _ _ _ _ _ _ _ _ _ HT B0 EOL ESL HS) as [R [M _]].
  unfold trel in R. cbv zeta in R.
  destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R10 & R11 & R12 & _).
  destruct t; cbn [DS.max_code tk_of] in *; [rewrite R10 | rewrite R11 | rewrite R12]; exact M.
Qed.

(** [build_tree] keeps every tree array at its allocated length. *)
Theorem br_build_tree_lens : forall s ts t,
  trel s ts -> TM.tree_lens s -> GBM.bt_safe s t -> TM.tree_lens (DT.build_tree s t).
Proof.
  intros s ts t HT HL HS.
  pose proof (brel_of_trel s ts t HT HL) as B0.
  assert (EOL : DS.ds_opt_len s = RT.ts_optlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  assert (ESL : DS.ds_static_len s = RT.ts_statlen ts) by (unfold trel in HT; cbv zeta in HT; tauto).
  pose proof HL as HL'. rewrite <- (bt_upd_self s t) in HS, HL' |- *.
  destruct (br_build_tree_upd _ _ _ _ _ _ _ _ _ _ _ _ _ HT B0 EOL ESL HS) as [_ [_ Hlens]].
  apply Hlens. exact HL.
Qed.
