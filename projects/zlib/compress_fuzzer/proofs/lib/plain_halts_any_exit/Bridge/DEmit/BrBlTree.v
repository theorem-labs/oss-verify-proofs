(** * Bridge.DEmit.BrBlTree — pair D30 (build half): [build_bl_tree], S5 vs RT.

    [build_bl_tree] is two [scan_tree]s ([BrScanTree]), a [build_tree] on
    the bit-length tree ([BrBuildTree]), the scan for the last non-zero
    bit-length code in [bl_order], and an [opt_len] update; both models
    run the same steps.  The extra facts this composition needs are S5
    frames: a [scan_tree] keeps every tree array's length ([scan_tree_lens]),
    and the other trees' lengths and max codes, which [trel] carries. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrScanTree BrBuildTree BrTally.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* 1.  S5 frames for [scan_tree]                                             *)
(* ------------------------------------------------------------------------- *)

Ltac split_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c end.

Lemma set_Freq_TB_lens : forall s n v, TM.tree_lens s -> TM.tree_lens (DS.set_Freq s DS.TB n v).
Proof.
  intros s n v H. unfold DS.set_Freq. cbn [DS.set_tree_fc DS.tree_fc]. unfold TM.tree_lens in *.
  autorewrite with s5f_bl_tree_fc. rewrite arr_len_set. exact H.
Qed.

Lemma scan_loop_lens : forall f s t mc n p q c mx mn,
  TM.tree_lens s -> TM.tree_lens (DT.scan_tree_loop f s t mc n p q c mx mn).
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn H; cbn [DT.scan_tree_loop]; [exact H|].
  destruct (n <=? mc); [|exact H]. cbv zeta.
  destruct (_ && _); [apply IH; exact H|].
  destruct (DT.tree_counts _ _) as [mx' mn']. apply IH.
  split_ifs; repeat apply set_Freq_TB_lens; exact H.
Qed.

Lemma scan_tree_lens : forall s t mc, TM.tree_lens s -> TM.tree_lens (DT.scan_tree s t mc).
Proof.
  intros s t mc H. unfold DT.scan_tree. cbv zeta.
  destruct (_ =? 0); apply scan_loop_lens;
    unfold DS.set_Len, DS.set_Dad; destruct t; cbn [DS.set_tree_dl DS.tree_dl]; unfold TM.tree_lens in *;
    autorewrite with s5f_dyn_ltree_dl s5f_dyn_dtree_dl s5f_bl_tree_dl; rewrite arr_len_set; exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The last non-zero bit-length code                                     *)
(* ------------------------------------------------------------------------- *)

Lemma bl_order_agree : forall i, 0 <= i -> arr_get DS.bl_order_a i = RT.bl_order i.
Proof. intros i Hi. unfold DS.bl_order_a, RT.bl_order. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.

Lemma bl_order_range : forall i, 0 <= i < 19 -> 0 <= RT.bl_order i < 19.
Proof.
  intros i Hi. assert (E : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9
                           \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18) by lia.
  assert (Hb : (0 <=? RT.bl_order i) && (RT.bl_order i <? 19) = true)
    by (repeat destruct E as [->|E]; try subst i; vm_compute; reflexivity).
  apply andb_prop in Hb. destruct Hb as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. lia.
Qed.

Lemma bbl_agree : forall f g s (B : RT.Tree) mb,
  (forall i, 0 <= i < 19 -> DS.Len s DS.TB i = RT.t_len B i) ->
  2 <= mb <= 18 -> (Z.to_nat (mb - 2) <= f)%nat -> (Z.to_nat (mb - 2) < g)%nat ->
  DT.build_bl_tree_loop f s mb = RT.bbl_scan g B mb.
Proof.
  induction f as [|f IH]; intros g s B mb HL Hmb Hf Hg.
  - destruct g as [|g]; [lia|]. cbn [DT.build_bl_tree_loop RT.bbl_scan].
    replace mb with 2 by lia. reflexivity.
  - destruct g as [|g]; [lia|]. cbn [DT.build_bl_tree_loop RT.bbl_scan].
    destruct (Z.leb_spec 3 mb) as [H3|H3].
    + replace (mb <? 3) with false by (symmetry; apply Z.ltb_ge; lia).
      rewrite bl_order_agree by lia. rewrite (HL (RT.bl_order mb)) by (apply bl_order_range; lia).
      destruct (negb (RT.t_len B (RT.bl_order mb) =? 0)); [reflexivity|].
      apply IH; [exact HL | lia | lia | lia].
    + replace (mb <? 3) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Lemma s5_bbl_eq : forall s,
  DT.build_bl_tree s =
  (let s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s) in
   let s2 := DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1) in
   let s3 := DT.build_tree s2 DS.TB in
   let mb := DT.build_bl_tree_loop 17 s3 (DS.BL_CODES - 1) in
   (DS.set_opt_len s3 (wrap64 (DS.ds_opt_len s3 + 3 * (mb + 1) + 5 + 5 + 4)), mb)).
Proof. reflexivity. Qed.

Lemma rt_bbl_eq : forall ts,
  RT.build_bl_tree ts =
  (let t1 := scan_ts RT.TK_L (RT.ts_maxcode ts RT.TK_L) ts in
   let t2 := scan_ts RT.TK_D (RT.ts_maxcode t1 RT.TK_D) t1 in
   let t3 := RT.build_tree RT.TK_BL t2 in
   let mbi := RT.bbl_scan (Z.to_nat RT.BL_CODES + 1) (RT.ts_trees t3 RT.TK_BL) (RT.BL_CODES - 1) in
   (mbi, RT.set_optlen (RT.u64 (RT.ts_optlen t3 + 3 * (mbi + 1) + 5 + 5 + 4)) t3)).
Proof. reflexivity. Qed.

Lemma scan_ts_trees : forall k mc ts j, j <> k -> j <> RT.TK_BL ->
  RT.ts_trees (scan_ts k mc ts) j = RT.ts_trees ts j.
Proof.
  intros k mc ts j H1 H2. unfold scan_ts. cbn [RT.set_tree RT.set_trees RT.ts_trees].
  replace (j =? RT.TK_BL) with false by (symmetry; apply Z.eqb_neq; exact H2).
  replace (j =? k) with false by (symmetry; apply Z.eqb_neq; exact H1). reflexivity.
Qed.

Lemma scan_ts_maxcode : forall k mc ts, RT.ts_maxcode (scan_ts k mc ts) = RT.ts_maxcode ts.
Proof. reflexivity. Qed.

Theorem br_build_bl_tree : forall s ts,
  trel s ts -> TM.tree_lens s ->
  scan_ok s DS.TL (DS.ds_l_max_code s) -> DS.ds_l_max_code s < DS.L_CODES ->
  scan_ok s DS.TD (DS.ds_d_max_code s) ->
  GBM.bt_safe (let s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s) in
               DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1)) DS.TB ->
  snd (DT.build_bl_tree s) = fst (RT.build_bl_tree ts)
  /\ trel (fst (DT.build_bl_tree s)) (snd (RT.build_bl_tree ts))
  /\ TM.tree_lens (fst (DT.build_bl_tree s)).
Proof.
  intros s ts HT HL HsL HmcL HsD HS.
  rewrite s5_bbl_eq, rt_bbl_eq. cbv zeta in HS |- *.
  pose proof HT as HT'. unfold trel in HT'. cbv zeta in HT'.
  destruct HT' as (_ & _ & _ & HdD & _ & _ & _ & _ & _ & EL & ED & _).
  (* scan TL *)
  pose proof (br_scan_tree' s ts DS.TL (DS.ds_l_max_code s) HT HL HsL HmcL) as T1.
  cbn [tk_of] in T1. rewrite EL in T1 at 2.
  set (s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s)) in *.
  set (t1 := scan_ts RT.TK_L (RT.ts_maxcode ts RT.TK_L) ts) in *.
  assert (L1 : TM.tree_lens s1) by (apply scan_tree_lens; exact HL).
  pose proof T1 as T1'. unfold trel in T1'. cbv zeta in T1'.
  destruct T1' as (_ & _ & _ & HdD1 & _ & _ & _ & _ & _ & _ & ED1 & _).
  assert (ED1s : DS.ds_d_max_code s1 = DS.ds_d_max_code s).
  { rewrite ED1, ED. subst t1. rewrite scan_ts_maxcode. reflexivity. }
  assert (HsD1 : scan_ok s1 DS.TD (DS.ds_d_max_code s1)).
  { destruct HsD as (Hne & H0 & H1 & H15). rewrite ED1s.
    split; [exact Hne|]. split; [exact H0|]. split; [exact H1|].
    intros i Hi. cbn [TM.tsize] in H1. unfold DS.Len, DS.tree_dl in *.
    rewrite (HdD1 i) by (unfold DS.D_CODES; lia). subst t1.
    rewrite scan_ts_trees by (unfold RT.TK_D, RT.TK_L, RT.TK_BL; lia).
    rewrite <- (HdD i) by (unfold DS.D_CODES; lia). apply H15. exact Hi. }
  (* scan TD *)
  pose proof (br_scan_tree' s1 t1 DS.TD (DS.ds_d_max_code s1) T1 L1 HsD1
                ltac:(destruct HsD1 as (_ & _ & H1 & _); cbn [TM.tsize] in H1; unfold DS.L_CODES; lia)) as T2.
  cbn [tk_of] in T2. rewrite ED1 in T2 at 2.
  set (s2 := DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1)) in *.
  set (t2 := scan_ts RT.TK_D (RT.ts_maxcode t1 RT.TK_D) t1) in *.
  assert (L2 : TM.tree_lens s2) by (apply scan_tree_lens; exact L1).
  (* build_tree TB *)
  pose proof (br_build_tree s2 t2 DS.TB T2 L2 HS) as T3. cbn [tk_of] in T3.
  pose proof (br_build_tree_lens s2 t2 DS.TB T2 L2 HS) as L3.
  set (s3 := DT.build_tree s2 DS.TB) in *.
  set (t3 := RT.build_tree RT.TK_BL t2) in *.
  pose proof T3 as T3'. unfold trel in T3'. cbv zeta in T3'.
  destruct T3' as (_ & _ & _ & _ & _ & HbD3 & _ & _ & _ & _ & _ & _ & _ & _ & EOL3 & _).
  assert (EMB : DT.build_bl_tree_loop 17 s3 (DS.BL_CODES - 1)
                = RT.bbl_scan (Z.to_nat RT.BL_CODES + 1) (RT.ts_trees t3 RT.TK_BL) (RT.BL_CODES - 1)).
  { apply bbl_agree.
    - intros i Hi. unfold DS.Len, DS.tree_dl. apply HbD3. unfold DS.BL_CODES. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. cbn. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. cbn. lia. }
  rewrite EMB. cbn [fst snd].
  split; [reflexivity|]. split.
  - unfold trel in *. cbv zeta in *. autorewrite with s5f_opt_len.
    cbn [RT.set_optlen RT.ts_trees RT.ts_blcount RT.ts_heap RT.ts_depth RT.ts_maxcode RT.ts_heaplen
         RT.ts_heapmax RT.ts_optlen RT.ts_statlen RT.ts_matches].
    destruct T3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
    repeat (split; [assumption|]). split; [|split; assumption].
    rewrite A15, wrap64_mod. reflexivity.
  - unfold TM.tree_lens in *. autorewrite with s5f_opt_len. exact L3.
Qed.

(** The same pair with the distance tree's scan condition read after the
    literal tree's scan (the state S5's [tree_phase] describes). *)
Theorem br_build_bl_tree_x3 : forall s ts,
  trel s ts -> TM.tree_lens s ->
  scan_ok s DS.TL (DS.ds_l_max_code s) -> DS.ds_l_max_code s < DS.L_CODES ->
  (let s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s) in scan_ok s1 DS.TD (DS.ds_d_max_code s1)) ->
  GBM.bt_safe (let s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s) in
               DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1)) DS.TB ->
  snd (DT.build_bl_tree s) = fst (RT.build_bl_tree ts)
  /\ trel (fst (DT.build_bl_tree s)) (snd (RT.build_bl_tree ts))
  /\ TM.tree_lens (fst (DT.build_bl_tree s)).
Proof.
  intros s ts HT HL HsL HmcL HsD1 HS.
  rewrite s5_bbl_eq, rt_bbl_eq. cbv zeta in HS, HsD1 |- *.
  pose proof HT as HT'. unfold trel in HT'. cbv zeta in HT'.
  destruct HT' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & EL & _).
  pose proof (br_scan_tree' s ts DS.TL (DS.ds_l_max_code s) HT HL HsL HmcL) as T1.
  cbn [tk_of] in T1. rewrite EL in T1 at 2.
  set (s1 := DT.scan_tree s DS.TL (DS.ds_l_max_code s)) in *.
  set (t1 := scan_ts RT.TK_L (RT.ts_maxcode ts RT.TK_L) ts) in *.
  assert (L1 : TM.tree_lens s1) by (apply scan_tree_lens; exact HL).
  pose proof T1 as T1'. unfold trel in T1'. cbv zeta in T1'.
  destruct T1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ED1 & _).
  pose proof (br_scan_tree' s1 t1 DS.TD (DS.ds_d_max_code s1) T1 L1 HsD1
                ltac:(destruct HsD1 as (_ & _ & H1 & _); cbn [TM.tsize] in H1; unfold DS.L_CODES; lia)) as T2.
  cbn [tk_of] in T2. rewrite ED1 in T2 at 2.
  set (s2 := DT.scan_tree s1 DS.TD (DS.ds_d_max_code s1)) in *.
  set (t2 := scan_ts RT.TK_D (RT.ts_maxcode t1 RT.TK_D) t1) in *.
  assert (L2 : TM.tree_lens s2) by (apply scan_tree_lens; exact L1).
  pose proof (br_build_tree s2 t2 DS.TB T2 L2 HS) as T3. cbn [tk_of] in T3.
  pose proof (br_build_tree_lens s2 t2 DS.TB T2 L2 HS) as L3.
  set (s3 := DT.build_tree s2 DS.TB) in *.
  set (t3 := RT.build_tree RT.TK_BL t2) in *.
  pose proof T3 as T3'. unfold trel in T3'. cbv zeta in T3'.
  destruct T3' as (_ & _ & _ & _ & _ & HbD3 & _ & _ & _ & _ & _ & _ & _ & _ & EOL3 & _).
  assert (EMB : DT.build_bl_tree_loop 17 s3 (DS.BL_CODES - 1)
                = RT.bbl_scan (Z.to_nat RT.BL_CODES + 1) (RT.ts_trees t3 RT.TK_BL) (RT.BL_CODES - 1)).
  { apply bbl_agree.
    - intros i Hi. unfold DS.Len, DS.tree_dl. apply HbD3. unfold DS.BL_CODES. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. cbn. lia.
    - unfold DS.BL_CODES, RT.BL_CODES. cbn. lia. }
  rewrite EMB. cbn [fst snd].
  split; [reflexivity|]. split.
  - unfold trel in *. cbv zeta in *. autorewrite with s5f_opt_len.
    cbn [RT.set_optlen RT.ts_trees RT.ts_blcount RT.ts_heap RT.ts_depth RT.ts_maxcode RT.ts_heaplen
         RT.ts_heapmax RT.ts_optlen RT.ts_statlen RT.ts_matches].
    destruct T3 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
    repeat (split; [assumption|]). split; [|split; assumption].
    rewrite A15, wrap64_mod. reflexivity.
  - unfold TM.tree_lens in *. autorewrite with s5f_opt_len. exact L3.
Qed.

Print Assumptions br_build_bl_tree.
Print Assumptions br_build_bl_tree_x3.
