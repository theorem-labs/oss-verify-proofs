(** * Bridge.DEmit.BrSendAll — pair D30 (send half) of PAIRS.md: [send_all_trees], S5 vs RT.

    S5's [FlushBlockModel.send_all_trees_eq] writes the dynamic-tree header
    as [sbs_run] over [sat_calls] (the three counts, then one 3-bit length
    per bit-length code in [bl_order]) followed by the two [send_tree]s;
    RT's [send_all_trees] is the same with [sat_ranks] for the lengths.  The
    proof chains [BrSbs.br_sbs_run] and [BrSendTree.br_send_tree'] twice;
    between them [nbw] (every field the tree relation reads) is unchanged,
    since the bit writer touches only [pending_buf], [pending], [bi_buf],
    [bi_valid].

    As in [BrSendTree], the statement adds [lc <= L_CODES] (RT's [send_go]
    fuel; see [BrScanTree.scan_cex]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel ScanModel SendModel FlushBlockModel
  RefSendTree4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Trees ZBitsOut.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSbs BrSendTree.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrTally.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SCM := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.ScanModel.

(* ------------------------------------------------------------------------- *)
(* 1.  The fields the tree relation reads survive the bit writer             *)
(* ------------------------------------------------------------------------- *)

Definition nbw (s : DS.deflate_state) :=
  (DS.ds_dyn_ltree_fc s, DS.ds_dyn_ltree_dl s, DS.ds_dyn_dtree_fc s, DS.ds_dyn_dtree_dl s,
   DS.ds_bl_tree_fc s, DS.ds_bl_tree_dl s, DS.ds_bl_count s, DS.ds_heap s, DS.ds_depth s,
   (DS.ds_l_max_code s, DS.ds_d_max_code s, DS.ds_bl_max_code s, DS.ds_heap_len s, DS.ds_heap_max s,
    DS.ds_opt_len s, DS.ds_static_len s, DS.ds_matches s)).

Lemma nbw_send_bits : forall s v l, nbw (DT.send_bits s v l) = nbw s.
Proof.
  intros s v l. rewrite SM.send_bits_shape. unfold SM.upd4, nbw.
  autorewrite with s5f_bi_valid s5f_bi_buf s5f_pending s5f_pending_buf. reflexivity.
Qed.

Lemma nbw_sbs : forall cs s, nbw (SM.sbs_run s cs) = nbw s.
Proof.
  induction cs as [|[v l] cs IH]; intros s; [reflexivity|]. cbn [SM.sbs_run]. rewrite IH. apply nbw_send_bits.
Qed.

Lemma nbw_send_loop : forall f s t mc n p q c mx mn, 1 <= mn <= 4 ->
  nbw (DT.send_tree_loop f s t mc n p q c mx mn) = nbw s.
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn Hmn; [reflexivity|].
  rewrite SM.send_loop_S by lia. destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? DS.Len s t (n + 1))); [apply IH; exact Hmn|].
  destruct (DT.tree_counts q (DS.Len s t (n + 1))) as [mx' mn'] eqn:E.
  destruct (SCM.tree_counts_range _ _ _ _ E) as [_ Hmn'].
  rewrite IH by lia. apply nbw_sbs.
Qed.

Lemma nbw_send_tree : forall s t mc, nbw (DT.send_tree s t mc) = nbw s.
Proof.
  intros s t mc. unfold DT.send_tree. cbv zeta. destruct (DS.Len s t 0 =? 0); apply nbw_send_loop; lia.
Qed.

(** Destruct both states down to their fields and identify the viewed ones. *)
Local Ltac nbw_subst :=
  intros s s'; destruct s, s'; intros E; unfold nbw in E; cbn in E; injection E; intros; subst.

Lemma trel_nbw : forall s s', nbw s' = nbw s -> forall ts, trel s ts -> trel s' ts.
Proof. nbw_subst. assumption. Qed.

Lemma tree_lens_nbw : forall s s', nbw s' = nbw s -> TM.tree_lens s -> TM.tree_lens s'.
Proof. nbw_subst. assumption. Qed.

Lemma Len_nbw : forall s s', nbw s' = nbw s -> forall t i, DS.Len s' t i = DS.Len s t i.
Proof.
  intros s s' E t i. destruct s, s'. unfold nbw in E. cbn in E. injection E. intros. subst.
  destruct t; reflexivity.
Qed.

Lemma scan_ok_nbw : forall s s', nbw s' = nbw s -> forall t mc, scan_ok s t mc -> scan_ok s' t mc.
Proof.
  intros s s' E t mc (A & B & C & D). split; [exact A|]. split; [exact B|]. split; [exact C|].
  intros i Hi. rewrite (Len_nbw s s' E). apply D. exact Hi.
Qed.

Lemma bl_lens_ok_nbw : forall s s', nbw s' = nbw s -> bl_lens_ok s -> bl_lens_ok s'.
Proof. intros s s' E H i Hi. rewrite (Len_nbw s s' E). apply H. exact Hi. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The header calls on RT's side                                         *)
(* ------------------------------------------------------------------------- *)

Fixpoint rt_bl_calls (bl : RT.Tree) (r : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (RT.t_len bl (RT.bl_order r), 3) :: rt_bl_calls bl (r + 1) n'
  end.

Lemma sat_ranks_eq : forall n fuel r bc bl b, n = Z.to_nat (bc - r) -> (n < fuel)%nat ->
  RT.sat_ranks fuel r bc bl b = rt_sbs b (rt_bl_calls bl r n).
Proof.
  induction n as [|n IH]; intros fuel r bc bl b Hn Hf; (destruct fuel as [|fuel]; [lia|]); cbn [RT.sat_ranks].
  - replace (bc <=? r) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (bc <=? r) with false by (symmetry; apply Z.leb_gt; lia).
    cbn [rt_bl_calls rt_sbs]. apply IH; lia.
Qed.

Lemma bl_order_range : forall r, 0 <= r < 19 -> 0 <= RT.bl_order r < 19.
Proof.
  intros r Hr. unfold RT.bl_order, Base.zlist.
  assert (Hall : Forall (fun x => 0 <= x < 19) RT.bl_order_l)
    by (unfold RT.bl_order_l; repeat (constructor; [lia|]); constructor).
  rewrite Forall_forall in Hall. apply Hall. apply nth_In. unfold RT.bl_order_l. cbn [length]. lia.
Qed.

Lemma bl_calls_eq : forall s B n r,
  (forall c, 0 <= c < 19 -> DS.Len s DS.TB c = RT.t_len B c) ->
  0 <= r -> r + Z.of_nat n <= 19 ->
  FBM.bl_calls s r n = rt_bl_calls B r n.
Proof.
  intros s B n. induction n as [|n IH]; intros r Hl Hr Hn; [reflexivity|].
  cbn [FBM.bl_calls rt_bl_calls].
  assert (Ho : arr_get DS.bl_order_a r = RT.bl_order r).
  { unfold DS.bl_order_a, RT.bl_order. rewrite BrTally.arr_of_list_zlist by lia. reflexivity. }
  rewrite Ho, Hl by (apply bl_order_range; lia). rewrite (IH (r + 1) Hl) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The pair                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem br_send_all_trees' : forall s b ts lc dc bc,
  bw_rel s b -> trel s ts -> TM.tree_lens s -> DS.ds_pending_out s = 0 ->
  lc = DS.ds_l_max_code s + 1 -> dc = DS.ds_d_max_code s + 1 -> 0 <= bc <= 19 -> lc <= DS.L_CODES ->
  scan_ok s DS.TL (lc - 1) -> scan_ok s DS.TD (dc - 1) -> bl_lens_ok s ->
  SM.sbs_ok (arr_len (DS.ds_pending_buf s)) s (FBM.sat_calls s lc dc bc) ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s)) (SM.sbs_run s (FBM.sat_calls s lc dc bc)) DS.TL (lc - 1) ->
  ST4.send_tree_safe (arr_len (DS.ds_pending_buf s))
    (DT.send_tree (SM.sbs_run s (FBM.sat_calls s lc dc bc)) DS.TL (lc - 1)) DS.TD (dc - 1) ->
  bw_rel (DT.send_all_trees s lc dc bc) (RT.send_all_trees lc dc bc (RT.set_bw b ts))
  /\ DS.ds_pending_out (DT.send_all_trees s lc dc bc) = 0
  /\ arr_len (DS.ds_pending_buf (DT.send_all_trees s lc dc bc)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s b ts lc dc bc Hb H Hl Hpo Hlc Hdc Hbc HlcL HsL HsD Hbll Hsb HstL HstD.
  pose proof H as (_ & _ & _ & _ & _ & T6 & _).
  assert (HlB : forall c, 0 <= c < 19 -> DS.Len s DS.TB c = RT.t_len (RT.ts_trees ts RT.TK_BL) c).
  { intros c Hc. unfold DS.Len, RT.t_len. cbn [DS.tree_dl]. apply T6. unfold DS.BL_CODES. lia. }
  set (cs := FBM.sat_calls s lc dc bc) in *.
  assert (Ecs : cs = [(lc - 257, 5); (dc - 1, 5); (bc - 4, 4)] ++ rt_bl_calls (RT.ts_trees ts RT.TK_BL) 0 (Z.to_nat bc)).
  { subst cs. unfold FBM.sat_calls. rewrite (bl_calls_eq s (RT.ts_trees ts RT.TK_BL)) by (try assumption; lia).
    reflexivity. }
  rewrite FBM.send_all_trees_eq by lia. fold cs.
  destruct (br_sbs_run cs s b Hb Hpo Hsb) as (R1 & R2 & R3).
  set (s1 := SM.sbs_run s cs) in *.
  assert (E1 : nbw s1 = nbw s) by apply nbw_sbs.
  destruct (br_send_tree' s1 (rt_sbs b cs) ts DS.TL (lc - 1) R1 (trel_nbw s s1 E1 ts H)
              (tree_lens_nbw s s1 E1 Hl) (scan_ok_nbw s s1 E1 _ _ HsL) ltac:(unfold DS.L_CODES in *; lia)
              (bl_lens_ok_nbw s s1 E1 Hbll) R2 ltac:(rewrite R3; exact HstL)) as (Q1 & Q2 & Q3).
  set (s2 := DT.send_tree s1 DS.TL (lc - 1)) in *.
  assert (E2 : nbw s2 = nbw s) by (subst s2; rewrite nbw_send_tree; exact E1).
  assert (HsD' : scan_ok s DS.TD (dc - 1)) by exact HsD.
  destruct (br_send_tree' s2 _ ts DS.TD (dc - 1) Q1 (trel_nbw s s2 E2 ts H)
              (tree_lens_nbw s s2 E2 Hl) (scan_ok_nbw s s2 E2 _ _ HsD)
              ltac:(destruct HsD' as (_ & _ & HD & _); cbn [TM.tsize] in HD; unfold DS.L_CODES; lia)
              (bl_lens_ok_nbw s s2 E2 Hbll) Q2 ltac:(rewrite Q3, R3; exact HstD)) as (P1 & P2 & P3).
  split; [|split; [exact P2 | rewrite P3, Q3, R3; reflexivity]].
  assert (ERT : RT.send_all_trees lc dc bc (RT.set_bw b ts)
                = RT.send_tree (RT.ts_trees ts RT.TK_D) (dc - 1) (RT.ts_trees ts RT.TK_BL)
                    (RT.send_tree (RT.ts_trees ts RT.TK_L) (lc - 1) (RT.ts_trees ts RT.TK_BL) (rt_sbs b cs))).
  { rewrite Ecs, rt_sbs_app. unfold RT.send_all_trees. cbv zeta.
    rewrite (sat_ranks_eq (Z.to_nat bc) _ 0 bc) by (unfold RT.BL_CODES; lia). reflexivity. }
  rewrite ERT. exact P1.
Qed.

Print Assumptions br_send_all_trees'.
