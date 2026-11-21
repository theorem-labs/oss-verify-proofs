(** * BtClPack — the code-length vector for [send_all_trees], packaged in
      LdDynV's own binder shapes.

    OWNER: an earlier development run.  LdDynV items 1-3 quantify a 19-slot vector [cl]; the
    natural witness is the BL tree's own length vector padded to the full
    alphabet, [tree_lens blt 18].  Everything below [maxcode] comes from
    BtItem6b's exports; everything above is dead (freq zero beyond maxcode,
    so length zero), and zero-padding changes neither [bl_count] (positive
    levels) nor the Kraft sum. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes SendGo Kraft15 KraftTree.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus2 BtCensus4 BtCensus5 BtPass1 BtItem6b BtBlSide BuildTree.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Zero-padding a length vector *)

Lemma tree_lens_app : forall t m1 m2,
  -1 <= m1 <= m2 ->
  SendGo.tree_lens t m2
  = SendGo.tree_lens t m1
    ++ map (fun i => Z.to_nat (t_len t (Z.of_nat i)))
           (seq (Z.to_nat (m1 + 1)) (Z.to_nat (m2 + 1) - Z.to_nat (m1 + 1))).
Proof.
  intros t m1 m2 Hm. unfold SendGo.tree_lens.
  rewrite <- map_app. f_equal.
  replace (Z.to_nat (m2 + 1))
    with (Z.to_nat (m1 + 1) + (Z.to_nat (m2 + 1) - Z.to_nat (m1 + 1)))%nat
    at 1 by lia.
  apply seq_app.
Qed.

Lemma padded_zeros : forall t m1 m2 x,
  -1 <= m1 <= m2 ->
  (forall i, m1 < i <= m2 -> t_len t i = 0) ->
  In x (map (fun i => Z.to_nat (t_len t (Z.of_nat i)))
            (seq (Z.to_nat (m1 + 1)) (Z.to_nat (m2 + 1) - Z.to_nat (m1 + 1)))) ->
  x = 0%nat.
Proof.
  intros t m1 m2 x Hm Hz Hin.
  apply in_map_iff in Hin as [i [He Hi]].
  apply in_seq in Hi.
  rewrite (Hz (Z.of_nat i)) in He by lia.
  subst x. reflexivity.
Qed.

Lemma bl_count_app_zeros : forall (L Z0 : list nat) b,
  (1 <= b)%nat ->
  (forall x, In x Z0 -> x = 0%nat) ->
  bl_count (L ++ Z0) b = bl_count L b.
Proof.
  intros L Z0 b Hb Hz.
  destruct b as [|b']; [lia|].
  cbn [bl_count]. unfold count_len.
  rewrite count_occ_app.
  assert (Hc0 : count_occ Nat.eq_dec Z0 (S b') = 0%nat).
  { apply count_occ_not_In. intro Hin.
    pose proof (Hz _ Hin). lia. }
  lia.
Qed.

Lemma kraft_sum_app_zeros : forall (L Z0 : list nat) mb,
  (forall x, In x Z0 -> x = 0%nat) ->
  kraft_sum (L ++ Z0) mb = kraft_sum L mb.
Proof.
  intros L Z0 mb Hz.
  unfold kraft_sum, kraft_sum_from.
  rewrite map_app, list_sum_app_nat.
  assert (Hc0 : list_sum (map (kraft_at mb 0) Z0) = 0%nat); [|lia].
  induction Z0 as [|a Z0 IH].
  - reflexivity.
  - cbn [map]. rewrite list_sum_cons.
    rewrite (Hz a (or_introl eq_refl)).
    rewrite IH by (intros x Hx; apply Hz; right; exact Hx).
    reflexivity.
Qed.

Lemma valid_lengths_pad : forall (L Z0 : list nat) mb,
  (forall x, In x Z0 -> x = 0%nat) ->
  ValidLengths L mb ->
  ValidLengths (L ++ Z0) mb.
Proof.
  intros L Z0 mb Hz [Hr Hs].
  split.
  - intros len Hin. apply in_app_or in Hin as [Hin|Hin].
    + apply Hr. exact Hin.
    + rewrite (Hz _ Hin). lia.
  - rewrite (kraft_sum_app_zeros L Z0 mb Hz). exact Hs.
Qed.

(** ** [bl_order] stays inside the alphabet *)

Lemma bl_order_range : forall r, 0 <= r <= 18 -> 0 <= bl_order r <= 18.
Proof.
  intros r Hr.
  assert (Hb : forallb (fun n => (0 <=? bl_order (Z.of_nat n))
                                 && (bl_order (Z.of_nat n) <=? 18))
                       (seq 0 19) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hb.
  specialize (Hb (Z.to_nat r)).
  rewrite Z2Nat.id in Hb by lia.
  destruct (andb_prop _ _ (Hb ltac:(apply in_seq; lia))) as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.



(** ** Reading one slot of a length vector *)

Lemma tree_lens_nth : forall t m (j : nat),
  (j < Z.to_nat (m + 1))%nat ->
  nth j (SendGo.tree_lens t m) 0%nat = Z.to_nat (t_len t (Z.of_nat j)).
Proof.
  intros t m j Hj. unfold SendGo.tree_lens.
  rewrite (nth_indep _ 0%nat (Z.to_nat (t_len t (Z.of_nat 0))))
    by (rewrite length_map, length_seq; exact Hj).
  change (Z.to_nat (t_len t (Z.of_nat 0)))
    with ((fun i => Z.to_nat (t_len t (Z.of_nat i))) 0%nat).
  rewrite map_nth.
  rewrite seq_nth by exact Hj.
  reflexivity.
Qed.

Lemma tree_lens_length : forall t m,
  length (SendGo.tree_lens t m) = Z.to_nat (m + 1).
Proof.
  intros. unfold SendGo.tree_lens.
  rewrite length_map, length_seq. reflexivity.
Qed.

(** ** LdDynV items 1-3 shapes at the built BL tree *)

Theorem bl_cl_pack :
  forall s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees s TK_BL)
          (ts_heap s) (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems TK_BL |} = Some stf ->
  ts_maxcode (build_tree TK_BL s) TK_BL = maxc1
  /\ -1 <= maxc1 <= 18
  /\ length (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL) 18) = 19%nat
  /\ LensOf (ts_trees (build_tree TK_BL s) TK_BL)
       (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL) 18)
  /\ BlcOf (ts_blcount (build_tree TK_BL s))
       (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL) 18)
  /\ ValidLengths (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL) 18)
       7%nat
  /\ AbsentBeyond (SendGo.tree_lens (ts_trees (build_tree TK_BL s) TK_BL) 18)
       maxc1
  /\ (forall r, 0 <= r <= 18 ->
      0 <= t_len (ts_trees (build_tree TK_BL s) TK_BL) (bl_order r) < 8).
Proof.
  intros s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hbl0 E0 E2 Eloop.
  assert (Hel : sd_elems TK_BL = 19) by reflexivity.
  assert (Hml : sd_max_length TK_BL = 7) by reflexivity.
  (* the heap length is bounded by the SMALL alphabet, via the census *)
  destruct (build_tree_parked TK_BL s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(rewrite Hel; unfold L_CODES; lia)
              E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz [Hcen Hfr0]]]].
  assert (Hmax : -1 <= maxc1 < 19)
    by (pose proof (io_maxc _ _ _ _ _ Hout1) as H; rewrite Hel in H; lia).
  assert (Hh19 : hlen1 <= 19).
  { pose proof (io_total _ _ _ _ _ Hout1) as Ht.
    unfold live_total in Ht.
    pose proof (wsum_ind_ub (fun s' => live_b t1 maxc1 s') 0
                  (Z.to_nat (sd_elems TK_BL))) as HB.
    cbn beta in HB.
    rewrite Hel in Ht, HB.
    change (Z.of_nat (Z.to_nat 19)) with 19 in HB. lia. }
  destruct (build_tree_out TK_BL s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
              ltac:(rewrite Hel; unfold L_CODES; lia)
              ltac:(rewrite Hml; lia)
              ltac:(rewrite Hml; replace (2 ^ 7) with 128 by reflexivity; lia)
              Hbl0 E0 E2 Eloop)
    as [Gmc [Gvl [Gblc [Gzk [Gdead [Ggap Grng]]]]]].
  rewrite Hel in Gdead, Ggap, Grng.
  rewrite Hml in Gvl, Grng.
  set (bt := ts_trees (build_tree TK_BL s) TK_BL) in *.
  (* everything above maxcode is dead and reads zero *)
  assert (Hdz : forall i, maxc1 < i <= 18 -> t_len bt i = 0).
  { intros i Hi. apply Gdead; [lia|]. apply Ggap. lia. }
  assert (Hpadz : forall x,
    In x (map (fun i => Z.to_nat (t_len bt (Z.of_nat i)))
              (seq (Z.to_nat (maxc1 + 1))
                   (Z.to_nat (18 + 1) - Z.to_nat (maxc1 + 1)))) ->
    x = 0%nat).
  { intros x Hin.
    apply (padded_zeros bt maxc1 18 x); [lia | | exact Hin].
    intros i Hi. apply Hdz. lia. }
  assert (Happ := tree_lens_app bt maxc1 18 ltac:(lia)).
  split; [exact Gmc|].
  split; [lia|].
  split; [rewrite tree_lens_length; reflexivity|].
  split; [|split; [|split; [|split]]].
  - (* LensOf *)
    intros j Hj.
    rewrite tree_lens_length in Hj.
    rewrite (tree_lens_nth bt 18 j Hj).
    rewrite Z2Nat.id; [reflexivity|].
    assert (0 <= Z.of_nat j < 19)
      by (cbn [Z.to_nat] in Hj; lia).
    pose proof (Grng (Z.of_nat j) ltac:(lia)). lia.
  - (* BlcOf *)
    intros b Hb.
    rewrite Happ.
    destruct (Z.eq_dec b 0) as [->|Hb0].
    + replace (Z.to_nat 0) with O by reflexivity.
      cbn [bl_count].
      pose proof (Gblc 0 ltac:(unfold MAX_BITS; lia)) as G0.
      replace (Z.to_nat 0) with O in G0 by reflexivity.
      cbn [bl_count] in G0. exact G0.
    + rewrite bl_count_app_zeros; [| lia | exact Hpadz].
      apply Gblc. exact Hb.
  - (* ValidLengths at 7 *)
    rewrite Happ.
    apply valid_lengths_pad; [exact Hpadz|].
    exact Gvl.
  - (* AbsentBeyond *)
    intros j Hj.
    destruct (Nat.lt_ge_cases j 19) as [Hj19|Hj19].
    + rewrite (tree_lens_nth bt 18 j)
        by (cbn [Z.to_nat]; lia).
      rewrite (Hdz (Z.of_nat j)) by lia.
      reflexivity.
    + rewrite nth_overflow; [reflexivity|].
      rewrite tree_lens_length. cbn [Z.to_nat]. lia.
  - (* three-bit fit *)
    intros r Hr.
    pose proof (bl_order_range r Hr).
    pose proof (Grng (bl_order r) ltac:(lia)).
    lia.
Qed.

Print Assumptions tree_lens_app.
Print Assumptions valid_lengths_pad.
Print Assumptions bl_order_range.
Print Assumptions bl_cl_pack.
