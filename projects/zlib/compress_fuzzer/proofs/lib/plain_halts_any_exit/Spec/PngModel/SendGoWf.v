(** * SendGoWf — B3: the item stream [send_tree] emits is well formed.

    OWNER: huffman-id, claim §HUFFID-SENDGO.

    The last link.  [SendGo.v] reduced [send_tree] to [emit_items] over
    [send_tree_items]; [SendGoLens.v] proved those items denote the tree's own
    length vector; [ClStream.v]'s round-trip additionally needs [CLWf], which is
    what says the repeat counts are in RFC 1951 range and that every symbol-16
    item's "previous length" really is the last length emitted.  That is proved
    here.

    THE INVARIANT.  On top of [SendGoLens]' index/run invariant, three more
    conjuncts, and each earns its place:

      acc = lens_n t 0 (n - count)
          the accumulator IS the lengths already emitted — needed because
          [CLWf]'s symbol-16 clause is stated against [last_len acc].

      acc = [] /\ prevlen = -1   \/   last_len acc = Some prevlen
          [prevlen] tracks the last EMITTED length.  The left disjunct is the
          initial state only, and it is what makes the [curlen = prevlen] arm
          unreachable at the start (a real length is nonneg and so never -1).

      (nextlen = 0 /\ maxcnt = 138 /\ mincnt = 3)
       \/ (nextlen <> 0 /\ nextlen =  prevlen /\ maxcnt = 6 /\ mincnt = 3)
       \/ (nextlen <> 0 /\ nextlen <> prevlen /\ maxcnt = 7 /\ mincnt = 4)
          THE ARMING TRICHOTOMY, and it is the whole content of B3.  zlib
          re-arms [maxcnt]/[mincnt] at every emit from the NEXT run's length and
          whether it equals the run just emitted; those three pairs are the only
          reachable ones, and together with [count + 1 <= maxcnt] they are
          exactly what forces the RFC ranges:
            (138,3) zeros    -> count' in [3,10] gives CZ3, [11,138] gives CZ11
            (6,3)   repeat   -> count' in [3,6],  so CRep count'   is in 3..6
            (7,4)   new len  -> count' in [4,7],  so CRep (count'-1) is in 3..6
          The 138 is reachable exactly because it IS maxcnt, and the two CRep
          bounds land inside 3..6 from opposite directions.  I checked this
          arithmetic by hand before stating B3 (§HUFFID-SENDGO) precisely so
          that this proof would not be chasing a false range claim. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** [CLWf] and [repeat] plumbing *)

Lemma repeat_snoc : forall (c : nat) k, repeat c (S k) = repeat c k ++ [c].
Proof.
  intros c k. induction k as [|k IH].
  - reflexivity.
  - cbn [repeat app]. f_equal. exact IH.
Qed.

Lemma last_len_repeat : forall k (c : nat) acc,
  (1 <= k)%nat -> last_len (acc ++ repeat c k) = Some c.
Proof.
  intros k c acc Hk.
  replace k with (S (k - 1))%nat by lia.
  rewrite repeat_snoc, app_assoc, last_len_snoc. reflexivity.
Qed.

(* RENAMED 2026-08-18 from [cl_lens_app] after ld-seams hit the collision:
   ClStream.v:145 declares a DIFFERENT lemma under that name (the length of a
   CONS, not the append law), so a consumer importing both silently gets the
   later one and the symptom is "Found no subterm matching" against a hypothesis
   that is perfectly correct.  This form has the better claim to the plain name,
   but ld-seams had already qualified their citation to ClStream.cl_lens_app, so
   renaming THIS one keeps a working consumer working.  Nothing cited this name. *)
Lemma cl_lens_app_dist : forall xs ys, cl_lens (xs ++ ys) = cl_lens xs ++ cl_lens ys.
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys; [reflexivity|].
  cbn [app cl_lens]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma CLWf_app : forall xs ys acc,
  CLWf acc xs -> CLWf (acc ++ cl_lens xs) ys -> CLWf acc (xs ++ ys).
Proof.
  intros xs. induction xs as [|x xs IH]; intros ys acc H1 H2.
  - cbn [app]. cbn [cl_lens] in H2. rewrite app_nil_r in H2. exact H2.
  - cbn [cl_lens] in H2. rewrite app_assoc in H2.
    destruct x as [l|p k|k|k]; cbn [app CLWf cl_item_lens] in H1 |- *.
    + destruct H1 as [Ha Hb]. split; [exact Ha|]. apply IH; assumption.
    + destruct H1 as [Ha [Hb Hc]]. split; [exact Ha|]. split; [exact Hb|].
      apply IH; assumption.
    + destruct H1 as [Ha Hb]. split; [exact Ha|]. apply IH; assumption.
    + destruct H1 as [Ha Hb]. split; [exact Ha|]. apply IH; assumption.
Qed.

Lemma CLWf_repeat_lit : forall k (c : nat) acc,
  (c <= 15)%nat -> CLWf acc (repeat (CLit c) k).
Proof.
  intros k c acc Hc. revert acc.
  induction k as [|k IH]; intros acc; [exact I|].
  cbn [repeat CLWf]. split; [exact Hc|]. apply IH.
Qed.

(** ** THE INDUCTION *)

Lemma send_items_wf : forall f t maxc n prevlen nextlen count maxcnt mincnt acc,
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  0 <= count -> 0 <= n - count -> n <= maxc + 1 ->
  nextlen = t_len t n ->
  (forall j, n - count <= j <= n -> t_len t j = nextlen) ->
  (maxc < n -> count = 0) ->
  (Z.to_nat (maxc + 1 - n) <= f)%nat ->
  acc = lens_n t 0 (Z.to_nat (n - count)) ->
  ((acc = [] /\ prevlen = -1) \/ last_len acc = Some (Z.to_nat prevlen)) ->
  ((nextlen = 0 /\ maxcnt = 138 /\ mincnt = 3)
   \/ (nextlen <> 0 /\ nextlen = prevlen /\ maxcnt = 6 /\ mincnt = 3)
   \/ (nextlen <> 0 /\ nextlen <> prevlen /\ maxcnt = 7 /\ mincnt = 4)) ->
  count + 1 <= maxcnt ->
  CLWf acc (send_items f t maxc n prevlen nextlen count maxcnt mincnt).
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt acc
           Hguard Hlen15 Hc Hnc Hn Hnl Hrun Hexit Hf Hacc Hprev Harm Hcm.
  - exact I.
  - cbn [send_items].
    destruct (Z.ltb maxc n) eqn:Eexit; [exact I|].
    apply Z.ltb_ge in Eexit.
    (* the current length is a real one *)
    assert (Hn0 : 0 <= n) by lia.
    assert (H15 : 0 <= t_len t n <= 15) by (apply Hlen15; lia).
    destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
             eqn:Eacc.
    + (* ACCUMULATE: nothing emitted, so [acc] and [prevlen] are unchanged *)
      apply andb_prop in Eacc as [Emax Eeq]. apply Z.eqb_eq in Eeq.
      apply Z.ltb_lt in Emax.
      assert (Hlt : n < maxc).
      { destruct (Z.eq_dec n maxc) as [->|Hne]; [|lia].
        rewrite Hguard in Eeq. lia. }
      (* EVERY hypothesis discharged explicitly, in order.  A [try lia; try
         assumption] prefix here closes an unpredictable subset and the bullet
         list then lands on the wrong goal -- the sixth instance of that failure
         in this lane today. *)
      apply IH.
      * exact Hguard.
      * exact Hlen15.
      * lia.
      * lia.
      * lia.
      * reflexivity.
      * (* the run extends by one, at the same length *)
        intros j Hj.
        destruct (Z.eq_dec j (n + 1)) as [->|Hjn]; [reflexivity|].
        rewrite <- Eeq. apply Hrun. lia.
      * lia.
      * lia.
      * (* acc is unchanged because (n+1)-(count+1) = n-count *)
        rewrite Hacc. f_equal. lia.
      * exact Hprev.
      * (* the arming survives: the guard says nextlen is unchanged *)
        rewrite <- Eeq. exact Harm.
      * lia.
    + (* EMIT.  Establish the item list's well-formedness arm by arm, then the
         recursion at the stepped accumulator. *)
      assert (Hcur15 : (Z.to_nat nextlen <= 15)%nat) by lia.
      assert (Hcnt1 : 1 <= count + 1) by lia.
      (* the emitted lengths, in every arm *)
      assert (Hitems : cl_lens
          (if Z.ltb (count + 1) mincnt
           then repeat (CLit (Z.to_nat nextlen)) (Z.to_nat (count + 1))
           else if negb (Z.eqb nextlen 0)
                then (if negb (Z.eqb nextlen prevlen)
                      then [CLit (Z.to_nat nextlen);
                            CRep (Z.to_nat nextlen) (Z.to_nat (count + 1 - 1))]
                      else [CRep (Z.to_nat nextlen) (Z.to_nat (count + 1))])
                else if Z.leb (count + 1) 10
                     then [CZ3 (Z.to_nat (count + 1))]
                     else [CZ11 (Z.to_nat (count + 1))])
        = repeat (Z.to_nat nextlen) (Z.to_nat (count + 1))).
      { destruct (Z.ltb (count + 1) mincnt).
        - apply cl_lens_repeat_lit.
        - destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
          + destruct (negb (Z.eqb nextlen prevlen)).
            * cbn [cl_lens cl_item_lens app].
              replace (Z.to_nat (count + 1)) with (S (Z.to_nat (count + 1 - 1)))
                by lia.
              cbn [repeat]. rewrite app_nil_r. reflexivity.
            * cbn [cl_lens cl_item_lens]. rewrite app_nil_r. reflexivity.
          + apply negb_false_iff, Z.eqb_eq in Ez. rewrite Ez. cbn [Z.to_nat].
            destruct (Z.leb (count + 1) 10);
              cbn [cl_lens cl_item_lens]; rewrite app_nil_r; reflexivity. }
      apply CLWf_app.
      * (* the item list itself *)
        destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
        -- apply CLWf_repeat_lit. exact Hcur15.
        -- apply Z.ltb_ge in Emin.
           destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
           ++ apply negb_true_iff, Z.eqb_neq in Ez.
              (* nonzero run: the arming is case B or C *)
              destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep.
              ** apply negb_true_iff, Z.eqb_neq in Ep.
                 (* case C: (7,4), so count' in [4,7] and count'-1 in [3,6] *)
                 assert (Hc74 : maxcnt = 7 /\ mincnt = 4)
                   by (destruct Harm as [[? ?]|[[? [? ?]]|[? [? [? ?]]]]]; lia).
                 cbn [CLWf cl_item_lens].
                 split; [exact Hcur15|]. split; [lia|]. split.
                 --- rewrite last_len_snoc. reflexivity.
                 --- exact I.
              ** apply negb_false_iff, Z.eqb_eq in Ep.
                 (* case B: (6,3), so count' in [3,6] *)
                 assert (Hc63 : maxcnt = 6 /\ mincnt = 3)
                   by (destruct Harm as [[? ?]|[[? [? ?]]|[? [? [? ?]]]]]; lia).
                 cbn [CLWf].
                 split; [lia|]. split; [|exact I].
                 (* last_len acc = Some prevlen, and prevlen = nextlen here *)
                 destruct Hprev as [[Hnil Hm1]|Hll]; [exfalso; lia|].
                 rewrite Hll, Ep. reflexivity.
           ++ apply negb_false_iff, Z.eqb_eq in Ez.
              (* zeros: the arming is case A, (138,3) *)
              assert (Hc138 : maxcnt = 138 /\ mincnt = 3)
                by (destruct Harm as [[? [? ?]]|[[? ?]|[? ?]]]; lia).
              destruct (Z.leb (count + 1) 10) eqn:Eten.
              ** apply Z.leb_le in Eten. cbn [CLWf]. split; [lia|exact I].
              ** apply Z.leb_gt in Eten. cbn [CLWf]. split; [lia|exact I].
      * (* the recursion, at the stepped accumulator *)
        rewrite Hitems.
        assert (Haccnew : acc ++ repeat (Z.to_nat nextlen) (Z.to_nat (count + 1))
                          = lens_n t 0 (Z.to_nat (n + 1 - 0))).
        { rewrite Hacc.
          replace (Z.to_nat (n + 1 - 0))
            with (Z.to_nat (n - count) + Z.to_nat (count + 1))%nat by lia.
          rewrite lens_n_app. f_equal.
          symmetry.
          replace (0 + Z.of_nat (Z.to_nat (n - count))) with (n - count) by lia.
          apply lens_n_const. intros j Hj. apply Hrun. lia. }
        apply IH.
        -- exact Hguard.
        -- exact Hlen15.
        -- lia.
        -- lia.
        -- lia.
        -- reflexivity.
        -- intros j Hj. assert (j = n + 1) by lia. subst j. reflexivity.
        -- lia.
        -- lia.
        -- exact Haccnew.
        -- (* prevlen becomes the run's length, and acc now ends with it.  The
              goal is already in append form -- no need to fold it back through
              Haccnew, which is what obligation 10 above is for. *)
           right. apply last_len_repeat. lia.
        -- (* the new arming, by its own definition *)
           destruct (Z.eqb (t_len t (n + 1)) 0) eqn:E0.
           ++ apply Z.eqb_eq in E0. left. split; [exact E0 | split; reflexivity].
           ++ apply Z.eqb_neq in E0.
              destruct (Z.eqb nextlen (t_len t (n + 1))) eqn:Eq2.
              ** apply Z.eqb_eq in Eq2. right; left.
                 split; [exact E0|]. split; [symmetry; exact Eq2|].
                 split; reflexivity.
              ** apply Z.eqb_neq in Eq2. right; right.
                 split; [exact E0|]. split; [intro Hx; apply Eq2; symmetry; exact Hx|].
                 split; reflexivity.
        -- (* 1 <= the new maxcnt *)
           destruct (Z.eqb (t_len t (n + 1)) 0); [lia|].
           destruct (Z.eqb nextlen (t_len t (n + 1))); lia.
Qed.

(** ** B3, at the entry point *)

Theorem send_tree_items_wf : forall t maxc,
  0 <= maxc <= 285 ->
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  CLWf [] (send_tree_items t maxc).
Proof.
  intros t maxc Hmc Hguard Hlen15.
  assert (H0 : 0 <= t_len t 0 <= 15) by (apply Hlen15; lia).
  assert (Hfuel : (Z.to_nat L_CODES + 3 = 289)%nat) by reflexivity.
  unfold send_tree_items.
  (* explicit bullets again: [try lia; try assumption] closed a different
     number of these than the signature predicts *)
  destruct (Z.eqb (t_len t 0) 0) eqn:E0.
  - apply Z.eqb_eq in E0.
    apply (send_items_wf _ t maxc 0 (-1) (t_len t 0) 0 138 3 []).
    + exact Hguard.
    + exact Hlen15.
    + lia.
    + lia.
    + lia.
    + reflexivity.
    + intros j Hj. assert (j = 0) by lia. subst j. reflexivity.
    + lia.
    + lia.
    + reflexivity.
    + left. split; reflexivity.
    + left. split; [exact E0 | split; reflexivity].
    + lia.
  - apply Z.eqb_neq in E0.
    apply (send_items_wf _ t maxc 0 (-1) (t_len t 0) 0 7 4 []).
    + exact Hguard.
    + exact Hlen15.
    + lia.
    + lia.
    + lia.
    + reflexivity.
    + intros j Hj. assert (j = 0) by lia. subst j. reflexivity.
    + lia.
    + lia.
    + reflexivity.
    + left. split; reflexivity.
    + (* a real length is nonneg, so it is never the initial prevlen of -1 *)
      right; right. split; [exact E0|]. split; [lia|]. split; reflexivity.
    + lia.
Qed.

Print Assumptions send_items_wf.
Print Assumptions send_tree_items_wf.
