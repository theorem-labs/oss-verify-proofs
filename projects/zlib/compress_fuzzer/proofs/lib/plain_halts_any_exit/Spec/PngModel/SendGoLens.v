(** * SendGoLens — B2: [send_tree_items] denotes the tree's own length vector.

    OWNER: huffman-id, claim §HUFFID-SENDGO.

    This is the CONTENT half of the send_go correspondence, whose statement was
    posted at §HUFFID-SENDGO-B1 and parked in SendGoOpen.v.  [SendGo.v] reduced
    [send_tree] to [emit_items] over [send_tree_items]; what was left was that
    those items denote symbols [0 .. max_code] of the tree.  That is proved here.

    THE INVARIANT, and the one observation that makes it work.  Induct on the
    fuel with

      cl_lens (send_items f t maxc n prevlen nextlen count maxcnt mincnt)
        = lens_n t (n - count) <the number of symbols from n-count to maxc>

    The pending run — the [count] symbols already accumulated plus the one at [n]
    — has NOT been emitted yet, so the item list still owes them.  Writing the
    left endpoint as [n - count] rather than [n] is what makes the ACCUMULATE arm
    trivial: it steps [n] to [n+1] and [count] to [count+1], so
    [(n+1) - (count+1) = n - count] and THE STATEMENT IS LITERALLY UNCHANGED.  A
    formulation that tracked [n] and the pending run separately needs a
    rebalancing step at every accumulate trip; this one needs none.

    WHY THE 0xffff GUARD IS A HYPOTHESIS.  [scan_tree] stores 65535 at
    [tree[max_code+1]] ([Trees.v:733]) and [send_tree] relies on it being
    "already set" ([Trees.v:784-785]).  It does two jobs here.  It forces the
    FINAL run to be emitted, so the loop exits with [count = 0] and nothing is
    left undenoted.  And — the part that is easy to miss — it is what rules out
    the accumulate arm at [n = maxc], which is the only place the induction could
    step past [maxc] with a nonempty pending run.  Without the guard B2 is FALSE,
    not merely unprovable. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes HuffMaxBits ClStream SendItems SendGo.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The length vector, counted from a low index

    Counted rather than ranged: [lens_n t lo k] is [k] lengths starting at [lo].
    A [map] over a [seq] would need a shift lemma at every split; this needs one
    induction. *)
Fixpoint lens_n (t : Tree) (lo : Z) (k : nat) : list nat :=
  match k with
  | O => []
  | S k' => Z.to_nat (t_len t lo) :: lens_n t (lo + 1) k'
  end.

Lemma lens_n_app : forall t a b lo,
  lens_n t lo (a + b) = lens_n t lo a ++ lens_n t (lo + Z.of_nat a) b.
Proof.
  intros t a. induction a as [|a IH]; intros b lo.
  - cbn [lens_n Nat.add app]. rewrite Z.add_0_r. reflexivity.
  - cbn [lens_n Nat.add app]. f_equal.
    rewrite IH. f_equal. f_equal. lia.
Qed.

(** A constant stretch of the tree is a [repeat]. *)
Lemma lens_n_const : forall t k lo x,
  (forall j, lo <= j < lo + Z.of_nat k -> t_len t j = x) ->
  lens_n t lo k = repeat (Z.to_nat x) k.
Proof.
  intros t k. induction k as [|k IH]; intros lo x H; [reflexivity|].
  cbn [lens_n repeat]. rewrite (H lo) by lia. f_equal.
  apply IH. intros j Hj. apply H. lia.
Qed.

Lemma lens_n_0 : forall t lo, lens_n t lo 0%nat = [].
Proof. reflexivity. Qed.

(** [tree_lens] (SendGo.v's [map]-over-[seq] form) is [lens_n] from 0. *)
Lemma lens_n_tree_lens : forall t maxc,
  lens_n t 0 (Z.to_nat (maxc + 1)) = tree_lens t maxc.
Proof.
  intros t maxc. unfold tree_lens.
  set (k := Z.to_nat (maxc + 1)).
  assert (Hgen : forall k0 lo,
            lens_n t (Z.of_nat lo) k0
            = map (fun i => Z.to_nat (t_len t (Z.of_nat i))) (seq lo k0)).
  { intros k0. induction k0 as [|k0 IHk]; intros lo; [reflexivity|].
    cbn [lens_n seq map]. f_equal.
    replace (Z.of_nat lo + 1) with (Z.of_nat (S lo)) by lia.
    apply IHk. }
  apply (Hgen k 0%nat).
Qed.

(** ** [cl_lens] of each arm's item list

    All four arms denote the same thing: [count'] copies of the run's length.
    That is why the run-partition argument does not have to case-split on the
    arm when it computes lengths — only when it checks well-formedness. *)

Lemma cl_lens_repeat_lit : forall c k, cl_lens (repeat (CLit c) k) = repeat c k.
Proof.
  intros c k. induction k as [|k IH]; [reflexivity|].
  cbn [repeat cl_lens cl_item_lens app]. f_equal. exact IH.
Qed.

(** ** THE INDUCTION *)

Lemma send_items_lens : forall f t maxc n prevlen nextlen count maxcnt mincnt,
  (* the guard, and the real code lengths it is distinguishable from *)
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (* loop invariant *)
  0 <= count -> 0 <= n - count -> n <= maxc + 1 ->
  nextlen = t_len t n ->
  (forall j, n - count <= j <= n -> t_len t j = nextlen) ->
  (maxc < n -> count = 0) ->
  (Z.to_nat (maxc + 1 - n) <= f)%nat ->
  cl_lens (send_items f t maxc n prevlen nextlen count maxcnt mincnt)
  = lens_n t (n - count) (Z.to_nat (maxc + 1 - (n - count))).
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt
           Hguard Hlen15 Hc Hnc Hn Hnl Hrun Hexit Hf.
  - (* no fuel: then n is already past maxc, so count = 0 and nothing is owed *)
    assert (Hpast : maxc < n) by lia.
    rewrite (Hexit Hpast).
    replace (Z.to_nat (maxc + 1 - (n - 0))) with 0%nat by lia.
    reflexivity.
  - cbn [send_items].
    destruct (Z.ltb maxc n) eqn:Eexit.
    + (* past the end: same as the no-fuel case *)
      apply Z.ltb_lt in Eexit.
      rewrite (Hexit Eexit).
      replace (Z.to_nat (maxc + 1 - (n - 0))) with 0%nat by lia.
      reflexivity.
    + apply Z.ltb_ge in Eexit.
      destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
               eqn:Eacc.
      * (* ACCUMULATE: the statement is unchanged, because
           (n+1) - (count+1) = n - count *)
        apply andb_prop in Eacc as [Emax Eeq]. apply Z.eqb_eq in Eeq.
        (* n < maxc: at n = maxc the next read is the 0xffff guard, which no real
           length equals, so this arm is unreachable there *)
        assert (Hlt : n < maxc).
        { destruct (Z.eq_dec n maxc) as [->|Hne]; [|lia].
          rewrite Hguard in Eeq.
          assert (0 <= t_len t maxc <= 15) by (apply Hlen15; lia). lia. }
        replace (n - count) with (n + 1 - (count + 1)) by lia.
        (* [try lia] closes more than the arithmetic goals -- it discharges the
           guard equation straight from [Hguard] too -- so the surviving goal
           COUNT is not the one you predict from IH's signature.  Closing with
           [try lia; try assumption] and then handling whatever is left is
           robust; a bullet list here silently lands on the wrong goal. *)
        apply IH; try lia; try assumption.
        (* only the run-extension obligation survives *)
        intros j Hj.
        destruct (Z.eq_dec j (n + 1)) as [->|Hjn]; [reflexivity|].
        rewrite <- Eeq. apply Hrun. lia.
      * (* EMIT: the pending run, count'+... copies of nextlen, then recurse *)
        assert (Hitems :
          cl_lens (if Z.ltb (count + 1) mincnt
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
            + (* zero-length run: [Z.to_nat nextlen] is 0 *)
              apply negb_false_iff, Z.eqb_eq in Ez.
              rewrite Ez. cbn [Z.to_nat].
              destruct (Z.leb (count + 1) 10);
                cbn [cl_lens cl_item_lens]; rewrite app_nil_r; reflexivity. }
        cbn [cl_lens].
        (* [cl_lens] of an append splits *)
        assert (Hsplit : forall xs ys, cl_lens (xs ++ ys) = cl_lens xs ++ cl_lens ys).
        { intros xs. induction xs as [|x xs IHx]; intros ys; [reflexivity|].
          cbn [app cl_lens]. rewrite IHx, app_assoc. reflexivity. }
        rewrite Hsplit, Hitems.
        (* the tail: the recursion owes symbols n+1 .. maxc *)
        rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                    (if Z.eqb (t_len t (n + 1)) 0 then 138
                     else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                    (if Z.eqb (t_len t (n + 1)) 0 then 3
                     else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
          try lia; try assumption.
        -- (* and the two pieces are the two halves of the target range *)
           replace (Z.to_nat (maxc + 1 - (n - count)))
             with (Z.to_nat (count + 1) + Z.to_nat (maxc + 1 - (n + 1 - 0)))%nat
             by lia.
           rewrite lens_n_app. f_equal.
           ++ (* the pending run IS a constant stretch of the tree *)
              symmetry. apply lens_n_const. intros j Hj. apply Hrun. lia.
           ++ f_equal. lia.
        -- intros j Hj. assert (j = n + 1) by lia. subst j. reflexivity.
Qed.

(** ** B2, at the entry point *)

Theorem send_tree_items_lens : forall t maxc,
  0 <= maxc <= 285 ->
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  cl_lens (send_tree_items t maxc) = tree_lens t maxc.
Proof.
  intros t maxc Hmc Hguard Hlen15.
  unfold send_tree_items.
  rewrite <- lens_n_tree_lens.
  replace (Z.to_nat (maxc + 1)) with (Z.to_nat (maxc + 1 - (0 - 0))) by lia.
  destruct (Z.eqb (t_len t 0) 0);
    (apply send_items_lens; try assumption; try lia;
     [ intros j Hj; assert (j = 0) by lia; subst j; reflexivity
     | replace (Z.to_nat L_CODES + 3)%nat with 289%nat by reflexivity; lia ]).
Qed.

Print Assumptions send_items_lens.
Print Assumptions send_tree_items_lens.
