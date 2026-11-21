(** * SendGo — B0 and B1: [send_go] IS [emit_items] over an item stream.

    OWNER: huffman-id, claim §HUFFID-SENDGO.

    WHAT THIS FILE BUYS.  §HUFFID-CHAIN proved that emitting a [CLItem] stream
    and decoding it round-trips.  What was missing was that [send_go] — zlib's
    actual code-length emitter — emits such a stream at all.  This file supplies
    the REDUCTION: [send_items] mirrors [send_go]'s recursion line for line, and
    [send_go_emit] proves the two agree as writers.

    WHY THE REDUCTION IS THE PAYOFF STEP.  After [send_go_emit] the remaining
    obligation contains NO [BW] AT ALL: what is left is
    [cl_lens (send_items ...) = the tree's lengths] and
    [CLWf [] (send_items ...)] — statements about lists.  Every bit-writer
    concern has been discharged into [BwStream] and [SendItems] and cannot come
    back.  That is worth more than it looks: it means the hard remaining
    induction is over a run-partition of a list of numbers rather than over a
    state machine that is also mutating a byte queue.

    NOT IN THIS FILE, and deliberately not in it: B2 and B3, the CONTENT of the
    correspondence.  Keeping them out of here is what lets "every delivered file
    is axiom-free" stay a CHECKABLE property of this set rather than a claim about
    which parts of a mixed file you should trust.










 *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec ZBitsOut ZBitsBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes HuffMaxBits ClStream SendItems.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** B0: [send_rep] is a run of literal codes

    [Trees.v:745]: a [do..while] that sends [count] copies of one code.  It runs
    at least once, so the correspondence needs [1 <= count], and it needs fuel
    for [count] trips. *)
Lemma send_rep_emit : forall f c bl count b,
  (Z.to_nat count <= f)%nat -> 1 <= count -> 0 <= c ->
  send_rep f c bl count b
  = emit_items bl (repeat (CLit (Z.to_nat c)) (Z.to_nat count)) b.
Proof.
  induction f as [|f IH]; intros c bl count b Hf Hc Hcc; [lia|].
  cbn [send_rep].
  destruct (Z.eqb (count - 1) 0) eqn:E.
  - (* last copy *)
    apply Z.eqb_eq in E.
    replace (Z.to_nat count) with 1%nat by lia.
    cbn [repeat emit_items emit_item].
    (* [CLit] carries a [nat]; [send_rep] a [Z].  [0 <= c] is what makes the two
       the same code, and it is a real hypothesis: a code LENGTH is nonneg. *)
    rewrite Z2Nat.id by lia. reflexivity.
  - apply Z.eqb_neq in E.
    replace (Z.to_nat count) with (S (Z.to_nat (count - 1))) by lia.
    cbn [repeat emit_items emit_item].
    rewrite Z2Nat.id by lia.
    apply IH; lia.
Qed.

(** ** [send_items]: [send_go]'s control flow, emitting items instead of bits

    Compare against [Trees.v:753-782].  The recursion, the guards, the [count']
    arithmetic and the [maxcnt]/[mincnt] re-arming are copied; only the four
    ACTIONS differ, and each produces exactly the item [emit_item] emits for it.
    [CLit]s come out as a [repeat] in the short-run arm because [send_rep] sends
    that many literal codes. *)
Fixpoint send_items (fuel : nat) (t : Tree)
                    (maxc n prevlen nextlen count maxcnt mincnt : Z)
  : list CLItem :=
  match fuel with
  | O => []
  | S f =>
      if Z.ltb maxc n then []
      else
        let curlen   := nextlen in
        let nextlen' := t_len t (n + 1) in
        let count'   := count + 1 in
        if (Z.ltb count' maxcnt) && (Z.eqb curlen nextlen') then
          send_items f t maxc (n + 1) prevlen nextlen' count' maxcnt mincnt
        else
          let items :=
            if Z.ltb count' mincnt then
              repeat (CLit (Z.to_nat curlen)) (Z.to_nat count')
            else if negb (Z.eqb curlen 0) then
              (if negb (Z.eqb curlen prevlen)
               then [CLit (Z.to_nat curlen);
                     CRep (Z.to_nat curlen) (Z.to_nat (count' - 1))]
               else [CRep (Z.to_nat curlen) (Z.to_nat count')])
            else if Z.leb count' 10 then [CZ3 (Z.to_nat count')]
            else [CZ11 (Z.to_nat count')] in
          let mc := if Z.eqb nextlen' 0 then 138
                    else if Z.eqb curlen nextlen' then 6 else 7 in
          let mn := if Z.eqb nextlen' 0 then 3
                    else if Z.eqb curlen nextlen' then 3 else 4 in
          items ++ send_items f t maxc (n + 1) curlen nextlen' 0 mc mn
  end.

(** [emit_items] over an append is the two emissions in order — the fact that
    lets the per-trip item list be spliced. *)
Lemma emit_items_app : forall bl xs ys b,
  emit_items bl (xs ++ ys) b = emit_items bl ys (emit_items bl xs b).
Proof.
  intros bl xs. induction xs as [|x xs IH]; intros ys b; [reflexivity|].
  cbn [app emit_items]. apply IH.
Qed.

(** ** B1: THE REDUCTION

    [send_go] and [emit_items o send_items] are the same writer.  The hypotheses
    are exactly the ranges [send_rep] needs in the short-run arm: a run is at
    least one long and never exceeds [send_rep]'s 140 trips, which holds because
    [mincnt] is at most 4 in every re-arming (so [mincnt <= 141] is the loosest
    bound that survives the induction).

    The per-trip emission is case-split DIRECTLY on the goal rather than lifted
    into an [assert].  An earlier attempt asserted it and the rewrite failed:
    [send_go]'s body binds the emission with [let p := ... in] and the goal had
    that ZETA-REDUCED, duplicating the [if] under [fst] and [snd], so the
    asserted term was convertible but not syntactically present. *)

(** Closes the re-armed [mincnt <= 141] side goal, whose value is an [if]
    chain over 3 and 4. *)
Ltac if_bound :=
  repeat match goal with |- context[if ?c then _ else _] => destruct c end; lia.

Theorem send_go_emit : forall f t maxc n prevlen nextlen count maxcnt mincnt bl b,
  (forall i, 0 <= t_len t i) ->
  0 <= count -> 0 <= nextlen -> mincnt <= 141 ->
  send_go f t maxc n prevlen nextlen count maxcnt mincnt bl b
  = emit_items bl (send_items f t maxc n prevlen nextlen count maxcnt mincnt) b.
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl b Hnn Hc Hnl Hmn.
  - reflexivity.
  - cbn [send_go send_items].
    destruct (Z.ltb maxc n); [reflexivity|].
    destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1)))).
    + (* still accumulating the run: nothing emitted *)
      apply IH; [assumption | lia | apply Hnn | lia].
    + rewrite emit_items_app.
      destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
      * (* short run: send_rep sends count' literal codes *)
        apply Z.ltb_lt in Emin.
        rewrite (send_rep_emit 140%nat nextlen bl (count + 1) b) by lia.
        apply IH; [assumption | lia | apply Hnn | if_bound].
      * destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
        -- (* nonzero length: symbol 16, optionally preceded by one literal *)
           destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep;
             cbn [fst snd emit_items emit_item]; unfold REP_3_6;
             rewrite !Z2Nat.id by lia;
             apply IH; [assumption | lia | apply Hnn | if_bound
                       |assumption | lia | apply Hnn | if_bound].
        -- (* zero length: symbol 17 or 18 by run length *)
           destruct (Z.leb (count + 1) 10) eqn:Eten;
             cbn [emit_items emit_item];
             [unfold REPZ_3_10 | unfold REPZ_11_138];
             rewrite !Z2Nat.id by lia;
             apply IH; [assumption | lia | apply Hnn | if_bound
                       |assumption | lia | apply Hnn | if_bound].
Qed.

(** ** The vocabulary B2 and B3 are stated in

    The two open obligations themselves live in SendGoOpen.v (statements only).
    Their subjects are defined HERE, because [send_tree_emit] above is already
    about [send_tree_items] and a definition should not live in the file that
    fails to prove things about it.

    [tree_lens t maxc] is the length vector [send_tree] walks: symbols
    [0 .. maxc] of the tree, as [nat]s. *)
Definition tree_lens (t : Tree) (maxc : Z) : list nat :=
  map (fun i => Z.to_nat (t_len t (Z.of_nat i))) (seq 0 (Z.to_nat (maxc + 1))).

(** The item stream [send_tree] starts from ([Trees.v:786-790]). *)
Definition send_tree_items (t : Tree) (maxc : Z) : list CLItem :=
  let nextlen := t_len t 0 in
  let mc := if Z.eqb nextlen 0 then 138 else 7 in
  let mn := if Z.eqb nextlen 0 then 3 else 4 in
  send_items (Z.to_nat L_CODES + 3) t maxc 0 (-1) nextlen 0 mc mn.

(** B1 specialised to [send_tree] — the reduction, at the entry point. *)
Corollary send_tree_emit : forall t maxc bl b,
  (forall i, 0 <= t_len t i) ->
  send_tree t maxc bl b = emit_items bl (send_tree_items t maxc) b.
Proof.
  intros t maxc bl b Hnn. unfold send_tree, send_tree_items.
  destruct (Z.eqb (t_len t 0) 0);
    apply send_go_emit; [exact Hnn | lia | apply Hnn | lia
                        | exact Hnn | lia | apply Hnn | lia].
Qed.

Print Assumptions send_rep_emit.
Print Assumptions send_go_emit.
Print Assumptions send_tree_emit.
