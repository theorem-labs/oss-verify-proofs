(** * KraftReach -- non-vacuity of item 6 at a TREE, not merely at a vector.

    OWNER: kraftsum.

    THE GAP THIS CLOSES, named by zlib-lead and it is a real one.  Every control
    in [Kraft15.v] is a control on a length VECTOR I chose -- a 286-entry skewed
    profile, a slack-1 instance at [maxBits = 3], an over-full negative.  Those
    show the predicate is satisfiable and discriminating.  **What they cannot show
    is that the premise class is non-empty at a tree something actually builds.**
    A statement can be non-vacuous at a hand-picked vector and vacuous at every
    reachable one, and this campaign has already lost a night to a premise that was
    unsatisfiable because an upstream guard returned an error before the state
    could be reached.

    SO THIS FILE INSTANTIATES ITEM 6'S CONCLUSION AT A REAL TREE.  [twt] is
    huffman-id's round-trip witness ([SendTreeRT.v:86]) --
    [mkTree zzero (zlist [3;3;3;3;3;0;0;0;0;0;2;65535])] -- and
    [SendTreeRT.twt_lens] is their Qed that [tree_lens twt 10] is
    [[3;3;3;3;3;0;0;0;0;0;2]].  That vector has a PRODUCER: it is what
    [send_tree_items] consumes in a test the emitter's round trip already passes,
    not a list chosen to satisfy [ValidLengths].

    Note the sentinel, which ld-seams pointed out and which this witness exhibits:
    [twt]'s index 11 holds 65535, and 11 is [maxc + 1] for [maxc = 10].  So the
    0xffff guard sits exactly OUTSIDE [tree_lens]'s window by construction, and
    [tree_lens twt 10] does not contain it -- the sentinel is adjacent to item 6's
    range on purpose rather than a counterexample to it.

    WHAT IS STILL NOT CLAIMED, and it is the honest limit of this file.  [twt] is a
    hand-written witness tree, NOT [build_tree]'s output.  So this establishes
    "the premise class is non-empty at a tree the emitter's own tests use", which
    is strictly stronger than a vector control and strictly weaker than "at a tree
    [build_tree] emits".  The stronger claim needs [build_tree] run on a concrete
    state; that probe is separate and its result is not assumed here. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Kraft15 KraftLens.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Item 6 holds at [twt], through the [nc] route

    Routed through [valid_lengths_of_nc] rather than through [valid_lengths_b] so
    the instance exercises the two-term interface ld-seams asked to consume, not
    just [Huff.v]'s decision procedure. *)
Theorem twt_item6 : ValidLengths (SendGo.tree_lens twt 10) 15%nat.
Proof.
  rewrite SendTreeRT.twt_lens.
  apply (valid_lengths_of_nc [3;3;3;3;3;0;0;0;0;0;2]%nat 15).
  - intros len Hin. cbn in Hin. lia.
  - apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** The same conclusion through the PER-LEVEL interface, independently -- so a
    defect in either route shows up as a disagreement rather than as a plausible
    Qed. *)
Theorem twt_item6_by_levels : ValidLengths (SendGo.tree_lens twt 10) 15%nat.
Proof.
  rewrite SendTreeRT.twt_lens.
  apply (valid_lengths_by_levels [3;3;3;3;3;0;0;0;0;0;2]%nat 15).
  - intros len Hin. cbn in Hin. lia.
  - intros b Hb Hprev. do 15 (destruct b as [|b]; [vm_compute; lia|]). lia.
Qed.

(** ** 2. And through the FULL reduction, hypothesis by hypothesis

    [tree_lens_valid_from_nc] is the theorem ld-seams consumes; instantiating it
    at [twt] discharges BOTH its hypotheses concretely, which is the check that
    the interface can actually be driven rather than merely stated.  The first
    hypothesis is [t_len twt i <= 15] over [0 <= i <= 10] -- note [twt]'s slot 11
    holds 65535, so the bound is FALSE one index past the window and the range
    restriction is doing real work here, not decoration. *)
(** A [Forall]-driven bound for one [nth], reused below.  [Forall] rather than
    [In] because [lia] does not case-split disjunctions in hypotheses and [In]
    over an eleven-element list is exactly that. *)
Lemma nth_bound_of_Forall : forall (l : list Z) hi k,
  0 <= hi -> Forall (fun x => 0 <= x <= hi) l -> 0 <= nth k l 0 <= hi.
Proof.
  intros l hi k Hhi HF.
  destruct (nth_in_or_default k l 0) as [Hin|Hd].
  - rewrite Forall_forall in HF. apply HF, Hin.
  - rewrite Hd. lia.
Qed.

Lemma twt_len_bound : forall i, 0 <= i <= 10 -> t_len twt i <= 15.
Proof.
  intros i Hi. unfold twt, t_len. cbn [tr_dl]. unfold zlist.
  (* Split the sentinel off the end: within [0..10] the lookup never reaches it,
     and the remaining eleven entries are uniformly bounded.  Enumerating the
     eleven indices instead would need eleven distinct binder names and would
     say nothing more. *)
  change [3;3;3;3;3;0;0;0;0;0;2;65535]
    with ([3;3;3;3;3;0;0;0;0;0;2] ++ [65535]).
  rewrite app_nth1 by (cbn [length]; lia).
  pose proof (nth_bound_of_Forall [3;3;3;3;3;0;0;0;0;0;2] 15 (Z.to_nat i)) as H.
  assert (HF : Forall (fun x => 0 <= x <= 15) [3;3;3;3;3;0;0;0;0;0;2])
    by (repeat (apply Forall_cons; [lia|]); apply Forall_nil).
  specialize (H (ltac:(lia)) HF). lia.
Qed.

(** THE NEGATIVE CONTROL that makes [twt_len_bound]'s range restriction sharp:
    one index further and the sentinel breaks the bound. *)
Example twt_sentinel_breaks_bound : t_len twt 11 = 65535.
Proof. vm_compute. reflexivity. Qed.

Theorem twt_item6_via_interface : ValidLengths (SendGo.tree_lens twt 10) 15%nat.
Proof.
  apply (tree_lens_valid_from_nc twt 10 twt_len_bound).
  rewrite SendTreeRT.twt_lens. apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** ** 3. The vector's slack, recorded

    [ld-seams]' point: a witness's SLACK decides what it can catch.  At
    [maxBits = 15] this vector has slack 4096, which an off-by-one in the exponent
    would survive; at [maxBits = 3] it has slack 1, which it would not.  Both are
    in [Kraft15.v]; the numbers are restated here beside the tree instance so a
    reader of this file knows which one is doing the discriminating. *)
(* [%nat] must wrap the WHOLE equation: the file is in Z_scope, so a trailing
   literal outside the parentheses is parsed as a Z. *)
Example twt_slack_at_15 :
  (2 ^ 15 - kraft_sum (SendGo.tree_lens twt 10) 15 = 4096)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

(** ** 4. THE STRONG WITNESS: item 6 AT [build_tree]'S OWN OUTPUT

    Section 1-3's [twt] is a hand-written tree, so it answers "non-empty at a tree
    the emitter's tests use" and not "non-empty at a tree [build_tree] emits".
    **[build_tree] turns out to be computable at a concrete state**, so the
    stronger question is decidable rather than a matter of argument -- and both of
    [KraftOwed.v]'s branches are reachable.

    Measured (probe [p9]/[p10], 0.64 s and 1.35 s wall):

      ov = 0 branch, four distance codes at frequencies 5,3,2,1:
        ts_maxcode = 3        tree_lens = [1;2;3;3]
        ts_blcount 0..7       = [0;1;1;2;0;0;0;0]
        kraft_sum ... 15      = 32768 = 2^15 EXACTLY

      ov > 0 branch, eighteen distance codes at Fibonacci frequencies:
        ts_maxcode = 17
        tree_lens = [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1]
        ts_blcount 0..16      = [0;1;1;1;1;1;1;1;1;1;1;1;1;0;2;4;0]
        kraft_sum ... 15      = 32768 = 2^15 EXACTLY

    **The [ov > 0] instance is the interesting one and the gap at length 13 is the
    proof that [gb_adjust] RAN**: a pure [gb_pass1] output over eighteen
    Fibonacci-weighted symbols has one code at each depth, so a hole at 13 with
    two at 14 and four at 15 is precisely the redistribution
    [blc[bits] -= 1; blc[bits+1] += 2; blc[maxlen] -= 1] performs.  Four codes are
    clamped to [max_length].

    **AND BOTH WITNESSES ARE EXACTLY TIGHT -- slack ZERO, not merely small.**  That
    is a fact about the target, not about my choice of witness: a Huffman code over
    at least two symbols is COMPLETE, so Kraft holds with EQUALITY, and
    [bt_force2] guarantees at least two symbols.  Combined with
    [KraftAdjust.zksum_gba_body] (each [gb_adjust] trip lowers the sum by exactly
    one), the general shape this predicts is

        pre-adjust sum = 2 ^ 15 + trips        post-adjust sum = 2 ^ 15

    which is obligation (i) -- the [gb_pass1] item -- stated as an equality.  **A
    prover of that branch should aim at EQUALITY rather than at the inequality item
    6 literally asks for**: it is a stronger statement, it is what the code
    actually achieves, and an inequality target would leave the slack unexplained.
    I am not taking (i); this is evidence for whoever does, and it is measurable
    the same way. *)

Definition dfreq : Tree := mkTree (zlist [5;3;2;1]) zzero.
Definition s0 : TSt := set_tree TK_D dfreq ts_new.
Definition rbt : TSt := build_tree TK_D s0.

Example rbt_maxcode : ts_maxcode rbt TK_D = 3.
Proof. vm_compute. reflexivity. Qed.

Example rbt_lens : SendGo.tree_lens (ts_trees rbt TK_D) 3 = [1;2;3;3]%nat.
Proof. vm_compute. reflexivity. Qed.

(** EXACTLY tight, so any exponent slip anywhere in the chain breaks it. *)
Example rbt_exact : (kraft_sum (SendGo.tree_lens (ts_trees rbt TK_D) 3) 15 = 32768)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

(** ITEM 6, AT AN ACTUAL [build_tree] OUTPUT. *)
Theorem build_tree_item6_ov0 :
  ValidLengths (SendGo.tree_lens (ts_trees rbt TK_D) 3) 15%nat.
Proof.
  rewrite rbt_lens.
  apply (valid_lengths_of_nc [1;2;3;3]%nat 15).
  - intros len Hin. cbn in Hin. lia.
  - apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** ** 5. THE ov > 0 WITNESS -- [gb_adjust] exercised *)
Definition fibfreq : Tree :=
  mkTree (zlist [1;1;2;3;5;8;13;21;34;55;89;144;233;377;610;987;1597;2584]) zzero.
Definition sf : TSt := set_tree TK_D fibfreq ts_new.
Definition rfb : TSt := build_tree TK_D sf.

Example rfb_maxcode : ts_maxcode rfb TK_D = 17.
Proof. vm_compute. reflexivity. Qed.

Example rfb_lens :
  SendGo.tree_lens (ts_trees rfb TK_D) 17
  = [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1]%nat.
Proof. vm_compute. reflexivity. Qed.

(** FOUR codes at [max_length], so the clamp fired and [ov > 0]. *)
Example rfb_four_at_15 :
  (bl_count (SendGo.tree_lens (ts_trees rfb TK_D) 17) 15 = 4)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

(** THE SIGNATURE OF [gb_adjust]: no code of length 13 survives, while 14 has two
    and 15 has four.  An unadjusted Fibonacci profile has one code at every depth,
    so this hole is the redistribution and nothing else. *)
Example rfb_gap_at_13 :
  (bl_count (SendGo.tree_lens (ts_trees rfb TK_D) 17) 13 = 0)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example rfb_two_at_14 :
  (bl_count (SendGo.tree_lens (ts_trees rfb TK_D) 17) 14 = 2)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

(** The ADJUSTED code is exactly tight -- this is the fact the hard branch must
    prove in general, exhibited at an instance. *)
Example rfb_exact :
  (kraft_sum (SendGo.tree_lens (ts_trees rfb TK_D) 17) 15 = 32768)%nat.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Theorem build_tree_item6_ovpos :
  ValidLengths (SendGo.tree_lens (ts_trees rfb TK_D) 17) 15%nat.
Proof.
  rewrite rfb_lens.
  apply (valid_lengths_of_nc
           [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1]%nat 15).
  - intros len Hin. cbn in Hin. lia.
  - apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** ** 6. AND OBLIGATION (iii)'S PREMISE CLASS IS NON-EMPTY TOO

    [BlcOf (ts_blcount s2) (tree_lens t maxc)] is the third open obligation.  It
    also needs to be known satisfiable at a reachable state, and it is -- at both
    witnesses.  Discharged through huffman-id's own adapter
    [HuffGenCodes.BlcOf_of_nat] (graded tree, [:560]) rather than by unfolding
    [BlcOf], which is what that lemma exists for: it converts the [Z]-indexed
    predicate into the [nat]-indexed witness that is easy to give. *)
Theorem rbt_BlcOf :
  HuffGenCodes.BlcOf (ts_blcount rbt) (SendGo.tree_lens (ts_trees rbt TK_D) 3).
Proof.
  apply HuffGenCodes.BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try (vm_compute; reflexivity). lia.
Qed.

Theorem rfb_BlcOf :
  HuffGenCodes.BlcOf (ts_blcount rfb) (SendGo.tree_lens (ts_trees rfb TK_D) 17).
Proof.
  apply HuffGenCodes.BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try (vm_compute; reflexivity). lia.
Qed.

(** So all three open obligations for item 6 are now known SATISFIABLE at states
    [build_tree] actually reaches, on both sides of the [ov] split.  None of them
    is proved in general -- that is the remaining work -- but none of them is
    vacuous, which was the open question. *)

Print Assumptions twt_item6.
Print Assumptions twt_item6_by_levels.
Print Assumptions nth_bound_of_Forall.
Print Assumptions twt_len_bound.
Print Assumptions twt_item6_via_interface.
Print Assumptions twt_slack_at_15.
Print Assumptions build_tree_item6_ov0.
Print Assumptions build_tree_item6_ovpos.
Print Assumptions rfb_gap_at_13.
Print Assumptions rfb_exact.
Print Assumptions rbt_BlcOf.
Print Assumptions rfb_BlcOf.
