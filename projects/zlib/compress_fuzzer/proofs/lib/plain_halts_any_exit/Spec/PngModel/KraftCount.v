(** * KraftCount -- the bridge from INDEX CARDINALITIES to the length histogram.

    OWNER: kraftsum.

    WHY.  Item 6's residual is now [DadBinaryShape t maxc], which mentions
    [bl_count (SendGo.tree_lens t maxc)] -- a histogram of a LIST.  A heap-counting
    argument does not produce that; it produces cardinalities over an INDEX RANGE
    ("how many symbols in [0 .. maxc] sit at depth [b]").  huffman-id asked
    explicitly which side of that line the bridge should fall on.  **It falls here.**
    Their half then never mentions a list.

    AND I ALMOST BUILT THE WRONG THING FIRST.  I announced I would take [BlcOf]
    next.  [BlcOf] is NOT on item 6's chain any more: the residual is stated over
    [bl_count (tree_lens t maxc)] directly, so no array-to-list bridge is needed,
    and [BlcOf] survives only in [KraftReach.v]'s non-vacuity controls and in the
    now-redundant [tree_lens_valid_from_zarr] route.  Checking that before building
    is zlib-lead's own card -- *a blocker or a task list assembled from "questions
    outstanding" rather than "what this branch consumes" costs you the branch* --
    and I would have violated it one message after acknowledging it.

    THE TRAP IN THIS BRIDGE, which is not obvious and which would have made
    [DadBinaryShape] unprovable.  The naive index count and [bl_count] DISAGREE AT
    ZERO.  [bl_count V 0 = 0] by definition ([Huff.v:265]), but the number of
    indices in [0 .. maxc] whose length is 0 is the count of zero-frequency
    symbols, which [bt_init] makes nonzero for any real block ([Trees.v:554]).
    Since [BinaryLevels] requires [I 0 + L 0 = 1], feeding it the raw index count
    would demand [I 0 = 1 - (number of absent symbols)] -- unsatisfiable the moment
    a block omits two symbols.  So [LeavesAt] carries [bl_count]'s own [match b
    with O => O | S _ => ...] shape, and the agreement is then total rather than
    only above zero. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo SendGoLens SendGoWf SendTreeRT.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Kraft15 KraftTree KraftLens KraftReach.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope nat_scope.

(** ** 1. [count_occ] of a [map] is a [filter] length

    General, and the only genuinely list-shaped step in the file. *)
Lemma count_occ_map_filter : forall (f : nat -> nat) (l : list nat) (b : nat),
  count_occ Nat.eq_dec (map f l) b
  = length (filter (fun i => Nat.eqb (f i) b) l).
Proof.
  intros f l b. induction l as [|a l IH]; [reflexivity|].
  cbn [map filter count_occ length].
  destruct (Nat.eq_dec (f a) b) as [He|Hne].
  - replace (Nat.eqb (f a) b) with true by (symmetry; apply Nat.eqb_eq, He).
    cbn [length]. lia.
  - replace (Nat.eqb (f a) b) with false by (symmetry; apply Nat.eqb_neq, Hne).
    exact IH.
Qed.

(** ** 2. The leaf count at a depth, as a cardinality over the index range

    Shaped like [bl_count]: zero at depth 0, whatever the array says above it.
    See the header for why the [O] case is not the naive count. *)
Definition LeavesAt (t : Tree) (maxc : Z) (b : nat) : nat :=
  match b with
  | O => O
  | S _ =>
      length (filter (fun i => Nat.eqb (Z.to_nat (t_len t (Z.of_nat i))) b)
                     (seq 0 (Z.to_nat (maxc + 1))))
  end.

Theorem LeavesAt_is_bl_count : forall t maxc b,
  LeavesAt t maxc b = bl_count (SendGo.tree_lens t maxc) b.
Proof.
  intros t maxc b. destruct b as [|b']; [reflexivity|].
  cbn [LeavesAt bl_count]. unfold count_len, SendGo.tree_lens.
  symmetry. apply count_occ_map_filter.
Qed.

(** ** 3. So the residual can be stated over cardinalities alone

    This is the form to hand a heap argument: no list, no [tree_lens], no
    [bl_count] -- just "how many symbols sit at each depth", plus an internal-node
    count completing the binary recurrence. *)
Definition DadLevelsByCount (t : Tree) (maxc : Z) : Prop :=
  exists I : nat -> nat, KraftTree.BinaryLevels I (LeavesAt t maxc).

Theorem dad_shape_of_counts : forall t maxc,
  DadLevelsByCount t maxc -> DadBinaryShape t maxc.
Proof.
  intros t maxc [I [Hroot Hsplit]]. exists I. split.
  - rewrite <- (LeavesAt_is_bl_count t maxc 0). exact Hroot.
  - intro b. rewrite <- !(LeavesAt_is_bl_count t maxc). apply Hsplit.
Qed.

(** ...and the composition all the way to item 6 at the L call site, so the whole
    chain from a cardinality statement to [ValidLengths] is one [apply]. *)
Theorem item6_at_L_site_by_counts : forall (s : TSt) (lcodes : Z),
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15)%Z ->
  DadLevelsByCount (ts_trees s TK_L) (lcodes - 1)%Z ->
  ValidLengths (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)%Z) 15.
Proof.
  intros s lcodes HL15 Hc.
  apply tree_lens_valid_from_dad_shape.
  - intros i Hi. specialize (HL15 i Hi). lia.
  - apply dad_shape_of_counts. exact Hc.
Qed.

(** ** 4. CONTROLS

    [LeavesAt] is a definition I wrote, so it is tied to the measured witnesses
    rather than trusted.  Both are actual [build_tree] outputs from
    [KraftReach.v]: [rbt] (ov = 0, [maxc = 3], lengths [[1;2;3;3]]) and [rfb]
    (ov > 0, [maxc = 17]). *)
Example leaves_ov0_profile :
  map (LeavesAt (ts_trees rbt TK_D) 3) (seq 0 5) = [0;1;1;2;0].
Proof. vm_compute. reflexivity. Qed.

(** The bridge, exercised at the witness INDEPENDENTLY of the lemma -- both sides
    computed, so this is a tripwire rather than the lemma testing itself. *)
Example leaves_ov0_agrees_computed :
  map (LeavesAt (ts_trees rbt TK_D) 3) (seq 0 5)
  = map (bl_count (SendGo.tree_lens (ts_trees rbt TK_D) 3)) (seq 0 5).
Proof. vm_compute. reflexivity. Qed.

(** THE ZERO CASE, which is the trap the header names.  At [maxc = 17] the ov > 0
    run has eighteen symbols all with positive length, so the naive count at depth
    0 is 0 there too -- that instance would NOT have caught the trap.  So the
    control is stated where it bites: a tree with an ABSENT symbol.  [twt]'s
    length vector is [[3;3;3;3;3;0;0;0;0;0;2]] -- FIVE zero-length entries -- and
    [LeavesAt] must still report 0 at depth 0, not 5. *)
Example leaves_twt_zero_case : LeavesAt twt 10 0 = 0.
Proof. reflexivity. Qed.

Example leaves_twt_naive_would_be_five :
  length (filter (fun i => Nat.eqb (Z.to_nat (t_len twt (Z.of_nat i))) 0)
                 (seq 0 (Z.to_nat (10 + 1)))) = 5.
Proof. vm_compute. reflexivity. Qed.

(** ...and the bridge still holds there, which is the point: [bl_count] agrees
    with the SHAPED count and not with the naive one. *)
Example leaves_twt_agrees :
  map (LeavesAt twt 10) (seq 0 4)
  = map (bl_count (SendGo.tree_lens twt 10)) (seq 0 4).
Proof. vm_compute. reflexivity. Qed.

(** ov > 0 witness, at the levels [gb_adjust] touched: the hole at 13, two at 14,
    four at 15 -- read through [LeavesAt] rather than through the list. *)
Example leaves_ovpos_at_13_14_15 :
  map (LeavesAt (ts_trees rfb TK_D) 17) [13;14;15] = [0;2;4].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions leaves_ov0_agrees_computed.
Print Assumptions leaves_twt_zero_case.
Print Assumptions leaves_twt_naive_would_be_five.
Print Assumptions leaves_ovpos_at_13_14_15.
Print Assumptions count_occ_map_filter.
Print Assumptions LeavesAt_is_bl_count.
Print Assumptions dad_shape_of_counts.
Print Assumptions item6_at_L_site_by_counts.
