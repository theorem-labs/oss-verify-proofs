(** * KraftTree -- Kraft's inequality for a binary tree, as pure arithmetic on
      LEVEL COUNTS.  This is the ov = 0 branch's mathematical core.

    OWNER: kraftsum.  Started on zlib-lead's ruling; duplication risk accepted by
    them, and huffman-id confirmed their parked ov = 0 item is the SUM half
    STATED and never attempted, so nothing exists under this.

    THE PROBLEM WITH THE OBVIOUS ROUTE.  In the ov = 0 case [gen_bitlen] writes
    [bits = t_len t (t_dad t n) + 1] ([Trees.v:402]), so the lengths ARE depths in
    the dad forest and Kraft "follows from the tree structure".  But the model has
    no tree: it has a [zarr] dad ARRAY, and [KraftOwed.v] is right that nothing in
    either tree states a fact about that relation.  Proving Kraft by induction over
    an inductive tree would first need an array-to-tree bridge, which is a second
    obligation as large as the first.

    SO THIS FILE AVOIDS TREES ENTIRELY.  Kraft's inequality for a binary tree is
    really a statement about two sequences of COUNTS -- internal nodes and leaves
    per depth -- satisfying two recurrences:

        I 0 + L 0 = 1                        one root
        I (S b) + L (S b) = 2 * I b          every internal node has exactly 2 children

    and from those two lines alone the inequality follows by telescoping, with no
    trees, no arrays, and no reference to [build_tree].  **That reduces the ov = 0
    branch to establishing two counting recurrences about the dad array** -- which
    is heap-shape work, squarely huffman-id's [bt_loop] territory, and is now the
    ONLY thing between item 6 and a proof on that branch.

    THE TELESCOPE, which is the whole idea.  Write [T b = I b + L b] for the nodes
    at depth [b] and consider [T b * 2 ^ (maxBits - b)].  The second recurrence
    gives

        T (S b) * 2 ^ (maxBits - S b) = T b * 2 ^ (maxBits - b) - L b * 2 ^ (maxBits - b)

    so each level converts exactly its own leaves' Kraft weight out of a running
    total that starts at [2 ^ maxBits].  Stated below as an EQUALITY with no
    subtraction ([level_telescope]), because [nat] subtraction truncates and an
    equality is what survives that.

    NON-VACUITY IS NOT ASSUMED.  The two recurrences are exercised at both
    [build_tree] outputs computed in [KraftReach.v] -- see section 3 -- so this is
    a reduction to a satisfiable hypothesis rather than to a named Prop. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Kraft15.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope nat_scope.

(** [list_sum] over an append.  Not in the stdlib under a name I could find, and
    the telescope grows the sum at its RIGHT end (via [seq_S]), so this is the
    shape the induction needs rather than [list_sum_cons]. *)
Lemma list_sum_app_nat : forall l1 l2,
  list_sum (l1 ++ l2) = list_sum l1 + list_sum l2.
Proof.
  induction l1 as [|a l1 IH]; intro l2; cbn [app].
  - rewrite list_sum_nil. lia.
  - rewrite !list_sum_cons, IH. lia.
Qed.

(** ** 1. The telescope

    Induction is on [k], the number of levels already converted, with [maxBits]
    fixed.  [seq_S] is what lets the sum grow at the RIGHT end, which is the end
    the recurrence moves. *)
Lemma level_telescope : forall (I L : nat -> nat) maxBits k,
  I 0 + L 0 = 1 ->
  (forall b, I (S b) + L (S b) = 2 * I b) ->
  k <= maxBits ->
  list_sum (map (fun b => L b * 2 ^ (maxBits - b)) (seq 0 k))
  + (I k + L k) * 2 ^ (maxBits - k)
  = 2 ^ maxBits.
Proof.
  intros I L maxBits k Hroot Hsplit Hk.
  induction k as [|k IH].
  - (* [list_sum_nil] rather than [cbn [list_sum]]: [list_sum] is
       [fold_right Init.Nat.add 0], so a delta list naming only [list_sum] leaves
       [list_sum []] unreduced and [lia] sees an opaque atom. *)
    cbn [seq map]. rewrite list_sum_nil, Nat.sub_0_r, Hroot. lia.
  - assert (Hk' : k <= maxBits) by lia.
    specialize (IH Hk').
    rewrite seq_S, map_app, list_sum_app_nat.
    cbn [map]. rewrite list_sum_cons, list_sum_nil.
    (* [seq_S 0 k] appends the index as [0 + k], not [k], so the new term reads
       [L (0 + k) * 2 ^ (maxBits - (0 + k))] and matches nothing until normalised. *)
    rewrite !Nat.add_0_l.
    rewrite (Hsplit k).
    assert (Hpow : 2 ^ (maxBits - k) = 2 * 2 ^ (maxBits - S k)).
    { replace (maxBits - k) with (S (maxBits - S k)) by lia.
      cbn [Nat.pow]. lia. }
    (* rewrite Hpow in BOTH: the goal carries [2 ^ (maxBits - k)] and the IH
       carries the halved form, and nia cannot relate two spellings of one power. *)
    rewrite Hpow in IH. rewrite Hpow.
    (* [nia], not [lia]: the step multiplies the unknowns [I k] / [L k] by the
       unknown power, so the identity is nonlinear in the atoms. *)
    nia.
Qed.

(** ** 2. Kraft, from the two recurrences

    The sum is taken over [1 .. maxBits] because that is the range
    [Kraft15.kraft_from_histogram] consumes -- [kraft_term _ 0 = 0], so a
    depth-0 leaf contributes nothing and the [b = 0] term is dropped rather than
    bounded. *)
Theorem kraft_of_level_counts : forall (I L : nat -> nat) maxBits,
  I 0 + L 0 = 1 ->
  (forall b, I (S b) + L (S b) = 2 * I b) ->
  list_sum (map (fun b => L b * 2 ^ (maxBits - b)) (seq 1 maxBits))
    <= 2 ^ maxBits.
Proof.
  intros I L maxBits Hroot Hsplit.
  destruct maxBits as [|m].
  - (* [maxBits = 0]: the sum is empty and [2 ^ 0 = 1] *)
    cbn [seq map]. rewrite list_sum_nil. cbn [Nat.pow]. lia.
  - pose proof (level_telescope I L (S m) (S m) Hroot Hsplit
                  (Nat.le_refl (S m))) as Htel.
    (* [seq 0 (S m) = 0 :: seq 1 m] by iota, so the telescope's sum is the
       target's sum plus the depth-0 term. *)
    change (seq 0 (S m)) with (0 :: seq 1 m) in Htel.
    cbn [map] in Htel. rewrite list_sum_cons in Htel.
    replace (S m - S m) with 0 in Htel by lia. cbn [Nat.pow] in Htel.
    (* the target's range grows at the right end *)
    (* [seq_S]'s arguments are (len, start), not (start, len) -- an explicit
       [seq_S 1 m] asks for [seq m 2] and matches nothing.  Bare [rewrite] lets
       unification pick them, and the appended index arrives as [1 + m]. *)
    rewrite seq_S, map_app, list_sum_app_nat.
    cbn [map]. rewrite list_sum_cons, list_sum_nil.
    replace (1 + m) with (S m) by lia.
    replace (S m - S m) with 0 by lia. cbn [Nat.pow].
    (* [L (S m) <= I (S m) + L (S m)], and the dropped depth-0 term is >= 0 *)
    nia.
Qed.

(** ** 2b. THE EQUALITY, which is what the runs actually satisfy

    zlib-lead's rule: measure what the real output satisfies, then state the lemma
    the runs already satisfy, rather than stating one and discovering the runs
    disagree.  Both [build_tree] outputs I computed land on **exactly** [2 ^ 15]
    ([KraftReach.rbt_exact], [KraftReach.rfb_exact]) -- slack zero, not small.  So
    the honest target is an equality, and it follows from the same telescope with
    ONE extra condition, which the measurements also confirm: **no internal nodes
    at the deepest level.**  [I 15 = 0] at both witnesses.

    [L 0 = 0] is FREE at every instantiation that matters, because [L] is always a
    [bl_count] and [Huff.bl_count_0] gives [bl_count V 0 = 0].  It is taken as a
    hypothesis only so this section stays independent of how [L] arises. *)
Theorem kraft_equality_of_level_counts : forall (I L : nat -> nat) maxBits,
  I 0 + L 0 = 1 ->
  (forall b, I (S b) + L (S b) = 2 * I b) ->
  I maxBits = 0 ->
  L 0 = 0 ->
  list_sum (map (fun b => L b * 2 ^ (maxBits - b)) (seq 1 maxBits))
  = 2 ^ maxBits.
Proof.
  intros I L maxBits Hroot Hsplit Htop Hzero.
  destruct maxBits as [|m].
  - (* maxBits = 0 forces I 0 = 0 and L 0 = 0, contradicting I 0 + L 0 = 1 *)
    cbn [Nat.pow] in *. lia.
  - pose proof (level_telescope I L (S m) (S m) Hroot Hsplit
                  (Nat.le_refl (S m))) as Htel.
    change (seq 0 (S m)) with (0 :: seq 1 m) in Htel.
    cbn [map] in Htel. rewrite list_sum_cons in Htel.
    replace (S m - S m) with 0 in Htel by lia. cbn [Nat.pow] in Htel.
    rewrite Htop, Hzero in Htel.
    rewrite seq_S, map_app, list_sum_app_nat.
    cbn [map]. rewrite list_sum_cons, list_sum_nil.
    replace (1 + m) with (S m) by lia.
    replace (S m - S m) with 0 by lia. cbn [Nat.pow].
    nia.
Qed.

(** ** 3. THE REMAINING OBLIGATION, named

    Everything above is arithmetic.  What the ov = 0 branch still owes is that the
    dad array's per-depth counts satisfy the two recurrences -- i.e. one root, and
    every internal node has exactly two children.  Stated as a predicate over the
    two count functions so it can be discharged about [build_tree]'s dad array
    without this file knowing anything about arrays. *)
Definition BinaryLevels (I L : nat -> nat) : Prop :=
  I 0 + L 0 = 1 /\ (forall b, I (S b) + L (S b) = 2 * I b).

(** The composition: level counts of the right shape give item 6's sum half, for
    any vector whose histogram those counts ARE. *)
Theorem valid_lengths_of_binary_levels : forall (I L : nat -> nat) V maxBits,
  BinaryLevels I L ->
  (forall b, 1 <= b -> b <= maxBits -> bl_count V b = L b) ->
  (forall len, In len V -> len <= maxBits) ->
  ValidLengths V maxBits.
Proof.
  intros I L V maxBits [Hroot Hsplit] Hhist Hub.
  apply (kraft_from_histogram V maxBits Hub).
  (* rewrite the histogram into the leaf counts, level by level *)
  assert (Heq :
    map (fun b => bl_count V b * 2 ^ (maxBits - b)) (seq 1 maxBits)
    = map (fun b => L b * 2 ^ (maxBits - b)) (seq 1 maxBits)).
  { apply map_ext_in. intros b Hb. apply in_seq in Hb.
    rewrite (Hhist b) by lia. reflexivity. }
  rewrite Heq.
  exact (kraft_of_level_counts I L maxBits Hroot Hsplit).
Qed.

(** The exact form of the shape predicate: [BinaryLevels] plus "the tree bottoms
    out at [maxBits]".  This is the residual I would hand a heap argument, because
    a heap argument knows both facts -- the combine loop makes two children per
    internal node, and nothing is internal below the deepest leaf. *)
Definition BinaryLevelsExact (I L : nat -> nat) (maxBits : nat) : Prop :=
  BinaryLevels I L /\ I maxBits = 0.

Theorem kraft_sum_equality_of_binary_levels : forall (I L : nat -> nat) V maxBits,
  BinaryLevelsExact I L maxBits ->
  (forall b, 1 <= b -> b <= maxBits -> bl_count V b = L b) ->
  L 0 = 0 ->
  (forall len, In len V -> len <= maxBits) ->
  kraft_sum V maxBits = 2 ^ maxBits.
Proof.
  intros I L V maxBits [[Hroot Hsplit] Htop] Hhist Hzero Hub.
  rewrite (kraft_sum_hist V maxBits Hub).
  assert (Heq :
    map (fun b => bl_count V b * 2 ^ (maxBits - b)) (seq 1 maxBits)
    = map (fun b => L b * 2 ^ (maxBits - b)) (seq 1 maxBits)).
  { apply map_ext_in. intros b Hb. apply in_seq in Hb.
    rewrite (Hhist b) by lia. reflexivity. }
  rewrite Heq.
  exact (kraft_equality_of_level_counts I L maxBits Hroot Hsplit Htop Hzero).
Qed.

(** ** 4. CONTROLS -- the recurrences at BOTH [build_tree] outputs

    [BinaryLevels] is a Prop I wrote, so it needs exercising at something
    reachable or the reduction above is a reduction to a named Prop.  The two
    witnesses are the length vectors [KraftReach.v] computed from actual
    [build_tree] runs.

    ov = 0 witness, [tree_lens = [1;2;3;3]]:  leaves 1,1,2 at depths 1,2,3.
    Internal counts are then forced: [I 0 = 1] (root is not a leaf), and
    [I (S b) = 2 * I b - L (S b)] gives [I 1 = 1], [I 2 = 1], [I 3 = 0]. *)
Definition L0 (b : nat) : nat :=
  match b with 1 => 1 | 2 => 1 | 3 => 2 | _ => 0 end.
Definition I0 (b : nat) : nat :=
  match b with 0 => 1 | 1 => 1 | 2 => 1 | _ => 0 end.

Lemma binary_levels_ov0 : BinaryLevels I0 L0.
Proof.
  split; [reflexivity|].
  intro b. do 4 (destruct b as [|b]; [reflexivity|]).
  (* past depth 3 everything is 0 on both sides *)
  cbn [I0 L0]. lia.
Qed.

(** The leaf counts really are the witness vector's histogram -- checked, not
    asserted, so the control cannot pass by my having written [L0] to fit. *)
Lemma L0_is_histogram : forall b, 1 <= b -> b <= 15 -> bl_count [1;2;3;3] b = L0 b.
Proof.
  intros b H1 H15.
  do 16 (destruct b as [|b]; [vm_compute; reflexivity|]). lia.
Qed.

Theorem item6_ov0_via_levels : ValidLengths [1;2;3;3] 15.
Proof.
  apply (valid_lengths_of_binary_levels I0 L0 [1;2;3;3] 15 binary_levels_ov0).
  - exact L0_is_histogram.
  - intros len Hin. cbn in Hin. lia.
Qed.

(** ov > 0 witness, [tree_lens = [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1]]:
    leaves 1 at depths 1..12, ZERO at 13, 2 at 14, 4 at 15.

    **THE INTERESTING PART: [BinaryLevels] STILL HOLDS after [gb_adjust].** The
    clamp and the redistribution produce a different tree shape, not a broken one
    -- [I 13 = 2] and [I 14 = 1] absorb the hole at depth 13, and the recurrence
    closes at depth 15 with [I 15 = 0].  So the ov > 0 branch is NOT a separate
    mathematical problem from the ov = 0 branch at this level of abstraction: both
    need the same two recurrences, and [gb_adjust] preserves them. That is a
    finding about the SPLIT, and it says the two branches may share one proof. *)
(** Written with FULLY EXPLICIT literal patterns and a [_ => 0] default, not with
    [if Nat.leb b 12 then 1 else 0].  The [leb] form cannot reduce once [b] is a
    symbolic variable, so the residual case of the recurrence proof (depths past
    15) left [cbn] with an undecided [if] and [lia] with an opaque atom.  Literal
    patterns reduce by constructor peeling and the default fires. *)
Definition Lf (b : nat) : nat :=
  match b with
  | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1
  | 7 => 1 | 8 => 1 | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 1
  | 13 => 0 | 14 => 2 | 15 => 4
  | _ => 0
  end.

(** [If_ 14 = 2], NOT 1 -- I wrote 1 first and the recurrence rejected it
    ("Unable to unify 4 with 3").  The forced values are
    [If_ (S b) = 2 * If_ b - Lf (S b)]: one internal node at each depth 0..12,
    then 2 at 13 (the hole at depth 13 consumes nothing), 2 at 14 (4 slots minus 2
    leaves), and 0 at 15 (4 slots minus 4 leaves).  Seventeen internal nodes for
    eighteen leaves, which is the right count for a full binary tree -- a
    cross-check the recurrence does not perform for me, and worth doing by hand
    since the recurrence alone would accept any consistent-but-wrong chain. *)
Definition If_ (b : nat) : nat :=
  match b with
  | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1
  | 7 => 1 | 8 => 1 | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 1
  | 13 => 2 | 14 => 2 | 15 => 0
  | _ => 0
  end.

Lemma binary_levels_ovpos : BinaryLevels If_ Lf.
Proof.
  split; [reflexivity|].
  intro b. do 16 (destruct b as [|b]; [vm_compute; reflexivity|]).
  cbn [If_ Lf]. lia.
Qed.

Lemma Lf_is_histogram : forall b, 1 <= b -> b <= 15 ->
  bl_count [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1] b = Lf b.
Proof.
  intros b H1 H15.
  do 16 (destruct b as [|b]; [vm_compute; reflexivity|]). lia.
Qed.

Theorem item6_ovpos_via_levels :
  ValidLengths [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1] 15.
Proof.
  apply (valid_lengths_of_binary_levels If_ Lf
           [15;15;15;15;14;14;12;11;10;9;8;7;6;5;4;3;2;1] 15
           binary_levels_ovpos).
  - exact Lf_is_histogram.
  - intros len Hin. cbn in Hin. lia.
Qed.

(** ** 5. NEGATIVE CONTROL -- the recurrences are what is doing the work

    Without this, [valid_lengths_of_binary_levels] could be true because
    [BinaryLevels] is satisfiable by anything.  An over-full profile CANNOT
    satisfy it: five leaves at depth 3 would need [I 2 = 2] (four slots at depth
    3) but also [I 2 <= 2 * I 1 - L 2], and the chain forces a contradiction.
    Exhibited concretely -- the over-full vector's histogram admits NO internal
    count sequence completing the recurrence. *)
Lemma over_full_has_no_binary_levels :
  ~ (exists I, BinaryLevels I (fun b => bl_count [3;3;3;3;3;3;3;0;0;0;2] b)).
Proof.
  intros [I [Hroot Hsplit]].
  (* walk the recurrence down four levels; each [bl_count] is a literal *)
  assert (HL0 : bl_count [3;3;3;3;3;3;3;0;0;0;2] 0 = 0) by reflexivity.
  assert (HL1 : bl_count [3;3;3;3;3;3;3;0;0;0;2] 1 = 0) by reflexivity.
  assert (HL2 : bl_count [3;3;3;3;3;3;3;0;0;0;2] 2 = 1) by reflexivity.
  assert (HL3 : bl_count [3;3;3;3;3;3;3;0;0;0;2] 3 = 7) by reflexivity.
  pose proof (Hsplit 0) as H1. pose proof (Hsplit 1) as H2.
  pose proof (Hsplit 2) as H3.
  rewrite HL0 in Hroot. rewrite HL1 in H1. rewrite HL2 in H2. rewrite HL3 in H3.
  (* I 0 = 1, I 1 = 2, I 2 = 3, and then depth 3 wants 7 leaves in 6 slots *)
  lia.
Qed.

Print Assumptions list_sum_app_nat.
Print Assumptions level_telescope.
Print Assumptions kraft_of_level_counts.
Print Assumptions kraft_equality_of_level_counts.
Print Assumptions kraft_sum_equality_of_binary_levels.
Print Assumptions valid_lengths_of_binary_levels.
Print Assumptions binary_levels_ov0.
Print Assumptions item6_ov0_via_levels.
Print Assumptions binary_levels_ovpos.
Print Assumptions item6_ovpos_via_levels.
Print Assumptions over_full_has_no_binary_levels.
