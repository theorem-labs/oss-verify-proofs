(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ItGTblReplInv — the mid-loop form of root-table replication, and the
      ENDPOINT that makes the induction worth doing.

    [ItGTblRepl] proved the two halves of the loop argument — achieved
    ([fill_makes_class_uniform]: one fill makes its class uniform) and preserved
    ([classes_disjoint_of_positions]: a later trip whose position has passed an
    earlier code's interval cannot touch that code's class). What remains is
    riding them round [it_loop]'s fixpoint.

    THIS FILE DOES THE ENDPOINT FIRST, DELIBERATELY. A mid-loop invariant is only
    worth proving if it implies the thing the consumer wants at the exit, and that
    implication is cheap to check while the induction is not. If [repl_at_full]
    below did not close, the invariant's SHAPE would be wrong and the induction
    would be wasted — so it is checked before the expensive half is written.
    (Register: "the loop's result lives on the EXITS"; a per-step obligation that
    does not compose to the exit statement is a per-step obligation nobody wants.)

    THE CEILING IS ALREADY A PARAMETER. huffman-id's constraint — carry a CONSTANT
    ceiling, never one indexed by the loop variable, so every recursive call's side
    condition is the same expression — is already satisfied by the landed design:
    [ItGTblCover]'s [Pos] takes [M0] as an argument and [pos_advance] is stated
    over it, so nothing here has to be refactored to get it.

    GTBL-ARMS, 2026-08-18. Scratch; not landed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblRev ItGTblGeom ItGTblCover ItGTblRepl.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The mid-loop clause                                                    *)
(* ######################################################################### *)

(** A root index's unit is "done" at position [P] on exactly the condition
    [CovBelow] already uses — its unit lies entirely below [P]:

      [(zrev root i + 1) * 2 ^ (15 - root) <= P]

    so the clause is stated with that guard on BOTH indices rather than with a
    fresh notion of progress. Reusing the landed predicate's own guard is what
    makes the eventual induction able to consume [CovInv] directly instead of
    needing a bridge between two ideas of "how far the loop has got". *)
Definition UnitDone (root i P : Z) : Prop :=
  (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root) <= P.

Definition ReplBelow (root : Z) (t : ztbl) (P : Z) : Prop :=
  forall i j, 0 <= i < 2 ^ root -> 0 <= j < 2 ^ root ->
    UnitDone root i P -> UnitDone root j P ->
    (* DIRECTION COPIED FROM THE CONSUMER, not chosen: [RootReplicated] states
       this as [i mod _ = j mod _], and stating it the other way round here made
       the endpoint fail to typecheck against the very theorem it exists to feed.
       The supplying side does not get to pick the orientation. *)
    i mod 2 ^ (c_bits (t i)) = j mod 2 ^ (c_bits (t i)) ->
    c_bits (t j) = c_bits (t i).

(** Weakening in [P], the same shape as [cov_le]: a smaller position has fewer
    done units, so the clause over them is implied. This is the direction the
    induction consumes when it steps backwards from the exit. *)
Lemma repl_le : forall root t P Q,
  ReplBelow root t Q -> P <= Q -> ReplBelow root t P.
Proof.
  intros root t P Q H Hpq i j Hi Hj Hui Huj Hmod.
  apply H; try assumption; unfold UnitDone in *; lia.
Qed.

(* ######################################################################### *)
(* 2.  THE ENDPOINT — checked before the induction is written                  *)
(* ######################################################################### *)

(** At the completed position every root unit is done, because [zrev] at width
    [root] is bounded by [2 ^ root] and the units tile [[0, 2 ^ 15)] exactly.
    This is the step that would have refuted the invariant's shape. *)
Lemma unit_done_at_full : forall root i,
  0 <= root <= 15 -> UnitDone root i (2 ^ 15).
Proof.
  intros root i Hr. unfold UnitDone.
  assert (Hz : zrev (Z.to_nat root) i < 2 ^ Z.of_nat (Z.to_nat root))
    by (apply zrev_lt).
  rewrite (Z2Nat.id root) in Hz by lia.
  assert (Hp : 0 < 2 ^ (15 - root)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hsplit : 2 ^ 15 = 2 ^ root * 2 ^ (15 - root)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hmul : (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root)
                 <= 2 ^ root * 2 ^ (15 - root))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(** THE ENDPOINT. [ReplBelow] at the completed position IS [RootReplicated] — the
    property huffman-id's obligation (b) consumes. So the induction, once written,
    lands exactly on the consumer's statement with no adapter. *)
Theorem repl_at_full : forall root t,
  0 <= root <= 15 -> ReplBelow root t (2 ^ 15) -> RootReplicated t root.
Proof.
  intros root t Hr H i j Hi Hj Hmod.
  exact (H i j Hi Hj (unit_done_at_full root i Hr)
           (unit_done_at_full root j Hr) Hmod).
Qed.

(** And the directional form the consumer actually instantiates, chained through
    the reduction already proved in [ItGTblRepl]. Stated here so the endpoint is
    verified against the SHAPE THE CONSUMER HAS rather than against the strong
    form that happens to be easier to state. *)
Corollary repl_at_full_prefixdet : forall root t,
  0 <= root <= 15 ->
  (forall i, 0 <= i < 2 ^ root -> 1 <= c_bits (t i)) ->
  ReplBelow root t (2 ^ 15) -> RootPrefixDet t root.
Proof.
  intros root t Hr Hpos H.
  exact (root_repl_gives_prefixdet t root Hpos (repl_at_full root t Hr H)).
Qed.

(** The base case, for completeness of the pair: at position 0 no unit is done, so
    the clause is vacuous. Cheap, and it means the induction has both ends pinned
    before its middle is written. *)
Lemma repl_at_zero : forall root t, 0 <= root <= 15 -> ReplBelow root t 0.
Proof.
  intros root t Hr i j Hi Hj Hui Huj Hmod.
  exfalso. unfold UnitDone in Hui.
  assert (Hz : 0 <= zrev (Z.to_nat root) i) by (apply zrev_nonneg).
  assert (Hp : 0 < 2 ^ (15 - root)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hge : 1 * 2 ^ (15 - root) <= (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Print Assumptions repl_le.
Print Assumptions unit_done_at_full.
Print Assumptions repl_at_full.
Print Assumptions repl_at_full_prefixdet.
Print Assumptions repl_at_zero.
