(** * DynLitCoded.v — the DYNAMIC-tree twin of [lit_coded] / [dist_coded]

    OWNER: dyntrees-supply.  Scratch only, additive, nothing admitted.

    ** WHY THIS FILE EXISTS

    A census of every `code_for`-premised declaration in the graded
    `Spec/PngModel` (all 11 files that mention it) returned two things:

    1. CONSUMERS ARE SELF-BOUNDING, so there is no fleet-wide defect here.
       [Huff.v:544 code_for_range] is
         [code_for lengths maxBits sym = Some cw -> sym < length lengths]
       so a lemma that TAKES [code_for ... = Some cw] already has the length
       fact.  I had worried the ten [DecodeBridge.v] lemmas premised on
       [code_for] were missing it; they are not, and six of them additionally
       carry [hdecode (code_table l maxBits) ... = Some (sym, rem)], which
       [DecodeBridge.v:521 hdecode_code_table_split] converts into the
       [code_for] premise outright.  That worry is RETRACTED.

    2. THE GAP IS ENTIRELY ON THE PRODUCER SIDE, and it is exactly two
       consumers: [CbEmit.v:550 cb_step_emits_lit] and [:638 cb_step_emits_ref]
       at a GENERAL [ll]/[dl].  Their code-existence premises are indexed from
       the SYMBOL BUFFER, not from a decode, so [hdecode_code_table_split] — the
       only general producer in the tree — cannot reach them: it runs in the
       DECODE direction and these need the TREE direction.  The only producers
       in the tree direction are [lit_coded] (CbEmit.v:532) and [dist_coded]
       (:736), both [vm_compute] reflection over the FIXED tables.

    So the missing object is a tree-direction, general-vector producer: the
    dynamic twin of [lit_coded].  That is what this file is.

    ** ONE CONSTANT NOT CARRIED

    The obvious shape to write is [lit_coded]'s, at 288.  **288 is the FIXED
    table's width** ([length fixed_lit_lengths]), not the dynamic alphabet's
    ([sd_elems TK_L = 286]).  Writing 288 here would be the template-constant
    error one level up from the one I already avoided in DynCodeFor.v.  So the
    general producer is stated WIDTH-PARAMETRIC and the widths are supplied at
    the instances, each read off the artifact. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk Huff DeflateSpec ZBitsOut Trees BwStream EmitSym CbEmit
  DecodeBridge.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import DynCodeFor.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** ** 0.  THE TWO WIDTHS ARE DIFFERENT NUMBERS, and both are read off the artifact *)

Example fixed_lit_table_is_288 : length fixed_lit_lengths = 288%nat.
Proof. vm_compute. reflexivity. Qed.
(** I wrote 30 here first and the build refused it: the table is THIRTY-TWO
    entries long while the distance alphabet is thirty.  That is exactly the
    unobservability [CbEmit.v:440-446] documents — [t_len static_dtree 30] reads
    off the end and returns 0, so an unbounded [tree_codes] over
    [fixed_dist_lengths] is FALSE at symbols 30 and 31, and [dist_coded]'s bound
    is 30 rather than [length fixed_dist_lengths].  Kept as a compiled record,
    because it means table width and alphabet width differ on the D side too —
    in the OPPOSITE direction from the L side (288 > 286, but 32 > 30 for a
    different reason). *)
Example fixed_dist_table_is_32 : length fixed_dist_lengths = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Example the_dist_alphabet_is_narrower_than_its_table :
  (Z.to_nat (sd_elems TK_D) < length fixed_dist_lengths)%nat.
Proof. vm_compute. lia. Qed.
Example dynamic_l_alphabet_is_286 : sd_elems TK_L = 286.
Proof. reflexivity. Qed.
Example dynamic_d_alphabet_is_30  : sd_elems TK_D = 30.
Proof. reflexivity. Qed.

(** The L widths genuinely differ — 288 vs 286 — which is why the general
    producer below takes the width as a parameter instead of naming one. *)
Example the_two_l_widths_are_not_the_same_number :
  Z.of_nat (length fixed_lit_lengths) <> sd_elems TK_L.
Proof. vm_compute. discriminate. Qed.

(** ** 1.  THE VECTOR-ONLY PRODUCER

    No tree at all.  This is the "length-vector-level fact" the census named as
    the missing piece: everything [code_for] needs, read straight off the
    vector.  Stated first because it is the weakest hypothesis set that works,
    and a header-side producer (which holds the sent vector, not the tree) can
    use it directly. *)

Lemma code_for_of_nth_nonzero : forall (L : list nat) (i : nat),
  (i < length L)%nat ->
  nth i L 0%nat <> 0%nat ->
  (nth i L 0%nat <= 15)%nat ->
  exists cw, code_for L 15%nat i = Some cw.
Proof.
  intros L i Hi Hnz Hle.
  apply (code_for_of_len_bound L 15%nat i (nth i L 0%nat)).
  - apply nth_error_nth'. exact Hi.
  - lia.
Qed.

(** ** 2.  THE TREE-DIRECTION PRODUCER, WIDTH-PARAMETRIC

    The dynamic twin of [lit_coded]/[dist_coded].  [w] is the caller's width;
    [(w <= length L)%nat] is the non-vacuity guard in the form a width-indexed
    caller can actually supply, and it is the same guard as DynCodeFor's
    [(Z.to_nat s < length L)%nat] specialised to a width.

    The [t_len] hypothesis is what [BuildChain.build_chain] delivers, so this
    composes with the freq-positivity side without an adapter. *)

Lemma dyn_coded_upto : forall (t : Tree) (L : list nat) (w : nat),
  (forall k, (k < length L)%nat ->
     t_len t (Z.of_nat k) = Z.of_nat (nth k L 0%nat)) ->
  (w <= length L)%nat ->
  forall i, (i < w)%nat ->
    1 <= t_len t (Z.of_nat i) <= 15 ->
    exists cw, code_for L 15%nat i = Some cw.
Proof.
  intros t L w HL Hw i Hi Hrange.
  (* the supply lemma concludes at [Z.to_nat s]; at [s = Z.of_nat i] that is
     [Z.to_nat (Z.of_nat i)], which is [i] only up to [Nat2Z.id] — so the
     round-trip is discharged explicitly rather than left to unification *)
  assert (Hg : exists cw, code_for L 15%nat (Z.to_nat (Z.of_nat i)) = Some cw).
  { apply (code_for_of_tlen_bound t L (Z.of_nat i) (t_len t (Z.of_nat i))).
    - exact HL.
    - rewrite Nat2Z.id. lia.
    - lia.
    - reflexivity.
    - exact Hrange. }
  rewrite Nat2Z.id in Hg. exact Hg.
Qed.

(** ** 3.  THE TWO INSTANCES AT THE DYNAMIC ALPHABET'S OWN WIDTHS

    [Z.to_nat (sd_elems TK_L)] and [Z.to_nat (sd_elems TK_D)] rather than 288
    and 30, so the numbers travel from Trees.v and are not retyped here. *)

Corollary dyn_lit_coded : forall (t : Tree) (ll : list nat),
  (forall k, (k < length ll)%nat ->
     t_len t (Z.of_nat k) = Z.of_nat (nth k ll 0%nat)) ->
  (Z.to_nat (sd_elems TK_L) <= length ll)%nat ->
  forall i, (i < Z.to_nat (sd_elems TK_L))%nat ->
    1 <= t_len t (Z.of_nat i) <= 15 ->
    exists cw, code_for ll 15%nat i = Some cw.
Proof.
  intros t ll HL Hw i Hi Hr.
  exact (dyn_coded_upto t ll (Z.to_nat (sd_elems TK_L)) HL Hw i Hi Hr).
Qed.

Corollary dyn_dist_coded : forall (t : Tree) (dl : list nat),
  (forall k, (k < length dl)%nat ->
     t_len t (Z.of_nat k) = Z.of_nat (nth k dl 0%nat)) ->
  (Z.to_nat (sd_elems TK_D) <= length dl)%nat ->
  forall i, (i < Z.to_nat (sd_elems TK_D))%nat ->
    1 <= t_len t (Z.of_nat i) <= 15 ->
    exists cw, code_for dl 15%nat i = Some cw.
Proof.
  intros t dl HL Hw i Hi Hr.
  exact (dyn_coded_upto t dl (Z.to_nat (sd_elems TK_D)) HL Hw i Hi Hr).
Qed.

(** ** 4.  WHAT IS **NOT** CLAIMED: this does not subsume [lit_coded]

    [lit_coded] is [vm_compute] reflection over a CLOSED table — it needs no
    tree and no length hypothesis because the 288 entries are literally there to
    compute.  My producer needs a tree relation and a width.  Neither implies
    the other, and it would be wrong to retire either:

      * at the FIXED tables, [lit_coded]/[dist_coded] remain strictly better
        (no hypotheses beyond the index bound);
      * at a DYNAMIC tree, reflection is impossible because the vector is not
        closed, and mine is the only route.

    Recorded because "I built the general version" invites retiring the special
    one, and here that would be a regression. *)

Example the_fixed_producer_is_still_the_better_one_at_fixed_tables :
  forall i, (i < 288)%nat ->
    exists cw, code_for fixed_lit_lengths 15%nat i = Some cw.
Proof. exact lit_coded. Qed.

(** ** 5.  DIRECTION CONTROL

    The census found exactly one general producer in the tree,
    [DecodeBridge.v:521 hdecode_code_table_split], and the reason it cannot
    serve [cb_step_emits_lit] is not strength but DIRECTION: it turns a
    successful DECODE into [code_for]; the emitter has a tree and a symbol
    buffer and no decode.  Stated as a shape comparison so the distinction is
    in the file and not only in a report — the two take unrelated inputs, so
    neither is a weakening of the other. *)

Example the_decode_producer_needs_a_decode :
  forall l maxBits bits sym rem,
    hdecode (code_table l maxBits) bits = Some (sym, rem) ->
    exists cw, code_for l maxBits sym = Some cw /\ bits = cw ++ rem.
Proof. exact hdecode_code_table_split. Qed.

(** ** 6.  AXIOM POSTURE *)
Print Assumptions code_for_of_nth_nonzero.
Print Assumptions dyn_coded_upto.
Print Assumptions dyn_lit_coded.
Print Assumptions dyn_dist_coded.
