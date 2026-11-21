(** * DynCodeFor.v — sub-item (i) of [DynamicTreesCodeTheBlock]

    length-in-range ==> [code_for] exists, at the L/D trees' 15 bits.

    OWNER: dyntrees-supply.  Scratch only, additive, nothing admitted.
    Built against the UNMODIFIED live graded tree; see build.sh.

    ** WHY THIS IS NOT THE TEMPLATE

    huffman-id's [covered_of_len_bound] (CoverChain.v:108, md5
    , pinned at pins/CoverChain.v.pin) is the
    BL instance: 19 symbols, lengths 1..7, concluding in [nth_error].  NONE of
    its three constants is reused here.  Each of mine is read off the artifact
    by [reflexivity] in section 0 below, so a reader can see the derivation
    rather than trust a transcription:

      sd_max_length TK_L = sd_max_length TK_D = 15   (Trees.v:264 + :82)
      sd_max_length TK_BL = 7                        (the template's bound)
      sd_elems TK_L = 286, sd_elems TK_D = 30        (Trees.v:262 + :77-79)

    and the conclusion is strengthened from [nth_error] all the way to
    [code_for], because that is the shape the consumer takes (section 3).

    ** THE NON-VACUITY GUARD, AND WHY IT IS SPELLED DIFFERENTLY

    The template's own comment is the load-bearing warning: [LensOf] quantifies
    over [k < length L] and is therefore VACUOUSLY TRUE OF THE EMPTY LIST, so
    the length hypothesis is what rules out [L = []].  The template spells the
    guard as the numeric [19 <= length cl] paired with [0 <= s <= 18].

    I spell it as the fact those two IMPLY and that the [LensOf] quantifier
    actually needs: [(Z.to_nat s < length L)%nat].  That is weaker (so more
    general), it is the exact side condition of the quantifier rather than a
    number copied across trees, and it still rules out [L = []] because
    [_ < length []] is false.  [the_length_guard_is_necessary] (section 4)
    refutes the guard-free statement outright, so this is necessity, not
    tidiness.

    ** LensOf IS NOT AVAILABLE TO REQUIRE — see the FINDING in section 2. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** ** 0.  EVERY CONSTANT, READ OFF THE ARTIFACT

    Not carried from the template.  [sd_max_length] (Trees.v:264) branches only
    on [TK_BL], so L and D share [MAX_BITS]; the BL line is here as the contrast
    that shows the template's 7 is a different number, not a portable one. *)

Example l_max_length_is_15  : sd_max_length TK_L  = 15. Proof. reflexivity. Qed.
Example d_max_length_is_15  : sd_max_length TK_D  = 15. Proof. reflexivity. Qed.
Example bl_max_length_is_7  : sd_max_length TK_BL = 7.  Proof. reflexivity. Qed.
Example l_elems_is_286      : sd_elems TK_L = 286.      Proof. reflexivity. Qed.
Example d_elems_is_30       : sd_elems TK_D = 30.       Proof. reflexivity. Qed.
Example bl_elems_is_19      : sd_elems TK_BL = 19.      Proof. reflexivity. Qed.

(** And the number in the consumer's own text is the same 15: [CbCodedAt]
    (SidCbGeneral.v:61) writes [code_for ll 15%nat].  So the [maxBits] my
    conclusion must produce is [Z.to_nat (sd_max_length TK_L)]. *)
Example the_consumers_maxbits_is_the_trees_maxlength :
  Z.to_nat (sd_max_length TK_L) = 15%nat.
Proof. reflexivity. Qed.

(** ** 1.  THE [maxBits]-GENERAL CORE

    [code_for] (Huff.v:509) returns [None] on exactly two conditions: no entry,
    or an entry outside [1 .. maxBits].  So an in-range entry is all that
    existence needs, at ANY [maxBits].

    huffman-id proved the [maxBits = 7] instance ([code_for_of_covered],
    HuffCover.v:95, pinned at pins/HuffCover.v.pin md5
    ).  That file is scratch-only and imports
    a module that does not build (section 2), so this is a re-proof at the
    general bound rather than a citation — and generalising [maxBits] costs
    nothing, which is itself worth recording: nobody should pay for a 15-bit
    twin of a 7-bit lemma. *)

Lemma code_for_of_len_bound : forall (L : list nat) (maxBits j len : nat),
  nth_error L j = Some len ->
  (1 <= len <= maxBits)%nat ->
  exists cw, code_for L maxBits j = Some cw.
Proof.
  intros L maxBits j len He Hlen. unfold code_for. rewrite He.
  replace (orb (Nat.eqb len 0) (Nat.ltb maxBits len)) with false
    by (symmetry; apply orb_false_iff; split;
        [apply Nat.eqb_neq | apply Nat.ltb_ge]; lia).
  eexists. reflexivity.
Qed.

(** ** 2.  THE L/D ANALOGUE

    FINDING (reported to zlib-lead before this file was written): [LensOf] is
    defined at HuffGenCodes.v:330 in the GRADED tree, but
    [Spec/PngModel/HuffGenCodes.vo] DOES NOT EXIST, so

      From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes.

    fails with "Unable to locate library HuffGenCodes ... (while searching for a
    .vos file)".  Verified by build, not by reading, in container
    libpng-quiet-w8.  The same holds for HuffMaxBits.vo, so
    [code_for_maxbits_irrel] is equally unreachable.

    Consequence for the STATEMENT: I take the [LensOf] body as an explicit
    hypothesis rather than the constant.  [LensOf] is a transparent
    [Definition], so the two are convertible and a consumer holding [LensOf t L]
    discharges this premise by [exact] — but I have NOT been able to compile
    that check, and I will not claim it until HuffGenCodes.vo exists.  The
    one-line tripwire to run at that moment is recorded in
    pins/PINS.md as LENSOF-TRIPWIRE.

    I deliberately do NOT introduce a second name for the predicate: two
    vocabularies for one fact is how a free variable gets loose. *)

Lemma code_for_of_tlen_bound : forall (t : Tree) (L : list nat) (s len : Z),
  (* [LensOf t L], inlined — see the FINDING above *)
  (forall k, (k < length L)%nat ->
     t_len t (Z.of_nat k) = Z.of_nat (nth k L 0%nat)) ->
  (* the non-vacuity guard: exactly the quantifier's own side condition *)
  (Z.to_nat s < length L)%nat ->
  0 <= s ->
  t_len t s = len ->
  1 <= len <= 15 ->
  exists cw, code_for L 15%nat (Z.to_nat s) = Some cw.
Proof.
  intros t L s len HL Hk Hs Ht Hr.
  apply (code_for_of_len_bound L 15%nat (Z.to_nat s) (nth (Z.to_nat s) L 0%nat)).
  - apply nth_error_nth'. exact Hk.
  - specialize (HL (Z.to_nat s) Hk).
    rewrite Z2Nat.id in HL by exact Hs.
    rewrite Ht in HL. lia.
Qed.

(** ** 3.  THE SAME THING AT THE TREE-KIND PARAMETER

    The upstream supply ([BuildChain.v:132 build_chain], huffman-id, Qed) does
    not conclude at the literal 15: it concludes
    [1 <= t_len ... s0 <= sd_max_length k] for a general kind [k].  So the form
    the composition actually needs takes [k] and a proof that [k] is not BL.
    Stated separately so the join is one [apply] and not an arithmetic step
    buried in someone else's script. *)

Lemma code_for_of_tlen_bound_kind : forall (k : Z) (t : Tree) (L : list nat) (s len : Z),
  k <> TK_BL ->
  (forall j, (j < length L)%nat ->
     t_len t (Z.of_nat j) = Z.of_nat (nth j L 0%nat)) ->
  (Z.to_nat s < length L)%nat ->
  0 <= s ->
  t_len t s = len ->
  1 <= len <= sd_max_length k ->
  exists cw, code_for L 15%nat (Z.to_nat s) = Some cw.
Proof.
  intros k t L s len Hk HL Hlen Hs Ht Hr.
  assert (Hm : sd_max_length k = 15).
  { unfold sd_max_length. destruct (Z.eqb_spec k TK_BL) as [->|_];
    [contradiction | reflexivity]. }
  rewrite Hm in Hr.
  exact (code_for_of_tlen_bound t L s len HL Hlen Hs Ht Hr).
Qed.

(** ** 4.  CONTROLS

    Two hypotheses were introduced (the non-vacuity guard, and the upper bound).
    Each gets a REFUTATION of the statement without it, which is strictly
    stronger than a [clear]-and-rebuild usage control: it shows the premise is
    necessary, not merely consumed. *)

(** (a) The guard.  Drop it and the statement is FALSE, witnessed by exactly the
    vacuity the template warned about: [L = []] satisfies the [LensOf] body
    vacuously, and [code_for [] _ _] is [None]. *)
Example the_length_guard_is_necessary :
  ~ (forall (t : Tree) (L : list nat) (s len : Z),
       (forall k, (k < length L)%nat ->
          t_len t (Z.of_nat k) = Z.of_nat (nth k L 0%nat)) ->
       0 <= s ->
       t_len t s = len ->
       1 <= len <= 15 ->
       exists cw, code_for L 15%nat (Z.to_nat s) = Some cw).
Proof.
  intros H.
  specialize (H (t_setlen tzero 0 1) [] 0 1).
  destruct H as [cw Hcw].
  - intros k Hk. cbn [length] in Hk. lia.
  - lia.
  - reflexivity.
  - lia.
  - cbn in Hcw. discriminate Hcw.
Qed.

(** (b) The upper bound.  A length ABOVE [maxBits] has no code — which is also
    the reason section 0's [sd_max_length TK_L = 15] has to be the SAME 15 the
    consumer writes in [code_for ll 15%nat].  If the tree's bound and the
    table's bound ever diverged, this is the lemma that would break. *)
Example the_maxbits_bound_is_necessary :
  ~ (forall (L : list nat) (maxBits j len : nat),
       nth_error L j = Some len ->
       (1 <= len)%nat ->
       exists cw, code_for L maxBits j = Some cw).
Proof.
  intros H. destruct (H [16%nat] 15%nat 0%nat 16%nat eq_refl ltac:(lia)) as [cw Hcw].
  cbn in Hcw. discriminate Hcw.
Qed.

(** (c) Inhabitability, inside the real constraints rather than at a legal but
    unreachable point.  At the consumer the L-tree index is a literal
    [0 <= cb_lc < 256] (a premise of [cb_step_emits_lit], CbEmit.v:550), and the
    dynamic header's L vector runs to [sd_elems TK_L = 286] entries.  So a
    witness must have [length L = 286] and be indexable at 255.  Here it is,
    with the guard DISCHARGED rather than assumed. *)
Definition dyn_witness_L : list nat := repeat 9%nat 286.
Definition dyn_witness_t : Tree :=
  mkTree zzero (fun i => if andb (Z.leb 0 i) (Z.ltb i 286) then 9 else 0).

Example the_guard_holds_at_a_real_literal_index :
  (Z.to_nat 255 < length dyn_witness_L)%nat.
Proof. unfold dyn_witness_L. rewrite repeat_length. cbn. lia. Qed.

Example inhabitable_at_a_real_literal_index :
  exists cw, code_for dyn_witness_L 15%nat (Z.to_nat 255) = Some cw.
Proof.
  apply (code_for_of_tlen_bound dyn_witness_t dyn_witness_L 255 9).
  - intros k Hk. unfold dyn_witness_L in Hk. rewrite repeat_length in Hk.
    assert (Hn : nth k dyn_witness_L 0%nat = 9%nat).
    { unfold dyn_witness_L.
      rewrite (nth_indep _ 0%nat 9%nat)
        by (rewrite repeat_length; exact Hk).
      apply nth_repeat. }
    rewrite Hn.
    unfold dyn_witness_t, t_len. cbn [tr_dl].
    destruct (andb (Z.leb 0 (Z.of_nat k)) (Z.ltb (Z.of_nat k) 286)) eqn:E.
    + reflexivity.
    + apply andb_false_iff in E as [E|E];
        [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
  - exact the_guard_holds_at_a_real_literal_index.
  - lia.
  - unfold dyn_witness_t, t_len. cbn [tr_dl]. reflexivity.
  - lia.
Qed.

(** ** 5.  AXIOM POSTURE *)
Print Assumptions code_for_of_len_bound.
Print Assumptions code_for_of_tlen_bound.
Print Assumptions code_for_of_tlen_bound_kind.
Print Assumptions the_length_guard_is_necessary.
Print Assumptions the_maxbits_bound_is_necessary.
Print Assumptions inhabitable_at_a_real_literal_index.
