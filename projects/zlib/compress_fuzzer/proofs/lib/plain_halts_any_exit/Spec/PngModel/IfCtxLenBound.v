(** * IfCtxLenBound — [lcode_len_bounded] at zlib's fixed literal/length table.

    wp5-pf, 2026-08-17.  Scratch, offered to wp4 for the InflateFast layer.

    WHY THIS ONE.  [InflateThy.if_wf_ctx_wf] reads

      forall a, if_wf a -> lcode_len_bounded (if_ctx a) -> if_ctx_wf (if_ctx a)

    and its proof discharges [lcode_two_level] and [dcode_two_level] from
    [if_wf] by [tauto].  So [lcode_len_bounded] is not one of three
    conjuncts to check — it is THE residual obligation, the only thing
    standing between [if_wf] and [if_ctx_wf].  wp4 nominated it; the
    measurement in IfCtxVacuity.v is why it is the right one of the three:

      - [lcode_two_level] / [dcode_two_level] are VACUOUS at the fixed
        tables (the subtable-pointer premise fires 0 times in 544 entries),
        so proving them there would certify nothing;
      - [lcode_len_bounded]'s premise fires on 104 of [lenfix]'s 512
        entries, and 104 is what RFC 1951's fixed-code layout predicts
        independently (23 seven-bit length symbols x 4 replications in a
        9-bit root, plus 6 eight-bit x 2).

    THE INDEXING SUBTLETY, which is the only real content here.
    [tbl_of_list l = fun i => ... nth (Z.to_nat i) l (0,0,0) ...], and
    [Z.to_nat] CLAMPS negatives to 0.  So [lenfix (-5)] is not the default
    entry — it is [lenfix 0].  A proof that case-splits on [0 <= v] and
    waves at "out of range gives the default" is wrong for every negative
    index.  Splitting on [Z.to_nat v < 512] instead is correct and simpler:
    negatives fold into the reflected range rather than out of it. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inflate InflateFast InflateThy.
(* Qualified by wp4 at splice time: pf authored these in a flat scratch
   dir where [IfCtxVacuity] was a top-level logical name. In the layer it
   is Spec.PngModel.IfCtxVacuity. Only this line changed. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import IfCtxVacuity.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** The boolean test of IfCtxVacuity, discharged into the Prop the layer
    states.  Proved once so the reflection below is a rewrite, not an
    argument. *)
Lemma len_bound_ok_sound : forall h, len_bound_ok h = true -> lc_len_ok h.
Proof.
  intros h H Hop. unfold len_bound_ok in H.
  destruct (Z.eqb (Z.land (c_op h) 16) 0) eqn:E.
  - apply Z.eqb_eq in E. lia.
  - cbn [negb implb] in H. apply andb_true_iff in H as [H1 H2].
    split; [now apply Z.leb_le | now apply Z.leb_le].
Qed.

Lemma lenfix_list_length : length lenfix_list = 512%nat.
Proof. vm_compute. reflexivity. Qed.

(** Every value [lenfix] can take is a value it takes at [Z.of_nat] of some
    index, because the table reads its argument only through [Z.to_nat]. *)
Lemma lenfix_via_nat : forall v, lenfix v = lenfix (Z.of_nat (Z.to_nat v)).
Proof. intro v. unfold lenfix, tbl_of_list. now rewrite Nat2Z.id. Qed.

(** THE RESULT. *)
Lemma lenfix_len_bounded : forall v, lc_len_ok (lenfix v).
Proof.
  intro v. apply len_bound_ok_sound.
  rewrite lenfix_via_nat.
  destruct (Nat.ltb (Z.to_nat v) 512) eqn:Hlt.
  - (* in range: reflect q3 at this index *)
    apply Nat.ltb_lt in Hlt.
    pose proof q3_lenfix_len_bound_holds_everywhere as Hall.
    rewrite forallb_forall in Hall.
    apply Hall, in_seq. lia.
  - (* past the end: [nth] returns the default, whose op is 0, so the
       premise of [lc_len_ok] cannot fire *)
    apply Nat.ltb_ge in Hlt.
    unfold lenfix, tbl_of_list.
    rewrite Nat2Z.id, nth_overflow by (rewrite lenfix_list_length; exact Hlt).
    reflexivity.
Qed.

(** [lc_chains] never fires at the fixed table — needed since the
    2026-08-19 relativisation, whose [lcode_index_range] clause 2 is
    conditioned on it.  Same reflection discipline as
    [lenfix_len_bounded]: in-range by [vm_compute] over the 512 real
    entries, past-the-end by [nth_overflow] (the default entry's op is 0,
    and negatives clamp INTO the range via [Z.to_nat], not out of it). *)
Example q4_lenfix_no_chains_up_to_512 :
  forallb (fun i => negb (lc_chains (c_op (lenfix (Z.of_nat i))))) (seq 0 512)
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lenfix_no_chains : forall v, lc_chains (c_op (lenfix v)) = false.
Proof.
  intro v. rewrite lenfix_via_nat.
  destruct (Nat.ltb (Z.to_nat v) 512) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    pose proof q4_lenfix_no_chains_up_to_512 as Hall.
    rewrite forallb_forall in Hall.
    apply negb_true_iff, Hall, in_seq. lia.
  - apply Nat.ltb_ge in Hlt.
    unfold lenfix, tbl_of_list.
    rewrite Nat2Z.id, nth_overflow by (rewrite lenfix_list_length; exact Hlt).
    reflexivity.
Qed.

(** The consumer-facing form: any context whose literal/length table is the
    fixed one satisfies the residual conjunct.

    RESTATED at the 2026-08-19 relativisation (zlib-port-repairs.md §2),
    and the two new premises are FORCED, not stylistic: under the repaired
    [lcode_len_bounded], the old statement ([f_lcode c = lenfix] alone) is
    FALSE — [lcode_index_range]'s clause 1 bounds [Z.land _ (f_lmask c)],
    and with [f_lmask c] unconstrained (say -1) no [n] exists.  The mask
    premise takes the [Z.ones k] shape [if_ctx] always produces
    ([Z.shiftl 1 lenbits - 1]); the witness is [n := 2 ^ k] — the doc's
    "n = 512 at lenbits = 9", generalised so the payoff lemma below keeps
    its ORIGINAL statement with lenbits bounds drawn from [if_wf].
    Clause 2 is vacuous at the fixed table ([lenfix_no_chains]). *)
Lemma lcode_len_bounded_of_lenfix :
  forall c k, 0 <= k -> f_lcode c = lenfix -> f_lmask c = Z.ones k ->
  lcode_len_bounded c.
Proof.
  intros c k Hk Hc Hm.
  exists (2 ^ k). split; [|split].
  - (* upto: the per-entry fact holds at EVERY index, range unneeded *)
    intros v _. rewrite Hc. apply lenfix_len_bounded.
  - (* clause 1: the masked root index, both bounds from the mask shape *)
    intro s. rewrite Hm, Z.land_ones by exact Hk.
    apply Z.mod_pos_bound.
    apply Z.pow_pos_nonneg; lia.
  - (* clause 2: vacuous — the chain test never fires at lenfix *)
    intros v s _ Hch. rewrite Hc, lenfix_no_chains in Hch. discriminate.
Qed.

(** And the payoff, stated so the consumer does not have to assemble it:
    at the fixed table, [if_wf] alone gives [if_ctx_wf].  STATEMENT
    UNCHANGED by the relativisation: [if_wf]'s [1 <= a_lenbits <= 15]
    supplies the mask-shape premises. *)
Lemma if_ctx_wf_of_if_wf_lenfix :
  forall a, if_wf a -> f_lcode (if_ctx a) = lenfix -> if_ctx_wf (if_ctx a).
Proof.
  intros a H Hc. apply if_wf_ctx_wf; [exact H|].
  destruct H as (_ & _ & _ & _ & _ & Hlenbits & _).
  apply (lcode_len_bounded_of_lenfix _ (a_lenbits a)); [lia | exact Hc |].
  cbn [f_lmask if_ctx].
  rewrite Z.shiftl_1_l, Z.ones_equiv. lia.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Locate lenfix_len_bounded.
Print Assumptions lenfix_len_bounded.
Locate lcode_len_bounded_of_lenfix.
Print Assumptions lcode_len_bounded_of_lenfix.
Locate if_ctx_wf_of_if_wf_lenfix.
Print Assumptions if_ctx_wf_of_if_wf_lenfix.
