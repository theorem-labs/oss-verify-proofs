(** * HuffCover — the capstone's one silent-failure hypothesis, made per-symbol
      and checkable.

    OWNER: huffman-id.

    THE PROBLEM.  [SendTreeRT.send_tree_roundtrip] carries four hypotheses.  Three
    are syntactic range facts (the 0xffff guard, lengths in 0..15, Kraft).  The
    fourth is

        cl_bits cl (send_tree_items t maxc) = Some bits

    and I flagged it in §HUFFID-COMPLETE as the only one that could fail SILENTLY
    in a real encoder rather than being a bound.  It is also the only one stated
    about a WHOLE STREAM rather than per symbol, which is exactly what makes it
    hard to audit: reading it tells you nothing about which symbol might be
    missing a code.

    WHAT THIS FILE DOES.  It replaces that hypothesis with [CLCovers], a
    per-symbol condition — "every code-length symbol the stream uses has a code of
    width 1..7 in [cl]" — and proves the reduction.  Nothing here is deep; the
    point is entirely that the obligation becomes NAMEABLE.  After this, the
    residual is a statement about [build_bl_tree] that someone can prove or
    refute, instead of an opaque equation about a bit list.

    WHY 1..7 AND NOT 1..15: the code-length tree's bound is [MAX_BL_BITS = 7]
    ([Trees.v:85]), and [DeflateSpec.read_lengths] decodes it with
    [code_table cl 7].  [HuffMaxBits.v] is what makes the L-B theorems apply
    there.

    THE REMAINING OBLIGATION, named so it can be assigned rather than assumed.
    [CLCovers cl (send_tree_items t maxc)] follows from two facts, and neither is
    in this layer:
      (S) [scan_tree]'s frequency counts are exactly the symbol multiset of
          [send_tree_items] — scan counts what send will emit.  Provable here in
          principle; [scan_go] and [send_items] have identical control flow (per
          [Trees.v]'s own header), so it is the same parallel induction as
          §HUFFID-SENDGO-B1, plus a no-wrap bound because [t_setfreq] applies
          [u16].  NOT PROVED.  I priced it at ~150 lines and did this reduction
          first because the reduction is what makes (S) worth having.
      (B) [build_bl_tree] assigns a POSITIVE LENGTH to every symbol with POSITIVE
          FREQUENCY, and a length at most 7.  That is [build_tree]/[gen_bitlen]
          territory, outside L-B per §RT-IDENTITY-PLAN, and it is the standard
          property of a Huffman construction rather than anything exotic.
    (S) and (B) together give coverage.  Stating them separately is the point:
    "the CL tree covers the stream" was unauditable, and these two are not. *)

(** CORRECTION APPENDED 2026-08-18 (huffman-id), not an edit of the text above.

    THE HEADER SAYS of obligation (S): "NOT PROVED.  I priced it at ~150 lines and
    did this reduction first."  (S) IS PROVED: [ScanCount.scan_tree_counts] gives the
    exact multiset equation and [ScanCount.scan_tree_positive] the positivity form
    this file asked for.

    AND THE PRICE WAS WRONG IN THE OTHER DIRECTION TOO: the composition of (S), (B)
    and [cl_bits_total] needed one repair that none of the three files could see --
    [scan_tree_positive] requires a FRESH frequency table, and [Trees.v:806-810]
    scans TWICE into the same [bl_tree].  Repaired in ScanBase.v.  So the residual
    named here was both already closed AND missing a hypothesis, which is what
    writing the composition (CoverChain.v) established. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import HuffGenCodes ClStream.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The code-length symbols an item stream uses

    One symbol per item, and it is the symbol [emit_item] sends: a literal length
    for [CLit], and RFC 1951 §3.2.7's 16/17/18 for the three repeat forms.  The
    short-run arm of [send_go] produces [count'] separate [CLit]s, so [count']
    copies appear here — which is exactly what [scan_go] adds to that slot. *)
Definition item_syms (it : CLItem) : list Z :=
  match it with
  | CLit l   => [Z.of_nat l]
  | CRep _ _ => [REP_3_6]
  | CZ3 _    => [REPZ_3_10]
  | CZ11 _   => [REPZ_11_138]
  end.

Definition items_syms (items : list CLItem) : list Z := flat_map item_syms items.

(** ** The per-symbol coverage condition *)

Definition CLCovers (cl : list nat) (items : list CLItem) : Prop :=
  forall s, In s (items_syms items) ->
    exists len, nth_error cl (Z.to_nat s) = Some len /\ (1 <= len <= 7)%nat.

(** A covered symbol has a codeword.  Indexed by [nat], because
    [cl_item_bits] applies [code_for] at literal [nat] indices (16/17/18) and a
    [Z]-indexed helper leaves [Z.to_nat REP_3_6] where the goal has [16%nat] —
    convertible but not syntactically equal, so the rewrite misses. *)
Lemma code_for_of_covered : forall cl (k : nat) len,
  nth_error cl k = Some len -> (1 <= len <= 7)%nat ->
  exists cw, code_for cl 7%nat k = Some cw.
Proof.
  intros cl k len He Hlen. unfold code_for. rewrite He.
  replace (orb (Nat.eqb len 0) (Nat.ltb 7 len)) with false
    by (symmetry; apply orb_false_iff; split;
        [apply Nat.eqb_neq | apply Nat.ltb_ge]; lia).
  eexists. reflexivity.
Qed.

(** ...hence so does every item, in each of the four shapes. *)
Lemma cl_item_bits_of_covered : forall cl it,
  (forall s, In s (item_syms it) ->
     exists len, nth_error cl (Z.to_nat s) = Some len /\ (1 <= len <= 7)%nat) ->
  exists b, cl_item_bits cl it = Some b.
Proof.
  intros cl it H.
  destruct it as [l|p k|k|k]; cbn [cl_item_bits item_syms] in *.
  - destruct (H (Z.of_nat l) (or_introl eq_refl)) as [len [He Hlen]].
    rewrite Nat2Z.id in He.
    destruct (code_for_of_covered cl l len He Hlen) as [cw Hcw].
    rewrite Hcw. eexists. reflexivity.
  - destruct (H REP_3_6 (or_introl eq_refl)) as [len [He Hlen]].
    change (Z.to_nat REP_3_6) with 16%nat in He.
    destruct (code_for_of_covered cl 16%nat len He Hlen) as [cw Hcw].
    rewrite Hcw. eexists. reflexivity.
  - destruct (H REPZ_3_10 (or_introl eq_refl)) as [len [He Hlen]].
    change (Z.to_nat REPZ_3_10) with 17%nat in He.
    destruct (code_for_of_covered cl 17%nat len He Hlen) as [cw Hcw].
    rewrite Hcw. eexists. reflexivity.
  - destruct (H REPZ_11_138 (or_introl eq_refl)) as [len [He Hlen]].
    change (Z.to_nat REPZ_11_138) with 18%nat in He.
    destruct (code_for_of_covered cl 18%nat len He Hlen) as [cw Hcw].
    rewrite Hcw. eexists. reflexivity.
Qed.

(** ** THE REDUCTION

    Per-symbol coverage gives the whole-stream hypothesis the capstone wants. *)
Theorem cl_bits_total : forall cl items,
  CLCovers cl items -> exists bits, cl_bits cl items = Some bits.
Proof.
  intros cl items. induction items as [|it tl IH]; intros Hcov.
  - exists []. reflexivity.
  - cbn [cl_bits].
    destruct (cl_item_bits_of_covered cl it) as [b1 Hb1].
    { intros s Hs. apply Hcov. cbn [items_syms flat_map]. apply in_or_app.
      left. exact Hs. }
    destruct (IH) as [b2 Hb2].
    { intros s Hs. apply Hcov. cbn [items_syms flat_map]. apply in_or_app.
      right. exact Hs. }
    rewrite Hb1, Hb2. eexists. reflexivity.
Qed.

(** ** NON-VACUITY: the witness stream is covered by its own tree

    [clw] / [itemsw] are ClStream.v's witness.  Discharging [CLCovers] on them
    shows the condition is satisfiable by a real (tree, stream) pair rather than
    only stated. *)
Example itemsw_syms : items_syms itemsw = [3; 16; 17; 2].
Proof. vm_compute. reflexivity. Qed.

Lemma clw_covers_itemsw : CLCovers clw itemsw.
Proof.
  intros s Hs. rewrite itemsw_syms in Hs.
  cbn [In] in Hs.
  destruct Hs as [<-|[<-|[<-|[<-|[]]]]];
    (exists 2%nat; split; [reflexivity | lia]).
Qed.

(** ...and the reduction then supplies the capstone's hypothesis. *)
Example clw_itemsw_has_bits : exists bits, cl_bits clw itemsw = Some bits.
Proof. apply cl_bits_total, clw_covers_itemsw. Qed.

Print Assumptions cl_bits_total.
Print Assumptions clw_covers_itemsw.
