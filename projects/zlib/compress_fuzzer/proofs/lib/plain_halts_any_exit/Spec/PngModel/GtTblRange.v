(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.GtTblRange — the table UPPER bound: the
      cheap half proved, and a correction to how the item was framed

    ============================================================================
    WHY THIS FILE EXISTS.  wp5-pf reports TWO lanes independently stopping at one
    statement from different directions — their fast/main-loop length-code bound,
    and expansion-1's `tbl_range` conjunct — and passes on expansion-1's framing:

        it is a missing DIRECTION, not a missing fact: ItGTblLeafPos and
        ItGTblRepl already carry `1 <= c_val` and `0 <= c_val` for built tables
        (LOWER bounds), and the upper bound is the same induction pointed the
        other way

    Those are MY landed lemmas, so the item is over my own work and nobody has
    claimed it.  Two lanes stopped at one statement is worth more than either stop.

    THE FRAMING IS HALF RIGHT, AND THE CORRECTION MAKES THE ITEM SMALLER AND
    REUSABLE.  The upper bound is not an arithmetic argument at all: the
    transcription's only table constructor is

        mkCodeT op bits val = {| c_op := u8 op ; c_bits := u8 bits ; c_val := u16 val |}
        u8 v = v mod 256          u16 v = v mod 65536         (Base.v:79-80, 103-104)

    so **every field of every mkCodeT-written entry is in range BY CONSTRUCTION**,
    unconditionally, for any arguments whatever.  Proved below in three
    `Z.mod_pos_bound`s.  There is no bound to establish and no direction to turn.

    SO THE REAL RESIDUE IS A PROVENANCE LEMMA, NOT A BOUNDS LEMMA:

        every entry of a built table is either an entry of t0, or a mkCodeT

    and with that one disjunction, EVERY mkCodeT-closed predicate is free — the
    range conjunct, expansion-1's length-code bound, and anything similar later.
    Stated as `TblProvenance` below.  **That is why the reframing matters rather
    than being pedantry: pointed at as a bounds lemma the item is one property;
    pointed at as provenance it is a lemma that retires a family.**

    AND THE HONEST PRICE, because "same induction pointed the other way" invites
    an underestimate.  My `it_model_leafpos` (ItGTblLeafPos.v:451) carries its
    predicate through FIVE write sites — `leafpos_tset`, `leafpos_marker`,
    `leafpos_finish`, `leafpos_loop`, plus the `it_pre` case split — and a
    provenance version needs the same five.  What collapses is the PER-SITE work,
    not the site count: LeafPos needed a real argument at each (the 240/64
    antecedents), provenance needs only "this write is a mkCodeT".  **So it is one
    induction of the same shape, not a corollary of the existing one** — the
    existing induction cannot carry it, because it carries a different predicate
    and a Qed'd theorem is not a reusable traversal.

    NOT CLAIMED SILENTLY: statement first, to wp5-pf and zlib-lead, per this
    lane's standing order.  The cheap half is Qed'd here so nobody re-derives it.
    ============================================================================

    GTBL-ARMS, 2026-08-19.  Landing candidate on the cheap half only; the
    provenance induction is a NAMED RESIDUE and is not proved here.  Read-only
    against the graded tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The predicate, in expansion-1's shape                                  *)
(* ######################################################################### *)

Definition TblRangeE (e : Code) : Prop :=
  0 <= c_op e < 256 /\ 0 <= c_bits e < 256 /\ 0 <= c_val e < 65536.

Definition TblRangeT (t : ztbl) : Prop := forall i, TblRangeE (t i).

(* ######################################################################### *)
(* 2.  THE CHEAP HALF — free at every write, unconditionally                   *)
(* ######################################################################### *)

(** No hypotheses on [op], [bits] or [val]: negative, huge, anything.  The
    truncations in the constructor are the whole proof. *)
Theorem mkCodeT_in_range : forall op bits val, TblRangeE (mkCodeT op bits val).
Proof.
  intros op bits val. unfold TblRangeE, mkCodeT, u8, u16. cbn [c_op c_bits c_val].
  repeat split; apply Z.mod_pos_bound; lia.
Qed.

(** And it is not vacuous on the arguments the model actually passes — pinned at a
    negative and at an over-range value, since those are the two cases a reader
    would doubt. *)
Example mkCodeT_in_range_at_awkward_arguments :
  (c_op (mkCodeT (-1) 0 0), c_val (mkCodeT 0 0 70000), c_bits (mkCodeT 999 999 999))
  = (255, 4464, 231).
Proof. vm_compute. reflexivity. Qed.

(** Preservation under the table setter is immediate, which is why the residue is
    about the WRITE SITES rather than about the setter. *)
Lemma tblrange_tset : forall t i e,
  TblRangeT t -> TblRangeE e -> TblRangeT (tset t i e).
Proof.
  intros t i e Ht He j. unfold tset. destruct (Z.eqb j i); [exact He|apply Ht].
Qed.

Corollary tblrange_tset_mkCodeT : forall t i op bits val,
  TblRangeT t -> TblRangeT (tset t i (mkCodeT op bits val)).
Proof.
  intros. apply tblrange_tset; [assumption|apply mkCodeT_in_range].
Qed.

(** THE INITIAL TABLE the [makefixed] and [state_fresh] call sites pass, so the
    eventual theorem's hypothesis is dischargeable rather than a shape nobody can
    supply.  [tnone] is [fun _ => mkCode 0 0 0] ([Base.v:137]) — note [mkCode],
    the raw constructor, not [mkCodeT], so this does NOT follow from
    [mkCodeT_in_range] and needs its own two lines. *)
Lemma tblrange_tnone : TblRangeT tnone.
Proof.
  intros i. unfold TblRangeT, TblRangeE, tnone. cbn [c_op c_bits c_val].
  repeat split; lia.
Qed.

(* ######################################################################### *)
(* 3.  THE RESIDUE, named and stated — NOT proved here                        *)
(* ######################################################################### *)

(** The one disjunction that retires the family.  A [Definition] of a Prop, never
    an [Admitted] theorem, so nothing here can be mistaken for proved. *)
Definition TblProvenance : Prop :=
  forall ty lens codes root0 t0 out i,
    it_model ty lens codes root0 t0 = Some out ->
    o_tbl out i = t0 i \/ exists op bits val, o_tbl out i = mkCodeT op bits val.

(** AND THE PAYOFF, proved: provenance gives the range for free, and would give
    any other mkCodeT-closed predicate the same way.  So a supplier who discharges
    [TblProvenance] closes expansion-1's conjunct and wp5-pf's length-code bound
    with one lemma rather than two. *)
Theorem provenance_gives_range :
  TblProvenance ->
  forall ty lens codes root0 t0 out,
    TblRangeT t0 ->
    it_model ty lens codes root0 t0 = Some out ->
    TblRangeT (o_tbl out).
Proof.
  intros Hprov ty lens codes root0 t0 out Ht0 Hmodel i.
  destruct (Hprov ty lens codes root0 t0 out i Hmodel) as [Heq | [op [bits [val Heq]]]].
  - rewrite Heq. apply Ht0.
  - rewrite Heq. apply mkCodeT_in_range.
Qed.

(** At the real call site, with the initial-table hypothesis discharged — the form
    a consumer wants, so nobody has to notice that [tnone] satisfies it. *)
Corollary provenance_gives_range_at_tnone :
  TblProvenance ->
  forall ty lens codes root0 out,
    it_model ty lens codes root0 tnone = Some out ->
    TblRangeT (o_tbl out).
Proof.
  intros Hprov ty lens codes root0 out Hmodel.
  apply (provenance_gives_range Hprov ty lens codes root0 tnone out
           tblrange_tnone Hmodel).
Qed.

(** NOTE ON WHY THIS IS NOT A COROLLARY OF MY LANDED LOWER BOUNDS, since that is
    what the two-lane framing suggests: [it_model_leafpos] is a Qed'd theorem
    about [LeafPosT], and a proved theorem is not a reusable traversal.  Its
    five-site induction would have to be re-run with the provenance predicate.
    The saving is that each site's obligation becomes "this write is a mkCodeT"
    instead of an arithmetic argument — the site COUNT is unchanged. *)

Print Assumptions mkCodeT_in_range.
Print Assumptions mkCodeT_in_range_at_awkward_arguments.
Print Assumptions tblrange_tset.
Print Assumptions tblrange_tset_mkCodeT.
Print Assumptions tblrange_tnone.
Print Assumptions provenance_gives_range.
Print Assumptions provenance_gives_range_at_tnone.
