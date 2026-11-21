(** * ItGClassHead — the (viii) HEAD for q4's ownership S-instance
    product: the per-cell fill classification the B3 assemblies consume.

    DRAFTED by an earlier development run per q7's freeze-v27 line ("whoever drafts it
    first sends the head"); an earlier development run corrects/ratifies.  STATEMENT
    ONLY — the Prop compiles here so both lanes bind one spelling; the
    proposed theorem shape is in the comment below, in q4's premise
    vocabulary to adjust as their ledger wants.

    DESIGN NOTES (the three decisions a reader needs):
    1. THREE disjuncts, not four.  The accepted-EMPTY world never meets
       this classification: the B3 DIST head carries the PreGo/PreEmpty
       disjunction, and the PreEmpty branch is assembled separately
       (two-marker pair + g1's vacuity family, no fill ever ran).  In
       the PreGo world it_pre_go_inv gives it_mx <> 0, so some code
       exists and the residue is exactly empty (complete) or the single
       it_finish cell (max==1 incomplete).
    2. The residue disjunct is the TABLE READ WITH INDEX TIE, per the
       agreed interface (q4 msg "form (b) confirmed with the index
       tie"): output-level record, root = 1, i = 1.  Population facts
       (count_len lens 1 = 1, higher counts zero) are NOT here — they
       are g1's obligation, derived walk-side (marker => incomplete +
       kraft), so the classification stays purely positional/structural.
    3. LEAF and POINTER arms are VERBATIM the frozen zr_two_own_v3 arms
       () minus the width conjunct — width is derived from
       children (ItGWidth.width_covers_of_children), so it must not
       appear here (no-circularity seam, falsifier-boarded).

    Consumed by: g1's two_own_v3_of_parts (ItGWidth.v) — its
    classification premise is EXACTLY this Prop's disjunction with the
    max1 population facts adjoined by g1 at assembly.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* zr_ptr_children verbatim from B3B5Stmts.v (), duplicated
   under the same until-landing-home rule as ItGWidth.v. *)
Definition zr_ptr_children (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) (i op val : Z) : Prop :=
  forall j, 0 <= j < 2 ^ op ->
    exists sym cw, code_for lens 15%nat sym = Some cw
      /\ root < Z.of_nat (length cw) <= root + op
      /\ T (val + j) = ent sym
      /\ c_bits (ent sym) = Z.of_nat (length cw) - root
      /\ firstn (length cw)
           (write_bits (Z.to_nat root) i ++ write_bits (Z.to_nat op) j)
         = cw.

(** THE HEAD.  Every root cell of a PreGo build's output table is a
    fill-written leaf, a fill-written sub-table pointer, or the single
    max==1 fix-up marker at cell 1. *)
Definition zr_fill_class (T : ztbl) (root : Z) (lens : list nat)
           (ent : nat -> Code) : Prop :=
  forall i, 0 <= i < 2 ^ root ->
    (exists sym cw, code_for lens 15%nat sym = Some cw
       /\ Z.of_nat (length cw) <= root
       /\ T i = ent sym
       /\ c_bits (ent sym) = Z.of_nat (length cw)
       /\ firstn (length cw) (write_bits (Z.to_nat root) i) = cw)
    \/ (c_bits (T i) = root
        /\ 1 <= c_op (T i) <= 15 - root
        /\ 2 ^ root <= c_val (T i)
        /\ zr_ptr_children T root lens ent i (c_op (T i)) (c_val (T i)))
    \/ (T i = mkCodeT 64 1 0 /\ root = 1 /\ i = 1).

(* PROPOSED THEOREM SHAPE for q4's S-instance product (adjust premises
   to your ledger's vocabulary; the CONCLUSION spelling is the contract):

   Theorem fill_class_holds :
     forall ty (l1 l2 : list nat) root0 t0 c st out ent,
       (ty = CT_LENS \/ ty = CT_DISTS) ->
       (ty = CT_DISTS -> Z.of_nat (length l1) <= 30) ->
       (forall len, In len l1 -> (len <= 15)%nat) ->
       it_pre ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 t0
         = PreGo c st ->
       it_model ty (zlens (l1 ++ l2)) (Z.of_nat (length l1)) root0 t0
         = Some out ->
       o_ret out = 0 ->
       (forall sym, ent sym
          = ZReproQ6K.it_entry c (Z.of_nat sym) (c_bits (ent sym))) ->
       zr_fill_class (o_tbl out) (o_bits out) l1 ent.

   g1 then adjoins, per marker cell reached through the third disjunct:
   the population facts (count_len l1 1 = 1, counts 2..15 zero) from
   marker=>incomplete (walk-side, g1's next bed) + kraft arithmetic,
   and applies two_own_v3_of_parts. *)
