(** * IfCtxVacuity — test wp4's vacuity trap BEFORE spending the slot.

    wp5-pf, 2026-08-17.  Scratch.

    wp4 nominated [InflateFast.if_ctx_wf]'s three conjuncts, instantiated at
    zlib's FIXED tables, as the next consumer edge — and flagged that
    [lcode_two_level] may be VACUOUS there, because its hypothesis
    [lc_chains (c_op ...) = true] is the subtable-pointer test and
    [DecodeBridge.lenfix_has_no_subtables] is already Qed.

    Shipping a vacuous conjunct as a consumer edge would be the vacuous
    version of the defect edge 2 just fixed, so this file answers the
    question by COMPUTATION before any proof is written.  Nothing here is a
    contribution; it is the go/no-go. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inflate InflateFast.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** ** Q1.  Does [lcode_two_level]'s hypothesis EVER fire at [lenfix]? *)
Definition lenfix_chain_hits : nat :=
  length (filter (fun i => lc_chains (c_op (lenfix (Z.of_nat i)))) (seq 0 512)).

Example q1_lenfix_chain_hits : lenfix_chain_hits = 0%nat.
Proof. vm_compute. reflexivity. Qed.

Example q1_distfix_chain_hits :
  length (filter (fun i => lc_chains (c_op (distfix (Z.of_nat i)))) (seq 0 32))
  = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** ** Q2.  Does [lcode_len_bounded]'s hypothesis fire, and how often?

    [lc_len_ok]'s premise is [Z.land (c_op h) 16 <> 0] — the length-base
    test.  A count, not an existence: "at least one" would not distinguish a
    corner case from the main path. *)
Definition lenfix_len_hits : nat :=
  length (filter (fun i => negb (Z.eqb (Z.land (c_op (lenfix (Z.of_nat i))) 16) 0))
                 (seq 0 512)).

(* Measured 104, and 104 is exactly what RFC 1951's fixed-code layout
   predicts, which is why the number is worth pinning rather than just
   passing.  Length symbols 257..279 carry 7-bit codes and are replicated
   2^(9-7) = 4 times in the 9-bit root table: 23 * 4 = 92.  Symbols 280..285
   carry 8-bit codes, replicated twice: 6 * 2 = 12.  92 + 12 = 104.  A count
   that matches an independent derivation from the standard is evidence the
   filter is testing the table I think it is; my first guess was 224 and the
   Compute corrected it. *)
Example q2_lenfix_len_hits_count : lenfix_len_hits = 104%nat.
Proof. vm_compute. reflexivity. Qed.

(** ** Q3.  And does the CONCLUSION actually hold at every firing entry?

    The go/no-go for [lcode_len_bounded] itself: if this is false at the
    fixed tables, that is a finding about the model rather than a
    formality — which is the outcome wp4 said would make the edge worth
    taking. *)
Definition len_bound_ok (h : Code) : bool :=
  implb (negb (Z.eqb (Z.land (c_op h) 16) 0))
        (Z.leb 3 (c_val h)
         && Z.leb (c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1) 258).

Example q3_lenfix_len_bound_holds_everywhere :
  forallb (fun i => len_bound_ok (lenfix (Z.of_nat i))) (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Locate q1_lenfix_chain_hits.
Print Assumptions q1_lenfix_chain_hits.
Locate q2_lenfix_len_hits_count.
Print Assumptions q2_lenfix_len_hits_count.
Locate q3_lenfix_len_bound_holds_everywhere.
Print Assumptions q3_lenfix_len_bound_holds_everywhere.
