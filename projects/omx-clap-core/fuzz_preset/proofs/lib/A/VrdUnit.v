(* fuzz_preset, slice S5b: the DEPTH INDUCTION that closes the reader's recursive unit.

   parse_value and parse_items are mutually recursive in one direction only: parse_value at nesting d calls
   parse_items at d (the container arm), and parse_items at d calls parse_value at d + 1 (the element loop), with the
   depth bounded by PjGrammar.MAXD - parse_items refuses at depth 32 (row 39 of its listing, `blt 31, a1`). So the
   unit closes by induction on MAXD - d, downwards from the deepest nesting: at d = MAXD the element loop's call is
   never made, and each step needs only the NEXT depth.

   The two step lemmas the segment lanes produce are exactly the hypotheses here:
     PI: parse_items at d, given parse_value at (d + 1) when d < MAXD (lanes IproB, IelemB)
     PV: parse_value at d, given parse_items at d (lanes VproB, VstrB, VnumB)
   and nothing else is assumed: no axiom, no admitted step, no released lemma. This file is pure logic over the two
   frozen texts (lib/A/PRH_FnParse.v), so it compiles and is proved BEFORE the walks land, and when they land the
   unit's two theorems follow by `apply vrd_unit_closed` with the lanes' lemmas as the two arguments.

   rule 24: no function is proved here either - this file proves an implication between the two texts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

(* The induction is on the remaining depth, so it is stated over abstract predicates: PV d holds "parse_value's text
   at nesting d", PI d "parse_items' text at nesting d". The slice instantiates them with tparse_value_specX d CTX and
   tparse_items_specX d CTX; keeping them abstract is what lets this file compile while the texts' premises are still
   being reconciled with the kit. *)
Section unit.
Variable PV PI : nat -> Prop.

(* parse_items at d from parse_value at the next depth, which the element loop needs only when d < MAXD *)
Hypothesis step_PI : forall d, ((d < MAXD)%nat -> PV (S d)) -> PI d.
(* parse_value at d from parse_items at the same depth, which the container arm calls *)
Hypothesis step_PV : forall d, PI d -> PV d.

(* the engine of the induction: both texts hold at every depth with at most n levels left below it *)
Lemma vrd_unit_upto : forall n d, (MAXD - d <= n)%nat -> PV d /\ PI d.
Proof.
induction n as [|n IH]; intros d Hn.
- assert (Hpi : PI d).
  { apply step_PI. intros Hlt. lia. }
  split; [apply step_PV | ]; exact Hpi.
- assert (Hpi : PI d).
  { apply step_PI. intros Hlt. apply (IH (S d)). lia. }
  split; [apply step_PV | ]; exact Hpi.
Qed.

(* the unit, at every depth the text admits *)
Theorem vrd_unit_closed : forall d, PV d /\ PI d.
Proof. intros d. apply (vrd_unit_upto (MAXD - d) d). lia. Qed.

End unit.

(* The two corollaries the slice delivers, in the shape the top theorem consumes: at the top value d = 0. *)
Corollary vrd_parse_value_closed : forall (PV PI : nat -> Prop),
  (forall d, ((d < MAXD)%nat -> PV (S d)) -> PI d) -> (forall d, PI d -> PV d) -> forall d, PV d.
Proof. intros PV PI HI HV d. exact (proj1 (vrd_unit_closed PV PI HI HV d)). Qed.

Corollary vrd_parse_items_closed : forall (PV PI : nat -> Prop),
  (forall d, ((d < MAXD)%nat -> PV (S d)) -> PI d) -> (forall d, PI d -> PV d) -> forall d, PI d.
Proof. intros PV PI HI HV d. exact (proj2 (vrd_unit_closed PV PI HI HV d)). Qed.
