(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Cells Step Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma rw_cells_mk_peel : forall segs m A s sizes bs,
  rw_cells segs m A (mk_CB_cells (s :: sizes) bs) ->
  rw_cells segs m A [CB s (firstn s bs)] /\ rw_cells segs m (A + Z.of_nat s) (mk_CB_cells sizes (skipn s bs)).
Proof.
  intros segs m A s sizes bs H. cbn [mk_CB_cells] in H.
  destruct (proj1 (rw_cells_app segs m A [CB s (firstn s bs)] (mk_CB_cells sizes (skipn s bs))) H) as [H1 H2].
  cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. exact (conj H1 H2).
Qed.

Ltac peelk FR N :=
  lazymatch type of FR with
  | rw_cells ?segs ?m ?A (mk_CB_cells (?s :: ?sizes) ?bs) =>
      let X := fresh in
      pose proof (rw_cells_mk_peel segs m A s sizes bs FR) as X; clear FR;
      destruct X as [N FR];
      (let j := fresh "jk" in set (j := firstn s bs) in N; clearbody j);
      (let j := fresh "jk" in set (j := skipn s bs) in FR; clearbody j);
      repeat match type of FR with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in FR end;
      repeat match type of FR with
      | rw_cells _ _ (?b + ?x + ?y) _ =>
          lazymatch x with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
          lazymatch y with Zpos _ => idtac | Zneg _ => idtac | Z0 => idtac end;
          let s' := eval vm_compute in (x + y)%Z in
          replace (b + x + y)%Z with (b + s')%Z in FR by (clear; lia)
      end
  end.
