(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import EbtFp.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac zsubf_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hout" in let H2 := fresh "Hrest" in destruct H as [H1 H2]; zsubf_split H2
  | _ => idtac
  end.
Ltac zsubf_one z :=
  first [ exact I
        | match goal with Hi : ~ (_ <= z < _) |- ~ (_ <= z < _) => solve [ let X := fresh "X" in intros X; apply Hi; clear - X; Lia.lia ] end
        | match goal with Hi : ~ (_ <= z < _) |- ~ (_ <= z < _) => solve [ let X := fresh "X" in intros X; apply Hi; L5FastLiaT.plia1 ] end
        | L5FastLiaT.plia2 ].
Ltac zsubf := let z := fresh "z" in let Hz := fresh "Hz" in let H := fresh "H" in
  intros z Hz H; cbn [art_out app fst snd] in H |- *; zsubf_split H; repeat split; zsubf_one z.

Goal forall a b : Z, 0 <= a -> forall z, 0 <= z < 2 ^ 64 -> art_out [(a, 100); (b, 8)] z -> art_out [(a + 10, 20); (b, 8); (a, 10)] z.
Proof. intros a b Ha. zsubf. Qed.
