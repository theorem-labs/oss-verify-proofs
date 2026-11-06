(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Spec Require Import Prelim Canon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zlength_zeros_out : forall j, zlength (zeros_out j) = 2 * Z.of_nat j.
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. unfold zlength in *. rewrite length_app, Nat2Z.inj_add, IH.
  cbn [length]. lia.
Qed.

Lemma zeros_out_app : forall j, zeros_out j ++ [48; 10] = zeros_out (S j).
Proof.
  induction j as [|j IH]; [reflexivity|]. rewrite zeros_out_S. rewrite <- app_assoc, IH. reflexivity.
Qed.
