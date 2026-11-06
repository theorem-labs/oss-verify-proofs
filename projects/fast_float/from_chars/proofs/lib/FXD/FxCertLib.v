(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition res_nil {A : Type} (r : option (list A)) : bool := match r with Some [] => true | _ => false end.
Lemma res_nil_eq : forall (A : Type) (r : option (list A)), res_nil r = true -> r = Some [].
Proof. intros A [[|x l]|]; cbn; intros H; [reflexivity | discriminate | discriminate]. Qed.
