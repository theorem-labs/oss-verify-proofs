(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Class HeapCeil : Type := mkHeapCeil {
  hceil : Z ;
  hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000
}.

(* [comment removed for export] *)
Ltac hcb :=
  let K := fresh "HCEILB" in
  pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as K.

Section Facts.
  Context {HCEIL : HeapCeil}.
  Lemma hceil_pos : 0 < hceil.                Proof. hcb. lia. Qed.
End Facts.
(* [comment removed for export] *)
