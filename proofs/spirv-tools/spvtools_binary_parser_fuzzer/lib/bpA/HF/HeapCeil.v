(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Class HeapCeil : Type := mkHeapCeil {
  hceil : Z ;
  hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000
}.

Ltac hcb :=
  let K := fresh "HCEILB" in
  pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as K.

Section Facts.
  Context {HCEIL : HeapCeil}.

End Facts.
