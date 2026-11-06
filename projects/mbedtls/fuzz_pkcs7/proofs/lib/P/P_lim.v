(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
Open Scope Z_scope.

Class Lim : Type := mkLim {
  lim_val : Z;
  lim_ge31 : 2 ^ 31 <= lim_val
}.

(* [comment removed for export] *)
Definition LIM {LM : Lim} : Z := lim_val.
Lemma LIM_ge {LM : Lim} : 2 ^ 31 <= LIM.
Proof. exact lim_ge31. Qed.

(* [comment removed for export] *)
Lemma source_alloc_limit_ge31 : 2 ^ 31 <= source_alloc_limit.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma sanitizer_source_limit_ge31 : 2 ^ 31 <= sanitizer_source_limit.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition Lim_shipped : Lim := mkLim source_alloc_limit source_alloc_limit_ge31.
Definition Lim_sanitizer : Lim := mkLim sanitizer_source_limit sanitizer_source_limit_ge31.
