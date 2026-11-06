From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Class AllocLim : Type := mk_alloc_lim { LIM : Z; LIM_ge : Z.le (Z.pow 2 31) LIM }.

Lemma source_limit_large : Z.le (Z.pow 2 31) source_alloc_limit.
Proof. apply Z.leb_le. reflexivity. Qed.

Lemma sanitizer_limit_large : Z.le (Z.pow 2 31) SanitizerBudgets.lim_source.
Proof. apply Z.leb_le. reflexivity. Qed.

Definition SrcLim : AllocLim := {| LIM := source_alloc_limit; LIM_ge := source_limit_large |}.
Definition SanLim : AllocLim := {| LIM := SanitizerBudgets.lim_source; LIM_ge := sanitizer_limit_large |}.
