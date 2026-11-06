(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
#[local] Notation mem := (word -> option byte).
Definition LIB_A : mem -> Prop := fun _ => True.
Lemma LIB_A_intro : forall m : mem, LIB_A m.
Proof. intros m. exact I. Qed.
