(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(730968, 168%nat) ; (708416, 119%nat) ; (708892, 171%nat) ; (709576, 60%nat) ; (710016, 102%nat) ; (709816, 50%nat) ; (710424, 135%nat) ; (710964, 78%nat) ; (711276, 13%nat) ; (711328, 50%nat) ; (702432, 47%nat) ; (702808, 34%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
