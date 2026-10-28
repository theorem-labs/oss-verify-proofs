(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(222224, 88%nat) ; (222576, 40%nat) ; (222736, 49%nat) ; (381188, 24%nat) ; (223820, 17%nat) ; (701568, 257%nat) ; (220720, 19%nat) ; (220796, 19%nat) ; (223004, 73%nat) ; (223296, 51%nat) ; (223500, 54%nat) ; (223716, 20%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
