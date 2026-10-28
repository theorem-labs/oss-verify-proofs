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
Definition ITR : list (Z * nat) := [(531420, 45%nat) ; (507336, 35%nat) ; (494248, 366%nat) ; (237076, 20%nat) ; (237156, 5%nat) ; (603044, 71%nat) ; (596960, 10%nat) ; (592016, 115%nat) ; (637500, 229%nat) ; (638416, 316%nat) ; (701520, 12%nat) ; (704784, 162%nat) ; (705432, 29%nat) ; (705624, 29%nat) ; (705740, 567%nat) ; (708808, 15%nat) ; (710068, 122%nat) ; (495712, 81%nat) ; (496036, 81%nat) ; (496360, 80%nat) ; (496680, 80%nat) ; (497000, 81%nat) ; (497324, 81%nat) ; (497648, 81%nat) ; (497972, 81%nat) ; (498296, 81%nat) ; (498620, 81%nat) ; (498944, 80%nat) ; (499264, 80%nat) ; (499584, 81%nat) ; (499908, 81%nat) ; (500232, 81%nat) ; (500556, 81%nat) ; (500880, 81%nat) ; (501204, 81%nat) ; (501528, 81%nat) ; (501852, 81%nat) ; (502176, 81%nat) ; (502500, 81%nat) ; (502824, 81%nat) ; (503148, 81%nat) ; (503472, 81%nat) ; (503796, 81%nat) ; (504120, 81%nat) ; (504444, 81%nat) ; (504768, 81%nat) ; (505092, 81%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
