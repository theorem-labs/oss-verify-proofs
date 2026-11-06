(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(525812, 45%nat) ; (501728, 35%nat) ; (488640, 366%nat) ; (231468, 20%nat) ; (231548, 5%nat) ; (597436, 71%nat) ; (591352, 10%nat) ; (586408, 115%nat) ; (631892, 229%nat) ; (632808, 316%nat) ; (695912, 12%nat) ; (699176, 162%nat) ; (699824, 29%nat) ; (700016, 29%nat) ; (700132, 567%nat) ; (703200, 15%nat) ; (704460, 122%nat) ; (490104, 81%nat) ; (490428, 81%nat) ; (490752, 80%nat) ; (491072, 80%nat) ; (491392, 81%nat) ; (491716, 81%nat) ; (492040, 81%nat) ; (492364, 81%nat) ; (492688, 81%nat) ; (493012, 81%nat) ; (493336, 80%nat) ; (493656, 80%nat) ; (493976, 81%nat) ; (494300, 81%nat) ; (494624, 81%nat) ; (494948, 81%nat) ; (495272, 81%nat) ; (495596, 81%nat) ; (495920, 81%nat) ; (496244, 81%nat) ; (496568, 81%nat) ; (496892, 81%nat) ; (497216, 81%nat) ; (497540, 81%nat) ; (497864, 81%nat) ; (498188, 81%nat) ; (498512, 81%nat) ; (498836, 81%nat) ; (499160, 81%nat) ; (499484, 81%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
