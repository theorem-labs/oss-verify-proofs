(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(526608, 45%nat) ; (502524, 35%nat) ; (489436, 366%nat) ; (232264, 20%nat) ; (232344, 5%nat) ; (598232, 71%nat) ; (592148, 10%nat) ; (587204, 115%nat) ; (632688, 229%nat) ; (633604, 316%nat) ; (696708, 12%nat) ; (699972, 162%nat) ; (700620, 29%nat) ; (700812, 29%nat) ; (700928, 567%nat) ; (703996, 15%nat) ; (705256, 122%nat) ; (490900, 81%nat) ; (491224, 81%nat) ; (491548, 80%nat) ; (491868, 80%nat) ; (492188, 81%nat) ; (492512, 81%nat) ; (492836, 81%nat) ; (493160, 81%nat) ; (493484, 81%nat) ; (493808, 81%nat) ; (494132, 80%nat) ; (494452, 80%nat) ; (494772, 81%nat) ; (495096, 81%nat) ; (495420, 81%nat) ; (495744, 81%nat) ; (496068, 81%nat) ; (496392, 81%nat) ; (496716, 81%nat) ; (497040, 81%nat) ; (497364, 81%nat) ; (497688, 81%nat) ; (498012, 81%nat) ; (498336, 81%nat) ; (498660, 81%nat) ; (498984, 81%nat) ; (499308, 81%nat) ; (499632, 81%nat) ; (499956, 81%nat) ; (500280, 81%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
