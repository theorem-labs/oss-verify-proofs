(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(522428, 45%nat) ; (498344, 35%nat) ; (485256, 366%nat) ; (228084, 20%nat) ; (228164, 5%nat) ; (594052, 71%nat) ; (587968, 10%nat) ; (583024, 115%nat) ; (628508, 229%nat) ; (629424, 316%nat) ; (692528, 12%nat) ; (695792, 162%nat) ; (696440, 29%nat) ; (696632, 29%nat) ; (696748, 567%nat) ; (699816, 15%nat) ; (701076, 122%nat) ; (486720, 81%nat) ; (487044, 81%nat) ; (487368, 80%nat) ; (487688, 80%nat) ; (488008, 81%nat) ; (488332, 81%nat) ; (488656, 81%nat) ; (488980, 81%nat) ; (489304, 81%nat) ; (489628, 81%nat) ; (489952, 80%nat) ; (490272, 80%nat) ; (490592, 81%nat) ; (490916, 81%nat) ; (491240, 81%nat) ; (491564, 81%nat) ; (491888, 81%nat) ; (492212, 81%nat) ; (492536, 81%nat) ; (492860, 81%nat) ; (493184, 81%nat) ; (493508, 81%nat) ; (493832, 81%nat) ; (494156, 81%nat) ; (494480, 81%nat) ; (494804, 81%nat) ; (495128, 81%nat) ; (495452, 81%nat) ; (495776, 81%nat) ; (496100, 81%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
