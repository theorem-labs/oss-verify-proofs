(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(331052, 30%nat) ; (331172, 6%nat) ; (394836, 371%nat) ; (396428, 303%nat) ; (500892, 5%nat) ; (500912, 319%nat) ; (523084, 6%nat) ; (618152, 215%nat) ; (686236, 6%nat) ; (737108, 12%nat) ; (1135792, 50%nat) ; (1135992, 1%nat) ; (1136196, 51%nat) ; (1136400, 19%nat) ; (1136476, 29%nat) ; (1167540, 100%nat) ; (1169044, 105%nat) ; (1170588, 12%nat) ; (1205560, 490%nat) ; (1209508, 162%nat) ; (1210156, 38%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
