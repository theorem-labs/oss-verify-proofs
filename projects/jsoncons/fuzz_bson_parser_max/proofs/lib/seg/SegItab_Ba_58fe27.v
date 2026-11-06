(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(331924, 30%nat) ; (332044, 6%nat) ; (395540, 371%nat) ; (397132, 303%nat) ; (501596, 5%nat) ; (501616, 319%nat) ; (523788, 6%nat) ; (618856, 215%nat) ; (686940, 6%nat) ; (740036, 12%nat) ; (1138644, 7%nat) ; (1138720, 50%nat) ; (1138920, 1%nat) ; (1139124, 51%nat) ; (1139328, 19%nat) ; (1139404, 29%nat) ; (1171972, 105%nat) ; (1173516, 12%nat) ; (1208488, 490%nat) ; (1212436, 162%nat) ; (1213084, 38%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
