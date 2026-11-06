(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(318432, 1%nat) ; (318436, 1%nat) ; (328884, 39%nat) ; (329040, 690%nat) ; (331800, 45%nat) ; (344208, 102%nat) ; (385224, 1%nat) ; (385232, 1%nat) ; (387872, 188%nat) ; (389840, 380%nat) ; (421860, 40%nat) ; (463712, 24%nat) ; (463892, 13%nat) ; (464052, 7%nat) ; (800676, 78%nat) ; (801848, 108%nat) ; (802280, 908%nat) ; (805912, 16%nat) ; (805976, 61%nat) ; (824260, 7%nat) ; (833320, 257%nat) ; (834348, 62%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
