(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(435596, 1%nat) ; (435600, 1%nat) ; (450764, 39%nat) ; (450920, 690%nat) ; (453680, 45%nat) ; (478768, 102%nat) ; (519784, 1%nat) ; (519792, 1%nat) ; (522432, 188%nat) ; (524400, 380%nat) ; (557764, 40%nat) ; (599616, 24%nat) ; (599796, 13%nat) ; (599956, 7%nat) ; (1294796, 78%nat) ; (1296156, 108%nat) ; (1296588, 908%nat) ; (1300220, 16%nat) ; (1300284, 61%nat) ; (1321472, 7%nat) ; (1330948, 257%nat) ; (1331976, 62%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
