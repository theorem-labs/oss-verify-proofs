(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(436556, 1%nat) ; (436560, 1%nat) ; (451724, 39%nat) ; (451880, 690%nat) ; (454640, 45%nat) ; (479728, 102%nat) ; (520744, 1%nat) ; (520752, 1%nat) ; (523392, 188%nat) ; (525360, 380%nat) ; (558724, 40%nat) ; (600576, 24%nat) ; (600756, 13%nat) ; (600916, 7%nat) ; (1300360, 78%nat) ; (1301720, 108%nat) ; (1302152, 908%nat) ; (1305784, 16%nat) ; (1305848, 61%nat) ; (1327036, 7%nat) ; (1336512, 257%nat) ; (1337540, 62%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
