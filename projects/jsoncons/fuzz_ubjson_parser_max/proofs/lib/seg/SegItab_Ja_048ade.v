(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Asan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(330332, 30%nat) ; (330452, 6%nat) ; (389256, 172%nat) ; (394116, 371%nat) ; (395708, 303%nat) ; (446656, 34%nat) ; (500172, 5%nat) ; (500192, 319%nat) ; (522364, 6%nat) ; (617432, 215%nat) ; (685516, 6%nat) ; (729372, 12%nat) ; (852432, 7%nat) ; (1128056, 50%nat) ; (1128256, 1%nat) ; (1128460, 51%nat) ; (1128664, 19%nat) ; (1128740, 29%nat) ; (1159804, 100%nat) ; (1161308, 105%nat) ; (1162852, 12%nat) ; (1197824, 490%nat) ; (1201772, 162%nat) ; (1202420, 38%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
