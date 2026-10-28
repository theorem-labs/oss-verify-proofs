(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition ITR : list (Z * nat) := [(332892, 30%nat) ; (333012, 6%nat) ; (391648, 172%nat) ; (396508, 371%nat) ; (398100, 303%nat) ; (449048, 34%nat) ; (502564, 5%nat) ; (502584, 319%nat) ; (524756, 6%nat) ; (619824, 215%nat) ; (687908, 6%nat) ; (749680, 12%nat) ; (874172, 8%nat) ; (1148288, 7%nat) ; (1148364, 50%nat) ; (1148564, 1%nat) ; (1148768, 51%nat) ; (1148972, 19%nat) ; (1149048, 29%nat) ; (1181616, 105%nat) ; (1183160, 12%nat) ; (1218132, 490%nat) ; (1222080, 162%nat) ; (1222728, 38%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
