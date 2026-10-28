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
Definition ITR : list (Z * nat) := [(1044072, 45%nat) ; (1019988, 35%nat) ; (1006900, 366%nat) ; (749728, 20%nat) ; (749808, 5%nat) ; (1115696, 71%nat) ; (1109612, 10%nat) ; (1104668, 115%nat) ; (1153132, 210%nat) ; (1154048, 316%nat) ; (1218768, 12%nat) ; (1222080, 162%nat) ; (1222728, 29%nat) ; (1223460, 29%nat) ; (1223576, 567%nat) ; (1230988, 15%nat) ; (1232248, 122%nat) ; (413356, 47%nat) ; (411160, 549%nat) ; (490632, 1%nat) ; (406400, 1%nat) ; (524756, 6%nat) ; (528612, 40%nat) ; (411156, 1%nat) ; (1008364, 81%nat) ; (1008688, 81%nat) ; (1009012, 80%nat) ; (1009332, 80%nat) ; (1009652, 81%nat) ; (1009976, 81%nat) ; (1010300, 81%nat) ; (1010624, 81%nat) ; (1010948, 81%nat) ; (1011272, 81%nat) ; (1011596, 80%nat) ; (1011916, 80%nat) ; (1012236, 81%nat) ; (1012560, 81%nat) ; (1012884, 81%nat) ; (1013208, 81%nat) ; (1013532, 81%nat) ; (1013856, 81%nat) ; (1014180, 81%nat) ; (1014504, 81%nat) ; (1014828, 81%nat) ; (1015152, 81%nat) ; (1015476, 81%nat) ; (1015800, 81%nat) ; (1016124, 81%nat) ; (1016448, 81%nat) ; (1016772, 81%nat) ; (1017096, 81%nat) ; (1017420, 81%nat) ; (1017744, 81%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
