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
Definition ITR : list (Z * nat) := [(406444, 1%nat) ; (406448, 1%nat) ; (421612, 39%nat) ; (421768, 690%nat) ; (424528, 45%nat) ; (449616, 102%nat) ; (490632, 1%nat) ; (490640, 1%nat) ; (493280, 188%nat) ; (495248, 380%nat) ; (528612, 40%nat) ; (570464, 24%nat) ; (570644, 13%nat) ; (570804, 7%nat) ; (1182580, 21%nat) ; (1182664, 78%nat) ; (1183420, 40%nat) ; (1183864, 148%nat) ; (1184456, 908%nat) ; (1188088, 16%nat) ; (1188152, 61%nat) ; (1209316, 13%nat) ; (1218132, 490%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
