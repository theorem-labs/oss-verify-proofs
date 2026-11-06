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
Definition ITR : list (Z * nat) := [(1034428, 45%nat) ; (1010344, 35%nat) ; (997256, 366%nat) ; (740084, 20%nat) ; (740164, 5%nat) ; (1106052, 71%nat) ; (1099968, 10%nat) ; (1095024, 115%nat) ; (1143488, 210%nat) ; (1144404, 316%nat) ; (1209124, 12%nat) ; (1212436, 162%nat) ; (1213084, 29%nat) ; (1213816, 29%nat) ; (1213932, 567%nat) ; (1221344, 15%nat) ; (1222604, 122%nat) ; (412388, 47%nat) ; (410192, 549%nat) ; (489664, 1%nat) ; (405432, 1%nat) ; (523788, 6%nat) ; (527644, 40%nat) ; (410188, 1%nat) ; (998720, 81%nat) ; (999044, 81%nat) ; (999368, 80%nat) ; (999688, 80%nat) ; (1000008, 81%nat) ; (1000332, 81%nat) ; (1000656, 81%nat) ; (1000980, 81%nat) ; (1001304, 81%nat) ; (1001628, 81%nat) ; (1001952, 80%nat) ; (1002272, 80%nat) ; (1002592, 81%nat) ; (1002916, 81%nat) ; (1003240, 81%nat) ; (1003564, 81%nat) ; (1003888, 81%nat) ; (1004212, 81%nat) ; (1004536, 81%nat) ; (1004860, 81%nat) ; (1005184, 81%nat) ; (1005508, 81%nat) ; (1005832, 81%nat) ; (1006156, 81%nat) ; (1006480, 81%nat) ; (1006804, 81%nat) ; (1007128, 81%nat) ; (1007452, 81%nat) ; (1007776, 81%nat) ; (1008100, 81%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
