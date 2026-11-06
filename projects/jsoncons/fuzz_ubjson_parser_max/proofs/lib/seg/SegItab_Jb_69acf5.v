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
Definition ITR : list (Z * nat) := [(1031500, 45%nat) ; (1007416, 35%nat) ; (994328, 366%nat) ; (737156, 20%nat) ; (737236, 5%nat) ; (1103124, 71%nat) ; (1097040, 10%nat) ; (1092096, 115%nat) ; (1140560, 210%nat) ; (1141476, 316%nat) ; (1206196, 12%nat) ; (1209508, 162%nat) ; (1210156, 29%nat) ; (1210888, 29%nat) ; (1211004, 567%nat) ; (1218416, 15%nat) ; (1219676, 122%nat) ; (411684, 47%nat) ; (409488, 549%nat) ; (488960, 1%nat) ; (404728, 1%nat) ; (523084, 6%nat) ; (526940, 40%nat) ; (409484, 1%nat) ; (995792, 81%nat) ; (996116, 81%nat) ; (996440, 80%nat) ; (996760, 80%nat) ; (997080, 81%nat) ; (997404, 81%nat) ; (997728, 81%nat) ; (998052, 81%nat) ; (998376, 81%nat) ; (998700, 81%nat) ; (999024, 80%nat) ; (999344, 80%nat) ; (999664, 81%nat) ; (999988, 81%nat) ; (1000312, 81%nat) ; (1000636, 81%nat) ; (1000960, 81%nat) ; (1001284, 81%nat) ; (1001608, 81%nat) ; (1001932, 81%nat) ; (1002256, 81%nat) ; (1002580, 81%nat) ; (1002904, 81%nat) ; (1003228, 81%nat) ; (1003552, 81%nat) ; (1003876, 81%nat) ; (1004200, 81%nat) ; (1004524, 81%nat) ; (1004848, 81%nat) ; (1005172, 81%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
