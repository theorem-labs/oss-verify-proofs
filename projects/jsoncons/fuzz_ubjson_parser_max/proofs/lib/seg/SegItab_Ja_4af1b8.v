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
Definition ITR : list (Z * nat) := [(1023764, 45%nat) ; (999680, 35%nat) ; (986592, 366%nat) ; (729420, 20%nat) ; (729500, 5%nat) ; (1095388, 71%nat) ; (1089304, 10%nat) ; (1084360, 115%nat) ; (1132824, 210%nat) ; (1133740, 316%nat) ; (1198460, 12%nat) ; (1201772, 162%nat) ; (1202420, 29%nat) ; (1203152, 29%nat) ; (1203268, 567%nat) ; (1210680, 15%nat) ; (1211940, 122%nat) ; (410964, 47%nat) ; (408768, 549%nat) ; (488240, 1%nat) ; (404008, 1%nat) ; (522364, 6%nat) ; (526220, 40%nat) ; (408764, 1%nat) ; (988056, 81%nat) ; (988380, 81%nat) ; (988704, 80%nat) ; (989024, 80%nat) ; (989344, 81%nat) ; (989668, 81%nat) ; (989992, 81%nat) ; (990316, 81%nat) ; (990640, 81%nat) ; (990964, 81%nat) ; (991288, 80%nat) ; (991608, 80%nat) ; (991928, 81%nat) ; (992252, 81%nat) ; (992576, 81%nat) ; (992900, 81%nat) ; (993224, 81%nat) ; (993548, 81%nat) ; (993872, 81%nat) ; (994196, 81%nat) ; (994520, 81%nat) ; (994844, 81%nat) ; (995168, 81%nat) ; (995492, 81%nat) ; (995816, 81%nat) ; (996140, 81%nat) ; (996464, 81%nat) ; (996788, 81%nat) ; (997112, 81%nat) ; (997436, 81%nat)].
Definition IT : itab := itab_of RSEGS ITR.
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
