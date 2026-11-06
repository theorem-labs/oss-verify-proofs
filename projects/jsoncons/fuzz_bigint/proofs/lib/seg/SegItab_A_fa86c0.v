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
Definition ITR : list (Z * nat) := [(318540, 1%nat) ; (343288, 24%nat) ; (400716, 6%nat) ; (581256, 402%nat) ; (597496, 189%nat) ; (598252, 1133%nat) ; (607408, 5%nat) ; (607524, 5%nat) ; (607904, 3%nat) ; (607916, 3%nat) ; (718440, 1%nat) ; (718724, 22%nat) ; (719412, 68%nat) ; (721968, 1%nat) ; (722080, 2%nat) ; (722116, 22%nat) ; (722204, 43%nat) ; (722408, 31%nat) ; (722632, 23%nat) ; (722756, 65%nat) ; (723904, 22%nat) ; (724324, 51%nat) ; (724528, 122%nat) ; (725016, 360%nat) ; (727020, 148%nat) ; (728452, 38%nat) ; (743680, 192%nat) ; (744448, 217%nat) ; (745316, 45%nat) ; (746288, 49%nat) ; (746484, 33%nat) ; (746748, 34%nat) ; (746884, 33%nat) ; (747016, 30%nat) ; (747136, 62%nat) ; (747384, 25%nat) ; (747484, 66%nat) ; (747748, 91%nat) ; (748112, 44%nat) ; (748288, 44%nat) ; (748464, 55%nat) ; (748684, 46%nat) ; (749144, 152%nat) ; (750176, 228%nat) ; (751088, 25%nat) ; (751196, 14%nat) ; (751252, 39%nat) ; (751408, 33%nat) ; (751700, 58%nat) ; (751932, 10%nat) ; (751972, 2%nat) ; (752144, 94%nat) ; (755496, 178%nat) ; (756208, 1345%nat) ; (761588, 68%nat) ; (762224, 118%nat) ; (762696, 250%nat) ; (763696, 115%nat) ; (766668, 108%nat) ; (767388, 81%nat) ; (767712, 73%nat) ; (768648, 112%nat) ; (769096, 53%nat) ; (770840, 64%nat) ; (771096, 66%nat) ; (771360, 2%nat) ; (776180, 106%nat) ; (834348, 62%nat) ; (856032, 28%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
