(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec AxSymExec3 LibSym.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.
Definition ITR : list (Z * nat) := [(132504, 26%nat) ; (132848, 13%nat) ; (133016, 118%nat) ; (133564, 29%nat) ; (133980, 119%nat) ; (134548, 80%nat) ; (134996, 26%nat) ; (135184, 86%nat) ; (135648, 51%nat) ; (136144, 39%nat) ; (136424, 16%nat) ; (136656, 23%nat) ; (138048, 40%nat) ; (138480, 65%nat) ; (140108, 13%nat) ; (140224, 1%nat) ; (140352, 11%nat) ; (141384, 18%nat) ; (142500, 5%nat) ; (142616, 5%nat) ; (142996, 6%nat) ; (253532, 1%nat) ; (253816, 22%nat) ; (254504, 9%nat) ; (254716, 7%nat) ; (257060, 2%nat) ; (257172, 63%nat) ; (257500, 31%nat) ; (257724, 54%nat) ; (258012, 22%nat) ; (258996, 17%nat) ; (259416, 6%nat) ; (259552, 1%nat) ; (259620, 98%nat) ; (260108, 220%nat) ; (261184, 47%nat) ; (262112, 15%nat) ; (262296, 22%nat) ; (262476, 24%nat) ; (263544, 33%nat) ; (278772, 47%nat) ; (279036, 13%nat) ; (279240, 14%nat) ; (279540, 86%nat) ; (280016, 19%nat) ; (280408, 25%nat) ; (281380, 25%nat) ; (281576, 21%nat) ; (281840, 50%nat) ; (282108, 72%nat) ; (282476, 56%nat) ; (282812, 63%nat) ; (283176, 26%nat) ; (283380, 19%nat) ; (283556, 29%nat) ; (283776, 14%nat) ; (284236, 43%nat) ; (284548, 74%nat) ; (285268, 47%nat) ; (285576, 129%nat) ; (286180, 52%nat) ; (286500, 16%nat) ; (286792, 70%nat) ; (287236, 34%nat) ; (287532, 5%nat) ; (290588, 142%nat) ; (291300, 91%nat) ; (292180, 29%nat) ; (292548, 17%nat) ; (292892, 30%nat) ; (293404, 10%nat) ; (294264, 22%nat) ; (295552, 38%nat) ; (295872, 25%nat) ; (296328, 16%nat) ; (296680, 20%nat) ; (297316, 50%nat) ; (297788, 16%nat) ; (297952, 19%nat) ; (298184, 53%nat) ; (298788, 22%nat) ; (301760, 33%nat) ; (301996, 49%nat) ; (302480, 133%nat) ; (303740, 132%nat) ; (305576, 132%nat) ; (308820, 72%nat) ; (309172, 21%nat) ; (309572, 122%nat) ; (310164, 12%nat) ; (310288, 235%nat) ; (311320, 49%nat) ; (311596, 27%nat) ; (311784, 78%nat) ; (312192, 25%nat) ; (312644, 57%nat) ; (312976, 6%nat) ; (313256, 274%nat) ; (314420, 82%nat) ; (315436, 52%nat) ; (315780, 101%nat) ; (362788, 29%nat) ; (363064, 28%nat) ; (363620, 71%nat) ; (364196, 62%nat) ; (364652, 34%nat) ; (365744, 3%nat) ; (368816, 18%nat)].
Definition IT : itab := Eval vm_compute in (itab_of RSEGS ITR).
Lemma IT_eq : IT = itab_of RSEGS ITR.
Proof. vm_cast_no_check (@eq_refl itab IT). Qed.
Lemma IT_sound : itab_sound RSEGS IT.
Proof. rewrite IT_eq. apply itab_of_sound. Qed.
