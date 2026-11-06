(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAinvMainFactsA.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsStartupHSc.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module K1.












Lemma rng_v518 : In (KRange (EVar 518) 1629 34359734272) (kn HS_1).
Proof. apply (@nth_error_In _ _ 84). vm_compute. reflexivity. Qed.

Lemma disj_g21_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 88). vm_compute. reflexivity. Qed.
Lemma disj_g16_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 89). vm_compute. reflexivity. Qed.
Lemma disj_g12_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 90). vm_compute. reflexivity. Qed.
Lemma disj_g10_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 92). vm_compute. reflexivity. Qed.
Lemma disj_g9_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 93). vm_compute. reflexivity. Qed.
Lemma disj_g8_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 94). vm_compute. reflexivity. Qed.
Lemma disj_g6_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 95). vm_compute. reflexivity. Qed.
Lemma disj_g22_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 101). vm_compute. reflexivity. Qed.








Lemma rng_v517 : In (KRange (EVar 517) 1629 34359736064) (kn HS_1).
Proof. apply (@nth_error_In _ _ 111). vm_compute. reflexivity. Qed.

Lemma disj_g16_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 115). vm_compute. reflexivity. Qed.
Lemma disj_g12_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 116). vm_compute. reflexivity. Qed.
Lemma disj_g10_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 118). vm_compute. reflexivity. Qed.
Lemma disj_g9_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 119). vm_compute. reflexivity. Qed.
Lemma disj_g8_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 120). vm_compute. reflexivity. Qed.
Lemma disj_g6_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 121). vm_compute. reflexivity. Qed.
Lemma disj_g21_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 127). vm_compute. reflexivity. Qed.


Lemma rng_v10 : In (KRange (EVar 10) 0 8) (kn HS_1).
Proof. apply (@nth_error_In _ _ 154). vm_compute. reflexivity. Qed.
Lemma rng_v397 : In (KRange (EVar 397) 1629 34359733495) (kn HS_1).
Proof. apply (@nth_error_In _ _ 158). vm_compute. reflexivity. Qed.











Lemma disj_g12_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 180). vm_compute. reflexivity. Qed.
Lemma disj_g10_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 182). vm_compute. reflexivity. Qed.
Lemma disj_g9_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 183). vm_compute. reflexivity. Qed.
Lemma disj_g8_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 184). vm_compute. reflexivity. Qed.
Lemma disj_g6_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 185). vm_compute. reflexivity. Qed.
Lemma disj_g16_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 191). vm_compute. reflexivity. Qed.













Lemma rng_v330 : In (KRange (EVar 330) 1 34359736319) (kn HS_1).
Proof. apply (@nth_error_In _ _ 233). vm_compute. reflexivity. Qed.

Lemma disj_g10_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 238). vm_compute. reflexivity. Qed.
Lemma disj_g9_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 239). vm_compute. reflexivity. Qed.
Lemma disj_g8_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 240). vm_compute. reflexivity. Qed.
Lemma disj_g6_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 241). vm_compute. reflexivity. Qed.
Lemma disj_g12_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 247). vm_compute. reflexivity. Qed.









Lemma rng_v248 : In (KRange (EVar 248) 1629 34359736304) (kn HS_1).
Proof. apply (@nth_error_In _ _ 284). vm_compute. reflexivity. Qed.



















Lemma disj_g9_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 313). vm_compute. reflexivity. Qed.
Lemma disj_g8_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 314). vm_compute. reflexivity. Qed.
Lemma disj_g6_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 315). vm_compute. reflexivity. Qed.
Lemma disj_g10_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 321). vm_compute. reflexivity. Qed.




Lemma rng_v247 : In (KRange (EVar 247) 1 34359736319) (kn HS_1).
Proof. apply (@nth_error_In _ _ 355). vm_compute. reflexivity. Qed.

Lemma disj_g8_g9 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 359). vm_compute. reflexivity. Qed.
Lemma disj_g6_g9 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 360). vm_compute. reflexivity. Qed.
Lemma disj_g9_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 366). vm_compute. reflexivity. Qed.














Lemma rng_v246 : In (KRange (EVar 246) 1629 34359734272) (kn HS_1).
Proof. apply (@nth_error_In _ _ 391). vm_compute. reflexivity. Qed.

Lemma disj_g6_g8 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 395). vm_compute. reflexivity. Qed.
Lemma disj_g8_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 401). vm_compute. reflexivity. Qed.






Lemma rng_v229 : In (KRange (EVar 229) 1 16) (kn HS_1).
Proof. apply (@nth_error_In _ _ 410). vm_compute. reflexivity. Qed.
Lemma align_w6 : In (KRange (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 229)) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 227)) (ELit 65535)))) (ELit 65536)) 0 0) (kn HS_1).
Proof. apply (@nth_error_In _ _ 411). vm_compute. reflexivity. Qed.


Lemma rng_v227 : In (KRange (EVar 227) 4295491576 34326181871) (kn HS_1).
Proof. apply (@nth_error_In _ _ 418). vm_compute. reflexivity. Qed.


Lemma disj_g6_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_1).
Proof. apply (@nth_error_In _ _ 429). vm_compute. reflexivity. Qed.






























Lemma rng_v0 : In (KRange (EVar 0) 4294901760 4294967295) (kn HS_1).
Proof. apply (@nth_error_In _ _ 619). vm_compute. reflexivity. Qed.














End K1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module K2.











Lemma rng_v518 : In (KRange (EVar 518) 1629 34359734272) (kn HS_2).
Proof. apply (@nth_error_In _ _ 83). vm_compute. reflexivity. Qed.

Lemma disj_g21_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 87). vm_compute. reflexivity. Qed.
Lemma disj_g16_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 88). vm_compute. reflexivity. Qed.
Lemma disj_g12_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 89). vm_compute. reflexivity. Qed.
Lemma disj_g10_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 91). vm_compute. reflexivity. Qed.
Lemma disj_g9_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 92). vm_compute. reflexivity. Qed.
Lemma disj_g8_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 93). vm_compute. reflexivity. Qed.
Lemma disj_g6_g22 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 94). vm_compute. reflexivity. Qed.
Lemma disj_g22_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 518); a_off := 0 |} (ELit 8388608) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 100). vm_compute. reflexivity. Qed.








Lemma rng_v517 : In (KRange (EVar 517) 1629 34359736064) (kn HS_2).
Proof. apply (@nth_error_In _ _ 110). vm_compute. reflexivity. Qed.

Lemma disj_g16_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 114). vm_compute. reflexivity. Qed.
Lemma disj_g12_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 115). vm_compute. reflexivity. Qed.
Lemma disj_g10_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 117). vm_compute. reflexivity. Qed.
Lemma disj_g9_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 118). vm_compute. reflexivity. Qed.
Lemma disj_g8_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 119). vm_compute. reflexivity. Qed.
Lemma disj_g6_g21 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 120). vm_compute. reflexivity. Qed.
Lemma disj_g21_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 517); a_off := 0 |} (ELit 1048576) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 126). vm_compute. reflexivity. Qed.


Lemma rng_v10 : In (KRange (EVar 10) 0 8) (kn HS_2).
Proof. apply (@nth_error_In _ _ 153). vm_compute. reflexivity. Qed.
Lemma rng_v397 : In (KRange (EVar 397) 1629 34359733495) (kn HS_2).
Proof. apply (@nth_error_In _ _ 157). vm_compute. reflexivity. Qed.











Lemma disj_g12_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 179). vm_compute. reflexivity. Qed.
Lemma disj_g10_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 181). vm_compute. reflexivity. Qed.
Lemma disj_g9_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 182). vm_compute. reflexivity. Qed.
Lemma disj_g8_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 183). vm_compute. reflexivity. Qed.
Lemma disj_g6_g16 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 184). vm_compute. reflexivity. Qed.
Lemma disj_g16_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 397); a_off := 0 |} (ELit 11571200) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 190). vm_compute. reflexivity. Qed.













Lemma rng_v330 : In (KRange (EVar 330) 1 34359736319) (kn HS_2).
Proof. apply (@nth_error_In _ _ 232). vm_compute. reflexivity. Qed.

Lemma disj_g10_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 237). vm_compute. reflexivity. Qed.
Lemma disj_g9_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 238). vm_compute. reflexivity. Qed.
Lemma disj_g8_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 239). vm_compute. reflexivity. Qed.
Lemma disj_g6_g12 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 240). vm_compute. reflexivity. Qed.
Lemma disj_g12_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 330); a_off := 0 |} (ELit 4096) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 246). vm_compute. reflexivity. Qed.









Lemma rng_v248 : In (KRange (EVar 248) 1629 34359736304) (kn HS_2).
Proof. apply (@nth_error_In _ _ 283). vm_compute. reflexivity. Qed.



















Lemma disj_g9_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 312). vm_compute. reflexivity. Qed.
Lemma disj_g8_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 313). vm_compute. reflexivity. Qed.
Lemma disj_g6_g10 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 314). vm_compute. reflexivity. Qed.
Lemma disj_g10_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 248); a_off := 0 |} (ELit 65536) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 320). vm_compute. reflexivity. Qed.




Lemma rng_v247 : In (KRange (EVar 247) 1 34359736319) (kn HS_2).
Proof. apply (@nth_error_In _ _ 354). vm_compute. reflexivity. Qed.

Lemma disj_g8_g9 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 358). vm_compute. reflexivity. Qed.
Lemma disj_g6_g9 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 359). vm_compute. reflexivity. Qed.
Lemma disj_g9_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 247); a_off := 0 |} (ELit 4096) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 365). vm_compute. reflexivity. Qed.














Lemma rng_v246 : In (KRange (EVar 246) 1629 34359734272) (kn HS_2).
Proof. apply (@nth_error_In _ _ 390). vm_compute. reflexivity. Qed.

Lemma disj_g6_g8 : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 394). vm_compute. reflexivity. Qed.
Lemma disj_g8_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 246); a_off := 0 |} (ELit 8388608) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 400). vm_compute. reflexivity. Qed.






Lemma rng_v229 : In (KRange (EVar 229) 1 16) (kn HS_2).
Proof. apply (@nth_error_In _ _ 409). vm_compute. reflexivity. Qed.
Lemma align_w6 : In (KRange (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 229)) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 227)) (ELit 65535)))) (ELit 65536)) 0 0) (kn HS_2).
Proof. apply (@nth_error_In _ _ 410). vm_compute. reflexivity. Qed.


Lemma rng_v227 : In (KRange (EVar 227) 4295491576 34326181871) (kn HS_2).
Proof. apply (@nth_error_In _ _ 417). vm_compute. reflexivity. Qed.


Lemma disj_g6_band : In (KDisj {| a_base := EMd Instr.M_MUL (ELit 4096) (EVar 227); a_off := 0 |} (ELit 137439023104) {| a_base := ELit 0; a_off := 2147446784 |} (ELit 17592186048512)) (kn HS_2).
Proof. apply (@nth_error_In _ _ 428). vm_compute. reflexivity. Qed.






























Lemma rng_v0 : In (KRange (EVar 0) 4294901760 4294967295) (kn HS_2).
Proof. apply (@nth_error_In _ _ 618). vm_compute. reflexivity. Qed.














End K2.
End AsAinvMainFactsA.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanHexScan OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageAsan OSSVerify.Proofs.glaze.binary_reflection.lib.AsStartupTabs.AsSDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsSInit.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require AzHexZero.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma Forall_ivs_of_b : forall (lo hi : Z) (l : list (word * word)),
  forallb (fun iv => (lo <=? bv_unsigned (fst iv)) && (bv_unsigned (fst iv) + bv_unsigned (snd iv) <=? hi))%bool l = true ->
  Forall (fun iv => lo <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= hi) l.
Proof.
  intros lo hi l H. apply Forall_forall. intros iv Hin.
  pose proof (proj1 (forallb_forall _ _) H iv Hin) as B. apply andb_prop in B as [B1 B2].
  apply Z.leb_le in B1. apply Z.leb_le in B2. lia.
Qed.

Lemma ASEGS_eq : ASEGS = AzImageAsan.ASEGS.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_S_wx : wx_segs_nowrap ASEGS.
Proof. rewrite ASEGS_eq. exact AzImageAsan.asan_segs_wx. Qed.

Lemma asan_S_in_hull : forall a : word,
  APS.in_hull AT_A (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof. rewrite ASEGS_eq. exact AzImageAsan.asan_in_hull. Qed.

Lemma asan_S_res_len : APS.res_len_ok ASEGS AT_A.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_S_res_hull : Forall (fun iv => img_lo AT_A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi AT_A)
                               (segments_reserved ASEGS).
Proof. apply Forall_ivs_of_b. vm_compute. reflexivity. Qed.

Lemma asan_S_hull_ok : APS.hull_ok AT_A.
Proof. exact AzImageAsan.asan_hull_ok. Qed.

Lemma asan_S_shadow_ok : APS.shadow_ok AT_A.
Proof. unfold APS.shadow_ok. cbn. lia. Qed.

Lemma asan_S_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x64d000.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_S_hull_ne : img_lo AT_A < img_hi AT_A.
Proof. cbn. lia. Qed.

(* [comment removed for export] *)
Lemma asan_S_res_tile : forall z, img_lo AT_A <= z < img_hi AT_A -> APS.in_ivs z (segments_reserved ASEGS) = true.
Proof.
  intros z Hz. cbn [img_lo img_hi AT_A] in Hz.
  replace (segments_reserved ASEGS) with
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x3a000); (Z_to_bv 64 0x4a000, Z_to_bv 64 0xb1000); (Z_to_bv 64 0xfb000, Z_to_bv 64 0x6000); (Z_to_bv 64 0x101000, Z_to_bv 64 0x55c000)]
    by (vm_compute; reflexivity).
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z_lt_ge_dec z 0x4a000); [|destruct (Z_lt_ge_dec z 0xfb000); [|destruct (Z_lt_ge_dec z 0x101000)]].
  - replace (0x10000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x10000 + 0x3a000) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (0x4a000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x4a000 + 0xb1000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite orb_true_r. reflexivity.
  - replace (0xfb000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0xfb000 + 0x6000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite !orb_true_r. reflexivity.
  - replace (0x101000 <=? z) with true by (symmetry; apply Z.leb_le; lia). replace (z <? 0x101000 + 0x55c000) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite !orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma asan_hex2 : scanN Asan_seg_bytes_002 64 0 0x6000 = true.
Proof. apply AzHexZero.scanN_of_data. vm_compute. reflexivity. Qed.
Lemma asan_hex3 : scanN Asan_seg_bytes_003 64 0 0x55c000 = true.
Proof. apply (AzHexZero.scanN_of_data_zero _ 11936%N). vm_compute. reflexivity. Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 0x6000%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_rw_window : forall m (x : word),
  0xfb000 <= bv_unsigned x < 0x65d000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite ASEGS_eq, AzImageAsan.asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 0x6000); [exact asan_hex2 | rewrite asan_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 0x55c000); [exact asan_hex3 | rewrite asan_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x101000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite ASEGS_eq, AzImageAsan.asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite ASEGS_eq, AzImageAsan.asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

Definition APH : PhdrInfo := Asan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS AT_A APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi AT_A]. lia.
  - vm_compute. reflexivity.
  - exact asan_S_res_hull.
  - rewrite asan_S_res_sizes. reflexivity.
  - cbn [rw_lo rw_len AT_A]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_S_shadow_ok.
Qed.
