(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Lemma c_134 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (hs_ofS HR_5) 0%nat 400000%nat 5000%nat None (pay_start ST_t1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)])) nf_w1n_1003 = COk s_135.
Proof. vm_cast_no_check (eq_refl (COk s_135)). Qed.
Lemma c_140 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (hs_ofS HR_5) 0%nat 400000%nat 5000%nat None (pay_start ST_t1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)])) nf_w1n_1001_a30 = COk s_141.
Proof. vm_cast_no_check (eq_refl (COk s_141)). Qed.
Lemma c_152 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))) (hs_ofS HR_7) 0%nat 400000%nat 5000%nat None (pay_start (mcase_hi (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)])) t1_asd5 = COk s_153.
Proof. vm_cast_no_check (eq_refl (COk s_153)). Qed.
Lemma c_158 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))) (hs_ofS HR_8) 0%nat 400000%nat 5000%nat None (pay_start ST_t1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)])) t1_as_nulld0 = COk s_159.
Proof. vm_cast_no_check (eq_refl (COk s_159)). Qed.
Lemma c_165 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)])) nl_d0n = COk s_166.
Proof. vm_cast_no_check (eq_refl (COk s_166)). Qed.
Lemma c_172 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]))) HS_none 0%nat 400000%nat 5000%nat None (pay_start T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)])) ts_g5 = COk s_173.
Proof. vm_cast_no_check (eq_refl (COk s_173)). Qed.
Lemma c_183 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))) (hs_of HT_9) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)])) c_r1 = COk s_184.
Proof. vm_cast_no_check (eq_refl (COk s_184)). Qed.
Lemma c_188 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))) (hs_of HT_10) 0%nat 400000%nat 5000%nat None (pay_start ST_c_r1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)])) c_s2 = COk s_189.
Proof. vm_cast_no_check (eq_refl (COk s_189)). Qed.
Lemma c_196 : check ASEGS IT_asan ASAN NX0 AsanInit.LIMIT (XNM (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) (XEm ASEGS ASAN NX0) (XBm ASEGS NX0 (iotab_of ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))) (hs_of HT_11) 0%nat 400000%nat 5000%nat None (pay_start ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)])) c_f2 = COk s_197.
Proof. vm_cast_no_check (eq_refl (COk s_197)). Qed.
