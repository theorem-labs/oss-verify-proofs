(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymPlan UbTargetEntry_defs UbTargetEntryK_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Abbreviation Qd1 := (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) (only parsing).
Definition XC : expr := Qd1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Abbreviation Qd2 := (PCall SumFreePro [] (PMunmap PExitCall)) (only parsing).
Definition p_k0_13085_16364_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_13085_16364_oom2 : plan := Qdt4 7 127 p_k0_13085_16364_cnt1 p_k0_13085_16364_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qdt7 Qdp1 := (PMmap Qdp1 Qd6) (only parsing).
Definition p_k0_13085_16364_cfg0_3 : plan := Qdt7 p_k0_13085_16364_oom2.
Definition p_k0_13085_16364_exit3_4 : plan := Qd5.
Local Abbreviation Qd8 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt9 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp2 Qdp3 Qdp4 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp5 Qdp6 Qdp7 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp8 Qdp9 Qdp10 Qd8))))))))))))))))))))))) (only parsing).
Definition p_k0_13085_16364_cfgpos_5 : plan := Qdt9 p_k0_13085_16364_oom2 XC 0 p_k0_13085_16364_exit3_4 XC 1 p_k0_13085_16364_exit3_4 XC 2 p_k0_13085_16364_exit3_4.
Definition p_k0_13085_16364 : plan := Qdt3 5 0 p_k0_13085_16364_cfg0_3 p_k0_13085_16364_cfgpos_5.

Local Abbreviation Qdc2_10 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qdc4_11 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd12 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qd13 := (SEmit 1 (Qdc2_10 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qd14 := (SCase (EVar 5) 0 (SAlt2 Qd12 Qd13) (SAlt2 Qd12 (SEmit 1 (Qdc2_10 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd13 (SCase Qd1 2 (SEmit 1 (Qdc4_11 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_11 48 10 48 10 (Qdc2_10 48 10 [])) (SExit 0)))))))) (only parsing).
Definition s_k0_13085_16364 : shape := Qd14.

Lemma chk_k0_13085_16364 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 13085 16364) p_k0_13085_16364 = COk s_k0_13085_16364.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_13085_16364)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_16365_18700_cnt1 : plan := Qd2.
Definition p_k0_16365_18700_oom2 : plan := Qdt4 7 127 p_k0_16365_18700_cnt1 p_k0_16365_18700_cnt1.
Definition p_k0_16365_18700_cfg0_3 : plan := Qdt7 p_k0_16365_18700_oom2.
Definition p_k0_16365_18700_exit3_4 : plan := Qd5.
Definition p_k0_16365_18700_cfgpos_5 : plan := Qdt9 p_k0_16365_18700_oom2 XC 0 p_k0_16365_18700_exit3_4 XC 1 p_k0_16365_18700_exit3_4 XC 2 p_k0_16365_18700_exit3_4.
Definition p_k0_16365_18700 : plan := Qdt3 5 0 p_k0_16365_18700_cfg0_3 p_k0_16365_18700_cfgpos_5.

Definition s_k0_16365_18700 : shape := Qd14.

Lemma chk_k0_16365_18700 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 16365 18700) p_k0_16365_18700 = COk s_k0_16365_18700.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_16365_18700)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_131052_262137_cnt1 : plan := Qd2.
Definition p_k2_131052_262137_oom2 : plan := Qdt4 7 127 p_k2_131052_262137_cnt1 p_k2_131052_262137_cnt1.
Definition p_k2_131052_262137_cfg0_3 : plan := Qdt7 p_k2_131052_262137_oom2.
Definition p_k2_131052_262137_exit3_4 : plan := Qd5.
Definition p_k2_131052_262137_cfgpos_5 : plan := Qdt9 p_k2_131052_262137_oom2 XC 0 p_k2_131052_262137_exit3_4 XC 1 p_k2_131052_262137_exit3_4 XC 2 p_k2_131052_262137_exit3_4.
Definition p_k2_131052_262137 : plan := Qdt3 5 0 p_k2_131052_262137_cfg0_3 p_k2_131052_262137_cfgpos_5.

Definition s_k2_131052_262137 : shape := Qd14.

Lemma chk_k2_131052_262137 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 131052 262137) p_k2_131052_262137 = COk s_k2_131052_262137.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_131052_262137)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k3_229371_524281_cnt1 : plan := Qd2.
Definition p_k3_229371_524281_oom2 : plan := Qdt4 7 127 p_k3_229371_524281_cnt1 p_k3_229371_524281_cnt1.
Definition p_k3_229371_524281_cfg0_3 : plan := Qdt7 p_k3_229371_524281_oom2.
Definition p_k3_229371_524281_exit3_4 : plan := Qd5.
Definition p_k3_229371_524281_cfgpos_5 : plan := Qdt9 p_k3_229371_524281_oom2 XC 0 p_k3_229371_524281_exit3_4 XC 1 p_k3_229371_524281_exit3_4 XC 2 p_k3_229371_524281_exit3_4.
Definition p_k3_229371_524281 : plan := Qdt3 5 0 p_k3_229371_524281_cfg0_3 p_k3_229371_524281_cfgpos_5.

Definition s_k3_229371_524281 : shape := Qd14.

Lemma chk_k3_229371_524281 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 3 229371 524281) p_k3_229371_524281 = COk s_k3_229371_524281.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k3_229371_524281)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k4_491515_1048569_cnt1 : plan := Qd2.
Definition p_k4_491515_1048569_oom2 : plan := Qdt4 7 127 p_k4_491515_1048569_cnt1 p_k4_491515_1048569_cnt1.
Definition p_k4_491515_1048569_cfg0_3 : plan := Qdt7 p_k4_491515_1048569_oom2.
Definition p_k4_491515_1048569_exit3_4 : plan := Qd5.
Definition p_k4_491515_1048569_cfgpos_5 : plan := Qdt9 p_k4_491515_1048569_oom2 XC 0 p_k4_491515_1048569_exit3_4 XC 1 p_k4_491515_1048569_exit3_4 XC 2 p_k4_491515_1048569_exit3_4.
Definition p_k4_491515_1048569 : plan := Qdt3 5 0 p_k4_491515_1048569_cfg0_3 p_k4_491515_1048569_cfgpos_5.

Definition s_k4_491515_1048569 : shape := Qd14.

Lemma chk_k4_491515_1048569 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 4 491515 1048569) p_k4_491515_1048569 = COk s_k4_491515_1048569.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k4_491515_1048569)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k5_1015803_2097145_cnt1 : plan := Qd2.
Definition p_k5_1015803_2097145_oom2 : plan := Qdt4 7 127 p_k5_1015803_2097145_cnt1 p_k5_1015803_2097145_cnt1.
Definition p_k5_1015803_2097145_cfg0_3 : plan := Qdt7 p_k5_1015803_2097145_oom2.
Definition p_k5_1015803_2097145_exit3_4 : plan := Qd5.
Definition p_k5_1015803_2097145_cfgpos_5 : plan := Qdt9 p_k5_1015803_2097145_oom2 XC 0 p_k5_1015803_2097145_exit3_4 XC 1 p_k5_1015803_2097145_exit3_4 XC 2 p_k5_1015803_2097145_exit3_4.
Definition p_k5_1015803_2097145 : plan := Qdt3 5 0 p_k5_1015803_2097145_cfg0_3 p_k5_1015803_2097145_cfgpos_5.

Definition s_k5_1015803_2097145 : shape := Qd14.

Lemma chk_k5_1015803_2097145 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 5 1015803 2097145) p_k5_1015803_2097145 = COk s_k5_1015803_2097145.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k5_1015803_2097145)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k6_2064379_4194297_cnt1 : plan := Qd2.
Definition p_k6_2064379_4194297_oom2 : plan := Qdt4 7 127 p_k6_2064379_4194297_cnt1 p_k6_2064379_4194297_cnt1.
Definition p_k6_2064379_4194297_cfg0_3 : plan := Qdt7 p_k6_2064379_4194297_oom2.
Definition p_k6_2064379_4194297_exit3_4 : plan := Qd5.
Definition p_k6_2064379_4194297_cfgpos_5 : plan := Qdt9 p_k6_2064379_4194297_oom2 XC 0 p_k6_2064379_4194297_exit3_4 XC 1 p_k6_2064379_4194297_exit3_4 XC 2 p_k6_2064379_4194297_exit3_4.
Definition p_k6_2064379_4194297 : plan := Qdt3 5 0 p_k6_2064379_4194297_cfg0_3 p_k6_2064379_4194297_cfgpos_5.

Definition s_k6_2064379_4194297 : shape := Qd14.

Lemma chk_k6_2064379_4194297 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 6 2064379 4194297) p_k6_2064379_4194297 = COk s_k6_2064379_4194297.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k6_2064379_4194297)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k7_4161531_8388601_cnt1 : plan := Qd2.
Definition p_k7_4161531_8388601_oom2 : plan := Qdt4 7 127 p_k7_4161531_8388601_cnt1 p_k7_4161531_8388601_cnt1.
Definition p_k7_4161531_8388601_cfg0_3 : plan := Qdt7 p_k7_4161531_8388601_oom2.
Definition p_k7_4161531_8388601_exit3_4 : plan := Qd5.
Definition p_k7_4161531_8388601_cfgpos_5 : plan := Qdt9 p_k7_4161531_8388601_oom2 XC 0 p_k7_4161531_8388601_exit3_4 XC 1 p_k7_4161531_8388601_exit3_4 XC 2 p_k7_4161531_8388601_exit3_4.
Definition p_k7_4161531_8388601 : plan := Qdt3 5 0 p_k7_4161531_8388601_cfg0_3 p_k7_4161531_8388601_cfgpos_5.

Definition s_k7_4161531_8388601 : shape := Qd14.

Lemma chk_k7_4161531_8388601 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 7 4161531 8388601) p_k7_4161531_8388601 = COk s_k7_4161531_8388601.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k7_4161531_8388601)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k8_8355835_16777209_cnt1 : plan := Qd2.
Definition p_k8_8355835_16777209_oom2 : plan := Qdt4 7 127 p_k8_8355835_16777209_cnt1 p_k8_8355835_16777209_cnt1.
Definition p_k8_8355835_16777209_cfg0_3 : plan := Qdt7 p_k8_8355835_16777209_oom2.
Definition p_k8_8355835_16777209_exit3_4 : plan := Qd5.
Definition p_k8_8355835_16777209_cfgpos_5 : plan := Qdt9 p_k8_8355835_16777209_oom2 XC 0 p_k8_8355835_16777209_exit3_4 XC 1 p_k8_8355835_16777209_exit3_4 XC 2 p_k8_8355835_16777209_exit3_4.
Definition p_k8_8355835_16777209 : plan := Qdt3 5 0 p_k8_8355835_16777209_cfg0_3 p_k8_8355835_16777209_cfgpos_5.

Definition s_k8_8355835_16777209 : shape := Qd14.

Lemma chk_k8_8355835_16777209 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 8 8355835 16777209) p_k8_8355835_16777209 = COk s_k8_8355835_16777209.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k8_8355835_16777209)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k9_16744443_33554425_cnt1 : plan := Qd2.
Definition p_k9_16744443_33554425_oom2 : plan := Qdt4 7 127 p_k9_16744443_33554425_cnt1 p_k9_16744443_33554425_cnt1.
Definition p_k9_16744443_33554425_cfg0_3 : plan := Qdt7 p_k9_16744443_33554425_oom2.
Definition p_k9_16744443_33554425_exit3_4 : plan := Qd5.
Definition p_k9_16744443_33554425_cfgpos_5 : plan := Qdt9 p_k9_16744443_33554425_oom2 XC 0 p_k9_16744443_33554425_exit3_4 XC 1 p_k9_16744443_33554425_exit3_4 XC 2 p_k9_16744443_33554425_exit3_4.
Definition p_k9_16744443_33554425 : plan := Qdt3 5 0 p_k9_16744443_33554425_cfg0_3 p_k9_16744443_33554425_cfgpos_5.

Definition s_k9_16744443_33554425 : shape := Qd14.

Lemma chk_k9_16744443_33554425 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 9 16744443 33554425) p_k9_16744443_33554425 = COk s_k9_16744443_33554425.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k9_16744443_33554425)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_33521659_67108857_cnt1 : plan := Qd2.
Definition p_k10_33521659_67108857_oom2 : plan := Qdt4 7 127 p_k10_33521659_67108857_cnt1 p_k10_33521659_67108857_cnt1.
Definition p_k10_33521659_67108857_cfg0_3 : plan := Qdt7 p_k10_33521659_67108857_oom2.
Definition p_k10_33521659_67108857_exit3_4 : plan := Qd5.
Definition p_k10_33521659_67108857_cfgpos_5 : plan := Qdt9 p_k10_33521659_67108857_oom2 XC 0 p_k10_33521659_67108857_exit3_4 XC 1 p_k10_33521659_67108857_exit3_4 XC 2 p_k10_33521659_67108857_exit3_4.
Definition p_k10_33521659_67108857 : plan := Qdt3 5 0 p_k10_33521659_67108857_cfg0_3 p_k10_33521659_67108857_cfgpos_5.

Definition s_k10_33521659_67108857 : shape := Qd14.

Lemma chk_k10_33521659_67108857 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 10 33521659 67108857) p_k10_33521659_67108857 = COk s_k10_33521659_67108857.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_33521659_67108857)). Qed.

