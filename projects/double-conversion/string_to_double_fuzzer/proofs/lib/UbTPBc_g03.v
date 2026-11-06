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
Definition p_k0_1_12_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_1_12_oom2 : plan := Qdt4 7 127 p_k0_1_12_cnt1 p_k0_1_12_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qd7 := (PCall SumEnframe [] (PCall SumEnframe [] Qd6)) (only parsing).
Local Abbreviation Qd8 := (PCall SumEnframe [] Qd7) (only parsing).
Local Abbreviation Qdt9 Qdp1 := (PMmap Qdp1 Qd8) (only parsing).
Definition p_k0_1_12_cfg0_3 : plan := Qdt9 p_k0_1_12_oom2.
Definition p_k0_1_12_exit3_4 : plan := Qd5.
Local Abbreviation Qd10 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt11 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp1 Qdp2 Qdp3 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp4 Qdp5 Qdp6 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp7 Qdp8 Qdp9 Qd10)))))))))))))))))))))) (only parsing).
Local Abbreviation Qdt12 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 := (PCall SumEnframe [] (PCall SumEnframe [] (Qdt11 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9))) (only parsing).
Local Abbreviation Qdt13 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (Qdt12 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10))) (only parsing).
Definition p_k0_1_12_cfgpos_5 : plan := Qdt13 p_k0_1_12_oom2 XC 0 p_k0_1_12_exit3_4 XC 1 p_k0_1_12_exit3_4 XC 2 p_k0_1_12_exit3_4.
Definition p_k0_1_12 : plan := Qdt3 5 0 p_k0_1_12_cfg0_3 p_k0_1_12_cfgpos_5.

Local Abbreviation Qdc2_14 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qdc4_15 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd16 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qd17 := (SEmit 1 (Qdc2_14 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qd18 := (SCase (EVar 5) 0 (SAlt2 Qd16 Qd17) (SAlt2 Qd16 (SEmit 1 (Qdc2_14 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd17 (SCase Qd1 2 (SEmit 1 (Qdc4_15 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_15 48 10 48 10 (Qdc2_14 48 10 [])) (SExit 0)))))))) (only parsing).
Definition s_k0_1_12 : shape := Qd18.

Lemma chk_k0_1_12 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 1 12) p_k0_1_12 = COk s_k0_1_12.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1_12)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_13_28_cnt1 : plan := Qd2.
Definition p_k0_13_28_oom2 : plan := Qdt4 7 127 p_k0_13_28_cnt1 p_k0_13_28_cnt1.
Definition p_k0_13_28_cfg0_3 : plan := Qdt9 p_k0_13_28_oom2.
Definition p_k0_13_28_exit3_4 : plan := Qd5.
Definition p_k0_13_28_cfgpos_5 : plan := Qdt13 p_k0_13_28_oom2 XC 0 p_k0_13_28_exit3_4 XC 1 p_k0_13_28_exit3_4 XC 2 p_k0_13_28_exit3_4.
Definition p_k0_13_28 : plan := Qdt3 5 0 p_k0_13_28_cfg0_3 p_k0_13_28_cfgpos_5.

Definition s_k0_13_28 : shape := Qd18.

Lemma chk_k0_13_28 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 13 28) p_k0_13_28 = COk s_k0_13_28.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_13_28)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_29_44_cnt1 : plan := Qd2.
Definition p_k0_29_44_oom2 : plan := Qdt4 7 127 p_k0_29_44_cnt1 p_k0_29_44_cnt1.
Definition p_k0_29_44_cfg0_3 : plan := Qdt9 p_k0_29_44_oom2.
Definition p_k0_29_44_exit3_4 : plan := Qd5.
Definition p_k0_29_44_cfgpos_5 : plan := Qdt13 p_k0_29_44_oom2 XC 0 p_k0_29_44_exit3_4 XC 1 p_k0_29_44_exit3_4 XC 2 p_k0_29_44_exit3_4.
Definition p_k0_29_44 : plan := Qdt3 5 0 p_k0_29_44_cfg0_3 p_k0_29_44_cfgpos_5.

Definition s_k0_29_44 : shape := Qd18.

Lemma chk_k0_29_44 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 29 44) p_k0_29_44 = COk s_k0_29_44.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_29_44)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45_60_cnt1 : plan := Qd2.
Definition p_k0_45_60_oom2 : plan := Qdt4 7 127 p_k0_45_60_cnt1 p_k0_45_60_cnt1.
Definition p_k0_45_60_cfg0_3 : plan := Qdt9 p_k0_45_60_oom2.
Definition p_k0_45_60_exit3_4 : plan := Qd5.
Definition p_k0_45_60_cfgpos_5 : plan := Qdt13 p_k0_45_60_oom2 XC 0 p_k0_45_60_exit3_4 XC 1 p_k0_45_60_exit3_4 XC 2 p_k0_45_60_exit3_4.
Definition p_k0_45_60 : plan := Qdt3 5 0 p_k0_45_60_cfg0_3 p_k0_45_60_cfgpos_5.

Definition s_k0_45_60 : shape := Qd18.

Lemma chk_k0_45_60 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 45 60) p_k0_45_60 = COk s_k0_45_60.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_45_60)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61_76_cnt1 : plan := Qd2.
Definition p_k0_61_76_oom2 : plan := Qdt4 7 127 p_k0_61_76_cnt1 p_k0_61_76_cnt1.
Definition p_k0_61_76_cfg0_3 : plan := Qdt9 p_k0_61_76_oom2.
Definition p_k0_61_76_exit3_4 : plan := Qd5.
Definition p_k0_61_76_cfgpos_5 : plan := Qdt13 p_k0_61_76_oom2 XC 0 p_k0_61_76_exit3_4 XC 1 p_k0_61_76_exit3_4 XC 2 p_k0_61_76_exit3_4.
Definition p_k0_61_76 : plan := Qdt3 5 0 p_k0_61_76_cfg0_3 p_k0_61_76_cfgpos_5.

Definition s_k0_61_76 : shape := Qd18.

Lemma chk_k0_61_76 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 61 76) p_k0_61_76 = COk s_k0_61_76.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_61_76)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_77_92_cnt1 : plan := Qd2.
Definition p_k0_77_92_oom2 : plan := Qdt4 7 127 p_k0_77_92_cnt1 p_k0_77_92_cnt1.
Definition p_k0_77_92_cfg0_3 : plan := Qdt9 p_k0_77_92_oom2.
Definition p_k0_77_92_exit3_4 : plan := Qd5.
Definition p_k0_77_92_cfgpos_5 : plan := Qdt13 p_k0_77_92_oom2 XC 0 p_k0_77_92_exit3_4 XC 1 p_k0_77_92_exit3_4 XC 2 p_k0_77_92_exit3_4.
Definition p_k0_77_92 : plan := Qdt3 5 0 p_k0_77_92_cfg0_3 p_k0_77_92_cfgpos_5.

Definition s_k0_77_92 : shape := Qd18.

Lemma chk_k0_77_92 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 77 92) p_k0_77_92 = COk s_k0_77_92.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_77_92)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_93_108_cnt1 : plan := Qd2.
Definition p_k0_93_108_oom2 : plan := Qdt4 7 127 p_k0_93_108_cnt1 p_k0_93_108_cnt1.
Definition p_k0_93_108_cfg0_3 : plan := Qdt9 p_k0_93_108_oom2.
Definition p_k0_93_108_exit3_4 : plan := Qd5.
Definition p_k0_93_108_cfgpos_5 : plan := Qdt13 p_k0_93_108_oom2 XC 0 p_k0_93_108_exit3_4 XC 1 p_k0_93_108_exit3_4 XC 2 p_k0_93_108_exit3_4.
Definition p_k0_93_108 : plan := Qdt3 5 0 p_k0_93_108_cfg0_3 p_k0_93_108_cfgpos_5.

Definition s_k0_93_108 : shape := Qd18.

Lemma chk_k0_93_108 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 93 108) p_k0_93_108 = COk s_k0_93_108.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_93_108)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_109_124_cnt1 : plan := Qd2.
Definition p_k0_109_124_oom2 : plan := Qdt4 7 127 p_k0_109_124_cnt1 p_k0_109_124_cnt1.
Definition p_k0_109_124_cfg0_3 : plan := PMmap p_k0_109_124_oom2 Qd7.
Definition p_k0_109_124_exit3_4 : plan := Qd5.
Local Abbreviation Qdt19 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (Qdt12 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10)) (only parsing).
Definition p_k0_109_124_cfgpos_5 : plan := Qdt19 p_k0_109_124_oom2 XC 0 p_k0_109_124_exit3_4 XC 1 p_k0_109_124_exit3_4 XC 2 p_k0_109_124_exit3_4.
Definition p_k0_109_124 : plan := Qdt3 5 0 p_k0_109_124_cfg0_3 p_k0_109_124_cfgpos_5.

Definition s_k0_109_124 : shape := Qd18.

Lemma chk_k0_109_124 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 109 124) p_k0_109_124 = COk s_k0_109_124.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_109_124)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_125_140_cnt1 : plan := Qd2.
Definition p_k0_125_140_oom2 : plan := Qdt4 7 127 p_k0_125_140_cnt1 p_k0_125_140_cnt1.
Definition p_k0_125_140_cfg0_3 : plan := Qdt9 p_k0_125_140_oom2.
Definition p_k0_125_140_exit3_4 : plan := Qd5.
Definition p_k0_125_140_cfgpos_5 : plan := Qdt13 p_k0_125_140_oom2 XC 0 p_k0_125_140_exit3_4 XC 1 p_k0_125_140_exit3_4 XC 2 p_k0_125_140_exit3_4.
Definition p_k0_125_140 : plan := Qdt3 5 0 p_k0_125_140_cfg0_3 p_k0_125_140_cfgpos_5.

Definition s_k0_125_140 : shape := Qd18.

Lemma chk_k0_125_140 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 125 140) p_k0_125_140 = COk s_k0_125_140.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_125_140)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_141_156_cnt1 : plan := Qd2.
Definition p_k0_141_156_oom2 : plan := Qdt4 7 127 p_k0_141_156_cnt1 p_k0_141_156_cnt1.
Definition p_k0_141_156_cfg0_3 : plan := Qdt9 p_k0_141_156_oom2.
Definition p_k0_141_156_exit3_4 : plan := Qd5.
Definition p_k0_141_156_cfgpos_5 : plan := Qdt13 p_k0_141_156_oom2 XC 0 p_k0_141_156_exit3_4 XC 1 p_k0_141_156_exit3_4 XC 2 p_k0_141_156_exit3_4.
Definition p_k0_141_156 : plan := Qdt3 5 0 p_k0_141_156_cfg0_3 p_k0_141_156_cfgpos_5.

Definition s_k0_141_156 : shape := Qd18.

Lemma chk_k0_141_156 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 141 156) p_k0_141_156 = COk s_k0_141_156.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_141_156)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_157_188_cnt1 : plan := Qd2.
Definition p_k0_157_188_oom2 : plan := Qdt4 7 127 p_k0_157_188_cnt1 p_k0_157_188_cnt1.
Definition p_k0_157_188_cfg0_3 : plan := Qdt9 p_k0_157_188_oom2.
Definition p_k0_157_188_exit3_4 : plan := Qd5.
Definition p_k0_157_188_cfgpos_5 : plan := Qdt13 p_k0_157_188_oom2 XC 0 p_k0_157_188_exit3_4 XC 1 p_k0_157_188_exit3_4 XC 2 p_k0_157_188_exit3_4.
Definition p_k0_157_188 : plan := Qdt3 5 0 p_k0_157_188_cfg0_3 p_k0_157_188_cfgpos_5.

Definition s_k0_157_188 : shape := Qd18.

Lemma chk_k0_157_188 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 157 188) p_k0_157_188 = COk s_k0_157_188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_157_188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_189_236_cnt1 : plan := Qd2.
Definition p_k0_189_236_oom2 : plan := Qdt4 7 127 p_k0_189_236_cnt1 p_k0_189_236_cnt1.
Definition p_k0_189_236_cfg0_3 : plan := Qdt9 p_k0_189_236_oom2.
Definition p_k0_189_236_exit3_4 : plan := Qd5.
Definition p_k0_189_236_cfgpos_5 : plan := Qdt13 p_k0_189_236_oom2 XC 0 p_k0_189_236_exit3_4 XC 1 p_k0_189_236_exit3_4 XC 2 p_k0_189_236_exit3_4.
Definition p_k0_189_236 : plan := Qdt3 5 0 p_k0_189_236_cfg0_3 p_k0_189_236_cfgpos_5.

Definition s_k0_189_236 : shape := Qd18.

Lemma chk_k0_189_236 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 189 236) p_k0_189_236 = COk s_k0_189_236.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_189_236)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_237_284_cnt1 : plan := Qd2.
Definition p_k0_237_284_oom2 : plan := Qdt4 7 127 p_k0_237_284_cnt1 p_k0_237_284_cnt1.
Definition p_k0_237_284_cfg0_3 : plan := PMmap p_k0_237_284_oom2 Qd7.
Definition p_k0_237_284_exit3_4 : plan := Qd5.
Definition p_k0_237_284_cfgpos_5 : plan := Qdt19 p_k0_237_284_oom2 XC 0 p_k0_237_284_exit3_4 XC 1 p_k0_237_284_exit3_4 XC 2 p_k0_237_284_exit3_4.
Definition p_k0_237_284 : plan := Qdt3 5 0 p_k0_237_284_cfg0_3 p_k0_237_284_cfgpos_5.

Definition s_k0_237_284 : shape := Qd18.

Lemma chk_k0_237_284 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 237 284) p_k0_237_284 = COk s_k0_237_284.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_237_284)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_285_316_cnt1 : plan := Qd2.
Definition p_k0_285_316_oom2 : plan := Qdt4 7 127 p_k0_285_316_cnt1 p_k0_285_316_cnt1.
Definition p_k0_285_316_cfg0_3 : plan := PMmap p_k0_285_316_oom2 Qd7.
Definition p_k0_285_316_exit3_4 : plan := Qd5.
Definition p_k0_285_316_cfgpos_5 : plan := Qdt19 p_k0_285_316_oom2 XC 0 p_k0_285_316_exit3_4 XC 1 p_k0_285_316_exit3_4 XC 2 p_k0_285_316_exit3_4.
Definition p_k0_285_316 : plan := Qdt3 5 0 p_k0_285_316_cfg0_3 p_k0_285_316_cfgpos_5.

Definition s_k0_285_316 : shape := Qd18.

Lemma chk_k0_285_316 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 285 316) p_k0_285_316 = COk s_k0_285_316.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_285_316)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_126957_131051_cnt1 : plan := Qd2.
Definition p_k1_126957_131051_oom2 : plan := Qdt4 7 127 p_k1_126957_131051_cnt1 p_k1_126957_131051_cnt1.
Definition p_k1_126957_131051_cfg0_3 : plan := PMmap p_k1_126957_131051_oom2 Qd6.
Definition p_k1_126957_131051_exit3_4 : plan := Qd5.
Definition p_k1_126957_131051_cfgpos_5 : plan := PMmap p_k1_126957_131051_oom2 (Qdt11 XC 0 p_k1_126957_131051_exit3_4 XC 1 p_k1_126957_131051_exit3_4 XC 2 p_k1_126957_131051_exit3_4).
Definition p_k1_126957_131051 : plan := Qdt3 5 0 p_k1_126957_131051_cfg0_3 p_k1_126957_131051_cfgpos_5.

Definition s_k1_126957_131051 : shape := Qd18.

Lemma chk_k1_126957_131051 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 126957 131051) p_k1_126957_131051 = COk s_k1_126957_131051.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_126957_131051)). Qed.

