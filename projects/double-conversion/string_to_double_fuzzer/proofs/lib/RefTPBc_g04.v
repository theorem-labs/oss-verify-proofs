(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import SymExec3 SymPlan RefTargetEntry_defs RefTargetEntryK_defs.
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
Definition p_k0_669_796_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_669_796_oom2 : plan := Qdt4 7 127 p_k0_669_796_cnt1 p_k0_669_796_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qd7 := (PCall SumEnframe [] Qd6) (only parsing).
Definition p_k0_669_796_cfg0_3 : plan := PMmap p_k0_669_796_oom2 Qd7.
Definition p_k0_669_796_exit3_4 : plan := Qd5.
Local Abbreviation Qd8 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt9 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp1 Qdp2 Qdp3 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp4 Qdp5 Qdp6 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp7 Qdp8 Qdp9 Qd8)))))))))))))))))))))) (only parsing).
Local Abbreviation Qdt10 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (Qdt9 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10))) (only parsing).
Definition p_k0_669_796_cfgpos_5 : plan := Qdt10 p_k0_669_796_oom2 XC 0 p_k0_669_796_exit3_4 XC 1 p_k0_669_796_exit3_4 XC 2 p_k0_669_796_exit3_4.
Definition p_k0_669_796 : plan := Qdt3 5 0 p_k0_669_796_cfg0_3 p_k0_669_796_cfgpos_5.

Local Abbreviation Qdc2_11 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qdc4_12 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd13 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qd14 := (SEmit 1 (Qdc2_11 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qd15 := (SCase (EVar 5) 0 (SAlt2 Qd13 Qd14) (SAlt2 Qd13 (SEmit 1 (Qdc2_11 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd14 (SCase Qd1 2 (SEmit 1 (Qdc4_12 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_12 48 10 48 10 (Qdc2_11 48 10 [])) (SExit 0)))))))) (only parsing).
Definition s_k0_669_796 : shape := Qd15.

Lemma chk_k0_669_796 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 669 796) p_k0_669_796 = COk s_k0_669_796.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_669_796)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_797_1004_cnt1 : plan := Qd2.
Definition p_k0_797_1004_oom2 : plan := Qdt4 7 127 p_k0_797_1004_cnt1 p_k0_797_1004_cnt1.
Definition p_k0_797_1004_cfg0_3 : plan := PMmap p_k0_797_1004_oom2 Qd7.
Definition p_k0_797_1004_exit3_4 : plan := Qd5.
Definition p_k0_797_1004_cfgpos_5 : plan := Qdt10 p_k0_797_1004_oom2 XC 0 p_k0_797_1004_exit3_4 XC 1 p_k0_797_1004_exit3_4 XC 2 p_k0_797_1004_exit3_4.
Definition p_k0_797_1004 : plan := Qdt3 5 0 p_k0_797_1004_cfg0_3 p_k0_797_1004_cfgpos_5.

Definition s_k0_797_1004 : shape := Qd15.

Lemma chk_k0_797_1004 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 797 1004) p_k0_797_1004 = COk s_k0_797_1004.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_797_1004)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1005_1148_cnt1 : plan := Qd2.
Definition p_k0_1005_1148_oom2 : plan := Qdt4 7 127 p_k0_1005_1148_cnt1 p_k0_1005_1148_cnt1.
Local Abbreviation Qdt16 Qdp1 := (PMmap Qdp1 Qd6) (only parsing).
Definition p_k0_1005_1148_cfg0_3 : plan := Qdt16 p_k0_1005_1148_oom2.
Definition p_k0_1005_1148_exit3_4 : plan := Qd5.
Local Abbreviation Qdt17 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (Qdt9 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10)) (only parsing).
Definition p_k0_1005_1148_cfgpos_5 : plan := Qdt17 p_k0_1005_1148_oom2 XC 0 p_k0_1005_1148_exit3_4 XC 1 p_k0_1005_1148_exit3_4 XC 2 p_k0_1005_1148_exit3_4.
Definition p_k0_1005_1148 : plan := Qdt3 5 0 p_k0_1005_1148_cfg0_3 p_k0_1005_1148_cfgpos_5.

Definition s_k0_1005_1148 : shape := Qd15.

Lemma chk_k0_1005_1148 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 1005 1148) p_k0_1005_1148 = COk s_k0_1005_1148.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1005_1148)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1149_1340_cnt1 : plan := Qd2.
Definition p_k0_1149_1340_oom2 : plan := Qdt4 7 127 p_k0_1149_1340_cnt1 p_k0_1149_1340_cnt1.
Definition p_k0_1149_1340_cfg0_3 : plan := Qdt16 p_k0_1149_1340_oom2.
Definition p_k0_1149_1340_exit3_4 : plan := Qd5.
Definition p_k0_1149_1340_cfgpos_5 : plan := Qdt17 p_k0_1149_1340_oom2 XC 0 p_k0_1149_1340_exit3_4 XC 1 p_k0_1149_1340_exit3_4 XC 2 p_k0_1149_1340_exit3_4.
Definition p_k0_1149_1340 : plan := Qdt3 5 0 p_k0_1149_1340_cfg0_3 p_k0_1149_1340_cfgpos_5.

Definition s_k0_1149_1340 : shape := Qd15.

Lemma chk_k0_1149_1340 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 1149 1340) p_k0_1149_1340 = COk s_k0_1149_1340.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1149_1340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1341_1628_cnt1 : plan := Qd2.
Definition p_k0_1341_1628_oom2 : plan := Qdt4 7 127 p_k0_1341_1628_cnt1 p_k0_1341_1628_cnt1.
Definition p_k0_1341_1628_cfg0_3 : plan := Qdt16 p_k0_1341_1628_oom2.
Definition p_k0_1341_1628_exit3_4 : plan := Qd5.
Definition p_k0_1341_1628_cfgpos_5 : plan := Qdt17 p_k0_1341_1628_oom2 XC 0 p_k0_1341_1628_exit3_4 XC 1 p_k0_1341_1628_exit3_4 XC 2 p_k0_1341_1628_exit3_4.
Definition p_k0_1341_1628 : plan := Qdt3 5 0 p_k0_1341_1628_cfg0_3 p_k0_1341_1628_cfgpos_5.

Definition s_k0_1341_1628 : shape := Qd15.

Lemma chk_k0_1341_1628 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 1341 1628) p_k0_1341_1628 = COk s_k0_1341_1628.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1341_1628)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1629_2028_cnt1 : plan := Qd2.
Definition p_k0_1629_2028_oom2 : plan := Qdt4 7 127 p_k0_1629_2028_cnt1 p_k0_1629_2028_cnt1.
Definition p_k0_1629_2028_cfg0_3 : plan := Qdt16 p_k0_1629_2028_oom2.
Definition p_k0_1629_2028_exit3_4 : plan := Qd5.
Definition p_k0_1629_2028_cfgpos_5 : plan := Qdt17 p_k0_1629_2028_oom2 XC 0 p_k0_1629_2028_exit3_4 XC 1 p_k0_1629_2028_exit3_4 XC 2 p_k0_1629_2028_exit3_4.
Definition p_k0_1629_2028 : plan := Qdt3 5 0 p_k0_1629_2028_cfg0_3 p_k0_1629_2028_cfgpos_5.

Definition s_k0_1629_2028 : shape := Qd15.

Lemma chk_k0_1629_2028 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 1629 2028) p_k0_1629_2028 = COk s_k0_1629_2028.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1629_2028)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2029_2332_cnt1 : plan := Qd2.
Definition p_k0_2029_2332_oom2 : plan := Qdt4 7 127 p_k0_2029_2332_cnt1 p_k0_2029_2332_cnt1.
Definition p_k0_2029_2332_cfg0_3 : plan := Qdt16 p_k0_2029_2332_oom2.
Definition p_k0_2029_2332_exit3_4 : plan := Qd5.
Definition p_k0_2029_2332_cfgpos_5 : plan := Qdt17 p_k0_2029_2332_oom2 XC 0 p_k0_2029_2332_exit3_4 XC 1 p_k0_2029_2332_exit3_4 XC 2 p_k0_2029_2332_exit3_4.
Definition p_k0_2029_2332 : plan := Qdt3 5 0 p_k0_2029_2332_cfg0_3 p_k0_2029_2332_cfgpos_5.

Definition s_k0_2029_2332 : shape := Qd15.

Lemma chk_k0_2029_2332 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 2029 2332) p_k0_2029_2332 = COk s_k0_2029_2332.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_2029_2332)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2333_2716_cnt1 : plan := Qd2.
Definition p_k0_2333_2716_oom2 : plan := Qdt4 7 127 p_k0_2333_2716_cnt1 p_k0_2333_2716_cnt1.
Definition p_k0_2333_2716_cfg0_3 : plan := Qdt16 p_k0_2333_2716_oom2.
Definition p_k0_2333_2716_exit3_4 : plan := Qd5.
Definition p_k0_2333_2716_cfgpos_5 : plan := Qdt17 p_k0_2333_2716_oom2 XC 0 p_k0_2333_2716_exit3_4 XC 1 p_k0_2333_2716_exit3_4 XC 2 p_k0_2333_2716_exit3_4.
Definition p_k0_2333_2716 : plan := Qdt3 5 0 p_k0_2333_2716_cfg0_3 p_k0_2333_2716_cfgpos_5.

Definition s_k0_2333_2716 : shape := Qd15.

Lemma chk_k0_2333_2716 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 2333 2716) p_k0_2333_2716 = COk s_k0_2333_2716.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_2333_2716)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2717_3260_cnt1 : plan := Qd2.
Definition p_k0_2717_3260_oom2 : plan := Qdt4 7 127 p_k0_2717_3260_cnt1 p_k0_2717_3260_cnt1.
Definition p_k0_2717_3260_cfg0_3 : plan := Qdt16 p_k0_2717_3260_oom2.
Definition p_k0_2717_3260_exit3_4 : plan := Qd5.
Definition p_k0_2717_3260_cfgpos_5 : plan := Qdt17 p_k0_2717_3260_oom2 XC 0 p_k0_2717_3260_exit3_4 XC 1 p_k0_2717_3260_exit3_4 XC 2 p_k0_2717_3260_exit3_4.
Definition p_k0_2717_3260 : plan := Qdt3 5 0 p_k0_2717_3260_cfg0_3 p_k0_2717_3260_cfgpos_5.

Definition s_k0_2717_3260 : shape := Qd15.

Lemma chk_k0_2717_3260 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 2717 3260) p_k0_2717_3260 = COk s_k0_2717_3260.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_2717_3260)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_3261_4076_cnt1 : plan := Qd2.
Definition p_k0_3261_4076_oom2 : plan := Qdt4 7 127 p_k0_3261_4076_cnt1 p_k0_3261_4076_cnt1.
Definition p_k0_3261_4076_cfg0_3 : plan := Qdt16 p_k0_3261_4076_oom2.
Definition p_k0_3261_4076_exit3_4 : plan := Qd5.
Definition p_k0_3261_4076_cfgpos_5 : plan := Qdt17 p_k0_3261_4076_oom2 XC 0 p_k0_3261_4076_exit3_4 XC 1 p_k0_3261_4076_exit3_4 XC 2 p_k0_3261_4076_exit3_4.
Definition p_k0_3261_4076 : plan := Qdt3 5 0 p_k0_3261_4076_cfg0_3 p_k0_3261_4076_cfgpos_5.

Definition s_k0_3261_4076 : shape := Qd15.

Lemma chk_k0_3261_4076 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 3261 4076) p_k0_3261_4076 = COk s_k0_3261_4076.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_3261_4076)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_4077_4668_cnt1 : plan := Qd2.
Definition p_k0_4077_4668_oom2 : plan := Qdt4 7 127 p_k0_4077_4668_cnt1 p_k0_4077_4668_cnt1.
Definition p_k0_4077_4668_cfg0_3 : plan := Qdt16 p_k0_4077_4668_oom2.
Definition p_k0_4077_4668_exit3_4 : plan := Qd5.
Definition p_k0_4077_4668_cfgpos_5 : plan := Qdt17 p_k0_4077_4668_oom2 XC 0 p_k0_4077_4668_exit3_4 XC 1 p_k0_4077_4668_exit3_4 XC 2 p_k0_4077_4668_exit3_4.
Definition p_k0_4077_4668 : plan := Qdt3 5 0 p_k0_4077_4668_cfg0_3 p_k0_4077_4668_cfgpos_5.

Definition s_k0_4077_4668 : shape := Qd15.

Lemma chk_k0_4077_4668 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 4077 4668) p_k0_4077_4668 = COk s_k0_4077_4668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_4077_4668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_4669_5436_cnt1 : plan := Qd2.
Definition p_k0_4669_5436_oom2 : plan := Qdt4 7 127 p_k0_4669_5436_cnt1 p_k0_4669_5436_cnt1.
Definition p_k0_4669_5436_cfg0_3 : plan := Qdt16 p_k0_4669_5436_oom2.
Definition p_k0_4669_5436_exit3_4 : plan := Qd5.
Definition p_k0_4669_5436_cfgpos_5 : plan := Qdt17 p_k0_4669_5436_oom2 XC 0 p_k0_4669_5436_exit3_4 XC 1 p_k0_4669_5436_exit3_4 XC 2 p_k0_4669_5436_exit3_4.
Definition p_k0_4669_5436 : plan := Qdt3 5 0 p_k0_4669_5436_cfg0_3 p_k0_4669_5436_cfgpos_5.

Definition s_k0_4669_5436 : shape := Qd15.

Lemma chk_k0_4669_5436 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 4669 5436) p_k0_4669_5436 = COk s_k0_4669_5436.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_4669_5436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_12269_13084_cnt1 : plan := Qd2.
Definition p_k0_12269_13084_oom2 : plan := Qdt4 7 127 p_k0_12269_13084_cnt1 p_k0_12269_13084_cnt1.
Definition p_k0_12269_13084_cfg0_3 : plan := Qdt16 p_k0_12269_13084_oom2.
Definition p_k0_12269_13084_exit3_4 : plan := Qd5.
Definition p_k0_12269_13084_cfgpos_5 : plan := Qdt17 p_k0_12269_13084_oom2 XC 0 p_k0_12269_13084_exit3_4 XC 1 p_k0_12269_13084_exit3_4 XC 2 p_k0_12269_13084_exit3_4.
Definition p_k0_12269_13084 : plan := Qdt3 5 0 p_k0_12269_13084_cfg0_3 p_k0_12269_13084_cfgpos_5.

Definition s_k0_12269_13084 : shape := Qd15.

Lemma chk_k0_12269_13084 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 12269 13084) p_k0_12269_13084 = COk s_k0_12269_13084.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_12269_13084)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_65517_65529_cnt1 : plan := Qd2.
Definition p_k0_65517_65529_oom2 : plan := Qdt4 7 127 p_k0_65517_65529_cnt1 p_k0_65517_65529_cnt1.
Definition p_k0_65517_65529_cfg0_3 : plan := Qdt16 p_k0_65517_65529_oom2.
Definition p_k0_65517_65529_exit3_4 : plan := Qd5.
Definition p_k0_65517_65529_cfgpos_5 : plan := Qdt17 p_k0_65517_65529_oom2 XC 0 p_k0_65517_65529_exit3_4 XC 1 p_k0_65517_65529_exit3_4 XC 2 p_k0_65517_65529_exit3_4.
Definition p_k0_65517_65529 : plan := Qdt3 5 0 p_k0_65517_65529_cfg0_3 p_k0_65517_65529_cfgpos_5.

Definition s_k0_65517_65529 : shape := Qd15.

Lemma chk_k0_65517_65529 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 65517 65529) p_k0_65517_65529 = COk s_k0_65517_65529.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_65517_65529)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_104829_106476_cnt1 : plan := Qd2.
Definition p_k1_104829_106476_oom2 : plan := Qdt4 7 127 p_k1_104829_106476_cnt1 p_k1_104829_106476_cnt1.
Definition p_k1_104829_106476_cfg0_3 : plan := Qdt16 p_k1_104829_106476_oom2.
Definition p_k1_104829_106476_exit3_4 : plan := Qd5.
Definition p_k1_104829_106476_cfgpos_5 : plan := Qdt17 p_k1_104829_106476_oom2 XC 0 p_k1_104829_106476_exit3_4 XC 1 p_k1_104829_106476_exit3_4 XC 2 p_k1_104829_106476_exit3_4.
Definition p_k1_104829_106476 : plan := Qdt3 5 0 p_k1_104829_106476_cfg0_3 p_k1_104829_106476_cfgpos_5.

Definition s_k1_104829_106476 : shape := Qd15.

Lemma chk_k1_104829_106476 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 104829 106476) p_k1_104829_106476 = COk s_k1_104829_106476.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_104829_106476)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_131052_131065_cnt1 : plan := Qd2.
Definition p_k1_131052_131065_oom2 : plan := Qdt4 7 127 p_k1_131052_131065_cnt1 p_k1_131052_131065_cnt1.
Definition p_k1_131052_131065_cfg0_3 : plan := Qdt16 p_k1_131052_131065_oom2.
Definition p_k1_131052_131065_exit3_4 : plan := Qd5.
Definition p_k1_131052_131065_cfgpos_5 : plan := Qdt17 p_k1_131052_131065_oom2 XC 0 p_k1_131052_131065_exit3_4 XC 1 p_k1_131052_131065_exit3_4 XC 2 p_k1_131052_131065_exit3_4.
Definition p_k1_131052_131065 : plan := Qdt3 5 0 p_k1_131052_131065_cfg0_3 p_k1_131052_131065_cfgpos_5.

Definition s_k1_131052_131065 : shape := Qd15.

Lemma chk_k1_131052_131065 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 131052 131065) p_k1_131052_131065 = COk s_k1_131052_131065.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_131052_131065)). Qed.

