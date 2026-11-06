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
Definition p_k1_74877_77804_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k1_74877_77804_oom2 : plan := Qdt4 7 127 p_k1_74877_77804_cnt1 p_k1_74877_77804_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qdt7 Qdp1 := (PMmap Qdp1 Qd6) (only parsing).
Definition p_k1_74877_77804_cfg0_3 : plan := Qdt7 p_k1_74877_77804_oom2.
Definition p_k1_74877_77804_exit3_4 : plan := Qd5.
Local Abbreviation Qd8 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt9 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp2 Qdp3 Qdp4 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp5 Qdp6 Qdp7 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp8 Qdp9 Qdp10 Qd8))))))))))))))))))))))) (only parsing).
Definition p_k1_74877_77804_cfgpos_5 : plan := Qdt9 p_k1_74877_77804_oom2 XC 0 p_k1_74877_77804_exit3_4 XC 1 p_k1_74877_77804_exit3_4 XC 2 p_k1_74877_77804_exit3_4.
Definition p_k1_74877_77804 : plan := Qdt3 5 0 p_k1_74877_77804_cfg0_3 p_k1_74877_77804_cfgpos_5.

Local Abbreviation Qdc2_10 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qdc4_11 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd12 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qd13 := (SEmit 1 (Qdc2_10 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qd14 := (SCase (EVar 5) 0 (SAlt2 Qd12 Qd13) (SAlt2 Qd12 (SEmit 1 (Qdc2_10 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd13 (SCase Qd1 2 (SEmit 1 (Qdc4_11 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_11 48 10 48 10 (Qdc2_10 48 10 [])) (SExit 0)))))))) (only parsing).
Definition s_k1_74877_77804 : shape := Qd14.

Lemma chk_k1_74877_77804 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 74877 77804) p_k1_74877_77804 = COk s_k1_74877_77804.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_74877_77804)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_77805_81900_cnt1 : plan := Qd2.
Definition p_k1_77805_81900_oom2 : plan := Qdt4 7 127 p_k1_77805_81900_cnt1 p_k1_77805_81900_cnt1.
Definition p_k1_77805_81900_cfg0_3 : plan := Qdt7 p_k1_77805_81900_oom2.
Definition p_k1_77805_81900_exit3_4 : plan := Qd5.
Definition p_k1_77805_81900_cfgpos_5 : plan := Qdt9 p_k1_77805_81900_oom2 XC 0 p_k1_77805_81900_exit3_4 XC 1 p_k1_77805_81900_exit3_4 XC 2 p_k1_77805_81900_exit3_4.
Definition p_k1_77805_81900 : plan := Qdt3 5 0 p_k1_77805_81900_cfg0_3 p_k1_77805_81900_cfgpos_5.

Definition s_k1_77805_81900 : shape := Qd14.

Lemma chk_k1_77805_81900 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 77805 81900) p_k1_77805_81900 = COk s_k1_77805_81900.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_77805_81900)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_81901_85996_cnt1 : plan := Qd2.
Definition p_k1_81901_85996_oom2 : plan := Qdt4 7 127 p_k1_81901_85996_cnt1 p_k1_81901_85996_cnt1.
Definition p_k1_81901_85996_cfg0_3 : plan := Qdt7 p_k1_81901_85996_oom2.
Definition p_k1_81901_85996_exit3_4 : plan := Qd5.
Definition p_k1_81901_85996_cfgpos_5 : plan := Qdt9 p_k1_81901_85996_oom2 XC 0 p_k1_81901_85996_exit3_4 XC 1 p_k1_81901_85996_exit3_4 XC 2 p_k1_81901_85996_exit3_4.
Definition p_k1_81901_85996 : plan := Qdt3 5 0 p_k1_81901_85996_cfg0_3 p_k1_81901_85996_cfgpos_5.

Definition s_k1_81901_85996 : shape := Qd14.

Lemma chk_k1_81901_85996 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 81901 85996) p_k1_81901_85996 = COk s_k1_81901_85996.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_81901_85996)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_87357_90092_cnt1 : plan := Qd2.
Definition p_k1_87357_90092_oom2 : plan := Qdt4 7 127 p_k1_87357_90092_cnt1 p_k1_87357_90092_cnt1.
Definition p_k1_87357_90092_cfg0_3 : plan := Qdt7 p_k1_87357_90092_oom2.
Definition p_k1_87357_90092_exit3_4 : plan := Qd5.
Definition p_k1_87357_90092_cfgpos_5 : plan := Qdt9 p_k1_87357_90092_oom2 XC 0 p_k1_87357_90092_exit3_4 XC 1 p_k1_87357_90092_exit3_4 XC 2 p_k1_87357_90092_exit3_4.
Definition p_k1_87357_90092 : plan := Qdt3 5 0 p_k1_87357_90092_cfg0_3 p_k1_87357_90092_cfgpos_5.

Definition s_k1_87357_90092 : shape := Qd14.

Lemma chk_k1_87357_90092 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 87357 90092) p_k1_87357_90092 = COk s_k1_87357_90092.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_87357_90092)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_90093_94188_cnt1 : plan := Qd2.
Definition p_k1_90093_94188_oom2 : plan := Qdt4 7 127 p_k1_90093_94188_cnt1 p_k1_90093_94188_cnt1.
Definition p_k1_90093_94188_cfg0_3 : plan := Qdt7 p_k1_90093_94188_oom2.
Definition p_k1_90093_94188_exit3_4 : plan := Qd5.
Definition p_k1_90093_94188_cfgpos_5 : plan := Qdt9 p_k1_90093_94188_oom2 XC 0 p_k1_90093_94188_exit3_4 XC 1 p_k1_90093_94188_exit3_4 XC 2 p_k1_90093_94188_exit3_4.
Definition p_k1_90093_94188 : plan := Qdt3 5 0 p_k1_90093_94188_cfg0_3 p_k1_90093_94188_cfgpos_5.

Definition s_k1_90093_94188 : shape := Qd14.

Lemma chk_k1_90093_94188 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 90093 94188) p_k1_90093_94188 = COk s_k1_90093_94188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_90093_94188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_94189_98284_cnt1 : plan := Qd2.
Definition p_k1_94189_98284_oom2 : plan := Qdt4 7 127 p_k1_94189_98284_cnt1 p_k1_94189_98284_cnt1.
Definition p_k1_94189_98284_cfg0_3 : plan := Qdt7 p_k1_94189_98284_oom2.
Definition p_k1_94189_98284_exit3_4 : plan := Qd5.
Definition p_k1_94189_98284_cfgpos_5 : plan := Qdt9 p_k1_94189_98284_oom2 XC 0 p_k1_94189_98284_exit3_4 XC 1 p_k1_94189_98284_exit3_4 XC 2 p_k1_94189_98284_exit3_4.
Definition p_k1_94189_98284 : plan := Qdt3 5 0 p_k1_94189_98284_cfg0_3 p_k1_94189_98284_cfgpos_5.

Definition s_k1_94189_98284 : shape := Qd14.

Lemma chk_k1_94189_98284 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 94189 98284) p_k1_94189_98284 = COk s_k1_94189_98284.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_94189_98284)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_98285_102380_cnt1 : plan := Qd2.
Definition p_k1_98285_102380_oom2 : plan := Qdt4 7 127 p_k1_98285_102380_cnt1 p_k1_98285_102380_cnt1.
Definition p_k1_98285_102380_cfg0_3 : plan := Qdt7 p_k1_98285_102380_oom2.
Definition p_k1_98285_102380_exit3_4 : plan := Qd5.
Definition p_k1_98285_102380_cfgpos_5 : plan := Qdt9 p_k1_98285_102380_oom2 XC 0 p_k1_98285_102380_exit3_4 XC 1 p_k1_98285_102380_exit3_4 XC 2 p_k1_98285_102380_exit3_4.
Definition p_k1_98285_102380 : plan := Qdt3 5 0 p_k1_98285_102380_cfg0_3 p_k1_98285_102380_cfgpos_5.

Definition s_k1_98285_102380 : shape := Qd14.

Lemma chk_k1_98285_102380 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 98285 102380) p_k1_98285_102380 = COk s_k1_98285_102380.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_98285_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_102381_104828_cnt1 : plan := Qd2.
Definition p_k1_102381_104828_oom2 : plan := Qdt4 7 127 p_k1_102381_104828_cnt1 p_k1_102381_104828_cnt1.
Definition p_k1_102381_104828_cfg0_3 : plan := Qdt7 p_k1_102381_104828_oom2.
Definition p_k1_102381_104828_exit3_4 : plan := Qd5.
Definition p_k1_102381_104828_cfgpos_5 : plan := Qdt9 p_k1_102381_104828_oom2 XC 0 p_k1_102381_104828_exit3_4 XC 1 p_k1_102381_104828_exit3_4 XC 2 p_k1_102381_104828_exit3_4.
Definition p_k1_102381_104828 : plan := Qdt3 5 0 p_k1_102381_104828_cfg0_3 p_k1_102381_104828_cfgpos_5.

Definition s_k1_102381_104828 : shape := Qd14.

Lemma chk_k1_102381_104828 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 102381 104828) p_k1_102381_104828 = COk s_k1_102381_104828.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_106477_110572_cnt1 : plan := Qd2.
Definition p_k1_106477_110572_oom2 : plan := Qdt4 7 127 p_k1_106477_110572_cnt1 p_k1_106477_110572_cnt1.
Definition p_k1_106477_110572_cfg0_3 : plan := Qdt7 p_k1_106477_110572_oom2.
Definition p_k1_106477_110572_exit3_4 : plan := Qd5.
Definition p_k1_106477_110572_cfgpos_5 : plan := Qdt9 p_k1_106477_110572_oom2 XC 0 p_k1_106477_110572_exit3_4 XC 1 p_k1_106477_110572_exit3_4 XC 2 p_k1_106477_110572_exit3_4.
Definition p_k1_106477_110572 : plan := Qdt3 5 0 p_k1_106477_110572_cfg0_3 p_k1_106477_110572_cfgpos_5.

Definition s_k1_106477_110572 : shape := Qd14.

Lemma chk_k1_106477_110572 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 106477 110572) p_k1_106477_110572 = COk s_k1_106477_110572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_110573_114668_cnt1 : plan := Qd2.
Definition p_k1_110573_114668_oom2 : plan := Qdt4 7 127 p_k1_110573_114668_cnt1 p_k1_110573_114668_cnt1.
Definition p_k1_110573_114668_cfg0_3 : plan := Qdt7 p_k1_110573_114668_oom2.
Definition p_k1_110573_114668_exit3_4 : plan := Qd5.
Definition p_k1_110573_114668_cfgpos_5 : plan := Qdt9 p_k1_110573_114668_oom2 XC 0 p_k1_110573_114668_exit3_4 XC 1 p_k1_110573_114668_exit3_4 XC 2 p_k1_110573_114668_exit3_4.
Definition p_k1_110573_114668 : plan := Qdt3 5 0 p_k1_110573_114668_cfg0_3 p_k1_110573_114668_cfgpos_5.

Definition s_k1_110573_114668 : shape := Qd14.

Lemma chk_k1_110573_114668 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 110573 114668) p_k1_110573_114668 = COk s_k1_110573_114668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_110573_114668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_114669_118764_cnt1 : plan := Qd2.
Definition p_k1_114669_118764_oom2 : plan := Qdt4 7 127 p_k1_114669_118764_cnt1 p_k1_114669_118764_cnt1.
Definition p_k1_114669_118764_cfg0_3 : plan := Qdt7 p_k1_114669_118764_oom2.
Definition p_k1_114669_118764_exit3_4 : plan := Qd5.
Definition p_k1_114669_118764_cfgpos_5 : plan := Qdt9 p_k1_114669_118764_oom2 XC 0 p_k1_114669_118764_exit3_4 XC 1 p_k1_114669_118764_exit3_4 XC 2 p_k1_114669_118764_exit3_4.
Definition p_k1_114669_118764 : plan := Qdt3 5 0 p_k1_114669_118764_cfg0_3 p_k1_114669_118764_cfgpos_5.

Definition s_k1_114669_118764 : shape := Qd14.

Lemma chk_k1_114669_118764 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 114669 118764) p_k1_114669_118764 = COk s_k1_114669_118764.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_114669_118764)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_118765_122860_cnt1 : plan := Qd2.
Definition p_k1_118765_122860_oom2 : plan := Qdt4 7 127 p_k1_118765_122860_cnt1 p_k1_118765_122860_cnt1.
Definition p_k1_118765_122860_cfg0_3 : plan := Qdt7 p_k1_118765_122860_oom2.
Definition p_k1_118765_122860_exit3_4 : plan := Qd5.
Definition p_k1_118765_122860_cfgpos_5 : plan := Qdt9 p_k1_118765_122860_oom2 XC 0 p_k1_118765_122860_exit3_4 XC 1 p_k1_118765_122860_exit3_4 XC 2 p_k1_118765_122860_exit3_4.
Definition p_k1_118765_122860 : plan := Qdt3 5 0 p_k1_118765_122860_cfg0_3 p_k1_118765_122860_cfgpos_5.

Definition s_k1_118765_122860 : shape := Qd14.

Lemma chk_k1_118765_122860 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 118765 122860) p_k1_118765_122860 = COk s_k1_118765_122860.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_122861_126956_cnt1 : plan := Qd2.
Definition p_k1_122861_126956_oom2 : plan := Qdt4 7 127 p_k1_122861_126956_cnt1 p_k1_122861_126956_cnt1.
Definition p_k1_122861_126956_cfg0_3 : plan := Qdt7 p_k1_122861_126956_oom2.
Definition p_k1_122861_126956_exit3_4 : plan := Qd5.
Definition p_k1_122861_126956_cfgpos_5 : plan := Qdt9 p_k1_122861_126956_oom2 XC 0 p_k1_122861_126956_exit3_4 XC 1 p_k1_122861_126956_exit3_4 XC 2 p_k1_122861_126956_exit3_4.
Definition p_k1_122861_126956 : plan := Qdt3 5 0 p_k1_122861_126956_cfg0_3 p_k1_122861_126956_cfgpos_5.

Definition s_k1_122861_126956 : shape := Qd14.

Lemma chk_k1_122861_126956 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 122861 126956) p_k1_122861_126956 = COk s_k1_122861_126956.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_122861_126956)). Qed.

