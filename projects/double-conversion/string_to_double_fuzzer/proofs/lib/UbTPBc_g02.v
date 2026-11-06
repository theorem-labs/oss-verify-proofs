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
Definition p_k0_36845_37436_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_36845_37436_oom2 : plan := Qdt3 7 127 p_k0_36845_37436_cnt1 p_k0_36845_37436_cnt1.
Local Abbreviation Qd4 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd5 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd4))))))))))))) (only parsing).
Definition p_k0_36845_37436_cfg0_3 : plan := PMmap p_k0_36845_37436_oom2 Qd5.
Definition p_k0_36845_37436_exit3_4 : plan := Qd4.
Local Abbreviation Qd6 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd4))) (only parsing).
Local Abbreviation Qdt7 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp2 Qdp3 Qdp4 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp5 Qdp6 Qdp7 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp8 Qdp9 Qdp10 Qd6))))))))))))))))))))))) (only parsing).
Definition p_k0_36845_37436_cfgpos_5 : plan := Qdt7 p_k0_36845_37436_oom2 XC 0 p_k0_36845_37436_exit3_4 XC 1 p_k0_36845_37436_exit3_4 XC 2 p_k0_36845_37436_exit3_4.
Definition p_k0_36845_37436 : plan := PSplit (EVar 5) 0 p_k0_36845_37436_cfg0_3 p_k0_36845_37436_cfgpos_5.

Local Abbreviation Qd8 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qdc2_9 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qd10 := (SEmit 1 (Qdc2_9 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qdc4_11 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd12 := (SAlt2 Qd8 (SEmit 1 (Qdc2_9 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd10 (SCase Qd1 2 (SEmit 1 (Qdc4_11 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_11 48 10 48 10 (Qdc2_9 48 10 [])) (SExit 0))))))) (only parsing).
Local Abbreviation Qd13 := (SCase (EVar 5) 0 (SAlt2 Qd8 Qd10) Qd12) (only parsing).
Definition s_k0_36845_37436 : shape := Qd13.

Lemma chk_k0_36845_37436 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 36845 37436) p_k0_36845_37436 = COk s_k0_36845_37436.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_52413_53228_cnt1 : plan := Qd2.
Definition p_k0_52413_53228_oom2 : plan := Qdt3 7 127 p_k0_52413_53228_cnt1 p_k0_52413_53228_cnt1.
Definition p_k0_52413_53228_cfg0_3 : plan := PMmap p_k0_52413_53228_oom2 Qd5.
Definition p_k0_52413_53228_exit3_4 : plan := Qd4.
Definition p_k0_52413_53228_cfgpos_5 : plan := Qdt7 p_k0_52413_53228_oom2 XC 0 p_k0_52413_53228_exit3_4 XC 1 p_k0_52413_53228_exit3_4 XC 2 p_k0_52413_53228_exit3_4.
Definition p_k0_52413_53228 : plan := PSplit (EVar 5) 0 p_k0_52413_53228_cfg0_3 p_k0_52413_53228_cfgpos_5.

Definition s_k0_52413_53228 : shape := Qd13.

Lemma chk_k0_52413_53228 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 52413 53228) p_k0_52413_53228 = COk s_k0_52413_53228.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_52413_53228)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_37437_40940_cnt1 : plan := Qd2.
Definition p_k1_37437_40940_exit3_2 : plan := Qd4.
Definition p_k1_37437_40940_oom3 : plan := Qdt3 7 127 p_k1_37437_40940_cnt1 p_k1_37437_40940_cnt1.
Definition p_k1_37437_40940_cfgpos_4 : plan := Qdt7 p_k1_37437_40940_oom3 XC 0 p_k1_37437_40940_exit3_2 XC 1 p_k1_37437_40940_exit3_2 XC 2 p_k1_37437_40940_exit3_2.
Local Abbreviation Qdt14 Qdp1 Qdp2 Qdp3 := (PSplit (EVar Qdp1) Qdp2 PContra Qdp3) (only parsing).
Definition p_k1_37437_40940 : plan := Qdt14 5 0 p_k1_37437_40940_cfgpos_4.

Local Abbreviation Qd15 := (SCase (EVar 5) 0 SNil Qd12) (only parsing).
Definition s_k1_37437_40940 : shape := Qd15.

Lemma chk_k1_37437_40940 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 37437 40940) p_k1_37437_40940 = COk s_k1_37437_40940.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_37437_40940)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_40941_43676_cnt1 : plan := Qd2.
Definition p_k1_40941_43676_exit3_2 : plan := Qd4.
Definition p_k1_40941_43676_oom3 : plan := Qdt3 7 127 p_k1_40941_43676_cnt1 p_k1_40941_43676_cnt1.
Definition p_k1_40941_43676_cfgpos_4 : plan := Qdt7 p_k1_40941_43676_oom3 XC 0 p_k1_40941_43676_exit3_2 XC 1 p_k1_40941_43676_exit3_2 XC 2 p_k1_40941_43676_exit3_2.
Definition p_k1_40941_43676 : plan := Qdt14 5 0 p_k1_40941_43676_cfgpos_4.

Definition s_k1_40941_43676 : shape := Qd15.

Lemma chk_k1_40941_43676 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 40941 43676) p_k1_40941_43676 = COk s_k1_40941_43676.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_40941_43676)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_43677_45036_cnt1 : plan := Qd2.
Definition p_k1_43677_45036_exit3_2 : plan := Qd4.
Definition p_k1_43677_45036_oom3 : plan := Qdt3 7 127 p_k1_43677_45036_cnt1 p_k1_43677_45036_cnt1.
Definition p_k1_43677_45036_cfgpos_4 : plan := Qdt7 p_k1_43677_45036_oom3 XC 0 p_k1_43677_45036_exit3_2 XC 1 p_k1_43677_45036_exit3_2 XC 2 p_k1_43677_45036_exit3_2.
Definition p_k1_43677_45036 : plan := Qdt14 5 0 p_k1_43677_45036_cfgpos_4.

Definition s_k1_43677_45036 : shape := Qd15.

Lemma chk_k1_43677_45036 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 43677 45036) p_k1_43677_45036 = COk s_k1_43677_45036.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_43677_45036)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_45037_49132_cnt1 : plan := Qd2.
Definition p_k1_45037_49132_exit3_2 : plan := Qd4.
Definition p_k1_45037_49132_oom3 : plan := Qdt3 7 127 p_k1_45037_49132_cnt1 p_k1_45037_49132_cnt1.
Definition p_k1_45037_49132_cfgpos_4 : plan := Qdt7 p_k1_45037_49132_oom3 XC 0 p_k1_45037_49132_exit3_2 XC 1 p_k1_45037_49132_exit3_2 XC 2 p_k1_45037_49132_exit3_2.
Definition p_k1_45037_49132 : plan := Qdt14 5 0 p_k1_45037_49132_cfgpos_4.

Definition s_k1_45037_49132 : shape := Qd15.

Lemma chk_k1_45037_49132 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 45037 49132) p_k1_45037_49132 = COk s_k1_45037_49132.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_49133_52412_cnt1 : plan := Qd2.
Definition p_k1_49133_52412_exit3_2 : plan := Qd4.
Definition p_k1_49133_52412_oom3 : plan := Qdt3 7 127 p_k1_49133_52412_cnt1 p_k1_49133_52412_cnt1.
Definition p_k1_49133_52412_cfgpos_4 : plan := Qdt7 p_k1_49133_52412_oom3 XC 0 p_k1_49133_52412_exit3_2 XC 1 p_k1_49133_52412_exit3_2 XC 2 p_k1_49133_52412_exit3_2.
Definition p_k1_49133_52412 : plan := Qdt14 5 0 p_k1_49133_52412_cfgpos_4.

Definition s_k1_49133_52412 : shape := Qd15.

Lemma chk_k1_49133_52412 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 49133 52412) p_k1_49133_52412 = COk s_k1_49133_52412.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_49133_52412)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_53229_57324_cnt1 : plan := Qd2.
Definition p_k1_53229_57324_exit3_2 : plan := Qd4.
Definition p_k1_53229_57324_oom3 : plan := Qdt3 7 127 p_k1_53229_57324_cnt1 p_k1_53229_57324_cnt1.
Definition p_k1_53229_57324_cfgpos_4 : plan := Qdt7 p_k1_53229_57324_oom3 XC 0 p_k1_53229_57324_exit3_2 XC 1 p_k1_53229_57324_exit3_2 XC 2 p_k1_53229_57324_exit3_2.
Definition p_k1_53229_57324 : plan := Qdt14 5 0 p_k1_53229_57324_cfgpos_4.

Definition s_k1_53229_57324 : shape := Qd15.

Lemma chk_k1_53229_57324 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 53229 57324) p_k1_53229_57324 = COk s_k1_53229_57324.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_53229_57324)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_57325_61420_cnt1 : plan := Qd2.
Definition p_k1_57325_61420_exit3_2 : plan := Qd4.
Definition p_k1_57325_61420_oom3 : plan := Qdt3 7 127 p_k1_57325_61420_cnt1 p_k1_57325_61420_cnt1.
Definition p_k1_57325_61420_cfgpos_4 : plan := Qdt7 p_k1_57325_61420_oom3 XC 0 p_k1_57325_61420_exit3_2 XC 1 p_k1_57325_61420_exit3_2 XC 2 p_k1_57325_61420_exit3_2.
Definition p_k1_57325_61420 : plan := Qdt14 5 0 p_k1_57325_61420_cfgpos_4.

Definition s_k1_57325_61420 : shape := Qd15.

Lemma chk_k1_57325_61420 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 57325 61420) p_k1_57325_61420 = COk s_k1_57325_61420.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_61421_65516_cnt1 : plan := Qd2.
Definition p_k1_61421_65516_exit3_2 : plan := Qd4.
Definition p_k1_61421_65516_oom3 : plan := Qdt3 7 127 p_k1_61421_65516_cnt1 p_k1_61421_65516_cnt1.
Definition p_k1_61421_65516_cfgpos_4 : plan := Qdt7 p_k1_61421_65516_oom3 XC 0 p_k1_61421_65516_exit3_2 XC 1 p_k1_61421_65516_exit3_2 XC 2 p_k1_61421_65516_exit3_2.
Definition p_k1_61421_65516 : plan := Qdt14 5 0 p_k1_61421_65516_cfgpos_4.

Definition s_k1_61421_65516 : shape := Qd15.

Lemma chk_k1_61421_65516 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 61421 65516) p_k1_61421_65516 = COk s_k1_61421_65516.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_98299_102380_cnt1 : plan := Qd2.
Definition p_k2_98299_102380_exit3_2 : plan := Qd4.
Definition p_k2_98299_102380_oom3 : plan := Qdt3 7 127 p_k2_98299_102380_cnt1 p_k2_98299_102380_cnt1.
Definition p_k2_98299_102380_cfgpos_4 : plan := Qdt7 p_k2_98299_102380_oom3 XC 0 p_k2_98299_102380_exit3_2 XC 1 p_k2_98299_102380_exit3_2 XC 2 p_k2_98299_102380_exit3_2.
Definition p_k2_98299_102380 : plan := Qdt14 5 0 p_k2_98299_102380_cfgpos_4.

Definition s_k2_98299_102380 : shape := Qd15.

Lemma chk_k2_98299_102380 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 98299 102380) p_k2_98299_102380 = COk s_k2_98299_102380.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_98299_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_102381_104828_cnt1 : plan := Qd2.
Definition p_k2_102381_104828_exit3_2 : plan := Qd4.
Definition p_k2_102381_104828_oom3 : plan := Qdt3 7 127 p_k2_102381_104828_cnt1 p_k2_102381_104828_cnt1.
Definition p_k2_102381_104828_cfgpos_4 : plan := Qdt7 p_k2_102381_104828_oom3 XC 0 p_k2_102381_104828_exit3_2 XC 1 p_k2_102381_104828_exit3_2 XC 2 p_k2_102381_104828_exit3_2.
Definition p_k2_102381_104828 : plan := Qdt14 5 0 p_k2_102381_104828_cfgpos_4.

Definition s_k2_102381_104828 : shape := Qd15.

Lemma chk_k2_102381_104828 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 102381 104828) p_k2_102381_104828 = COk s_k2_102381_104828.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_106477_110572_cnt1 : plan := Qd2.
Definition p_k2_106477_110572_exit3_2 : plan := Qd4.
Definition p_k2_106477_110572_oom3 : plan := Qdt3 7 127 p_k2_106477_110572_cnt1 p_k2_106477_110572_cnt1.
Definition p_k2_106477_110572_cfgpos_4 : plan := Qdt7 p_k2_106477_110572_oom3 XC 0 p_k2_106477_110572_exit3_2 XC 1 p_k2_106477_110572_exit3_2 XC 2 p_k2_106477_110572_exit3_2.
Definition p_k2_106477_110572 : plan := Qdt14 5 0 p_k2_106477_110572_cfgpos_4.

Definition s_k2_106477_110572 : shape := Qd15.

Lemma chk_k2_106477_110572 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 106477 110572) p_k2_106477_110572 = COk s_k2_106477_110572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_110573_114668_cnt1 : plan := Qd2.
Definition p_k2_110573_114668_exit3_2 : plan := Qd4.
Definition p_k2_110573_114668_oom3 : plan := Qdt3 7 127 p_k2_110573_114668_cnt1 p_k2_110573_114668_cnt1.
Definition p_k2_110573_114668_cfgpos_4 : plan := Qdt7 p_k2_110573_114668_oom3 XC 0 p_k2_110573_114668_exit3_2 XC 1 p_k2_110573_114668_exit3_2 XC 2 p_k2_110573_114668_exit3_2.
Definition p_k2_110573_114668 : plan := Qdt14 5 0 p_k2_110573_114668_cfgpos_4.

Definition s_k2_110573_114668 : shape := Qd15.

Lemma chk_k2_110573_114668 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 110573 114668) p_k2_110573_114668 = COk s_k2_110573_114668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_110573_114668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_114669_118764_cnt1 : plan := Qd2.
Definition p_k2_114669_118764_exit3_2 : plan := Qd4.
Definition p_k2_114669_118764_oom3 : plan := Qdt3 7 127 p_k2_114669_118764_cnt1 p_k2_114669_118764_cnt1.
Definition p_k2_114669_118764_cfgpos_4 : plan := Qdt7 p_k2_114669_118764_oom3 XC 0 p_k2_114669_118764_exit3_2 XC 1 p_k2_114669_118764_exit3_2 XC 2 p_k2_114669_118764_exit3_2.
Definition p_k2_114669_118764 : plan := Qdt14 5 0 p_k2_114669_118764_cfgpos_4.

Definition s_k2_114669_118764 : shape := Qd15.

Lemma chk_k2_114669_118764 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 114669 118764) p_k2_114669_118764 = COk s_k2_114669_118764.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_114669_118764)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_118765_122860_cnt1 : plan := Qd2.
Definition p_k2_118765_122860_exit3_2 : plan := Qd4.
Definition p_k2_118765_122860_oom3 : plan := Qdt3 7 127 p_k2_118765_122860_cnt1 p_k2_118765_122860_cnt1.
Definition p_k2_118765_122860_cfgpos_4 : plan := Qdt7 p_k2_118765_122860_oom3 XC 0 p_k2_118765_122860_exit3_2 XC 1 p_k2_118765_122860_exit3_2 XC 2 p_k2_118765_122860_exit3_2.
Definition p_k2_118765_122860 : plan := Qdt14 5 0 p_k2_118765_122860_cfgpos_4.

Definition s_k2_118765_122860 : shape := Qd15.

Lemma chk_k2_118765_122860 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 118765 122860) p_k2_118765_122860 = COk s_k2_118765_122860.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_122861_126956_cnt1 : plan := Qd2.
Definition p_k2_122861_126956_exit3_2 : plan := Qd4.
Definition p_k2_122861_126956_oom3 : plan := Qdt3 7 127 p_k2_122861_126956_cnt1 p_k2_122861_126956_cnt1.
Definition p_k2_122861_126956_cfgpos_4 : plan := Qdt7 p_k2_122861_126956_oom3 XC 0 p_k2_122861_126956_exit3_2 XC 1 p_k2_122861_126956_exit3_2 XC 2 p_k2_122861_126956_exit3_2.
Definition p_k2_122861_126956 : plan := Qdt14 5 0 p_k2_122861_126956_cfgpos_4.

Definition s_k2_122861_126956 : shape := Qd15.

Lemma chk_k2_122861_126956 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 122861 126956) p_k2_122861_126956 = COk s_k2_122861_126956.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_122861_126956)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_126957_131051_cnt1 : plan := Qd2.
Definition p_k2_126957_131051_exit3_2 : plan := Qd4.
Definition p_k2_126957_131051_oom3 : plan := Qdt3 7 127 p_k2_126957_131051_cnt1 p_k2_126957_131051_cnt1.
Definition p_k2_126957_131051_cfgpos_4 : plan := Qdt7 p_k2_126957_131051_oom3 XC 0 p_k2_126957_131051_exit3_2 XC 1 p_k2_126957_131051_exit3_2 XC 2 p_k2_126957_131051_exit3_2.
Definition p_k2_126957_131051 : plan := Qdt14 5 0 p_k2_126957_131051_cfgpos_4.

Definition s_k2_126957_131051 : shape := Qd15.

Lemma chk_k2_126957_131051 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 2 126957 131051) p_k2_126957_131051 = COk s_k2_126957_131051.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_126957_131051)). Qed.

