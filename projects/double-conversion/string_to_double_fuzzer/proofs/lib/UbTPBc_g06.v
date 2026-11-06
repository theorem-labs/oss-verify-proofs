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
Definition p_k0_21821_24556_cnt1 : plan := Qd2.
Local Abbreviation Qdt3 Qdp1 Qdp2 Qdp3 Qdp4 := (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4) (only parsing).
Local Abbreviation Qdt4 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (Qdt3 Qdp1 Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k0_21821_24556_oom2 : plan := Qdt4 7 127 p_k0_21821_24556_cnt1 p_k0_21821_24556_cnt1.
Local Abbreviation Qd5 := (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] Qd2))) (only parsing).
Local Abbreviation Qd6 := (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd5))))))))))))) (only parsing).
Local Abbreviation Qdt7 Qdp1 := (PMmap Qdp1 Qd6) (only parsing).
Definition p_k0_21821_24556_cfg0_3 : plan := Qdt7 p_k0_21821_24556_oom2.
Definition p_k0_21821_24556_exit3_4 : plan := Qd5.
Local Abbreviation Qd8 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd5))) (only parsing).
Local Abbreviation Qdt9 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp2 Qdp3 Qdp4 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp5 Qdp6 Qdp7 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp8 Qdp9 Qdp10 Qd8))))))))))))))))))))))) (only parsing).
Definition p_k0_21821_24556_cfgpos_5 : plan := Qdt9 p_k0_21821_24556_oom2 XC 0 p_k0_21821_24556_exit3_4 XC 1 p_k0_21821_24556_exit3_4 XC 2 p_k0_21821_24556_exit3_4.
Definition p_k0_21821_24556 : plan := Qdt3 5 0 p_k0_21821_24556_cfg0_3 p_k0_21821_24556_cfgpos_5.

Local Abbreviation Qdc2_10 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qdc4_11 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd12 := (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (only parsing).
Local Abbreviation Qd13 := (SEmit 1 (Qdc2_10 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qd14 := (SCase (EVar 5) 0 (SAlt2 Qd12 Qd13) (SAlt2 Qd12 (SEmit 1 (Qdc2_10 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd13 (SCase Qd1 2 (SEmit 1 (Qdc4_11 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_11 48 10 48 10 (Qdc2_10 48 10 [])) (SExit 0)))))))) (only parsing).
Definition s_k0_21821_24556 : shape := Qd14.

Lemma chk_k0_21821_24556 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 21821 24556) p_k0_21821_24556 = COk s_k0_21821_24556.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_21821_24556)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_26189_28652_cnt1 : plan := Qd2.
Definition p_k0_26189_28652_oom2 : plan := Qdt4 7 127 p_k0_26189_28652_cnt1 p_k0_26189_28652_cnt1.
Definition p_k0_26189_28652_cfg0_3 : plan := Qdt7 p_k0_26189_28652_oom2.
Definition p_k0_26189_28652_exit3_4 : plan := Qd5.
Definition p_k0_26189_28652_cfgpos_5 : plan := Qdt9 p_k0_26189_28652_oom2 XC 0 p_k0_26189_28652_exit3_4 XC 1 p_k0_26189_28652_exit3_4 XC 2 p_k0_26189_28652_exit3_4.
Definition p_k0_26189_28652 : plan := Qdt3 5 0 p_k0_26189_28652_cfg0_3 p_k0_26189_28652_cfgpos_5.

Definition s_k0_26189_28652 : shape := Qd14.

Lemma chk_k0_26189_28652 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 26189 28652) p_k0_26189_28652 = COk s_k0_26189_28652.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_26189_28652)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_28653_32748_cnt1 : plan := Qd2.
Definition p_k0_28653_32748_oom2 : plan := Qdt4 7 127 p_k0_28653_32748_cnt1 p_k0_28653_32748_cnt1.
Definition p_k0_28653_32748_cfg0_3 : plan := Qdt7 p_k0_28653_32748_oom2.
Definition p_k0_28653_32748_exit3_4 : plan := Qd5.
Definition p_k0_28653_32748_cfgpos_5 : plan := Qdt9 p_k0_28653_32748_oom2 XC 0 p_k0_28653_32748_exit3_4 XC 1 p_k0_28653_32748_exit3_4 XC 2 p_k0_28653_32748_exit3_4.
Definition p_k0_28653_32748 : plan := Qdt3 5 0 p_k0_28653_32748_cfg0_3 p_k0_28653_32748_cfgpos_5.

Definition s_k0_28653_32748 : shape := Qd14.

Lemma chk_k0_28653_32748 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 28653 32748) p_k0_28653_32748 = COk s_k0_28653_32748.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_28653_32748)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_32749_36844_cnt1 : plan := Qd2.
Definition p_k0_32749_36844_oom2 : plan := Qdt4 7 127 p_k0_32749_36844_cnt1 p_k0_32749_36844_cnt1.
Definition p_k0_32749_36844_cfg0_3 : plan := Qdt7 p_k0_32749_36844_oom2.
Definition p_k0_32749_36844_exit3_4 : plan := Qd5.
Definition p_k0_32749_36844_cfgpos_5 : plan := Qdt9 p_k0_32749_36844_oom2 XC 0 p_k0_32749_36844_exit3_4 XC 1 p_k0_32749_36844_exit3_4 XC 2 p_k0_32749_36844_exit3_4.
Definition p_k0_32749_36844 : plan := Qdt3 5 0 p_k0_32749_36844_cfg0_3 p_k0_32749_36844_cfgpos_5.

Definition s_k0_32749_36844 : shape := Qd14.

Lemma chk_k0_32749_36844 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 32749 36844) p_k0_32749_36844 = COk s_k0_32749_36844.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_32749_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_37437_40940_cnt1 : plan := Qd2.
Definition p_k0_37437_40940_oom2 : plan := Qdt4 7 127 p_k0_37437_40940_cnt1 p_k0_37437_40940_cnt1.
Definition p_k0_37437_40940_cfg0_3 : plan := Qdt7 p_k0_37437_40940_oom2.
Definition p_k0_37437_40940_exit3_4 : plan := Qd5.
Definition p_k0_37437_40940_cfgpos_5 : plan := Qdt9 p_k0_37437_40940_oom2 XC 0 p_k0_37437_40940_exit3_4 XC 1 p_k0_37437_40940_exit3_4 XC 2 p_k0_37437_40940_exit3_4.
Definition p_k0_37437_40940 : plan := Qdt3 5 0 p_k0_37437_40940_cfg0_3 p_k0_37437_40940_cfgpos_5.

Definition s_k0_37437_40940 : shape := Qd14.

Lemma chk_k0_37437_40940 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 37437 40940) p_k0_37437_40940 = COk s_k0_37437_40940.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_37437_40940)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_40941_43676_cnt1 : plan := Qd2.
Definition p_k0_40941_43676_oom2 : plan := Qdt4 7 127 p_k0_40941_43676_cnt1 p_k0_40941_43676_cnt1.
Definition p_k0_40941_43676_cfg0_3 : plan := Qdt7 p_k0_40941_43676_oom2.
Definition p_k0_40941_43676_exit3_4 : plan := Qd5.
Definition p_k0_40941_43676_cfgpos_5 : plan := Qdt9 p_k0_40941_43676_oom2 XC 0 p_k0_40941_43676_exit3_4 XC 1 p_k0_40941_43676_exit3_4 XC 2 p_k0_40941_43676_exit3_4.
Definition p_k0_40941_43676 : plan := Qdt3 5 0 p_k0_40941_43676_cfg0_3 p_k0_40941_43676_cfgpos_5.

Definition s_k0_40941_43676 : shape := Qd14.

Lemma chk_k0_40941_43676 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 40941 43676) p_k0_40941_43676 = COk s_k0_40941_43676.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_40941_43676)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45037_49132_cnt1 : plan := Qd2.
Definition p_k0_45037_49132_oom2 : plan := Qdt4 7 127 p_k0_45037_49132_cnt1 p_k0_45037_49132_cnt1.
Definition p_k0_45037_49132_cfg0_3 : plan := Qdt7 p_k0_45037_49132_oom2.
Definition p_k0_45037_49132_exit3_4 : plan := Qd5.
Definition p_k0_45037_49132_cfgpos_5 : plan := Qdt9 p_k0_45037_49132_oom2 XC 0 p_k0_45037_49132_exit3_4 XC 1 p_k0_45037_49132_exit3_4 XC 2 p_k0_45037_49132_exit3_4.
Definition p_k0_45037_49132 : plan := Qdt3 5 0 p_k0_45037_49132_cfg0_3 p_k0_45037_49132_cfgpos_5.

Definition s_k0_45037_49132 : shape := Qd14.

Lemma chk_k0_45037_49132 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 45037 49132) p_k0_45037_49132 = COk s_k0_45037_49132.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_49133_52412_cnt1 : plan := Qd2.
Definition p_k0_49133_52412_oom2 : plan := Qdt4 7 127 p_k0_49133_52412_cnt1 p_k0_49133_52412_cnt1.
Definition p_k0_49133_52412_cfg0_3 : plan := Qdt7 p_k0_49133_52412_oom2.
Definition p_k0_49133_52412_exit3_4 : plan := Qd5.
Definition p_k0_49133_52412_cfgpos_5 : plan := Qdt9 p_k0_49133_52412_oom2 XC 0 p_k0_49133_52412_exit3_4 XC 1 p_k0_49133_52412_exit3_4 XC 2 p_k0_49133_52412_exit3_4.
Definition p_k0_49133_52412 : plan := Qdt3 5 0 p_k0_49133_52412_cfg0_3 p_k0_49133_52412_cfgpos_5.

Definition s_k0_49133_52412 : shape := Qd14.

Lemma chk_k0_49133_52412 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 49133 52412) p_k0_49133_52412 = COk s_k0_49133_52412.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_49133_52412)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_53229_57324_cnt1 : plan := Qd2.
Definition p_k0_53229_57324_oom2 : plan := Qdt4 7 127 p_k0_53229_57324_cnt1 p_k0_53229_57324_cnt1.
Definition p_k0_53229_57324_cfg0_3 : plan := Qdt7 p_k0_53229_57324_oom2.
Definition p_k0_53229_57324_exit3_4 : plan := Qd5.
Definition p_k0_53229_57324_cfgpos_5 : plan := Qdt9 p_k0_53229_57324_oom2 XC 0 p_k0_53229_57324_exit3_4 XC 1 p_k0_53229_57324_exit3_4 XC 2 p_k0_53229_57324_exit3_4.
Definition p_k0_53229_57324 : plan := Qdt3 5 0 p_k0_53229_57324_cfg0_3 p_k0_53229_57324_cfgpos_5.

Definition s_k0_53229_57324 : shape := Qd14.

Lemma chk_k0_53229_57324 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 53229 57324) p_k0_53229_57324 = COk s_k0_53229_57324.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_53229_57324)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_57325_61420_cnt1 : plan := Qd2.
Definition p_k0_57325_61420_oom2 : plan := Qdt4 7 127 p_k0_57325_61420_cnt1 p_k0_57325_61420_cnt1.
Definition p_k0_57325_61420_cfg0_3 : plan := Qdt7 p_k0_57325_61420_oom2.
Definition p_k0_57325_61420_exit3_4 : plan := Qd5.
Definition p_k0_57325_61420_cfgpos_5 : plan := Qdt9 p_k0_57325_61420_oom2 XC 0 p_k0_57325_61420_exit3_4 XC 1 p_k0_57325_61420_exit3_4 XC 2 p_k0_57325_61420_exit3_4.
Definition p_k0_57325_61420 : plan := Qdt3 5 0 p_k0_57325_61420_cfg0_3 p_k0_57325_61420_cfgpos_5.

Definition s_k0_57325_61420 : shape := Qd14.

Lemma chk_k0_57325_61420 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 57325 61420) p_k0_57325_61420 = COk s_k0_57325_61420.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61421_65516_cnt1 : plan := Qd2.
Definition p_k0_61421_65516_oom2 : plan := Qdt4 7 127 p_k0_61421_65516_cnt1 p_k0_61421_65516_cnt1.
Definition p_k0_61421_65516_cfg0_3 : plan := Qdt7 p_k0_61421_65516_oom2.
Definition p_k0_61421_65516_exit3_4 : plan := Qd5.
Definition p_k0_61421_65516_cfgpos_5 : plan := Qdt9 p_k0_61421_65516_oom2 XC 0 p_k0_61421_65516_exit3_4 XC 1 p_k0_61421_65516_exit3_4 XC 2 p_k0_61421_65516_exit3_4.
Definition p_k0_61421_65516 : plan := Qdt3 5 0 p_k0_61421_65516_cfg0_3 p_k0_61421_65516_cfgpos_5.

Definition s_k0_61421_65516 : shape := Qd14.

Lemma chk_k0_61421_65516 : check ImgU.M.loaded_segments ITAB U0 NX0 20000%nat 400%nat (cs_T 61421 65516) p_k0_61421_65516 = COk s_k0_61421_65516.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_65517_69612_cnt1 : plan := Qd2.
Definition p_k1_65517_69612_oom2 : plan := Qdt4 7 127 p_k1_65517_69612_cnt1 p_k1_65517_69612_cnt1.
Definition p_k1_65517_69612_cfg0_3 : plan := Qdt7 p_k1_65517_69612_oom2.
Definition p_k1_65517_69612_exit3_4 : plan := Qd5.
Definition p_k1_65517_69612_cfgpos_5 : plan := Qdt9 p_k1_65517_69612_oom2 XC 0 p_k1_65517_69612_exit3_4 XC 1 p_k1_65517_69612_exit3_4 XC 2 p_k1_65517_69612_exit3_4.
Definition p_k1_65517_69612 : plan := Qdt3 5 0 p_k1_65517_69612_cfg0_3 p_k1_65517_69612_cfgpos_5.

Definition s_k1_65517_69612 : shape := Qd14.

Lemma chk_k1_65517_69612 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 65517 69612) p_k1_65517_69612 = COk s_k1_65517_69612.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_65517_69612)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_69613_73708_cnt1 : plan := Qd2.
Definition p_k1_69613_73708_oom2 : plan := Qdt4 7 127 p_k1_69613_73708_cnt1 p_k1_69613_73708_cnt1.
Definition p_k1_69613_73708_cfg0_3 : plan := Qdt7 p_k1_69613_73708_oom2.
Definition p_k1_69613_73708_exit3_4 : plan := Qd5.
Definition p_k1_69613_73708_cfgpos_5 : plan := Qdt9 p_k1_69613_73708_oom2 XC 0 p_k1_69613_73708_exit3_4 XC 1 p_k1_69613_73708_exit3_4 XC 2 p_k1_69613_73708_exit3_4.
Definition p_k1_69613_73708 : plan := Qdt3 5 0 p_k1_69613_73708_cfg0_3 p_k1_69613_73708_cfgpos_5.

Definition s_k1_69613_73708 : shape := Qd14.

Lemma chk_k1_69613_73708 : check ImgU.M.loaded_segments ITAB U0 NX0k 20000%nat 400%nat (cs_Tk 1 69613 73708) p_k1_69613_73708 = COk s_k1_69613_73708.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_69613_73708)). Qed.

