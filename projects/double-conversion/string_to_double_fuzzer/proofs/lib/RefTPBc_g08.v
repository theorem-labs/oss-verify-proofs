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
Local Abbreviation Qd3 := (PCall SumMainRet [] Qd2) (only parsing).
Local Abbreviation Qd4 := (PResume Qd3) (only parsing).
Definition p_k0_0_0_cfg0_1 : plan := PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume Qd4)))))))))).
Definition p_k0_0_0_exit3_2 : plan := Qd4.
Definition p_k0_0_0_cfgpos_3 : plan := PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit XC 0 p_k0_0_0_exit3_2 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit XC 1 p_k0_0_0_exit3_2 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit XC 2 p_k0_0_0_exit3_2 (PCall SumLib [] (PCall SumPrintf [] (PResume Qd4)))))))))))))))))))))).
Definition p_k0_0_0 : plan := PSplit (EVar 5) 0 p_k0_0_0_cfg0_1 p_k0_0_0_cfgpos_3.

Local Abbreviation Qdc2_5 Qde1 Qde2 Qd0 := (Qde1 :: Qde2 :: Qd0) (only parsing).
Local Abbreviation Qd6 := (SEmit 1 (Qdc2_5 48 10 []) (SExit 0)) (only parsing).
Local Abbreviation Qdc4_7 Qde1 Qde2 Qde3 Qde4 Qd0 := (Qde1 :: Qde2 :: Qde3 :: Qde4 :: Qd0) (only parsing).
Local Abbreviation Qd8 := (SEmit 1 (Qdc2_5 48 10 []) (SCase Qd1 0 (SExit 0) (SCase Qd1 1 Qd6 (SCase Qd1 2 (SEmit 1 (Qdc4_7 48 10 48 10 []) (SExit 0)) (SEmit 1 (Qdc4_7 48 10 48 10 (Qdc2_5 48 10 [])) (SExit 0)))))) (only parsing).
Definition s_k0_0_0 : shape := SCase (EVar 5) 0 Qd6 Qd8.

Lemma chk_k0_0_0 : check ImgP.M.loaded_segments ITAB P0 NX0 20000%nat 400%nat (cs_T 0 0) p_k0_0_0 = COk s_k0_0_0.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_0_0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_36845_37436_cnt1 : plan := Qd2.
Local Abbreviation Qd9 := (PCall SumFreePro [] (PMunmap Qd3)) (only parsing).
Definition p_k1_36845_37436_exit3_2 : plan := Qd9.
Local Abbreviation Qdt10 Qdp1 Qdp2 Qdp3 Qdp4 := (PResume (PSplit (EVar Qdp1) Qdp2 Qdp3 Qdp4)) (only parsing).
Definition p_k1_36845_37436_oom3 : plan := Qdt10 7 127 p_k1_36845_37436_cnt1 p_k1_36845_37436_cnt1.
Local Abbreviation Qd11 := (PCall SumLib [] (PCall SumPrintf [] (PResume Qd9))) (only parsing).
Local Abbreviation Qdt12 Qdp1 Qdp2 Qdp3 Qdp4 Qdp5 Qdp6 Qdp7 Qdp8 Qdp9 Qdp10 := (PMmap Qdp1 (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumLib [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit Qdp2 Qdp3 Qdp4 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp5 Qdp6 Qdp7 (PCall SumLib [] (PCall SumPrintf [] (PResume (PSplit Qdp8 Qdp9 Qdp10 Qd11))))))))))))))))))))))) (only parsing).
Definition p_k1_36845_37436_cfgpos_4 : plan := Qdt12 p_k1_36845_37436_oom3 XC 0 p_k1_36845_37436_exit3_2 XC 1 p_k1_36845_37436_exit3_2 XC 2 p_k1_36845_37436_exit3_2.
Local Abbreviation Qdt13 Qdp1 Qdp2 Qdp3 := (PSplit (EVar Qdp1) Qdp2 PContra Qdp3) (only parsing).
Definition p_k1_36845_37436 : plan := Qdt13 5 0 p_k1_36845_37436_cfgpos_4.

Local Abbreviation Qd14 := (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) Qd8)) (only parsing).
Definition s_k1_36845_37436 : shape := Qd14.

Lemma chk_k1_36845_37436 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 36845 37436) p_k1_36845_37436 = COk s_k1_36845_37436.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_52413_53228_cnt1 : plan := Qd2.
Definition p_k1_52413_53228_exit3_2 : plan := Qd9.
Definition p_k1_52413_53228_oom3 : plan := Qdt10 7 127 p_k1_52413_53228_cnt1 p_k1_52413_53228_cnt1.
Definition p_k1_52413_53228_cfgpos_4 : plan := Qdt12 p_k1_52413_53228_oom3 XC 0 p_k1_52413_53228_exit3_2 XC 1 p_k1_52413_53228_exit3_2 XC 2 p_k1_52413_53228_exit3_2.
Definition p_k1_52413_53228 : plan := Qdt13 5 0 p_k1_52413_53228_cfgpos_4.

Definition s_k1_52413_53228 : shape := Qd14.

Lemma chk_k1_52413_53228 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 1 52413 53228) p_k1_52413_53228 = COk s_k1_52413_53228.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_52413_53228)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_104829_106476_cnt1 : plan := Qd2.
Definition p_k2_104829_106476_exit3_2 : plan := Qd9.
Definition p_k2_104829_106476_oom3 : plan := Qdt10 7 127 p_k2_104829_106476_cnt1 p_k2_104829_106476_cnt1.
Definition p_k2_104829_106476_cfgpos_4 : plan := Qdt12 p_k2_104829_106476_oom3 XC 0 p_k2_104829_106476_exit3_2 XC 1 p_k2_104829_106476_exit3_2 XC 2 p_k2_104829_106476_exit3_2.
Definition p_k2_104829_106476 : plan := Qdt13 5 0 p_k2_104829_106476_cfgpos_4.

Definition s_k2_104829_106476 : shape := Qd14.

Lemma chk_k2_104829_106476 : check ImgP.M.loaded_segments ITAB P0 NX0k 20000%nat 400%nat (cs_Tk 2 104829 106476) p_k2_104829_106476 = COk s_k2_104829_106476.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_104829_106476)). Qed.

