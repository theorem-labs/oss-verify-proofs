(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymPlan UbSymPlanSoundA UbTargetAssemblyTop UbTargetCover.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbTPBc_g01.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetEntry_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetEntryK_defs.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_0_0_cfg0_1 : plan :=
  PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))).
Definition p_k0_0_0_exit3_2 : plan :=
  PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))).
Definition p_k0_0_0_cfgpos_3 : plan :=
  PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_0_0_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_0_0_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_0_0_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))).
Definition p_k0_0_0 : plan :=
  PSplit (EVar 5) 0 (p_k0_0_0_cfg0_1) (p_k0_0_0_cfgpos_3).

Definition s_k0_0_0 : shape :=
  (SCase (EVar 5) 0 (SEmit 1 [48; 10] (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0))))))).

Lemma chk_k0_0_0 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 0 0) p_k0_0_0 = COk s_k0_0_0.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_0_0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2717_3260_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_2717_3260_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_2717_3260_cnt1) (p_k0_2717_3260_cnt1)).
Definition p_k0_2717_3260_cfg0_3 : plan :=
  PMmap (p_k0_2717_3260_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_2717_3260_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_2717_3260_cfgpos_5 : plan :=
  PMmap (p_k0_2717_3260_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_2717_3260_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_2717_3260_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_2717_3260_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_2717_3260 : plan :=
  PSplit (EVar 5) 0 (p_k0_2717_3260_cfg0_3) (p_k0_2717_3260_cfgpos_5).

Definition s_k0_2717_3260 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_2717_3260 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 2717 3260) p_k0_2717_3260 = COk s_k0_2717_3260.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2717_3260)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_8173_9340_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_8173_9340_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_8173_9340_cnt1) (p_k0_8173_9340_cnt1)).
Definition p_k0_8173_9340_cfg0_3 : plan :=
  PMmap (p_k0_8173_9340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_8173_9340_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_8173_9340_cfgpos_5 : plan :=
  PMmap (p_k0_8173_9340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_8173_9340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_8173_9340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_8173_9340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_8173_9340 : plan :=
  PSplit (EVar 5) 0 (p_k0_8173_9340_cfg0_3) (p_k0_8173_9340_cfgpos_5).

Definition s_k0_8173_9340 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_8173_9340 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 8173 9340) p_k0_8173_9340 = COk s_k0_8173_9340.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_8173_9340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_10909_12268_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_10909_12268_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_10909_12268_cnt1) (p_k0_10909_12268_cnt1)).
Definition p_k0_10909_12268_cfg0_3 : plan :=
  PMmap (p_k0_10909_12268_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_10909_12268_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_10909_12268_cfgpos_5 : plan :=
  PMmap (p_k0_10909_12268_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_10909_12268_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_10909_12268_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_10909_12268_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_10909_12268 : plan :=
  PSplit (EVar 5) 0 (p_k0_10909_12268_cfg0_3) (p_k0_10909_12268_cfgpos_5).

Definition s_k0_10909_12268 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_10909_12268 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 10909 12268) p_k0_10909_12268 = COk s_k0_10909_12268.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_10909_12268)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_12269_13084_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_12269_13084_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_12269_13084_cnt1) (p_k0_12269_13084_cnt1)).
Definition p_k0_12269_13084_cfg0_3 : plan :=
  PMmap (p_k0_12269_13084_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_12269_13084_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_12269_13084_cfgpos_5 : plan :=
  PMmap (p_k0_12269_13084_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_12269_13084_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_12269_13084_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_12269_13084_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_12269_13084 : plan :=
  PSplit (EVar 5) 0 (p_k0_12269_13084_cfg0_3) (p_k0_12269_13084_cfgpos_5).

Definition s_k0_12269_13084 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_12269_13084 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 12269 13084) p_k0_12269_13084 = COk s_k0_12269_13084.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_12269_13084)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_18701_20460_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_18701_20460_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_18701_20460_cnt1) (p_k0_18701_20460_cnt1)).
Definition p_k0_18701_20460_cfg0_3 : plan :=
  PMmap (p_k0_18701_20460_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_18701_20460_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_18701_20460_cfgpos_5 : plan :=
  PMmap (p_k0_18701_20460_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_18701_20460_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_18701_20460_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_18701_20460_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_18701_20460 : plan :=
  PSplit (EVar 5) 0 (p_k0_18701_20460_cfg0_3) (p_k0_18701_20460_cfgpos_5).

Definition s_k0_18701_20460 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_18701_20460 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 18701 20460) p_k0_18701_20460 = COk s_k0_18701_20460.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_18701_20460)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_45037_49132_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_45037_49132_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_45037_49132_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_45037_49132_cnt1) (p_k1_45037_49132_cnt1)).
Definition p_k1_45037_49132_cfgpos_4 : plan :=
  PMmap (p_k1_45037_49132_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_45037_49132_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_45037_49132_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_45037_49132_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_45037_49132 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_45037_49132_cfgpos_4).

Definition s_k1_45037_49132 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_45037_49132 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 45037 49132) p_k1_45037_49132 = COk s_k1_45037_49132.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_49133_52412_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_49133_52412_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_49133_52412_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_49133_52412_cnt1) (p_k1_49133_52412_cnt1)).
Definition p_k1_49133_52412_cfgpos_4 : plan :=
  PMmap (p_k1_49133_52412_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_49133_52412_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_49133_52412_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_49133_52412_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_49133_52412 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_49133_52412_cfgpos_4).

Definition s_k1_49133_52412 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_49133_52412 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 49133 52412) p_k1_49133_52412 = COk s_k1_49133_52412.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_49133_52412)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_52413_53228_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_52413_53228_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_52413_53228_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_52413_53228_cnt1) (p_k1_52413_53228_cnt1)).
Definition p_k1_52413_53228_cfgpos_4 : plan :=
  PMmap (p_k1_52413_53228_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_52413_53228_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_52413_53228_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_52413_53228_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_52413_53228 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_52413_53228_cfgpos_4).

Definition s_k1_52413_53228 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_52413_53228 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 52413 53228) p_k1_52413_53228 = COk s_k1_52413_53228.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_52413_53228)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_57325_61420_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_57325_61420_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_57325_61420_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_57325_61420_cnt1) (p_k1_57325_61420_cnt1)).
Definition p_k1_57325_61420_cfgpos_4 : plan :=
  PMmap (p_k1_57325_61420_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_57325_61420_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_57325_61420_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_57325_61420_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_57325_61420 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_57325_61420_cfgpos_4).

Definition s_k1_57325_61420 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_57325_61420 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 57325 61420) p_k1_57325_61420 = COk s_k1_57325_61420.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_61421_65516_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_61421_65516_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_61421_65516_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_61421_65516_cnt1) (p_k1_61421_65516_cnt1)).
Definition p_k1_61421_65516_cfgpos_4 : plan :=
  PMmap (p_k1_61421_65516_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_61421_65516_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_61421_65516_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_61421_65516_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_61421_65516 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_61421_65516_cfgpos_4).

Definition s_k1_61421_65516 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_61421_65516 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 61421 65516) p_k1_61421_65516 = COk s_k1_61421_65516.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_73709_74876_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_73709_74876_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_73709_74876_cnt1) (p_k1_73709_74876_cnt1)).
Definition p_k1_73709_74876_cfg0_3 : plan :=
  PMmap (p_k1_73709_74876_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_73709_74876_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_73709_74876_cfgpos_5 : plan :=
  PMmap (p_k1_73709_74876_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_73709_74876_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_73709_74876_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_73709_74876_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_73709_74876 : plan :=
  PSplit (EVar 5) 0 (p_k1_73709_74876_cfg0_3) (p_k1_73709_74876_cfgpos_5).

Definition s_k1_73709_74876 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_73709_74876 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 73709 74876) p_k1_73709_74876 = COk s_k1_73709_74876.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_73709_74876)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_85997_87356_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_85997_87356_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_85997_87356_cnt1) (p_k1_85997_87356_cnt1)).
Definition p_k1_85997_87356_cfg0_3 : plan :=
  PMmap (p_k1_85997_87356_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_85997_87356_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_85997_87356_cfgpos_5 : plan :=
  PMmap (p_k1_85997_87356_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_85997_87356_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_85997_87356_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_85997_87356_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_85997_87356 : plan :=
  PSplit (EVar 5) 0 (p_k1_85997_87356_cfg0_3) (p_k1_85997_87356_cfgpos_5).

Definition s_k1_85997_87356 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_85997_87356 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 85997 87356) p_k1_85997_87356 = COk s_k1_85997_87356.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_85997_87356)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_126957_131051_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_126957_131051_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_126957_131051_cnt1) (p_k1_126957_131051_cnt1)).
Definition p_k1_126957_131051_cfg0_3 : plan :=
  PMmap (p_k1_126957_131051_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_126957_131051_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_126957_131051_cfgpos_5 : plan :=
  PMmap (p_k1_126957_131051_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_126957_131051_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_126957_131051_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_126957_131051_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_126957_131051 : plan :=
  PSplit (EVar 5) 0 (p_k1_126957_131051_cfg0_3) (p_k1_126957_131051_cfgpos_5).

Definition s_k1_126957_131051 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_126957_131051 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 126957 131051) p_k1_126957_131051 = COk s_k1_126957_131051.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_126957_131051)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_131052_131065_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_131052_131065_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_131052_131065_cnt1) (p_k1_131052_131065_cnt1)).
Definition p_k1_131052_131065_cfg0_3 : plan :=
  PMmap (p_k1_131052_131065_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_131052_131065_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_131052_131065_cfgpos_5 : plan :=
  PMmap (p_k1_131052_131065_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_131052_131065_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_131052_131065_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_131052_131065_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_131052_131065 : plan :=
  PSplit (EVar 5) 0 (p_k1_131052_131065_cfg0_3) (p_k1_131052_131065_cfgpos_5).

Definition s_k1_131052_131065 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_131052_131065 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 131052 131065) p_k1_131052_131065 = COk s_k1_131052_131065.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_131052_131065)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_98299_102380_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_98299_102380_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_98299_102380_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_98299_102380_cnt1) (p_k2_98299_102380_cnt1)).
Definition p_k2_98299_102380_cfgpos_4 : plan :=
  PMmap (p_k2_98299_102380_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_98299_102380_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_98299_102380_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_98299_102380_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_98299_102380 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_98299_102380_cfgpos_4).

Definition s_k2_98299_102380 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_98299_102380 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 98299 102380) p_k2_98299_102380 = COk s_k2_98299_102380.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_98299_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_102381_104828_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_102381_104828_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_102381_104828_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_102381_104828_cnt1) (p_k2_102381_104828_cnt1)).
Definition p_k2_102381_104828_cfgpos_4 : plan :=
  PMmap (p_k2_102381_104828_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_102381_104828_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_102381_104828_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_102381_104828_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_102381_104828 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_102381_104828_cfgpos_4).

Definition s_k2_102381_104828 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_102381_104828 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 102381 104828) p_k2_102381_104828 = COk s_k2_102381_104828.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_104829_106476_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_104829_106476_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_104829_106476_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_104829_106476_cnt1) (p_k2_104829_106476_cnt1)).
Definition p_k2_104829_106476_cfgpos_4 : plan :=
  PMmap (p_k2_104829_106476_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_104829_106476_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_104829_106476_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_104829_106476_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_104829_106476 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_104829_106476_cfgpos_4).

Definition s_k2_104829_106476 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_104829_106476 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 104829 106476) p_k2_104829_106476 = COk s_k2_104829_106476.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_104829_106476)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_106477_110572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_106477_110572_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_106477_110572_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_106477_110572_cnt1) (p_k2_106477_110572_cnt1)).
Definition p_k2_106477_110572_cfgpos_4 : plan :=
  PMmap (p_k2_106477_110572_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_106477_110572_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_106477_110572_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_106477_110572_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_106477_110572 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_106477_110572_cfgpos_4).

Definition s_k2_106477_110572 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_106477_110572 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 106477 110572) p_k2_106477_110572 = COk s_k2_106477_110572.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_114669_118764_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_114669_118764_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_114669_118764_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_114669_118764_cnt1) (p_k2_114669_118764_cnt1)).
Definition p_k2_114669_118764_cfgpos_4 : plan :=
  PMmap (p_k2_114669_118764_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_114669_118764_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_114669_118764_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_114669_118764_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_114669_118764 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_114669_118764_cfgpos_4).

Definition s_k2_114669_118764 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_114669_118764 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 114669 118764) p_k2_114669_118764 = COk s_k2_114669_118764.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_114669_118764)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_126957_131051_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_126957_131051_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_126957_131051_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_126957_131051_cnt1) (p_k2_126957_131051_cnt1)).
Definition p_k2_126957_131051_cfgpos_4 : plan :=
  PMmap (p_k2_126957_131051_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_126957_131051_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_126957_131051_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_126957_131051_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_126957_131051 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_126957_131051_cfgpos_4).

Definition s_k2_126957_131051 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_126957_131051 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 126957 131051) p_k2_126957_131051 = COk s_k2_126957_131051.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_126957_131051)). Qed.

End UbTPBc_g01.
From Stdlib Require Zify.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg Spec UbWorld UbTargetPre UbWorldK UbTargetPreK SymExec3 SymPlan UbSymPlanSoundA. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetEntry_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetEntryK_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetShape. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetShapeTop. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbTargetAssemblyTop.UbTargetAssembly. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTargetCover.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTargetAssemblyTop. Import UbTPBc_g01.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.

Section WithFP. Context {FP : PropExec.FPState}.
Section LIB.
Hypothesis LIB : lib_ok.

(* [comment removed for export] *)
Lemma cso_k0_0_0 : class_shape_ok false s_k0_0_0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_0_0 : TP0 0 0.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 0 0 p_k0_0_0 s_k0_0_0 chk_k0_0_0 cso_k0_0_0); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2717_3260 : class_shape_ok true s_k0_2717_3260 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2717_3260 : TP0 2717 3260.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 2717 3260 p_k0_2717_3260 s_k0_2717_3260 chk_k0_2717_3260 cso_k0_2717_3260); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_8173_9340 : class_shape_ok true s_k0_8173_9340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_8173_9340 : TP0 8173 9340.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 8173 9340 p_k0_8173_9340 s_k0_8173_9340 chk_k0_8173_9340 cso_k0_8173_9340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_10909_12268 : class_shape_ok true s_k0_10909_12268 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_10909_12268 : TP0 10909 12268.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 10909 12268 p_k0_10909_12268 s_k0_10909_12268 chk_k0_10909_12268 cso_k0_10909_12268); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_12269_13084 : class_shape_ok true s_k0_12269_13084 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_12269_13084 : TP0 12269 13084.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 12269 13084 p_k0_12269_13084 s_k0_12269_13084 chk_k0_12269_13084 cso_k0_12269_13084); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_18701_20460 : class_shape_ok true s_k0_18701_20460 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_18701_20460 : TP0 18701 20460.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 18701 20460 p_k0_18701_20460 s_k0_18701_20460 chk_k0_18701_20460 cso_k0_18701_20460); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_45037_49132 : class_shape_ok1 true s_k1_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_45037_49132 : TPK 1 45037 49132.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 45037 49132 p_k1_45037_49132 s_k1_45037_49132 chk_k1_45037_49132 cso_k1_45037_49132); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_49133_52412 : class_shape_ok1 true s_k1_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_49133_52412 : TPK 1 49133 52412.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 49133 52412 p_k1_49133_52412 s_k1_49133_52412 chk_k1_49133_52412 cso_k1_49133_52412); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_52413_53228 : class_shape_ok1 true s_k1_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_52413_53228 : TPK 1 52413 53228.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 52413 53228 p_k1_52413_53228 s_k1_52413_53228 chk_k1_52413_53228 cso_k1_52413_53228); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_57325_61420 : class_shape_ok1 true s_k1_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_57325_61420 : TPK 1 57325 61420.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 57325 61420 p_k1_57325_61420 s_k1_57325_61420 chk_k1_57325_61420 cso_k1_57325_61420); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_61421_65516 : class_shape_ok1 true s_k1_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_61421_65516 : TPK 1 61421 65516.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 61421 65516 p_k1_61421_65516 s_k1_61421_65516 chk_k1_61421_65516 cso_k1_61421_65516); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_73709_74876 : class_shape_ok true s_k1_73709_74876 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_73709_74876 : TPK 1 73709 74876.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 73709 74876 p_k1_73709_74876 s_k1_73709_74876 chk_k1_73709_74876 cso_k1_73709_74876); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_85997_87356 : class_shape_ok true s_k1_85997_87356 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_85997_87356 : TPK 1 85997 87356.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 85997 87356 p_k1_85997_87356 s_k1_85997_87356 chk_k1_85997_87356 cso_k1_85997_87356); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_126957_131051 : class_shape_ok true s_k1_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_126957_131051 : TPK 1 126957 131051.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 126957 131051 p_k1_126957_131051 s_k1_126957_131051 chk_k1_126957_131051 cso_k1_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_131052_131065 : class_shape_ok true s_k1_131052_131065 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_131052_131065 : TPK 1 131052 131065.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 131052 131065 p_k1_131052_131065 s_k1_131052_131065 chk_k1_131052_131065 cso_k1_131052_131065); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_98299_102380 : class_shape_ok1 true s_k2_98299_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_98299_102380 : TPK 2 98299 102380.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 98299 102380 p_k2_98299_102380 s_k2_98299_102380 chk_k2_98299_102380 cso_k2_98299_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_102381_104828 : class_shape_ok1 true s_k2_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_102381_104828 : TPK 2 102381 104828.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 102381 104828 p_k2_102381_104828 s_k2_102381_104828 chk_k2_102381_104828 cso_k2_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_104829_106476 : class_shape_ok1 true s_k2_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_104829_106476 : TPK 2 104829 106476.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 104829 106476 p_k2_104829_106476 s_k2_104829_106476 chk_k2_104829_106476 cso_k2_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_106477_110572 : class_shape_ok1 true s_k2_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_106477_110572 : TPK 2 106477 110572.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 106477 110572 p_k2_106477_110572 s_k2_106477_110572 chk_k2_106477_110572 cso_k2_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_114669_118764 : class_shape_ok1 true s_k2_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_114669_118764 : TPK 2 114669 118764.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 114669 118764 p_k2_114669_118764 s_k2_114669_118764 chk_k2_114669_118764 cso_k2_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_126957_131051 : class_shape_ok1 true s_k2_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_126957_131051 : TPK 2 126957 131051.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 126957 131051 p_k2_126957_131051 s_k2_126957_131051 chk_k2_126957_131051 cso_k2_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

End LIB.
End WithFP.
