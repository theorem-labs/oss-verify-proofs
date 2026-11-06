(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec ShapeAlg Spec RefWorld RefTargetPre RefWorldK RefTargetPreK SymExec3 SymPlan SymPlanSoundA RefTargetAssemblyTop RefTargetCover.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefTPBc_g02.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec3 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymPlan OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetEntry_defs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetEntryK_defs.
Unset Lia Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1_12_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1_12_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1_12_cnt1) (p_k0_1_12_cnt1)).
Definition p_k0_1_12_cfg0_3 : plan :=
  PMmap (p_k0_1_12_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_1_12_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1_12_cfgpos_5 : plan :=
  PMmap (p_k0_1_12_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_1_12_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_1_12_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_1_12_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_1_12 : plan :=
  PSplit (EVar 5) 0 (p_k0_1_12_cfg0_3) (p_k0_1_12_cfgpos_5).

Definition s_k0_1_12 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1_12 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 1 12) p_k0_1_12 = COk s_k0_1_12.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1_12)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_13_28_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_13_28_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_13_28_cnt1) (p_k0_13_28_cnt1)).
Definition p_k0_13_28_cfg0_3 : plan :=
  PMmap (p_k0_13_28_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_13_28_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_13_28_cfgpos_5 : plan :=
  PMmap (p_k0_13_28_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_13_28_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_13_28_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_13_28_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_13_28 : plan :=
  PSplit (EVar 5) 0 (p_k0_13_28_cfg0_3) (p_k0_13_28_cfgpos_5).

Definition s_k0_13_28 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_13_28 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 13 28) p_k0_13_28 = COk s_k0_13_28.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_13_28)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_29_44_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_29_44_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_29_44_cnt1) (p_k0_29_44_cnt1)).
Definition p_k0_29_44_cfg0_3 : plan :=
  PMmap (p_k0_29_44_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_29_44_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_29_44_cfgpos_5 : plan :=
  PMmap (p_k0_29_44_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_29_44_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_29_44_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_29_44_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_29_44 : plan :=
  PSplit (EVar 5) 0 (p_k0_29_44_cfg0_3) (p_k0_29_44_cfgpos_5).

Definition s_k0_29_44 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_29_44 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 29 44) p_k0_29_44 = COk s_k0_29_44.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_29_44)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45_60_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_45_60_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_45_60_cnt1) (p_k0_45_60_cnt1)).
Definition p_k0_45_60_cfg0_3 : plan :=
  PMmap (p_k0_45_60_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_45_60_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_45_60_cfgpos_5 : plan :=
  PMmap (p_k0_45_60_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_45_60_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_45_60_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_45_60_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_45_60 : plan :=
  PSplit (EVar 5) 0 (p_k0_45_60_cfg0_3) (p_k0_45_60_cfgpos_5).

Definition s_k0_45_60 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_45_60 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 45 60) p_k0_45_60 = COk s_k0_45_60.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_45_60)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61_76_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_61_76_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_61_76_cnt1) (p_k0_61_76_cnt1)).
Definition p_k0_61_76_cfg0_3 : plan :=
  PMmap (p_k0_61_76_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_61_76_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_61_76_cfgpos_5 : plan :=
  PMmap (p_k0_61_76_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_61_76_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_61_76_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_61_76_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_61_76 : plan :=
  PSplit (EVar 5) 0 (p_k0_61_76_cfg0_3) (p_k0_61_76_cfgpos_5).

Definition s_k0_61_76 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_61_76 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 61 76) p_k0_61_76 = COk s_k0_61_76.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_61_76)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_93_108_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_93_108_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_93_108_cnt1) (p_k0_93_108_cnt1)).
Definition p_k0_93_108_cfg0_3 : plan :=
  PMmap (p_k0_93_108_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_93_108_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_93_108_cfgpos_5 : plan :=
  PMmap (p_k0_93_108_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_93_108_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_93_108_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_93_108_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_93_108 : plan :=
  PSplit (EVar 5) 0 (p_k0_93_108_cfg0_3) (p_k0_93_108_cfgpos_5).

Definition s_k0_93_108 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_93_108 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 93 108) p_k0_93_108 = COk s_k0_93_108.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_93_108)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_125_140_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_125_140_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_125_140_cnt1) (p_k0_125_140_cnt1)).
Definition p_k0_125_140_cfg0_3 : plan :=
  PMmap (p_k0_125_140_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_125_140_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_125_140_cfgpos_5 : plan :=
  PMmap (p_k0_125_140_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_125_140_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_125_140_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_125_140_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_125_140 : plan :=
  PSplit (EVar 5) 0 (p_k0_125_140_cfg0_3) (p_k0_125_140_cfgpos_5).

Definition s_k0_125_140 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_125_140 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 125 140) p_k0_125_140 = COk s_k0_125_140.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_125_140)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_141_156_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_141_156_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_141_156_cnt1) (p_k0_141_156_cnt1)).
Definition p_k0_141_156_cfg0_3 : plan :=
  PMmap (p_k0_141_156_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_141_156_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_141_156_cfgpos_5 : plan :=
  PMmap (p_k0_141_156_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_141_156_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_141_156_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_141_156_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_141_156 : plan :=
  PSplit (EVar 5) 0 (p_k0_141_156_cfg0_3) (p_k0_141_156_cfgpos_5).

Definition s_k0_141_156 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_141_156 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 141 156) p_k0_141_156 = COk s_k0_141_156.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_141_156)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_157_188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_157_188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_157_188_cnt1) (p_k0_157_188_cnt1)).
Definition p_k0_157_188_cfg0_3 : plan :=
  PMmap (p_k0_157_188_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_157_188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_157_188_cfgpos_5 : plan :=
  PMmap (p_k0_157_188_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_157_188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_157_188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_157_188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_157_188 : plan :=
  PSplit (EVar 5) 0 (p_k0_157_188_cfg0_3) (p_k0_157_188_cfgpos_5).

Definition s_k0_157_188 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_157_188 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 157 188) p_k0_157_188 = COk s_k0_157_188.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_157_188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_189_236_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_189_236_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_189_236_cnt1) (p_k0_189_236_cnt1)).
Definition p_k0_189_236_cfg0_3 : plan :=
  PMmap (p_k0_189_236_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_189_236_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_189_236_cfgpos_5 : plan :=
  PMmap (p_k0_189_236_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_189_236_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_189_236_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_189_236_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_189_236 : plan :=
  PSplit (EVar 5) 0 (p_k0_189_236_cfg0_3) (p_k0_189_236_cfgpos_5).

Definition s_k0_189_236 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_189_236 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 189 236) p_k0_189_236 = COk s_k0_189_236.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_189_236)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_237_284_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_237_284_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_237_284_cnt1) (p_k0_237_284_cnt1)).
Definition p_k0_237_284_cfg0_3 : plan :=
  PMmap (p_k0_237_284_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_237_284_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_237_284_cfgpos_5 : plan :=
  PMmap (p_k0_237_284_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_237_284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_237_284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_237_284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_237_284 : plan :=
  PSplit (EVar 5) 0 (p_k0_237_284_cfg0_3) (p_k0_237_284_cfgpos_5).

Definition s_k0_237_284 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_237_284 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 237 284) p_k0_237_284 = COk s_k0_237_284.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_237_284)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_285_316_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_285_316_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_285_316_cnt1) (p_k0_285_316_cnt1)).
Definition p_k0_285_316_cfg0_3 : plan :=
  PMmap (p_k0_285_316_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_285_316_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_285_316_cfgpos_5 : plan :=
  PMmap (p_k0_285_316_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_285_316_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_285_316_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_285_316_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_285_316 : plan :=
  PSplit (EVar 5) 0 (p_k0_285_316_cfg0_3) (p_k0_285_316_cfgpos_5).

Definition s_k0_285_316 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_285_316 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 285 316) p_k0_285_316 = COk s_k0_285_316.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_285_316)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_317_396_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_317_396_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_317_396_cnt1) (p_k0_317_396_cnt1)).
Definition p_k0_317_396_cfg0_3 : plan :=
  PMmap (p_k0_317_396_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_317_396_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_317_396_cfgpos_5 : plan :=
  PMmap (p_k0_317_396_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_317_396_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_317_396_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_317_396_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_317_396 : plan :=
  PSplit (EVar 5) 0 (p_k0_317_396_cfg0_3) (p_k0_317_396_cfgpos_5).

Definition s_k0_317_396 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_317_396 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 317 396) p_k0_317_396 = COk s_k0_317_396.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_317_396)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_397_492_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_397_492_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_397_492_cnt1) (p_k0_397_492_cnt1)).
Definition p_k0_397_492_cfg0_3 : plan :=
  PMmap (p_k0_397_492_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_397_492_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_397_492_cfgpos_5 : plan :=
  PMmap (p_k0_397_492_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_397_492_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_397_492_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_397_492_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_397_492 : plan :=
  PSplit (EVar 5) 0 (p_k0_397_492_cfg0_3) (p_k0_397_492_cfgpos_5).

Definition s_k0_397_492 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_397_492 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 397 492) p_k0_397_492 = COk s_k0_397_492.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_397_492)). Qed.

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

Lemma chk_k0_18701_20460 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 18701 20460) p_k0_18701_20460 = COk s_k0_18701_20460.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_18701_20460)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_57325_61420_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_57325_61420_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_57325_61420_cnt1) (p_k0_57325_61420_cnt1)).
Definition p_k0_57325_61420_cfg0_3 : plan :=
  PMmap (p_k0_57325_61420_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_57325_61420_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_57325_61420_cfgpos_5 : plan :=
  PMmap (p_k0_57325_61420_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_57325_61420_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_57325_61420_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_57325_61420_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_57325_61420 : plan :=
  PSplit (EVar 5) 0 (p_k0_57325_61420_cfg0_3) (p_k0_57325_61420_cfgpos_5).

Definition s_k0_57325_61420 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_57325_61420 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 57325 61420) p_k0_57325_61420 = COk s_k0_57325_61420.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61421_65516_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_61421_65516_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_61421_65516_cnt1) (p_k0_61421_65516_cnt1)).
Definition p_k0_61421_65516_cfg0_3 : plan :=
  PMmap (p_k0_61421_65516_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_61421_65516_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_61421_65516_cfgpos_5 : plan :=
  PMmap (p_k0_61421_65516_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_61421_65516_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_61421_65516_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_61421_65516_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_61421_65516 : plan :=
  PSplit (EVar 5) 0 (p_k0_61421_65516_cfg0_3) (p_k0_61421_65516_cfgpos_5).

Definition s_k0_61421_65516 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_61421_65516 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 61421 65516) p_k0_61421_65516 = COk s_k0_61421_65516.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_61421_65516)). Qed.

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

Lemma chk_k1_49133_52412 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 49133 52412) p_k1_49133_52412 = COk s_k1_49133_52412.
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

Lemma chk_k1_52413_53228 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 52413 53228) p_k1_52413_53228 = COk s_k1_52413_53228.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_52413_53228)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_53229_57324_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_53229_57324_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_53229_57324_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_53229_57324_cnt1) (p_k1_53229_57324_cnt1)).
Definition p_k1_53229_57324_cfgpos_4 : plan :=
  PMmap (p_k1_53229_57324_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_53229_57324_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_53229_57324_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_53229_57324_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_53229_57324 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_53229_57324_cfgpos_4).

Definition s_k1_53229_57324 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_53229_57324 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 53229 57324) p_k1_53229_57324 = COk s_k1_53229_57324.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_53229_57324)). Qed.

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

Lemma chk_k1_57325_61420 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 57325 61420) p_k1_57325_61420 = COk s_k1_57325_61420.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_65517_69612_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_65517_69612_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_65517_69612_cnt1) (p_k1_65517_69612_cnt1)).
Definition p_k1_65517_69612_cfg0_3 : plan :=
  PMmap (p_k1_65517_69612_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_65517_69612_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_65517_69612_cfgpos_5 : plan :=
  PMmap (p_k1_65517_69612_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_65517_69612_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_65517_69612_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_65517_69612_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_65517_69612 : plan :=
  PSplit (EVar 5) 0 (p_k1_65517_69612_cfg0_3) (p_k1_65517_69612_cfgpos_5).

Definition s_k1_65517_69612 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_65517_69612 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 65517 69612) p_k1_65517_69612 = COk s_k1_65517_69612.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_65517_69612)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_77805_81900_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_77805_81900_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_77805_81900_cnt1) (p_k1_77805_81900_cnt1)).
Definition p_k1_77805_81900_cfg0_3 : plan :=
  PMmap (p_k1_77805_81900_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_77805_81900_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_77805_81900_cfgpos_5 : plan :=
  PMmap (p_k1_77805_81900_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_77805_81900_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_77805_81900_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_77805_81900_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_77805_81900 : plan :=
  PSplit (EVar 5) 0 (p_k1_77805_81900_cfg0_3) (p_k1_77805_81900_cfgpos_5).

Definition s_k1_77805_81900 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_77805_81900 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 77805 81900) p_k1_77805_81900 = COk s_k1_77805_81900.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_77805_81900)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_87357_90092_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_87357_90092_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_87357_90092_cnt1) (p_k1_87357_90092_cnt1)).
Definition p_k1_87357_90092_cfg0_3 : plan :=
  PMmap (p_k1_87357_90092_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_87357_90092_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_87357_90092_cfgpos_5 : plan :=
  PMmap (p_k1_87357_90092_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_87357_90092_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_87357_90092_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_87357_90092_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_87357_90092 : plan :=
  PSplit (EVar 5) 0 (p_k1_87357_90092_cfg0_3) (p_k1_87357_90092_cfgpos_5).

Definition s_k1_87357_90092 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_87357_90092 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 87357 90092) p_k1_87357_90092 = COk s_k1_87357_90092.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_87357_90092)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_114669_118764_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_114669_118764_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_114669_118764_cnt1) (p_k1_114669_118764_cnt1)).
Definition p_k1_114669_118764_cfg0_3 : plan :=
  PMmap (p_k1_114669_118764_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_114669_118764_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_114669_118764_cfgpos_5 : plan :=
  PMmap (p_k1_114669_118764_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_114669_118764_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_114669_118764_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_114669_118764_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_114669_118764 : plan :=
  PSplit (EVar 5) 0 (p_k1_114669_118764_cfg0_3) (p_k1_114669_118764_cfgpos_5).

Definition s_k1_114669_118764 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_114669_118764 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 114669 118764) p_k1_114669_118764 = COk s_k1_114669_118764.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_114669_118764)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_122861_126956_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_122861_126956_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_122861_126956_cnt1) (p_k1_122861_126956_cnt1)).
Definition p_k1_122861_126956_cfg0_3 : plan :=
  PMmap (p_k1_122861_126956_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_122861_126956_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_122861_126956_cfgpos_5 : plan :=
  PMmap (p_k1_122861_126956_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_122861_126956_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_122861_126956_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_122861_126956_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_122861_126956 : plan :=
  PSplit (EVar 5) 0 (p_k1_122861_126956_cfg0_3) (p_k1_122861_126956_cfgpos_5).

Definition s_k1_122861_126956 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_122861_126956 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 122861 126956) p_k1_122861_126956 = COk s_k1_122861_126956.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_122861_126956)). Qed.

End RefTPBc_g02.
From Stdlib Require Zify.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg Spec RefWorld RefTargetPre RefWorldK RefTargetPreK SymExec3 SymPlan SymPlanSoundA. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetEntry_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetEntryK_defs. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetShape. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetShapeTop. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefTargetAssemblyTop. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefTargetAssemblyTop.RefTargetAssembly. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetCover.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetAssemblyTop. Import RefTPBc_g02.
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
Lemma cso_k0_1_12 : class_shape_ok true s_k0_1_12 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1_12 : TP0 1 12.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1 12 p_k0_1_12 s_k0_1_12 chk_k0_1_12 cso_k0_1_12); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_13_28 : class_shape_ok true s_k0_13_28 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13_28 : TP0 13 28.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 13 28 p_k0_13_28 s_k0_13_28 chk_k0_13_28 cso_k0_13_28); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_29_44 : class_shape_ok true s_k0_29_44 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_29_44 : TP0 29 44.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 29 44 p_k0_29_44 s_k0_29_44 chk_k0_29_44 cso_k0_29_44); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45_60 : class_shape_ok true s_k0_45_60 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45_60 : TP0 45 60.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 45 60 p_k0_45_60 s_k0_45_60 chk_k0_45_60 cso_k0_45_60); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61_76 : class_shape_ok true s_k0_61_76 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61_76 : TP0 61 76.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 61 76 p_k0_61_76 s_k0_61_76 chk_k0_61_76 cso_k0_61_76); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_93_108 : class_shape_ok true s_k0_93_108 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_93_108 : TP0 93 108.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 93 108 p_k0_93_108 s_k0_93_108 chk_k0_93_108 cso_k0_93_108); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_125_140 : class_shape_ok true s_k0_125_140 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_125_140 : TP0 125 140.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 125 140 p_k0_125_140 s_k0_125_140 chk_k0_125_140 cso_k0_125_140); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_141_156 : class_shape_ok true s_k0_141_156 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_141_156 : TP0 141 156.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 141 156 p_k0_141_156 s_k0_141_156 chk_k0_141_156 cso_k0_141_156); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_157_188 : class_shape_ok true s_k0_157_188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_157_188 : TP0 157 188.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 157 188 p_k0_157_188 s_k0_157_188 chk_k0_157_188 cso_k0_157_188); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_189_236 : class_shape_ok true s_k0_189_236 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_189_236 : TP0 189 236.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 189 236 p_k0_189_236 s_k0_189_236 chk_k0_189_236 cso_k0_189_236); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_237_284 : class_shape_ok true s_k0_237_284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_237_284 : TP0 237 284.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 237 284 p_k0_237_284 s_k0_237_284 chk_k0_237_284 cso_k0_237_284); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_285_316 : class_shape_ok true s_k0_285_316 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_285_316 : TP0 285 316.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 285 316 p_k0_285_316 s_k0_285_316 chk_k0_285_316 cso_k0_285_316); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_317_396 : class_shape_ok true s_k0_317_396 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_317_396 : TP0 317 396.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 317 396 p_k0_317_396 s_k0_317_396 chk_k0_317_396 cso_k0_317_396); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_397_492 : class_shape_ok true s_k0_397_492 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_397_492 : TP0 397 492.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 397 492 p_k0_397_492 s_k0_397_492 chk_k0_397_492 cso_k0_397_492); try eassumption; lia.
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
Lemma cso_k0_57325_61420 : class_shape_ok true s_k0_57325_61420 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_57325_61420 : TP0 57325 61420.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 57325 61420 p_k0_57325_61420 s_k0_57325_61420 chk_k0_57325_61420 cso_k0_57325_61420); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_61421_65516 : class_shape_ok true s_k0_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_61421_65516 : TP0 61421 65516.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 61421 65516 p_k0_61421_65516 s_k0_61421_65516 chk_k0_61421_65516 cso_k0_61421_65516); try eassumption; lia.
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
Lemma cso_k1_53229_57324 : class_shape_ok1 true s_k1_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_53229_57324 : TPK 1 53229 57324.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 53229 57324 p_k1_53229_57324 s_k1_53229_57324 chk_k1_53229_57324 cso_k1_53229_57324); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_65517_69612 : class_shape_ok true s_k1_65517_69612 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_65517_69612 : TPK 1 65517 69612.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 65517 69612 p_k1_65517_69612 s_k1_65517_69612 chk_k1_65517_69612 cso_k1_65517_69612); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_77805_81900 : class_shape_ok true s_k1_77805_81900 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_77805_81900 : TPK 1 77805 81900.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 77805 81900 p_k1_77805_81900 s_k1_77805_81900 chk_k1_77805_81900 cso_k1_77805_81900); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_87357_90092 : class_shape_ok true s_k1_87357_90092 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_87357_90092 : TPK 1 87357 90092.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 87357 90092 p_k1_87357_90092 s_k1_87357_90092 chk_k1_87357_90092 cso_k1_87357_90092); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_114669_118764 : class_shape_ok true s_k1_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_114669_118764 : TPK 1 114669 118764.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 114669 118764 p_k1_114669_118764 s_k1_114669_118764 chk_k1_114669_118764 cso_k1_114669_118764); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_122861_126956 : class_shape_ok true s_k1_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_122861_126956 : TPK 1 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 122861 126956 p_k1_122861_126956 s_k1_122861_126956 chk_k1_122861_126956 cso_k1_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

End LIB.
End WithFP.
