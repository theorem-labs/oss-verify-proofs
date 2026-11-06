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

Module RefTPBc_g04.
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
Definition p_k0_1005_1148_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1005_1148_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1005_1148_cnt1) (p_k0_1005_1148_cnt1)).
Definition p_k0_1005_1148_cfg0_3 : plan :=
  PMmap (p_k0_1005_1148_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1005_1148_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1005_1148_cfgpos_5 : plan :=
  PMmap (p_k0_1005_1148_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_1005_1148_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_1005_1148_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_1005_1148_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1005_1148 : plan :=
  PSplit (EVar 5) 0 (p_k0_1005_1148_cfg0_3) (p_k0_1005_1148_cfgpos_5).

Definition s_k0_1005_1148 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1005_1148 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 1005 1148) p_k0_1005_1148 = COk s_k0_1005_1148.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1005_1148)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1341_1628_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1341_1628_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1341_1628_cnt1) (p_k0_1341_1628_cnt1)).
Definition p_k0_1341_1628_cfg0_3 : plan :=
  PMmap (p_k0_1341_1628_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1341_1628_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1341_1628_cfgpos_5 : plan :=
  PMmap (p_k0_1341_1628_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_1341_1628_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_1341_1628_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_1341_1628_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1341_1628 : plan :=
  PSplit (EVar 5) 0 (p_k0_1341_1628_cfg0_3) (p_k0_1341_1628_cfgpos_5).

Definition s_k0_1341_1628 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1341_1628 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 1341 1628) p_k0_1341_1628 = COk s_k0_1341_1628.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1341_1628)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2333_2716_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_2333_2716_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_2333_2716_cnt1) (p_k0_2333_2716_cnt1)).
Definition p_k0_2333_2716_cfg0_3 : plan :=
  PMmap (p_k0_2333_2716_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_2333_2716_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_2333_2716_cfgpos_5 : plan :=
  PMmap (p_k0_2333_2716_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_2333_2716_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_2333_2716_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_2333_2716_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_2333_2716 : plan :=
  PSplit (EVar 5) 0 (p_k0_2333_2716_cfg0_3) (p_k0_2333_2716_cfgpos_5).

Definition s_k0_2333_2716 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_2333_2716 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 2333 2716) p_k0_2333_2716 = COk s_k0_2333_2716.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2333_2716)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_3261_4076_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_3261_4076_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_3261_4076_cnt1) (p_k0_3261_4076_cnt1)).
Definition p_k0_3261_4076_cfg0_3 : plan :=
  PMmap (p_k0_3261_4076_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_3261_4076_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_3261_4076_cfgpos_5 : plan :=
  PMmap (p_k0_3261_4076_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_3261_4076_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_3261_4076_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_3261_4076_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_3261_4076 : plan :=
  PSplit (EVar 5) 0 (p_k0_3261_4076_cfg0_3) (p_k0_3261_4076_cfgpos_5).

Definition s_k0_3261_4076 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_3261_4076 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 3261 4076) p_k0_3261_4076 = COk s_k0_3261_4076.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_3261_4076)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_6541_8172_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_6541_8172_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_6541_8172_cnt1) (p_k0_6541_8172_cnt1)).
Definition p_k0_6541_8172_cfg0_3 : plan :=
  PMmap (p_k0_6541_8172_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_6541_8172_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_6541_8172_cfgpos_5 : plan :=
  PMmap (p_k0_6541_8172_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_6541_8172_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_6541_8172_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_6541_8172_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_6541_8172 : plan :=
  PSplit (EVar 5) 0 (p_k0_6541_8172_cfg0_3) (p_k0_6541_8172_cfgpos_5).

Definition s_k0_6541_8172 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_6541_8172 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 6541 8172) p_k0_6541_8172 = COk s_k0_6541_8172.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_6541_8172)). Qed.

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

Lemma chk_k0_8173_9340 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 8173 9340) p_k0_8173_9340 = COk s_k0_8173_9340.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_8173_9340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_9341_10908_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_9341_10908_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_9341_10908_cnt1) (p_k0_9341_10908_cnt1)).
Definition p_k0_9341_10908_cfg0_3 : plan :=
  PMmap (p_k0_9341_10908_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_9341_10908_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_9341_10908_cfgpos_5 : plan :=
  PMmap (p_k0_9341_10908_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_9341_10908_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_9341_10908_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_9341_10908_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_9341_10908 : plan :=
  PSplit (EVar 5) 0 (p_k0_9341_10908_cfg0_3) (p_k0_9341_10908_cfgpos_5).

Definition s_k0_9341_10908 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_9341_10908 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 9341 10908) p_k0_9341_10908 = COk s_k0_9341_10908.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_9341_10908)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_13085_16364_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_13085_16364_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_13085_16364_cnt1) (p_k0_13085_16364_cnt1)).
Definition p_k0_13085_16364_cfg0_3 : plan :=
  PMmap (p_k0_13085_16364_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_13085_16364_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_13085_16364_cfgpos_5 : plan :=
  PMmap (p_k0_13085_16364_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_13085_16364_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_13085_16364_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_13085_16364_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_13085_16364 : plan :=
  PSplit (EVar 5) 0 (p_k0_13085_16364_cfg0_3) (p_k0_13085_16364_cfgpos_5).

Definition s_k0_13085_16364 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_13085_16364 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 13085 16364) p_k0_13085_16364 = COk s_k0_13085_16364.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_13085_16364)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_20461_21820_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_20461_21820_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_20461_21820_cnt1) (p_k0_20461_21820_cnt1)).
Definition p_k0_20461_21820_cfg0_3 : plan :=
  PMmap (p_k0_20461_21820_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_20461_21820_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_20461_21820_cfgpos_5 : plan :=
  PMmap (p_k0_20461_21820_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_20461_21820_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_20461_21820_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_20461_21820_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_20461_21820 : plan :=
  PSplit (EVar 5) 0 (p_k0_20461_21820_cfg0_3) (p_k0_20461_21820_cfgpos_5).

Definition s_k0_20461_21820 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_20461_21820 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 20461 21820) p_k0_20461_21820 = COk s_k0_20461_21820.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_20461_21820)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_28653_32748_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_28653_32748_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_28653_32748_cnt1) (p_k0_28653_32748_cnt1)).
Definition p_k0_28653_32748_cfg0_3 : plan :=
  PMmap (p_k0_28653_32748_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_28653_32748_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_28653_32748_cfgpos_5 : plan :=
  PMmap (p_k0_28653_32748_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_28653_32748_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_28653_32748_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_28653_32748_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_28653_32748 : plan :=
  PSplit (EVar 5) 0 (p_k0_28653_32748_cfg0_3) (p_k0_28653_32748_cfgpos_5).

Definition s_k0_28653_32748 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_28653_32748 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 28653 32748) p_k0_28653_32748 = COk s_k0_28653_32748.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_28653_32748)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_36845_37436_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_36845_37436_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_36845_37436_cnt1) (p_k0_36845_37436_cnt1)).
Definition p_k0_36845_37436_cfg0_3 : plan :=
  PMmap (p_k0_36845_37436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_36845_37436_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_36845_37436_cfgpos_5 : plan :=
  PMmap (p_k0_36845_37436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_36845_37436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_36845_37436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_36845_37436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_36845_37436 : plan :=
  PSplit (EVar 5) 0 (p_k0_36845_37436_cfg0_3) (p_k0_36845_37436_cfgpos_5).

Definition s_k0_36845_37436 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_36845_37436 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 36845 37436) p_k0_36845_37436 = COk s_k0_36845_37436.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45037_49132_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_45037_49132_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_45037_49132_cnt1) (p_k0_45037_49132_cnt1)).
Definition p_k0_45037_49132_cfg0_3 : plan :=
  PMmap (p_k0_45037_49132_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_45037_49132_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_45037_49132_cfgpos_5 : plan :=
  PMmap (p_k0_45037_49132_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_45037_49132_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_45037_49132_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_45037_49132_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_45037_49132 : plan :=
  PSplit (EVar 5) 0 (p_k0_45037_49132_cfg0_3) (p_k0_45037_49132_cfgpos_5).

Definition s_k0_45037_49132 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_45037_49132 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 45037 49132) p_k0_45037_49132 = COk s_k0_45037_49132.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_49133_52412_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_49133_52412_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_49133_52412_cnt1) (p_k0_49133_52412_cnt1)).
Definition p_k0_49133_52412_cfg0_3 : plan :=
  PMmap (p_k0_49133_52412_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_49133_52412_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_49133_52412_cfgpos_5 : plan :=
  PMmap (p_k0_49133_52412_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_49133_52412_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_49133_52412_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_49133_52412_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_49133_52412 : plan :=
  PSplit (EVar 5) 0 (p_k0_49133_52412_cfg0_3) (p_k0_49133_52412_cfgpos_5).

Definition s_k0_49133_52412 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_49133_52412 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 49133 52412) p_k0_49133_52412 = COk s_k0_49133_52412.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_49133_52412)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_52413_53228_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_52413_53228_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_52413_53228_cnt1) (p_k0_52413_53228_cnt1)).
Definition p_k0_52413_53228_cfg0_3 : plan :=
  PMmap (p_k0_52413_53228_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_52413_53228_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_52413_53228_cfgpos_5 : plan :=
  PMmap (p_k0_52413_53228_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_52413_53228_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_52413_53228_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_52413_53228_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_52413_53228 : plan :=
  PSplit (EVar 5) 0 (p_k0_52413_53228_cfg0_3) (p_k0_52413_53228_cfgpos_5).

Definition s_k0_52413_53228 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_52413_53228 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 52413 53228) p_k0_52413_53228 = COk s_k0_52413_53228.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_52413_53228)). Qed.

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

Lemma chk_k1_45037_49132 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 45037 49132) p_k1_45037_49132 = COk s_k1_45037_49132.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_69613_73708_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_69613_73708_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_69613_73708_cnt1) (p_k1_69613_73708_cnt1)).
Definition p_k1_69613_73708_cfg0_3 : plan :=
  PMmap (p_k1_69613_73708_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_69613_73708_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_69613_73708_cfgpos_5 : plan :=
  PMmap (p_k1_69613_73708_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_69613_73708_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_69613_73708_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_69613_73708_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_69613_73708 : plan :=
  PSplit (EVar 5) 0 (p_k1_69613_73708_cfg0_3) (p_k1_69613_73708_cfgpos_5).

Definition s_k1_69613_73708 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_69613_73708 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 69613 73708) p_k1_69613_73708 = COk s_k1_69613_73708.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_69613_73708)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_98285_102380_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_98285_102380_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_98285_102380_cnt1) (p_k1_98285_102380_cnt1)).
Definition p_k1_98285_102380_cfg0_3 : plan :=
  PMmap (p_k1_98285_102380_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_98285_102380_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_98285_102380_cfgpos_5 : plan :=
  PMmap (p_k1_98285_102380_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_98285_102380_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_98285_102380_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_98285_102380_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_98285_102380 : plan :=
  PSplit (EVar 5) 0 (p_k1_98285_102380_cfg0_3) (p_k1_98285_102380_cfgpos_5).

Definition s_k1_98285_102380 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_98285_102380 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 98285 102380) p_k1_98285_102380 = COk s_k1_98285_102380.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_98285_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_102381_104828_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_102381_104828_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_102381_104828_cnt1) (p_k1_102381_104828_cnt1)).
Definition p_k1_102381_104828_cfg0_3 : plan :=
  PMmap (p_k1_102381_104828_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_102381_104828_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_102381_104828_cfgpos_5 : plan :=
  PMmap (p_k1_102381_104828_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_102381_104828_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_102381_104828_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_102381_104828_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_102381_104828 : plan :=
  PSplit (EVar 5) 0 (p_k1_102381_104828_cfg0_3) (p_k1_102381_104828_cfgpos_5).

Definition s_k1_102381_104828 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_102381_104828 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 102381 104828) p_k1_102381_104828 = COk s_k1_102381_104828.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_104829_106476_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_104829_106476_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_104829_106476_cnt1) (p_k1_104829_106476_cnt1)).
Definition p_k1_104829_106476_cfg0_3 : plan :=
  PMmap (p_k1_104829_106476_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_104829_106476_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_104829_106476_cfgpos_5 : plan :=
  PMmap (p_k1_104829_106476_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_104829_106476_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_104829_106476_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_104829_106476_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_104829_106476 : plan :=
  PSplit (EVar 5) 0 (p_k1_104829_106476_cfg0_3) (p_k1_104829_106476_cfgpos_5).

Definition s_k1_104829_106476 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_104829_106476 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 104829 106476) p_k1_104829_106476 = COk s_k1_104829_106476.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_104829_106476)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_106477_110572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_106477_110572_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_106477_110572_cnt1) (p_k1_106477_110572_cnt1)).
Definition p_k1_106477_110572_cfg0_3 : plan :=
  PMmap (p_k1_106477_110572_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_106477_110572_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_106477_110572_cfgpos_5 : plan :=
  PMmap (p_k1_106477_110572_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_106477_110572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_106477_110572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_106477_110572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_106477_110572 : plan :=
  PSplit (EVar 5) 0 (p_k1_106477_110572_cfg0_3) (p_k1_106477_110572_cfgpos_5).

Definition s_k1_106477_110572 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_106477_110572 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 106477 110572) p_k1_106477_110572 = COk s_k1_106477_110572.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_110573_114668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_110573_114668_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_110573_114668_cnt1) (p_k1_110573_114668_cnt1)).
Definition p_k1_110573_114668_cfg0_3 : plan :=
  PMmap (p_k1_110573_114668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_110573_114668_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_110573_114668_cfgpos_5 : plan :=
  PMmap (p_k1_110573_114668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_110573_114668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_110573_114668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_110573_114668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_110573_114668 : plan :=
  PSplit (EVar 5) 0 (p_k1_110573_114668_cfg0_3) (p_k1_110573_114668_cfgpos_5).

Definition s_k1_110573_114668 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_110573_114668 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 110573 114668) p_k1_110573_114668 = COk s_k1_110573_114668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_110573_114668)). Qed.

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

Lemma chk_k1_131052_131065 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 131052 131065) p_k1_131052_131065 = COk s_k1_131052_131065.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_131052_131065)). Qed.

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

Lemma chk_k2_104829_106476 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 104829 106476) p_k2_104829_106476 = COk s_k2_104829_106476.
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

Lemma chk_k2_106477_110572 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 106477 110572) p_k2_106477_110572 = COk s_k2_106477_110572.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_118765_122860_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_118765_122860_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_118765_122860_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_118765_122860_cnt1) (p_k2_118765_122860_cnt1)).
Definition p_k2_118765_122860_cfgpos_4 : plan :=
  PMmap (p_k2_118765_122860_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_118765_122860_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_118765_122860_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_118765_122860_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_118765_122860 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_118765_122860_cfgpos_4).

Definition s_k2_118765_122860 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_118765_122860 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 118765 122860) p_k2_118765_122860 = COk s_k2_118765_122860.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_131052_262137_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_131052_262137_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_131052_262137_cnt1) (p_k2_131052_262137_cnt1)).
Definition p_k2_131052_262137_cfg0_3 : plan :=
  PMmap (p_k2_131052_262137_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k2_131052_262137_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_131052_262137_cfgpos_5 : plan :=
  PMmap (p_k2_131052_262137_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_131052_262137_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_131052_262137_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_131052_262137_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_131052_262137 : plan :=
  PSplit (EVar 5) 0 (p_k2_131052_262137_cfg0_3) (p_k2_131052_262137_cfgpos_5).

Definition s_k2_131052_262137 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_131052_262137 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 131052 262137) p_k2_131052_262137 = COk s_k2_131052_262137.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_131052_262137)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k3_229371_524281_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k3_229371_524281_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k3_229371_524281_cnt1) (p_k3_229371_524281_cnt1)).
Definition p_k3_229371_524281_cfg0_3 : plan :=
  PMmap (p_k3_229371_524281_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k3_229371_524281_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k3_229371_524281_cfgpos_5 : plan :=
  PMmap (p_k3_229371_524281_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k3_229371_524281_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k3_229371_524281_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k3_229371_524281_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k3_229371_524281 : plan :=
  PSplit (EVar 5) 0 (p_k3_229371_524281_cfg0_3) (p_k3_229371_524281_cfgpos_5).

Definition s_k3_229371_524281 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k3_229371_524281 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 3 229371 524281) p_k3_229371_524281 = COk s_k3_229371_524281.
Proof. native_cast_no_check (@eq_refl cres (COk s_k3_229371_524281)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k7_4161531_8388601_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k7_4161531_8388601_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k7_4161531_8388601_cnt1) (p_k7_4161531_8388601_cnt1)).
Definition p_k7_4161531_8388601_cfg0_3 : plan :=
  PMmap (p_k7_4161531_8388601_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k7_4161531_8388601_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k7_4161531_8388601_cfgpos_5 : plan :=
  PMmap (p_k7_4161531_8388601_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k7_4161531_8388601_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k7_4161531_8388601_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k7_4161531_8388601_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k7_4161531_8388601 : plan :=
  PSplit (EVar 5) 0 (p_k7_4161531_8388601_cfg0_3) (p_k7_4161531_8388601_cfgpos_5).

Definition s_k7_4161531_8388601 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k7_4161531_8388601 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 7 4161531 8388601) p_k7_4161531_8388601 = COk s_k7_4161531_8388601.
Proof. native_cast_no_check (@eq_refl cres (COk s_k7_4161531_8388601)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_33521659_67108857_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_33521659_67108857_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_33521659_67108857_cnt1) (p_k10_33521659_67108857_cnt1)).
Definition p_k10_33521659_67108857_cfg0_3 : plan :=
  PMmap (p_k10_33521659_67108857_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_33521659_67108857_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_33521659_67108857_cfgpos_5 : plan :=
  PMmap (p_k10_33521659_67108857_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k10_33521659_67108857_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k10_33521659_67108857_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k10_33521659_67108857_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_33521659_67108857 : plan :=
  PSplit (EVar 5) 0 (p_k10_33521659_67108857_cfg0_3) (p_k10_33521659_67108857_cfgpos_5).

Definition s_k10_33521659_67108857 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_33521659_67108857 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 10 33521659 67108857) p_k10_33521659_67108857 = COk s_k10_33521659_67108857.
Proof. native_cast_no_check (@eq_refl cres (COk s_k10_33521659_67108857)). Qed.

End RefTPBc_g04.
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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetAssemblyTop. Import RefTPBc_g04.
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
Lemma cso_k0_1005_1148 : class_shape_ok true s_k0_1005_1148 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1005_1148 : TP0 1005 1148.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1005 1148 p_k0_1005_1148 s_k0_1005_1148 chk_k0_1005_1148 cso_k0_1005_1148); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1341_1628 : class_shape_ok true s_k0_1341_1628 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1341_1628 : TP0 1341 1628.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1341 1628 p_k0_1341_1628 s_k0_1341_1628 chk_k0_1341_1628 cso_k0_1341_1628); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2333_2716 : class_shape_ok true s_k0_2333_2716 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2333_2716 : TP0 2333 2716.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 2333 2716 p_k0_2333_2716 s_k0_2333_2716 chk_k0_2333_2716 cso_k0_2333_2716); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_3261_4076 : class_shape_ok true s_k0_3261_4076 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_3261_4076 : TP0 3261 4076.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 3261 4076 p_k0_3261_4076 s_k0_3261_4076 chk_k0_3261_4076 cso_k0_3261_4076); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_6541_8172 : class_shape_ok true s_k0_6541_8172 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_6541_8172 : TP0 6541 8172.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 6541 8172 p_k0_6541_8172 s_k0_6541_8172 chk_k0_6541_8172 cso_k0_6541_8172); try eassumption; lia.
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
Lemma cso_k0_9341_10908 : class_shape_ok true s_k0_9341_10908 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_9341_10908 : TP0 9341 10908.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 9341 10908 p_k0_9341_10908 s_k0_9341_10908 chk_k0_9341_10908 cso_k0_9341_10908); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_13085_16364 : class_shape_ok true s_k0_13085_16364 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_13085_16364 : TP0 13085 16364.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 13085 16364 p_k0_13085_16364 s_k0_13085_16364 chk_k0_13085_16364 cso_k0_13085_16364); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_20461_21820 : class_shape_ok true s_k0_20461_21820 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_20461_21820 : TP0 20461 21820.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 20461 21820 p_k0_20461_21820 s_k0_20461_21820 chk_k0_20461_21820 cso_k0_20461_21820); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_28653_32748 : class_shape_ok true s_k0_28653_32748 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_28653_32748 : TP0 28653 32748.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 28653 32748 p_k0_28653_32748 s_k0_28653_32748 chk_k0_28653_32748 cso_k0_28653_32748); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_36845_37436 : class_shape_ok true s_k0_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_36845_37436 : TP0 36845 37436.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 36845 37436 p_k0_36845_37436 s_k0_36845_37436 chk_k0_36845_37436 cso_k0_36845_37436); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_45037_49132 : class_shape_ok true s_k0_45037_49132 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_45037_49132 : TP0 45037 49132.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 45037 49132 p_k0_45037_49132 s_k0_45037_49132 chk_k0_45037_49132 cso_k0_45037_49132); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_49133_52412 : class_shape_ok true s_k0_49133_52412 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_49133_52412 : TP0 49133 52412.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 49133 52412 p_k0_49133_52412 s_k0_49133_52412 chk_k0_49133_52412 cso_k0_49133_52412); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_52413_53228 : class_shape_ok true s_k0_52413_53228 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_52413_53228 : TP0 52413 53228.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 52413 53228 p_k0_52413_53228 s_k0_52413_53228 chk_k0_52413_53228 cso_k0_52413_53228); try eassumption; lia.
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
Lemma cso_k1_69613_73708 : class_shape_ok true s_k1_69613_73708 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_69613_73708 : TPK 1 69613 73708.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 69613 73708 p_k1_69613_73708 s_k1_69613_73708 chk_k1_69613_73708 cso_k1_69613_73708); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_98285_102380 : class_shape_ok true s_k1_98285_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_98285_102380 : TPK 1 98285 102380.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 98285 102380 p_k1_98285_102380 s_k1_98285_102380 chk_k1_98285_102380 cso_k1_98285_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_102381_104828 : class_shape_ok true s_k1_102381_104828 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_102381_104828 : TPK 1 102381 104828.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 102381 104828 p_k1_102381_104828 s_k1_102381_104828 chk_k1_102381_104828 cso_k1_102381_104828); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_104829_106476 : class_shape_ok true s_k1_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_104829_106476 : TPK 1 104829 106476.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 104829 106476 p_k1_104829_106476 s_k1_104829_106476 chk_k1_104829_106476 cso_k1_104829_106476); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_106477_110572 : class_shape_ok true s_k1_106477_110572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_106477_110572 : TPK 1 106477 110572.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 106477 110572 p_k1_106477_110572 s_k1_106477_110572 chk_k1_106477_110572 cso_k1_106477_110572); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_110573_114668 : class_shape_ok true s_k1_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_110573_114668 : TPK 1 110573 114668.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 110573 114668 p_k1_110573_114668 s_k1_110573_114668 chk_k1_110573_114668 cso_k1_110573_114668); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k2_118765_122860 : class_shape_ok1 true s_k2_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_118765_122860 : TPK 2 118765 122860.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 118765 122860 p_k2_118765_122860 s_k2_118765_122860 chk_k2_118765_122860 cso_k2_118765_122860); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_131052_262137 : class_shape_ok true s_k2_131052_262137 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_131052_262137 : TPK 2 131052 262137.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 2 20000 400 131052 262137 p_k2_131052_262137 s_k2_131052_262137 chk_k2_131052_262137 cso_k2_131052_262137); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k3_229371_524281 : class_shape_ok true s_k3_229371_524281 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k3_229371_524281 : TPK 3 229371 524281.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 3 20000 400 229371 524281 p_k3_229371_524281 s_k3_229371_524281 chk_k3_229371_524281 cso_k3_229371_524281); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k7_4161531_8388601 : class_shape_ok true s_k7_4161531_8388601 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k7_4161531_8388601 : TPK 7 4161531 8388601.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 7 20000 400 4161531 8388601 p_k7_4161531_8388601 s_k7_4161531_8388601 chk_k7_4161531_8388601 cso_k7_4161531_8388601); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k10_33521659_67108857 : class_shape_ok true s_k10_33521659_67108857 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k10_33521659_67108857 : TPK 10 33521659 67108857.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 10 20000 400 33521659 67108857 p_k10_33521659_67108857 s_k10_33521659_67108857 chk_k10_33521659_67108857 cso_k10_33521659_67108857); try eassumption; unfold capk; cbn; lia.
Qed.

End LIB.
End WithFP.
