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

Module UbTPBc_g03.
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

Lemma chk_k0_29_44 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 29 44) p_k0_29_44 = COk s_k0_29_44.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_29_44)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_573_668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_573_668_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_573_668_cnt1) (p_k0_573_668_cnt1)).
Definition p_k0_573_668_cfg0_3 : plan :=
  PMmap (p_k0_573_668_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_573_668_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_573_668_cfgpos_5 : plan :=
  PMmap (p_k0_573_668_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_573_668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_573_668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_573_668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_573_668 : plan :=
  PSplit (EVar 5) 0 (p_k0_573_668_cfg0_3) (p_k0_573_668_cfgpos_5).

Definition s_k0_573_668 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_573_668 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 573 668) p_k0_573_668 = COk s_k0_573_668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_573_668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_797_1004_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_797_1004_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_797_1004_cnt1) (p_k0_797_1004_cnt1)).
Definition p_k0_797_1004_cfg0_3 : plan :=
  PMmap (p_k0_797_1004_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_797_1004_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_797_1004_cfgpos_5 : plan :=
  PMmap (p_k0_797_1004_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_797_1004_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_797_1004_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_797_1004_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_797_1004 : plan :=
  PSplit (EVar 5) 0 (p_k0_797_1004_cfg0_3) (p_k0_797_1004_cfgpos_5).

Definition s_k0_797_1004 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_797_1004 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 797 1004) p_k0_797_1004 = COk s_k0_797_1004.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_797_1004)). Qed.

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

Lemma chk_k0_1005_1148 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 1005 1148) p_k0_1005_1148 = COk s_k0_1005_1148.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1005_1148)). Qed.

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

Lemma chk_k0_2333_2716 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 2333 2716) p_k0_2333_2716 = COk s_k0_2333_2716.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2333_2716)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_4077_4668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_4077_4668_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_4077_4668_cnt1) (p_k0_4077_4668_cnt1)).
Definition p_k0_4077_4668_cfg0_3 : plan :=
  PMmap (p_k0_4077_4668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_4077_4668_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_4077_4668_cfgpos_5 : plan :=
  PMmap (p_k0_4077_4668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_4077_4668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_4077_4668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_4077_4668_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_4077_4668 : plan :=
  PSplit (EVar 5) 0 (p_k0_4077_4668_cfg0_3) (p_k0_4077_4668_cfgpos_5).

Definition s_k0_4077_4668 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_4077_4668 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 4077 4668) p_k0_4077_4668 = COk s_k0_4077_4668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_4077_4668)). Qed.

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

Lemma chk_k0_13085_16364 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 13085 16364) p_k0_13085_16364 = COk s_k0_13085_16364.
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

Lemma chk_k0_20461_21820 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 20461 21820) p_k0_20461_21820 = COk s_k0_20461_21820.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_20461_21820)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_21821_24556_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_21821_24556_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_21821_24556_cnt1) (p_k0_21821_24556_cnt1)).
Definition p_k0_21821_24556_cfg0_3 : plan :=
  PMmap (p_k0_21821_24556_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_21821_24556_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_21821_24556_cfgpos_5 : plan :=
  PMmap (p_k0_21821_24556_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_21821_24556_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_21821_24556_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_21821_24556_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_21821_24556 : plan :=
  PSplit (EVar 5) 0 (p_k0_21821_24556_cfg0_3) (p_k0_21821_24556_cfgpos_5).

Definition s_k0_21821_24556 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_21821_24556 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 21821 24556) p_k0_21821_24556 = COk s_k0_21821_24556.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_21821_24556)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_24557_26188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_24557_26188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_24557_26188_cnt1) (p_k0_24557_26188_cnt1)).
Definition p_k0_24557_26188_cfg0_3 : plan :=
  PMmap (p_k0_24557_26188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_24557_26188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_24557_26188_cfgpos_5 : plan :=
  PMmap (p_k0_24557_26188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_24557_26188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_24557_26188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_24557_26188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_24557_26188 : plan :=
  PSplit (EVar 5) 0 (p_k0_24557_26188_cfg0_3) (p_k0_24557_26188_cfgpos_5).

Definition s_k0_24557_26188 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_24557_26188 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 24557 26188) p_k0_24557_26188 = COk s_k0_24557_26188.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_24557_26188)). Qed.

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

Lemma chk_k0_28653_32748 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 28653 32748) p_k0_28653_32748 = COk s_k0_28653_32748.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_28653_32748)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_32749_36844_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_32749_36844_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_32749_36844_cnt1) (p_k0_32749_36844_cnt1)).
Definition p_k0_32749_36844_cfg0_3 : plan :=
  PMmap (p_k0_32749_36844_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_32749_36844_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_32749_36844_cfgpos_5 : plan :=
  PMmap (p_k0_32749_36844_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_32749_36844_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_32749_36844_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_32749_36844_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_32749_36844 : plan :=
  PSplit (EVar 5) 0 (p_k0_32749_36844_cfg0_3) (p_k0_32749_36844_cfgpos_5).

Definition s_k0_32749_36844 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_32749_36844 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 32749 36844) p_k0_32749_36844 = COk s_k0_32749_36844.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_32749_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_37437_40940_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_37437_40940_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_37437_40940_cnt1) (p_k0_37437_40940_cnt1)).
Definition p_k0_37437_40940_cfg0_3 : plan :=
  PMmap (p_k0_37437_40940_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_37437_40940_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_37437_40940_cfgpos_5 : plan :=
  PMmap (p_k0_37437_40940_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_37437_40940_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_37437_40940_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_37437_40940_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_37437_40940 : plan :=
  PSplit (EVar 5) 0 (p_k0_37437_40940_cfg0_3) (p_k0_37437_40940_cfgpos_5).

Definition s_k0_37437_40940 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_37437_40940 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 37437 40940) p_k0_37437_40940 = COk s_k0_37437_40940.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_37437_40940)). Qed.

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

Lemma chk_k0_61421_65516 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 61421 65516) p_k0_61421_65516 = COk s_k0_61421_65516.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_65517_65529_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_65517_65529_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_65517_65529_cnt1) (p_k0_65517_65529_cnt1)).
Definition p_k0_65517_65529_cfg0_3 : plan :=
  PMmap (p_k0_65517_65529_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_65517_65529_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_65517_65529_cfgpos_5 : plan :=
  PMmap (p_k0_65517_65529_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_65517_65529_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_65517_65529_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_65517_65529_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_65517_65529 : plan :=
  PSplit (EVar 5) 0 (p_k0_65517_65529_cfg0_3) (p_k0_65517_65529_cfgpos_5).

Definition s_k0_65517_65529 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_65517_65529 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 65517 65529) p_k0_65517_65529 = COk s_k0_65517_65529.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_65517_65529)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_36845_37436_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_36845_37436_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_36845_37436_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_36845_37436_cnt1) (p_k1_36845_37436_cnt1)).
Definition p_k1_36845_37436_cfgpos_4 : plan :=
  PMmap (p_k1_36845_37436_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_36845_37436_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_36845_37436_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_36845_37436_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_36845_37436 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_36845_37436_cfgpos_4).

Definition s_k1_36845_37436 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_36845_37436 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 36845 37436) p_k1_36845_37436 = COk s_k1_36845_37436.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_37437_40940_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_37437_40940_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_37437_40940_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_37437_40940_cnt1) (p_k1_37437_40940_cnt1)).
Definition p_k1_37437_40940_cfgpos_4 : plan :=
  PMmap (p_k1_37437_40940_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_37437_40940_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_37437_40940_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_37437_40940_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_37437_40940 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_37437_40940_cfgpos_4).

Definition s_k1_37437_40940 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_37437_40940 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 37437 40940) p_k1_37437_40940 = COk s_k1_37437_40940.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_37437_40940)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_40941_43676_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_40941_43676_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_40941_43676_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_40941_43676_cnt1) (p_k1_40941_43676_cnt1)).
Definition p_k1_40941_43676_cfgpos_4 : plan :=
  PMmap (p_k1_40941_43676_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_40941_43676_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_40941_43676_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_40941_43676_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_40941_43676 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_40941_43676_cfgpos_4).

Definition s_k1_40941_43676 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_40941_43676 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 40941 43676) p_k1_40941_43676 = COk s_k1_40941_43676.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_40941_43676)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_43677_45036_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_43677_45036_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_43677_45036_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_43677_45036_cnt1) (p_k1_43677_45036_cnt1)).
Definition p_k1_43677_45036_cfgpos_4 : plan :=
  PMmap (p_k1_43677_45036_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_43677_45036_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_43677_45036_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_43677_45036_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_43677_45036 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_43677_45036_cfgpos_4).

Definition s_k1_43677_45036 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_43677_45036 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 43677 45036) p_k1_43677_45036 = COk s_k1_43677_45036.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_43677_45036)). Qed.

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

Lemma chk_k1_69613_73708 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 69613 73708) p_k1_69613_73708 = COk s_k1_69613_73708.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_69613_73708)). Qed.

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

Lemma chk_k1_77805_81900 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 77805 81900) p_k1_77805_81900 = COk s_k1_77805_81900.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_77805_81900)). Qed.

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

Lemma chk_k1_98285_102380 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 98285 102380) p_k1_98285_102380 = COk s_k1_98285_102380.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_98285_102380)). Qed.

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

Lemma chk_k1_104829_106476 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 104829 106476) p_k1_104829_106476 = COk s_k1_104829_106476.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_104829_106476)). Qed.

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

Lemma chk_k2_118765_122860 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 118765 122860) p_k2_118765_122860 = COk s_k2_118765_122860.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_122861_126956_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_122861_126956_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_122861_126956_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_122861_126956_cnt1) (p_k2_122861_126956_cnt1)).
Definition p_k2_122861_126956_cfgpos_4 : plan :=
  PMmap (p_k2_122861_126956_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_122861_126956_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_122861_126956_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_122861_126956_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_122861_126956 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_122861_126956_cfgpos_4).

Definition s_k2_122861_126956 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_122861_126956 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 122861 126956) p_k2_122861_126956 = COk s_k2_122861_126956.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_122861_126956)). Qed.

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

Lemma chk_k2_131052_262137 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 131052 262137) p_k2_131052_262137 = COk s_k2_131052_262137.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_131052_262137)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k5_1015803_2097145_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k5_1015803_2097145_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k5_1015803_2097145_cnt1) (p_k5_1015803_2097145_cnt1)).
Definition p_k5_1015803_2097145_cfg0_3 : plan :=
  PMmap (p_k5_1015803_2097145_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k5_1015803_2097145_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k5_1015803_2097145_cfgpos_5 : plan :=
  PMmap (p_k5_1015803_2097145_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k5_1015803_2097145_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k5_1015803_2097145_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k5_1015803_2097145_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k5_1015803_2097145 : plan :=
  PSplit (EVar 5) 0 (p_k5_1015803_2097145_cfg0_3) (p_k5_1015803_2097145_cfgpos_5).

Definition s_k5_1015803_2097145 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k5_1015803_2097145 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 5 1015803 2097145) p_k5_1015803_2097145 = COk s_k5_1015803_2097145.
Proof. native_cast_no_check (@eq_refl cres (COk s_k5_1015803_2097145)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k6_2064379_4194297_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k6_2064379_4194297_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k6_2064379_4194297_cnt1) (p_k6_2064379_4194297_cnt1)).
Definition p_k6_2064379_4194297_cfg0_3 : plan :=
  PMmap (p_k6_2064379_4194297_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k6_2064379_4194297_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k6_2064379_4194297_cfgpos_5 : plan :=
  PMmap (p_k6_2064379_4194297_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k6_2064379_4194297_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k6_2064379_4194297_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k6_2064379_4194297_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k6_2064379_4194297 : plan :=
  PSplit (EVar 5) 0 (p_k6_2064379_4194297_cfg0_3) (p_k6_2064379_4194297_cfgpos_5).

Definition s_k6_2064379_4194297 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k6_2064379_4194297 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 6 2064379 4194297) p_k6_2064379_4194297 = COk s_k6_2064379_4194297.
Proof. native_cast_no_check (@eq_refl cres (COk s_k6_2064379_4194297)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k9_16744443_33554425_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k9_16744443_33554425_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k9_16744443_33554425_cnt1) (p_k9_16744443_33554425_cnt1)).
Definition p_k9_16744443_33554425_cfg0_3 : plan :=
  PMmap (p_k9_16744443_33554425_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k9_16744443_33554425_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k9_16744443_33554425_cfgpos_5 : plan :=
  PMmap (p_k9_16744443_33554425_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k9_16744443_33554425_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k9_16744443_33554425_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k9_16744443_33554425_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k9_16744443_33554425 : plan :=
  PSplit (EVar 5) 0 (p_k9_16744443_33554425_cfg0_3) (p_k9_16744443_33554425_cfgpos_5).

Definition s_k9_16744443_33554425 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k9_16744443_33554425 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 9 16744443 33554425) p_k9_16744443_33554425 = COk s_k9_16744443_33554425.
Proof. native_cast_no_check (@eq_refl cres (COk s_k9_16744443_33554425)). Qed.

End UbTPBc_g03.
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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTargetAssemblyTop. Import UbTPBc_g03.
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
Lemma cso_k0_29_44 : class_shape_ok true s_k0_29_44 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_29_44 : TP0 29 44.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 29 44 p_k0_29_44 s_k0_29_44 chk_k0_29_44 cso_k0_29_44); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_573_668 : class_shape_ok true s_k0_573_668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_573_668 : TP0 573 668.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 573 668 p_k0_573_668 s_k0_573_668 chk_k0_573_668 cso_k0_573_668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_797_1004 : class_shape_ok true s_k0_797_1004 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_797_1004 : TP0 797 1004.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 797 1004 p_k0_797_1004 s_k0_797_1004 chk_k0_797_1004 cso_k0_797_1004); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_1005_1148 : class_shape_ok true s_k0_1005_1148 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1005_1148 : TP0 1005 1148.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1005 1148 p_k0_1005_1148 s_k0_1005_1148 chk_k0_1005_1148 cso_k0_1005_1148); try eassumption; lia.
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
Lemma cso_k0_4077_4668 : class_shape_ok true s_k0_4077_4668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4077_4668 : TP0 4077 4668.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 4077 4668 p_k0_4077_4668 s_k0_4077_4668 chk_k0_4077_4668 cso_k0_4077_4668); try eassumption; lia.
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
Lemma cso_k0_21821_24556 : class_shape_ok true s_k0_21821_24556 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_21821_24556 : TP0 21821 24556.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 21821 24556 p_k0_21821_24556 s_k0_21821_24556 chk_k0_21821_24556 cso_k0_21821_24556); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_24557_26188 : class_shape_ok true s_k0_24557_26188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_24557_26188 : TP0 24557 26188.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 24557 26188 p_k0_24557_26188 s_k0_24557_26188 chk_k0_24557_26188 cso_k0_24557_26188); try eassumption; lia.
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
Lemma cso_k0_32749_36844 : class_shape_ok true s_k0_32749_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_32749_36844 : TP0 32749 36844.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 32749 36844 p_k0_32749_36844 s_k0_32749_36844 chk_k0_32749_36844 cso_k0_32749_36844); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_37437_40940 : class_shape_ok true s_k0_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_37437_40940 : TP0 37437 40940.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 37437 40940 p_k0_37437_40940 s_k0_37437_40940 chk_k0_37437_40940 cso_k0_37437_40940); try eassumption; lia.
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
Lemma cso_k0_65517_65529 : class_shape_ok true s_k0_65517_65529 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_65517_65529 : TP0 65517 65529.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 65517 65529 p_k0_65517_65529 s_k0_65517_65529 chk_k0_65517_65529 cso_k0_65517_65529); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_36845_37436 : class_shape_ok1 true s_k1_36845_37436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_36845_37436 : TPK 1 36845 37436.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 36845 37436 p_k1_36845_37436 s_k1_36845_37436 chk_k1_36845_37436 cso_k1_36845_37436); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_37437_40940 : class_shape_ok1 true s_k1_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_37437_40940 : TPK 1 37437 40940.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 37437 40940 p_k1_37437_40940 s_k1_37437_40940 chk_k1_37437_40940 cso_k1_37437_40940); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_40941_43676 : class_shape_ok1 true s_k1_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_40941_43676 : TPK 1 40941 43676.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 40941 43676 p_k1_40941_43676 s_k1_40941_43676 chk_k1_40941_43676 cso_k1_40941_43676); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_43677_45036 : class_shape_ok1 true s_k1_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_43677_45036 : TPK 1 43677 45036.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 43677 45036 p_k1_43677_45036 s_k1_43677_45036 chk_k1_43677_45036 cso_k1_43677_45036); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_77805_81900 : class_shape_ok true s_k1_77805_81900 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_77805_81900 : TPK 1 77805 81900.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 77805 81900 p_k1_77805_81900 s_k1_77805_81900 chk_k1_77805_81900 cso_k1_77805_81900); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_104829_106476 : class_shape_ok true s_k1_104829_106476 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_104829_106476 : TPK 1 104829 106476.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 104829 106476 p_k1_104829_106476 s_k1_104829_106476 chk_k1_104829_106476 cso_k1_104829_106476); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k2_122861_126956 : class_shape_ok1 true s_k2_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_122861_126956 : TPK 2 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 122861 126956 p_k2_122861_126956 s_k2_122861_126956 chk_k2_122861_126956 cso_k2_122861_126956); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k5_1015803_2097145 : class_shape_ok true s_k5_1015803_2097145 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k5_1015803_2097145 : TPK 5 1015803 2097145.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 5 20000 400 1015803 2097145 p_k5_1015803_2097145 s_k5_1015803_2097145 chk_k5_1015803_2097145 cso_k5_1015803_2097145); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k6_2064379_4194297 : class_shape_ok true s_k6_2064379_4194297 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k6_2064379_4194297 : TPK 6 2064379 4194297.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 6 20000 400 2064379 4194297 p_k6_2064379_4194297 s_k6_2064379_4194297 chk_k6_2064379_4194297 cso_k6_2064379_4194297); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k9_16744443_33554425 : class_shape_ok true s_k9_16744443_33554425 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k9_16744443_33554425 : TPK 9 16744443 33554425.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 9 20000 400 16744443 33554425 p_k9_16744443_33554425 s_k9_16744443_33554425 chk_k9_16744443_33554425 cso_k9_16744443_33554425); try eassumption; unfold capk; cbn; lia.
Qed.

End LIB.
End WithFP.
