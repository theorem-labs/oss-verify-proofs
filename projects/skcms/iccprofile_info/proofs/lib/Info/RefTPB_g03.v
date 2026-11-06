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

Module RefTPBc_g03.
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
Definition p_k0_77_92_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_77_92_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_77_92_cnt1) (p_k0_77_92_cnt1)).
Definition p_k0_77_92_cfg0_3 : plan :=
  PMmap (p_k0_77_92_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_77_92_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_77_92_cfgpos_5 : plan :=
  PMmap (p_k0_77_92_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_77_92_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_77_92_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_77_92_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_77_92 : plan :=
  PSplit (EVar 5) 0 (p_k0_77_92_cfg0_3) (p_k0_77_92_cfgpos_5).

Definition s_k0_77_92 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_77_92 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 77 92) p_k0_77_92 = COk s_k0_77_92.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_77_92)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_109_124_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_109_124_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_109_124_cnt1) (p_k0_109_124_cnt1)).
Definition p_k0_109_124_cfg0_3 : plan :=
  PMmap (p_k0_109_124_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_109_124_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_109_124_cfgpos_5 : plan :=
  PMmap (p_k0_109_124_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_109_124_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_109_124_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_109_124_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_109_124 : plan :=
  PSplit (EVar 5) 0 (p_k0_109_124_cfg0_3) (p_k0_109_124_cfgpos_5).

Definition s_k0_109_124 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_109_124 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 109 124) p_k0_109_124 = COk s_k0_109_124.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_109_124)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_493_572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_493_572_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_493_572_cnt1) (p_k0_493_572_cnt1)).
Definition p_k0_493_572_cfg0_3 : plan :=
  PMmap (p_k0_493_572_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_493_572_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_493_572_cfgpos_5 : plan :=
  PMmap (p_k0_493_572_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_493_572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_493_572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_493_572_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_493_572 : plan :=
  PSplit (EVar 5) 0 (p_k0_493_572_cfg0_3) (p_k0_493_572_cfgpos_5).

Definition s_k0_493_572 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_493_572 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 493 572) p_k0_493_572 = COk s_k0_493_572.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_493_572)). Qed.

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

Lemma chk_k0_573_668 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 573 668) p_k0_573_668 = COk s_k0_573_668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_573_668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_669_796_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_669_796_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_669_796_cnt1) (p_k0_669_796_cnt1)).
Definition p_k0_669_796_cfg0_3 : plan :=
  PMmap (p_k0_669_796_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_669_796_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_669_796_cfgpos_5 : plan :=
  PMmap (p_k0_669_796_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_669_796_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_669_796_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_669_796_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_669_796 : plan :=
  PSplit (EVar 5) 0 (p_k0_669_796_cfg0_3) (p_k0_669_796_cfgpos_5).

Definition s_k0_669_796 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_669_796 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 669 796) p_k0_669_796 = COk s_k0_669_796.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_669_796)). Qed.

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

Lemma chk_k0_797_1004 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 797 1004) p_k0_797_1004 = COk s_k0_797_1004.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_797_1004)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1149_1340_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1149_1340_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1149_1340_cnt1) (p_k0_1149_1340_cnt1)).
Definition p_k0_1149_1340_cfg0_3 : plan :=
  PMmap (p_k0_1149_1340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1149_1340_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1149_1340_cfgpos_5 : plan :=
  PMmap (p_k0_1149_1340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_1149_1340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_1149_1340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_1149_1340_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1149_1340 : plan :=
  PSplit (EVar 5) 0 (p_k0_1149_1340_cfg0_3) (p_k0_1149_1340_cfgpos_5).

Definition s_k0_1149_1340 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1149_1340 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 1149 1340) p_k0_1149_1340 = COk s_k0_1149_1340.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1149_1340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_4669_5436_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_4669_5436_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_4669_5436_cnt1) (p_k0_4669_5436_cnt1)).
Definition p_k0_4669_5436_cfg0_3 : plan :=
  PMmap (p_k0_4669_5436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_4669_5436_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_4669_5436_cfgpos_5 : plan :=
  PMmap (p_k0_4669_5436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_4669_5436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_4669_5436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_4669_5436_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_4669_5436 : plan :=
  PSplit (EVar 5) 0 (p_k0_4669_5436_cfg0_3) (p_k0_4669_5436_cfgpos_5).

Definition s_k0_4669_5436 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_4669_5436 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 4669 5436) p_k0_4669_5436 = COk s_k0_4669_5436.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_4669_5436)). Qed.

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

Lemma chk_k0_10909_12268 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 10909 12268) p_k0_10909_12268 = COk s_k0_10909_12268.
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

Lemma chk_k0_12269_13084 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 12269 13084) p_k0_12269_13084 = COk s_k0_12269_13084.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_12269_13084)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_16365_18700_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_16365_18700_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_16365_18700_cnt1) (p_k0_16365_18700_cnt1)).
Definition p_k0_16365_18700_cfg0_3 : plan :=
  PMmap (p_k0_16365_18700_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_16365_18700_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_16365_18700_cfgpos_5 : plan :=
  PMmap (p_k0_16365_18700_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_16365_18700_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_16365_18700_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_16365_18700_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_16365_18700 : plan :=
  PSplit (EVar 5) 0 (p_k0_16365_18700_cfg0_3) (p_k0_16365_18700_cfgpos_5).

Definition s_k0_16365_18700 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_16365_18700 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 16365 18700) p_k0_16365_18700 = COk s_k0_16365_18700.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_16365_18700)). Qed.

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

Lemma chk_k0_21821_24556 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 21821 24556) p_k0_21821_24556 = COk s_k0_21821_24556.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_21821_24556)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_26189_28652_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_26189_28652_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_26189_28652_cnt1) (p_k0_26189_28652_cnt1)).
Definition p_k0_26189_28652_cfg0_3 : plan :=
  PMmap (p_k0_26189_28652_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_26189_28652_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_26189_28652_cfgpos_5 : plan :=
  PMmap (p_k0_26189_28652_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_26189_28652_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_26189_28652_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_26189_28652_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_26189_28652 : plan :=
  PSplit (EVar 5) 0 (p_k0_26189_28652_cfg0_3) (p_k0_26189_28652_cfgpos_5).

Definition s_k0_26189_28652 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_26189_28652 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 26189 28652) p_k0_26189_28652 = COk s_k0_26189_28652.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_26189_28652)). Qed.

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

Lemma chk_k0_32749_36844 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 32749 36844) p_k0_32749_36844 = COk s_k0_32749_36844.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_32749_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_40941_43676_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_40941_43676_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_40941_43676_cnt1) (p_k0_40941_43676_cnt1)).
Definition p_k0_40941_43676_cfg0_3 : plan :=
  PMmap (p_k0_40941_43676_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_40941_43676_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_40941_43676_cfgpos_5 : plan :=
  PMmap (p_k0_40941_43676_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_40941_43676_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_40941_43676_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_40941_43676_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_40941_43676 : plan :=
  PSplit (EVar 5) 0 (p_k0_40941_43676_cfg0_3) (p_k0_40941_43676_cfgpos_5).

Definition s_k0_40941_43676 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_40941_43676 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 40941 43676) p_k0_40941_43676 = COk s_k0_40941_43676.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_40941_43676)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_43677_45036_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_43677_45036_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_43677_45036_cnt1) (p_k0_43677_45036_cnt1)).
Definition p_k0_43677_45036_cfg0_3 : plan :=
  PMmap (p_k0_43677_45036_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_43677_45036_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_43677_45036_cfgpos_5 : plan :=
  PMmap (p_k0_43677_45036_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_43677_45036_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_43677_45036_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_43677_45036_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_43677_45036 : plan :=
  PSplit (EVar 5) 0 (p_k0_43677_45036_cfg0_3) (p_k0_43677_45036_cfgpos_5).

Definition s_k0_43677_45036 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_43677_45036 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 43677 45036) p_k0_43677_45036 = COk s_k0_43677_45036.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_43677_45036)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_53229_57324_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_53229_57324_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_53229_57324_cnt1) (p_k0_53229_57324_cnt1)).
Definition p_k0_53229_57324_cfg0_3 : plan :=
  PMmap (p_k0_53229_57324_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_53229_57324_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_53229_57324_cfgpos_5 : plan :=
  PMmap (p_k0_53229_57324_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_53229_57324_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_53229_57324_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_53229_57324_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_53229_57324 : plan :=
  PSplit (EVar 5) 0 (p_k0_53229_57324_cfg0_3) (p_k0_53229_57324_cfgpos_5).

Definition s_k0_53229_57324 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_53229_57324 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 53229 57324) p_k0_53229_57324 = COk s_k0_53229_57324.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_53229_57324)). Qed.

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

Lemma chk_k1_43677_45036 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 43677 45036) p_k1_43677_45036 = COk s_k1_43677_45036.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_43677_45036)). Qed.

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

Lemma chk_k1_73709_74876 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 73709 74876) p_k1_73709_74876 = COk s_k1_73709_74876.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_73709_74876)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_74877_77804_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_74877_77804_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_74877_77804_cnt1) (p_k1_74877_77804_cnt1)).
Definition p_k1_74877_77804_cfg0_3 : plan :=
  PMmap (p_k1_74877_77804_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_74877_77804_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_74877_77804_cfgpos_5 : plan :=
  PMmap (p_k1_74877_77804_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_74877_77804_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_74877_77804_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_74877_77804_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_74877_77804 : plan :=
  PSplit (EVar 5) 0 (p_k1_74877_77804_cfg0_3) (p_k1_74877_77804_cfgpos_5).

Definition s_k1_74877_77804 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_74877_77804 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 74877 77804) p_k1_74877_77804 = COk s_k1_74877_77804.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_74877_77804)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_81901_85996_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_81901_85996_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_81901_85996_cnt1) (p_k1_81901_85996_cnt1)).
Definition p_k1_81901_85996_cfg0_3 : plan :=
  PMmap (p_k1_81901_85996_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_81901_85996_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_81901_85996_cfgpos_5 : plan :=
  PMmap (p_k1_81901_85996_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_81901_85996_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_81901_85996_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_81901_85996_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_81901_85996 : plan :=
  PSplit (EVar 5) 0 (p_k1_81901_85996_cfg0_3) (p_k1_81901_85996_cfgpos_5).

Definition s_k1_81901_85996 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_81901_85996 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 81901 85996) p_k1_81901_85996 = COk s_k1_81901_85996.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_81901_85996)). Qed.

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

Lemma chk_k1_85997_87356 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 85997 87356) p_k1_85997_87356 = COk s_k1_85997_87356.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_85997_87356)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_90093_94188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_90093_94188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_90093_94188_cnt1) (p_k1_90093_94188_cnt1)).
Definition p_k1_90093_94188_cfg0_3 : plan :=
  PMmap (p_k1_90093_94188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_90093_94188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_90093_94188_cfgpos_5 : plan :=
  PMmap (p_k1_90093_94188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_90093_94188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_90093_94188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_90093_94188_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_90093_94188 : plan :=
  PSplit (EVar 5) 0 (p_k1_90093_94188_cfg0_3) (p_k1_90093_94188_cfgpos_5).

Definition s_k1_90093_94188 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_90093_94188 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 90093 94188) p_k1_90093_94188 = COk s_k1_90093_94188.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_90093_94188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_118765_122860_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_118765_122860_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_118765_122860_cnt1) (p_k1_118765_122860_cnt1)).
Definition p_k1_118765_122860_cfg0_3 : plan :=
  PMmap (p_k1_118765_122860_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_118765_122860_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_118765_122860_cfgpos_5 : plan :=
  PMmap (p_k1_118765_122860_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_118765_122860_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_118765_122860_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_118765_122860_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_118765_122860 : plan :=
  PSplit (EVar 5) 0 (p_k1_118765_122860_cfg0_3) (p_k1_118765_122860_cfgpos_5).

Definition s_k1_118765_122860 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_118765_122860 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 118765 122860) p_k1_118765_122860 = COk s_k1_118765_122860.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_118765_122860)). Qed.

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

Lemma chk_k1_126957_131051 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 126957 131051) p_k1_126957_131051 = COk s_k1_126957_131051.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_126957_131051)). Qed.

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

Lemma chk_k2_98299_102380 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 98299 102380) p_k2_98299_102380 = COk s_k2_98299_102380.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_98299_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k8_8355835_16777209_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k8_8355835_16777209_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k8_8355835_16777209_cnt1) (p_k8_8355835_16777209_cnt1)).
Definition p_k8_8355835_16777209_cfg0_3 : plan :=
  PMmap (p_k8_8355835_16777209_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k8_8355835_16777209_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k8_8355835_16777209_cfgpos_5 : plan :=
  PMmap (p_k8_8355835_16777209_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k8_8355835_16777209_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k8_8355835_16777209_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k8_8355835_16777209_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k8_8355835_16777209 : plan :=
  PSplit (EVar 5) 0 (p_k8_8355835_16777209_cfg0_3) (p_k8_8355835_16777209_cfgpos_5).

Definition s_k8_8355835_16777209 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k8_8355835_16777209 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 8 8355835 16777209) p_k8_8355835_16777209 = COk s_k8_8355835_16777209.
Proof. native_cast_no_check (@eq_refl cres (COk s_k8_8355835_16777209)). Qed.

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

Lemma chk_k9_16744443_33554425 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 9 16744443 33554425) p_k9_16744443_33554425 = COk s_k9_16744443_33554425.
Proof. native_cast_no_check (@eq_refl cres (COk s_k9_16744443_33554425)). Qed.

End RefTPBc_g03.
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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetAssemblyTop. Import RefTPBc_g03.
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
Lemma cso_k0_77_92 : class_shape_ok true s_k0_77_92 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_77_92 : TP0 77 92.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 77 92 p_k0_77_92 s_k0_77_92 chk_k0_77_92 cso_k0_77_92); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_109_124 : class_shape_ok true s_k0_109_124 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_109_124 : TP0 109 124.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 109 124 p_k0_109_124 s_k0_109_124 chk_k0_109_124 cso_k0_109_124); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_493_572 : class_shape_ok true s_k0_493_572 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_493_572 : TP0 493 572.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 493 572 p_k0_493_572 s_k0_493_572 chk_k0_493_572 cso_k0_493_572); try eassumption; lia.
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
Lemma cso_k0_669_796 : class_shape_ok true s_k0_669_796 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_669_796 : TP0 669 796.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 669 796 p_k0_669_796 s_k0_669_796 chk_k0_669_796 cso_k0_669_796); try eassumption; lia.
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
Lemma cso_k0_1149_1340 : class_shape_ok true s_k0_1149_1340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1149_1340 : TP0 1149 1340.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1149 1340 p_k0_1149_1340 s_k0_1149_1340 chk_k0_1149_1340 cso_k0_1149_1340); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_4669_5436 : class_shape_ok true s_k0_4669_5436 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4669_5436 : TP0 4669 5436.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 4669 5436 p_k0_4669_5436 s_k0_4669_5436 chk_k0_4669_5436 cso_k0_4669_5436); try eassumption; lia.
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
Lemma cso_k0_16365_18700 : class_shape_ok true s_k0_16365_18700 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_16365_18700 : TP0 16365 18700.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 16365 18700 p_k0_16365_18700 s_k0_16365_18700 chk_k0_16365_18700 cso_k0_16365_18700); try eassumption; lia.
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
Lemma cso_k0_26189_28652 : class_shape_ok true s_k0_26189_28652 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_26189_28652 : TP0 26189 28652.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 26189 28652 p_k0_26189_28652 s_k0_26189_28652 chk_k0_26189_28652 cso_k0_26189_28652); try eassumption; lia.
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
Lemma cso_k0_40941_43676 : class_shape_ok true s_k0_40941_43676 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_40941_43676 : TP0 40941 43676.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 40941 43676 p_k0_40941_43676 s_k0_40941_43676 chk_k0_40941_43676 cso_k0_40941_43676); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_43677_45036 : class_shape_ok true s_k0_43677_45036 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_43677_45036 : TP0 43677 45036.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 43677 45036 p_k0_43677_45036 s_k0_43677_45036 chk_k0_43677_45036 cso_k0_43677_45036); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_53229_57324 : class_shape_ok true s_k0_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_53229_57324 : TP0 53229 57324.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 53229 57324 p_k0_53229_57324 s_k0_53229_57324 chk_k0_53229_57324 cso_k0_53229_57324); try eassumption; lia.
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
Lemma cso_k1_73709_74876 : class_shape_ok true s_k1_73709_74876 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_73709_74876 : TPK 1 73709 74876.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 73709 74876 p_k1_73709_74876 s_k1_73709_74876 chk_k1_73709_74876 cso_k1_73709_74876); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_74877_77804 : class_shape_ok true s_k1_74877_77804 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_74877_77804 : TPK 1 74877 77804.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 74877 77804 p_k1_74877_77804 s_k1_74877_77804 chk_k1_74877_77804 cso_k1_74877_77804); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_81901_85996 : class_shape_ok true s_k1_81901_85996 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_81901_85996 : TPK 1 81901 85996.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 81901 85996 p_k1_81901_85996 s_k1_81901_85996 chk_k1_81901_85996 cso_k1_81901_85996); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_90093_94188 : class_shape_ok true s_k1_90093_94188 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_90093_94188 : TPK 1 90093 94188.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 90093 94188 p_k1_90093_94188 s_k1_90093_94188 chk_k1_90093_94188 cso_k1_90093_94188); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_118765_122860 : class_shape_ok true s_k1_118765_122860 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_118765_122860 : TPK 1 118765 122860.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 118765 122860 p_k1_118765_122860 s_k1_118765_122860 chk_k1_118765_122860 cso_k1_118765_122860); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k2_98299_102380 : class_shape_ok1 true s_k2_98299_102380 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_98299_102380 : TPK 2 98299 102380.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 98299 102380 p_k2_98299_102380 s_k2_98299_102380 chk_k2_98299_102380 cso_k2_98299_102380); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k8_8355835_16777209 : class_shape_ok true s_k8_8355835_16777209 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k8_8355835_16777209 : TPK 8 8355835 16777209.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 8 20000 400 8355835 16777209 p_k8_8355835_16777209 s_k8_8355835_16777209 chk_k8_8355835_16777209 cso_k8_8355835_16777209); try eassumption; unfold capk; cbn; lia.
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
