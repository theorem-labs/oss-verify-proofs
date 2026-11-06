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

Module RefTPBc_g01.
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

Lemma chk_k0_0_0 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 0 0) p_k0_0_0 = COk s_k0_0_0.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_0_0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1629_2028_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1629_2028_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1629_2028_cnt1) (p_k0_1629_2028_cnt1)).
Definition p_k0_1629_2028_cfg0_3 : plan :=
  PMmap (p_k0_1629_2028_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1629_2028_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1629_2028_cfgpos_5 : plan :=
  PMmap (p_k0_1629_2028_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_1629_2028_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_1629_2028_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_1629_2028_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1629_2028 : plan :=
  PSplit (EVar 5) 0 (p_k0_1629_2028_cfg0_3) (p_k0_1629_2028_cfgpos_5).

Definition s_k0_1629_2028 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1629_2028 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 1629 2028) p_k0_1629_2028 = COk s_k0_1629_2028.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1629_2028)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_2029_2332_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_2029_2332_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_2029_2332_cnt1) (p_k0_2029_2332_cnt1)).
Definition p_k0_2029_2332_cfg0_3 : plan :=
  PMmap (p_k0_2029_2332_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_2029_2332_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_2029_2332_cfgpos_5 : plan :=
  PMmap (p_k0_2029_2332_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_2029_2332_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_2029_2332_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_2029_2332_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_2029_2332 : plan :=
  PSplit (EVar 5) 0 (p_k0_2029_2332_cfg0_3) (p_k0_2029_2332_cfgpos_5).

Definition s_k0_2029_2332 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_2029_2332 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 2029 2332) p_k0_2029_2332 = COk s_k0_2029_2332.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2029_2332)). Qed.

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

Lemma chk_k0_2717_3260 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 2717 3260) p_k0_2717_3260 = COk s_k0_2717_3260.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2717_3260)). Qed.

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

Lemma chk_k0_4077_4668 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 4077 4668) p_k0_4077_4668 = COk s_k0_4077_4668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_4077_4668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_5437_6540_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_5437_6540_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_5437_6540_cnt1) (p_k0_5437_6540_cnt1)).
Definition p_k0_5437_6540_cfg0_3 : plan :=
  PMmap (p_k0_5437_6540_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_5437_6540_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_5437_6540_cfgpos_5 : plan :=
  PMmap (p_k0_5437_6540_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k0_5437_6540_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k0_5437_6540_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k0_5437_6540_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_5437_6540 : plan :=
  PSplit (EVar 5) 0 (p_k0_5437_6540_cfg0_3) (p_k0_5437_6540_cfgpos_5).

Definition s_k0_5437_6540 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_5437_6540 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 5437 6540) p_k0_5437_6540 = COk s_k0_5437_6540.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_5437_6540)). Qed.

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

Lemma chk_k0_24557_26188 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 24557 26188) p_k0_24557_26188 = COk s_k0_24557_26188.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_24557_26188)). Qed.

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

Lemma chk_k0_37437_40940 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 37437 40940) p_k0_37437_40940 = COk s_k0_37437_40940.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_37437_40940)). Qed.

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

Lemma chk_k0_65517_65529 : check Plain.M.loaded_segments ITAB SRC1 NX0 20000%nat 400%nat (cs_T 65517 65529) p_k0_65517_65529 = COk s_k0_65517_65529.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_65517_65529)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_32763_36844_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_32763_36844_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_32763_36844_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_32763_36844_cnt1) (p_k1_32763_36844_cnt1)).
Definition p_k1_32763_36844_cfgpos_4 : plan :=
  PMmap (p_k1_32763_36844_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_32763_36844_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_32763_36844_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_32763_36844_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_32763_36844 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_32763_36844_cfgpos_4).

Definition s_k1_32763_36844 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_32763_36844 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 32763 36844) p_k1_32763_36844 = COk s_k1_32763_36844.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_32763_36844)). Qed.

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

Lemma chk_k1_36845_37436 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 36845 37436) p_k1_36845_37436 = COk s_k1_36845_37436.
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

Lemma chk_k1_37437_40940 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 37437 40940) p_k1_37437_40940 = COk s_k1_37437_40940.
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

Lemma chk_k1_40941_43676 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 40941 43676) p_k1_40941_43676 = COk s_k1_40941_43676.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_40941_43676)). Qed.

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

Lemma chk_k1_61421_65516 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 61421 65516) p_k1_61421_65516 = COk s_k1_61421_65516.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_94189_98284_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_94189_98284_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_94189_98284_cnt1) (p_k1_94189_98284_cnt1)).
Definition p_k1_94189_98284_cfg0_3 : plan :=
  PMmap (p_k1_94189_98284_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_94189_98284_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_94189_98284_cfgpos_5 : plan :=
  PMmap (p_k1_94189_98284_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k1_94189_98284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k1_94189_98284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k1_94189_98284_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_94189_98284 : plan :=
  PSplit (EVar 5) 0 (p_k1_94189_98284_cfg0_3) (p_k1_94189_98284_cfgpos_5).

Definition s_k1_94189_98284 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_94189_98284 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 1 94189 98284) p_k1_94189_98284 = COk s_k1_94189_98284.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_94189_98284)). Qed.

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

Lemma chk_k2_102381_104828 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 102381 104828) p_k2_102381_104828 = COk s_k2_102381_104828.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_110573_114668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_110573_114668_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_110573_114668_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_110573_114668_cnt1) (p_k2_110573_114668_cnt1)).
Definition p_k2_110573_114668_cfgpos_4 : plan :=
  PMmap (p_k2_110573_114668_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k2_110573_114668_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k2_110573_114668_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k2_110573_114668_exit3_2) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_110573_114668 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_110573_114668_cfgpos_4).

Definition s_k2_110573_114668 : shape :=
  (SCase (EVar 5) 0 SNil ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_110573_114668 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 110573 114668) p_k2_110573_114668 = COk s_k2_110573_114668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_110573_114668)). Qed.

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

Lemma chk_k2_114669_118764 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 114669 118764) p_k2_114669_118764 = COk s_k2_114669_118764.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_114669_118764)). Qed.

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

Lemma chk_k2_122861_126956 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 122861 126956) p_k2_122861_126956 = COk s_k2_122861_126956.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_122861_126956)). Qed.

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

Lemma chk_k2_126957_131051 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 2 126957 131051) p_k2_126957_131051 = COk s_k2_126957_131051.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_126957_131051)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k4_491515_1048569_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k4_491515_1048569_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k4_491515_1048569_cnt1) (p_k4_491515_1048569_cnt1)).
Definition p_k4_491515_1048569_cfg0_3 : plan :=
  PMmap (p_k4_491515_1048569_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k4_491515_1048569_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k4_491515_1048569_cfgpos_5 : plan :=
  PMmap (p_k4_491515_1048569_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumFuzz [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit ((XC)) 0 (p_k4_491515_1048569_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 1 (p_k4_491515_1048569_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PSplit ((XC)) 2 (p_k4_491515_1048569_exit3_4) (PCall SumFuzz [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k4_491515_1048569 : plan :=
  PSplit (EVar 5) 0 (p_k4_491515_1048569_cfg0_3) (p_k4_491515_1048569_cfgpos_5).

Definition s_k4_491515_1048569 : shape :=
  (SCase (EVar 5) 0 ((SEmit 1 [48; 10] (SExit 0))) ((SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k4_491515_1048569 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 4 491515 1048569) p_k4_491515_1048569 = COk s_k4_491515_1048569.
Proof. native_cast_no_check (@eq_refl cres (COk s_k4_491515_1048569)). Qed.

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

Lemma chk_k5_1015803_2097145 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 5 1015803 2097145) p_k5_1015803_2097145 = COk s_k5_1015803_2097145.
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

Lemma chk_k6_2064379_4194297 : check Plain.M.loaded_segments ITAB SRC1 NX0k 20000%nat 400%nat (cs_Tk 6 2064379 4194297) p_k6_2064379_4194297 = COk s_k6_2064379_4194297.
Proof. native_cast_no_check (@eq_refl cres (COk s_k6_2064379_4194297)). Qed.

End RefTPBc_g01.
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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefTargetAssemblyTop. Import RefTPBc_g01.
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
Lemma cso_k0_1629_2028 : class_shape_ok true s_k0_1629_2028 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1629_2028 : TP0 1629 2028.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1629 2028 p_k0_1629_2028 s_k0_1629_2028 chk_k0_1629_2028 cso_k0_1629_2028); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_2029_2332 : class_shape_ok true s_k0_2029_2332 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_2029_2332 : TP0 2029 2332.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 2029 2332 p_k0_2029_2332 s_k0_2029_2332 chk_k0_2029_2332 cso_k0_2029_2332); try eassumption; lia.
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
Lemma cso_k0_4077_4668 : class_shape_ok true s_k0_4077_4668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_4077_4668 : TP0 4077 4668.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 4077 4668 p_k0_4077_4668 s_k0_4077_4668 chk_k0_4077_4668 cso_k0_4077_4668); try eassumption; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k0_5437_6540 : class_shape_ok true s_k0_5437_6540 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_5437_6540 : TP0 5437 6540.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 5437 6540 p_k0_5437_6540 s_k0_5437_6540 chk_k0_5437_6540 cso_k0_5437_6540); try eassumption; lia.
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
Lemma cso_k0_37437_40940 : class_shape_ok true s_k0_37437_40940 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_37437_40940 : TP0 37437 40940.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 37437 40940 p_k0_37437_40940 s_k0_37437_40940 chk_k0_37437_40940 cso_k0_37437_40940); try eassumption; lia.
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
Lemma cso_k1_32763_36844 : class_shape_ok1 true s_k1_32763_36844 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_32763_36844 : TPK 1 32763 36844.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 32763 36844 p_k1_32763_36844 s_k1_32763_36844 chk_k1_32763_36844 cso_k1_32763_36844); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_61421_65516 : class_shape_ok1 true s_k1_61421_65516 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_61421_65516 : TPK 1 61421 65516.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 61421 65516 p_k1_61421_65516 s_k1_61421_65516 chk_k1_61421_65516 cso_k1_61421_65516); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k1_94189_98284 : class_shape_ok true s_k1_94189_98284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_94189_98284 : TPK 1 94189 98284.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 94189 98284 p_k1_94189_98284 s_k1_94189_98284 chk_k1_94189_98284 cso_k1_94189_98284); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k2_110573_114668 : class_shape_ok1 true s_k2_110573_114668 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_110573_114668 : TPK 2 110573 114668.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 110573 114668 p_k2_110573_114668 s_k2_110573_114668 chk_k2_110573_114668 cso_k2_110573_114668); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k2_122861_126956 : class_shape_ok1 true s_k2_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_122861_126956 : TPK 2 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 122861 126956 p_k2_122861_126956 s_k2_122861_126956 chk_k2_122861_126956 cso_k2_122861_126956); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k2_126957_131051 : class_shape_ok1 true s_k2_126957_131051 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k2_126957_131051 : TPK 2 126957 131051.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 2 20000 400 126957 131051 p_k2_126957_131051 s_k2_126957_131051 chk_k2_126957_131051 cso_k2_126957_131051); try eassumption; unfold capk; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma cso_k4_491515_1048569 : class_shape_ok true s_k4_491515_1048569 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k4_491515_1048569 : TPK 4 491515 1048569.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 4 20000 400 491515 1048569 p_k4_491515_1048569 s_k4_491515_1048569 chk_k4_491515_1048569 cso_k4_491515_1048569); try eassumption; unfold capk; cbn; lia.
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

End LIB.
End WithFP.
