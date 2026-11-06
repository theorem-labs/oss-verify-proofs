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

Module UbTPBc_g04.
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

Lemma chk_k0_1149_1340 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 1149 1340) p_k0_1149_1340 = COk s_k0_1149_1340.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1149_1340)). Qed.

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

Lemma chk_k0_1341_1628 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 1341 1628) p_k0_1341_1628 = COk s_k0_1341_1628.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_1341_1628)). Qed.

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

Lemma chk_k0_1629_2028 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 1629 2028) p_k0_1629_2028 = COk s_k0_1629_2028.
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

Lemma chk_k0_2029_2332 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 2029 2332) p_k0_2029_2332 = COk s_k0_2029_2332.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_2029_2332)). Qed.

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

Lemma chk_k0_3261_4076 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 3261 4076) p_k0_3261_4076 = COk s_k0_3261_4076.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_3261_4076)). Qed.

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

Lemma chk_k0_4669_5436 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 4669 5436) p_k0_4669_5436 = COk s_k0_4669_5436.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_4669_5436)). Qed.

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

Lemma chk_k0_5437_6540 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 5437 6540) p_k0_5437_6540 = COk s_k0_5437_6540.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_5437_6540)). Qed.

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

Lemma chk_k0_6541_8172 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 6541 8172) p_k0_6541_8172 = COk s_k0_6541_8172.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_6541_8172)). Qed.

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

Lemma chk_k0_9341_10908 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 9341 10908) p_k0_9341_10908 = COk s_k0_9341_10908.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_9341_10908)). Qed.

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

Lemma chk_k0_16365_18700 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 16365 18700) p_k0_16365_18700 = COk s_k0_16365_18700.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_16365_18700)). Qed.

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

Lemma chk_k0_26189_28652 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 26189 28652) p_k0_26189_28652 = COk s_k0_26189_28652.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_26189_28652)). Qed.

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

Lemma chk_k0_36845_37436 : check Ubsan.M.loaded_segments ITAB INFOUB NX0 20000%nat 400%nat (cs_T 36845 37436) p_k0_36845_37436 = COk s_k0_36845_37436.
Proof. native_cast_no_check (@eq_refl cres (COk s_k0_36845_37436)). Qed.

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

Lemma chk_k1_53229_57324 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 53229 57324) p_k1_53229_57324 = COk s_k1_53229_57324.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_53229_57324)). Qed.

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

Lemma chk_k1_65517_69612 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 65517 69612) p_k1_65517_69612 = COk s_k1_65517_69612.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_65517_69612)). Qed.

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

Lemma chk_k1_74877_77804 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 74877 77804) p_k1_74877_77804 = COk s_k1_74877_77804.
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

Lemma chk_k1_81901_85996 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 81901 85996) p_k1_81901_85996 = COk s_k1_81901_85996.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_81901_85996)). Qed.

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

Lemma chk_k1_87357_90092 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 87357 90092) p_k1_87357_90092 = COk s_k1_87357_90092.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_87357_90092)). Qed.

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

Lemma chk_k1_90093_94188 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 90093 94188) p_k1_90093_94188 = COk s_k1_90093_94188.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_90093_94188)). Qed.

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

Lemma chk_k1_94189_98284 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 94189 98284) p_k1_94189_98284 = COk s_k1_94189_98284.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_94189_98284)). Qed.

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

Lemma chk_k1_102381_104828 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 102381 104828) p_k1_102381_104828 = COk s_k1_102381_104828.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_102381_104828)). Qed.

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

Lemma chk_k1_106477_110572 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 106477 110572) p_k1_106477_110572 = COk s_k1_106477_110572.
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

Lemma chk_k1_110573_114668 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 110573 114668) p_k1_110573_114668 = COk s_k1_110573_114668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_110573_114668)). Qed.

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

Lemma chk_k1_114669_118764 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 114669 118764) p_k1_114669_118764 = COk s_k1_114669_118764.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_114669_118764)). Qed.

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

Lemma chk_k1_118765_122860 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 118765 122860) p_k1_118765_122860 = COk s_k1_118765_122860.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_118765_122860)). Qed.

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

Lemma chk_k1_122861_126956 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 1 122861 126956) p_k1_122861_126956 = COk s_k1_122861_126956.
Proof. native_cast_no_check (@eq_refl cres (COk s_k1_122861_126956)). Qed.

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

Lemma chk_k2_110573_114668 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 2 110573 114668) p_k2_110573_114668 = COk s_k2_110573_114668.
Proof. native_cast_no_check (@eq_refl cres (COk s_k2_110573_114668)). Qed.

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

Lemma chk_k3_229371_524281 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 3 229371 524281) p_k3_229371_524281 = COk s_k3_229371_524281.
Proof. native_cast_no_check (@eq_refl cres (COk s_k3_229371_524281)). Qed.

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

Lemma chk_k4_491515_1048569 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 4 491515 1048569) p_k4_491515_1048569 = COk s_k4_491515_1048569.
Proof. native_cast_no_check (@eq_refl cres (COk s_k4_491515_1048569)). Qed.

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

Lemma chk_k7_4161531_8388601 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 7 4161531 8388601) p_k7_4161531_8388601 = COk s_k7_4161531_8388601.
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

Lemma chk_k10_33521659_67108857 : check Ubsan.M.loaded_segments ITAB INFOUB NX0k 20000%nat 400%nat (cs_Tk 10 33521659 67108857) p_k10_33521659_67108857 = COk s_k10_33521659_67108857.
Proof. native_cast_no_check (@eq_refl cres (COk s_k10_33521659_67108857)). Qed.

End UbTPBc_g04.
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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbTargetAssemblyTop. Import UbTPBc_g04.
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
Lemma cso_k0_1149_1340 : class_shape_ok true s_k0_1149_1340 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_1149_1340 : TP0 1149 1340.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 1149 1340 p_k0_1149_1340 s_k0_1149_1340 chk_k0_1149_1340 cso_k0_1149_1340); try eassumption; lia.
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
Lemma cso_k0_3261_4076 : class_shape_ok true s_k0_3261_4076 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_3261_4076 : TP0 3261 4076.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 3261 4076 p_k0_3261_4076 s_k0_3261_4076 chk_k0_3261_4076 cso_k0_3261_4076); try eassumption; lia.
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
Lemma cso_k0_5437_6540 : class_shape_ok true s_k0_5437_6540 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_5437_6540 : TP0 5437 6540.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 5437 6540 p_k0_5437_6540 s_k0_5437_6540 chk_k0_5437_6540 cso_k0_5437_6540); try eassumption; lia.
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
Lemma cso_k0_9341_10908 : class_shape_ok true s_k0_9341_10908 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_9341_10908 : TP0 9341 10908.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 9341 10908 p_k0_9341_10908 s_k0_9341_10908 chk_k0_9341_10908 cso_k0_9341_10908); try eassumption; lia.
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
Lemma cso_k0_26189_28652 : class_shape_ok true s_k0_26189_28652 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k0_26189_28652 : TP0 26189 28652.
Proof.
  unfold TP0. intros.
  eapply (target_class_sound LIB 20000 400 26189 28652 p_k0_26189_28652 s_k0_26189_28652 chk_k0_26189_28652 cso_k0_26189_28652); try eassumption; lia.
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
Lemma cso_k1_53229_57324 : class_shape_ok1 true s_k1_53229_57324 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_53229_57324 : TPK 1 53229 57324.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_low_k LIB 1 20000 400 53229 57324 p_k1_53229_57324 s_k1_53229_57324 chk_k1_53229_57324 cso_k1_53229_57324); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_87357_90092 : class_shape_ok true s_k1_87357_90092 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_87357_90092 : TPK 1 87357 90092.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 87357 90092 p_k1_87357_90092 s_k1_87357_90092 chk_k1_87357_90092 cso_k1_87357_90092); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_94189_98284 : class_shape_ok true s_k1_94189_98284 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_94189_98284 : TPK 1 94189 98284.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 94189 98284 p_k1_94189_98284 s_k1_94189_98284 chk_k1_94189_98284 cso_k1_94189_98284); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_114669_118764 : class_shape_ok true s_k1_114669_118764 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_114669_118764 : TPK 1 114669 118764.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 114669 118764 p_k1_114669_118764 s_k1_114669_118764 chk_k1_114669_118764 cso_k1_114669_118764); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k1_122861_126956 : class_shape_ok true s_k1_122861_126956 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k1_122861_126956 : TPK 1 122861 126956.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 1 20000 400 122861 126956 p_k1_122861_126956 s_k1_122861_126956 chk_k1_122861_126956 cso_k1_122861_126956); try eassumption; unfold capk; cbn; lia.
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
Lemma cso_k3_229371_524281 : class_shape_ok true s_k3_229371_524281 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem tp_k3_229371_524281 : TPK 3 229371 524281.
Proof.
  unfold TPK. intros.
  eapply (target_class_sound_k LIB 3 20000 400 229371 524281 p_k3_229371_524281 s_k3_229371_524281 chk_k3_229371_524281 cso_k3_229371_524281); try eassumption; unfold capk; cbn; lia.
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
