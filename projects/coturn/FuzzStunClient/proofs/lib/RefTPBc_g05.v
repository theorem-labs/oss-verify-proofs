(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymPlan RefATB RefTargetEntry_defs RefTargetEntryK_defs TargetKDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_40941_43676_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_40941_43676_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_40941_43676_cnt1) (p_k0_40941_43676_cnt1)).
Definition p_k0_40941_43676_cfg0_3 : plan :=
  PMmap (p_k0_40941_43676_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_40941_43676_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_40941_43676_cfgpos_5 : plan :=
  PMmap (p_k0_40941_43676_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_40941_43676_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_40941_43676_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_40941_43676_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_40941_43676 : plan :=
  PSplit (EVar 5) 0 (p_k0_40941_43676_cfg0_3) (p_k0_40941_43676_cfgpos_5).

Definition s_k0_40941_43676 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_40941_43676 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 40941 43676) p_k0_40941_43676 = COk s_k0_40941_43676.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_40941_43676)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_43677_45036_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_43677_45036_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_43677_45036_cnt1) (p_k0_43677_45036_cnt1)).
Definition p_k0_43677_45036_cfg0_3 : plan :=
  PMmap (p_k0_43677_45036_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_43677_45036_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_43677_45036_cfgpos_5 : plan :=
  PMmap (p_k0_43677_45036_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_43677_45036_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_43677_45036_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_43677_45036_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_43677_45036 : plan :=
  PSplit (EVar 5) 0 (p_k0_43677_45036_cfg0_3) (p_k0_43677_45036_cfgpos_5).

Definition s_k0_43677_45036 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_43677_45036 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 43677 45036) p_k0_43677_45036 = COk s_k0_43677_45036.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_43677_45036)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45037_49132_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_45037_49132_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_45037_49132_cnt1) (p_k0_45037_49132_cnt1)).
Definition p_k0_45037_49132_cfg0_3 : plan :=
  PMmap (p_k0_45037_49132_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_45037_49132_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_45037_49132_cfgpos_5 : plan :=
  PMmap (p_k0_45037_49132_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_45037_49132_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_45037_49132_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_45037_49132_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_45037_49132 : plan :=
  PSplit (EVar 5) 0 (p_k0_45037_49132_cfg0_3) (p_k0_45037_49132_cfgpos_5).

Definition s_k0_45037_49132 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_45037_49132 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 45037 49132) p_k0_45037_49132 = COk s_k0_45037_49132.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_45037_49132)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_49133_52412_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_49133_52412_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_49133_52412_cnt1) (p_k0_49133_52412_cnt1)).
Definition p_k0_49133_52412_cfg0_3 : plan :=
  PMmap (p_k0_49133_52412_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_49133_52412_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_49133_52412_cfgpos_5 : plan :=
  PMmap (p_k0_49133_52412_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_49133_52412_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_49133_52412_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_49133_52412_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_49133_52412 : plan :=
  PSplit (EVar 5) 0 (p_k0_49133_52412_cfg0_3) (p_k0_49133_52412_cfgpos_5).

Definition s_k0_49133_52412 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_49133_52412 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 49133 52412) p_k0_49133_52412 = COk s_k0_49133_52412.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_49133_52412)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_52413_53228_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_52413_53228_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_52413_53228_cnt1) (p_k0_52413_53228_cnt1)).
Definition p_k0_52413_53228_cfg0_3 : plan :=
  PMmap (p_k0_52413_53228_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_52413_53228_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_52413_53228_cfgpos_5 : plan :=
  PMmap (p_k0_52413_53228_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_52413_53228_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_52413_53228_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_52413_53228_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_52413_53228 : plan :=
  PSplit (EVar 5) 0 (p_k0_52413_53228_cfg0_3) (p_k0_52413_53228_cfgpos_5).

Definition s_k0_52413_53228 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_52413_53228 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 52413 53228) p_k0_52413_53228 = COk s_k0_52413_53228.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_52413_53228)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_53229_57324_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_53229_57324_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_53229_57324_cnt1) (p_k0_53229_57324_cnt1)).
Definition p_k0_53229_57324_cfg0_3 : plan :=
  PMmap (p_k0_53229_57324_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_53229_57324_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_53229_57324_cfgpos_5 : plan :=
  PMmap (p_k0_53229_57324_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_53229_57324_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_53229_57324_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_53229_57324_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_53229_57324 : plan :=
  PSplit (EVar 5) 0 (p_k0_53229_57324_cfg0_3) (p_k0_53229_57324_cfgpos_5).

Definition s_k0_53229_57324 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_53229_57324 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 53229 57324) p_k0_53229_57324 = COk s_k0_53229_57324.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_53229_57324)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_57325_61420_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_57325_61420_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_57325_61420_cnt1) (p_k0_57325_61420_cnt1)).
Definition p_k0_57325_61420_cfg0_3 : plan :=
  PMmap (p_k0_57325_61420_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_57325_61420_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_57325_61420_cfgpos_5 : plan :=
  PMmap (p_k0_57325_61420_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_57325_61420_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_57325_61420_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_57325_61420_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_57325_61420 : plan :=
  PSplit (EVar 5) 0 (p_k0_57325_61420_cfg0_3) (p_k0_57325_61420_cfgpos_5).

Definition s_k0_57325_61420 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_57325_61420 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 57325 61420) p_k0_57325_61420 = COk s_k0_57325_61420.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_57325_61420)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61421_65516_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_61421_65516_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_61421_65516_cnt1) (p_k0_61421_65516_cnt1)).
Definition p_k0_61421_65516_cfg0_3 : plan :=
  PMmap (p_k0_61421_65516_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_61421_65516_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_61421_65516_cfgpos_5 : plan :=
  PMmap (p_k0_61421_65516_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_61421_65516_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_61421_65516_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_61421_65516_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_61421_65516 : plan :=
  PSplit (EVar 5) 0 (p_k0_61421_65516_cfg0_3) (p_k0_61421_65516_cfgpos_5).

Definition s_k0_61421_65516 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_61421_65516 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 61421 65516) p_k0_61421_65516 = COk s_k0_61421_65516.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_61421_65516)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_65517_65529_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_65517_65529_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_65517_65529_cnt1) (p_k0_65517_65529_cnt1)).
Definition p_k0_65517_65529_cfg0_3 : plan :=
  PMmap (p_k0_65517_65529_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_65517_65529_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_65517_65529_cfgpos_5 : plan :=
  PMmap (p_k0_65517_65529_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_65517_65529_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_65517_65529_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_65517_65529_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_65517_65529 : plan :=
  PSplit (EVar 5) 0 (p_k0_65517_65529_cfg0_3) (p_k0_65517_65529_cfgpos_5).

Definition s_k0_65517_65529 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_65517_65529 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 65517 65529) p_k0_65517_65529 = COk s_k0_65517_65529.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_65517_65529)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_32763_36844_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_32763_36844_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_32763_36844_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_32763_36844_cnt1) (p_k1_32763_36844_cnt1)).
Definition p_k1_32763_36844_cfgpos_4 : plan :=
  PMmap (p_k1_32763_36844_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_32763_36844_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_32763_36844_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_32763_36844_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_32763_36844 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_32763_36844_cfgpos_4).

Definition s_k1_32763_36844 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_32763_36844 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 32763 36844) p_k1_32763_36844 = COk s_k1_32763_36844.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_32763_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_36845_37436_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_36845_37436_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_36845_37436_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_36845_37436_cnt1) (p_k1_36845_37436_cnt1)).
Definition p_k1_36845_37436_cfgpos_4 : plan :=
  PMmap (p_k1_36845_37436_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_36845_37436_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_36845_37436_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_36845_37436_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_36845_37436 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_36845_37436_cfgpos_4).

Definition s_k1_36845_37436 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_36845_37436 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 36845 37436) p_k1_36845_37436 = COk s_k1_36845_37436.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_37437_40940_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_37437_40940_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_37437_40940_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_37437_40940_cnt1) (p_k1_37437_40940_cnt1)).
Definition p_k1_37437_40940_cfgpos_4 : plan :=
  PMmap (p_k1_37437_40940_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_37437_40940_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_37437_40940_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_37437_40940_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_37437_40940 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k1_37437_40940_cfgpos_4).

Definition s_k1_37437_40940 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_37437_40940 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 37437 40940) p_k1_37437_40940 = COk s_k1_37437_40940.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_37437_40940)). Qed.

