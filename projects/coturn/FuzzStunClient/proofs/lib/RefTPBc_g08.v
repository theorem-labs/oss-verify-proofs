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
Definition p_k1_118765_122860_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_118765_122860_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_118765_122860_cnt1) (p_k1_118765_122860_cnt1)).
Definition p_k1_118765_122860_cfg0_3 : plan :=
  PMmap (p_k1_118765_122860_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_118765_122860_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_118765_122860_cfgpos_5 : plan :=
  PMmap (p_k1_118765_122860_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_118765_122860_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_118765_122860_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_118765_122860_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_118765_122860 : plan :=
  PSplit (EVar 5) 0 (p_k1_118765_122860_cfg0_3) (p_k1_118765_122860_cfgpos_5).

Definition s_k1_118765_122860 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_118765_122860 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 118765 122860) p_k1_118765_122860 = COk s_k1_118765_122860.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_122861_126956_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_122861_126956_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_122861_126956_cnt1) (p_k1_122861_126956_cnt1)).
Definition p_k1_122861_126956_cfg0_3 : plan :=
  PMmap (p_k1_122861_126956_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_122861_126956_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_122861_126956_cfgpos_5 : plan :=
  PMmap (p_k1_122861_126956_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_122861_126956_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_122861_126956_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_122861_126956_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_122861_126956 : plan :=
  PSplit (EVar 5) 0 (p_k1_122861_126956_cfg0_3) (p_k1_122861_126956_cfgpos_5).

Definition s_k1_122861_126956 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_122861_126956 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 122861 126956) p_k1_122861_126956 = COk s_k1_122861_126956.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_122861_126956)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_126957_131051_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_126957_131051_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_126957_131051_cnt1) (p_k1_126957_131051_cnt1)).
Definition p_k1_126957_131051_cfg0_3 : plan :=
  PMmap (p_k1_126957_131051_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_126957_131051_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_126957_131051_cfgpos_5 : plan :=
  PMmap (p_k1_126957_131051_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_126957_131051_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_126957_131051_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_126957_131051_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_126957_131051 : plan :=
  PSplit (EVar 5) 0 (p_k1_126957_131051_cfg0_3) (p_k1_126957_131051_cfgpos_5).

Definition s_k1_126957_131051 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_126957_131051 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 126957 131051) p_k1_126957_131051 = COk s_k1_126957_131051.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_126957_131051)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_131052_131065_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_131052_131065_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_131052_131065_cnt1) (p_k1_131052_131065_cnt1)).
Definition p_k1_131052_131065_cfg0_3 : plan :=
  PMmap (p_k1_131052_131065_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_131052_131065_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_131052_131065_cfgpos_5 : plan :=
  PMmap (p_k1_131052_131065_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_131052_131065_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_131052_131065_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_131052_131065_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_131052_131065 : plan :=
  PSplit (EVar 5) 0 (p_k1_131052_131065_cfg0_3) (p_k1_131052_131065_cfgpos_5).

Definition s_k1_131052_131065 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_131052_131065 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 1 131052 131065) p_k1_131052_131065 = COk s_k1_131052_131065.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_131052_131065)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_98299_102380_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_98299_102380_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_98299_102380_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_98299_102380_cnt1) (p_k2_98299_102380_cnt1)).
Definition p_k2_98299_102380_cfgpos_4 : plan :=
  PMmap (p_k2_98299_102380_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_98299_102380_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_98299_102380_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_98299_102380_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_98299_102380 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_98299_102380_cfgpos_4).

Definition s_k2_98299_102380 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_98299_102380 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 98299 102380) p_k2_98299_102380 = COk s_k2_98299_102380.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_98299_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_102381_104828_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_102381_104828_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_102381_104828_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_102381_104828_cnt1) (p_k2_102381_104828_cnt1)).
Definition p_k2_102381_104828_cfgpos_4 : plan :=
  PMmap (p_k2_102381_104828_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_102381_104828_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_102381_104828_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_102381_104828_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_102381_104828 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_102381_104828_cfgpos_4).

Definition s_k2_102381_104828 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_102381_104828 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 102381 104828) p_k2_102381_104828 = COk s_k2_102381_104828.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_104829_106476_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_104829_106476_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_104829_106476_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_104829_106476_cnt1) (p_k2_104829_106476_cnt1)).
Definition p_k2_104829_106476_cfgpos_4 : plan :=
  PMmap (p_k2_104829_106476_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_104829_106476_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_104829_106476_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_104829_106476_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_104829_106476 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_104829_106476_cfgpos_4).

Definition s_k2_104829_106476 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_104829_106476 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 104829 106476) p_k2_104829_106476 = COk s_k2_104829_106476.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_104829_106476)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_106477_110572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_106477_110572_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_106477_110572_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_106477_110572_cnt1) (p_k2_106477_110572_cnt1)).
Definition p_k2_106477_110572_cfgpos_4 : plan :=
  PMmap (p_k2_106477_110572_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_106477_110572_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_106477_110572_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_106477_110572_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_106477_110572 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_106477_110572_cfgpos_4).

Definition s_k2_106477_110572 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_106477_110572 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 106477 110572) p_k2_106477_110572 = COk s_k2_106477_110572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_110573_114668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_110573_114668_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_110573_114668_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_110573_114668_cnt1) (p_k2_110573_114668_cnt1)).
Definition p_k2_110573_114668_cfgpos_4 : plan :=
  PMmap (p_k2_110573_114668_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_110573_114668_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_110573_114668_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_110573_114668_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_110573_114668 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_110573_114668_cfgpos_4).

Definition s_k2_110573_114668 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_110573_114668 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 110573 114668) p_k2_110573_114668 = COk s_k2_110573_114668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_110573_114668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_114669_118764_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_114669_118764_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_114669_118764_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_114669_118764_cnt1) (p_k2_114669_118764_cnt1)).
Definition p_k2_114669_118764_cfgpos_4 : plan :=
  PMmap (p_k2_114669_118764_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_114669_118764_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_114669_118764_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_114669_118764_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_114669_118764 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_114669_118764_cfgpos_4).

Definition s_k2_114669_118764 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_114669_118764 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 114669 118764) p_k2_114669_118764 = COk s_k2_114669_118764.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_114669_118764)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_118765_122860_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_118765_122860_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_118765_122860_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_118765_122860_cnt1) (p_k2_118765_122860_cnt1)).
Definition p_k2_118765_122860_cfgpos_4 : plan :=
  PMmap (p_k2_118765_122860_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_118765_122860_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_118765_122860_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_118765_122860_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_118765_122860 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_118765_122860_cfgpos_4).

Definition s_k2_118765_122860 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_118765_122860 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 118765 122860) p_k2_118765_122860 = COk s_k2_118765_122860.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_118765_122860)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_122861_126956_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_122861_126956_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_122861_126956_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_122861_126956_cnt1) (p_k2_122861_126956_cnt1)).
Definition p_k2_122861_126956_cfgpos_4 : plan :=
  PMmap (p_k2_122861_126956_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_122861_126956_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_122861_126956_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_122861_126956_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_122861_126956 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_122861_126956_cfgpos_4).

Definition s_k2_122861_126956 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_122861_126956 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 122861 126956) p_k2_122861_126956 = COk s_k2_122861_126956.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_122861_126956)). Qed.

