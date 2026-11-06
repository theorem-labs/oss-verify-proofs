(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec3 SymPlan UbATB UbTargetEntry_defs UbTargetEntryK_defs TargetKDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2. Import SP.
Open Scope Z_scope.
(* [comment removed for export] *)
Definition XC : expr := EAlu ALU_AND (EBlob false 0 2 1) (ELit 3).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_77805_81900_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_77805_81900_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_77805_81900_cnt1) (p_k1_77805_81900_cnt1)).
Definition p_k1_77805_81900_cfg0_3 : plan :=
  PMmap (p_k1_77805_81900_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_77805_81900_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_77805_81900_cfgpos_5 : plan :=
  PMmap (p_k1_77805_81900_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_77805_81900_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_77805_81900_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_77805_81900_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_77805_81900 : plan :=
  PSplit (EVar 5) 0 (p_k1_77805_81900_cfg0_3) (p_k1_77805_81900_cfgpos_5).

Definition s_k1_77805_81900 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_77805_81900 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 77805 81900) p_k1_77805_81900 = COk s_k1_77805_81900.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_77805_81900)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_81901_85996_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_81901_85996_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_81901_85996_cnt1) (p_k1_81901_85996_cnt1)).
Definition p_k1_81901_85996_cfg0_3 : plan :=
  PMmap (p_k1_81901_85996_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_81901_85996_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_81901_85996_cfgpos_5 : plan :=
  PMmap (p_k1_81901_85996_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_81901_85996_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_81901_85996_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_81901_85996_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_81901_85996 : plan :=
  PSplit (EVar 5) 0 (p_k1_81901_85996_cfg0_3) (p_k1_81901_85996_cfgpos_5).

Definition s_k1_81901_85996 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_81901_85996 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 81901 85996) p_k1_81901_85996 = COk s_k1_81901_85996.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_81901_85996)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_85997_87356_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_85997_87356_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_85997_87356_cnt1) (p_k1_85997_87356_cnt1)).
Definition p_k1_85997_87356_cfg0_3 : plan :=
  PMmap (p_k1_85997_87356_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_85997_87356_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_85997_87356_cfgpos_5 : plan :=
  PMmap (p_k1_85997_87356_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_85997_87356_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_85997_87356_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_85997_87356_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_85997_87356 : plan :=
  PSplit (EVar 5) 0 (p_k1_85997_87356_cfg0_3) (p_k1_85997_87356_cfgpos_5).

Definition s_k1_85997_87356 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_85997_87356 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 85997 87356) p_k1_85997_87356 = COk s_k1_85997_87356.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_85997_87356)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_87357_90092_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_87357_90092_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_87357_90092_cnt1) (p_k1_87357_90092_cnt1)).
Definition p_k1_87357_90092_cfg0_3 : plan :=
  PMmap (p_k1_87357_90092_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_87357_90092_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_87357_90092_cfgpos_5 : plan :=
  PMmap (p_k1_87357_90092_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_87357_90092_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_87357_90092_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_87357_90092_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_87357_90092 : plan :=
  PSplit (EVar 5) 0 (p_k1_87357_90092_cfg0_3) (p_k1_87357_90092_cfgpos_5).

Definition s_k1_87357_90092 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_87357_90092 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 87357 90092) p_k1_87357_90092 = COk s_k1_87357_90092.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_87357_90092)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_90093_94188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_90093_94188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_90093_94188_cnt1) (p_k1_90093_94188_cnt1)).
Definition p_k1_90093_94188_cfg0_3 : plan :=
  PMmap (p_k1_90093_94188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_90093_94188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_90093_94188_cfgpos_5 : plan :=
  PMmap (p_k1_90093_94188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_90093_94188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_90093_94188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_90093_94188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_90093_94188 : plan :=
  PSplit (EVar 5) 0 (p_k1_90093_94188_cfg0_3) (p_k1_90093_94188_cfgpos_5).

Definition s_k1_90093_94188 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_90093_94188 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 90093 94188) p_k1_90093_94188 = COk s_k1_90093_94188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_90093_94188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_94189_98284_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_94189_98284_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_94189_98284_cnt1) (p_k1_94189_98284_cnt1)).
Definition p_k1_94189_98284_cfg0_3 : plan :=
  PMmap (p_k1_94189_98284_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_94189_98284_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_94189_98284_cfgpos_5 : plan :=
  PMmap (p_k1_94189_98284_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_94189_98284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_94189_98284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_94189_98284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_94189_98284 : plan :=
  PSplit (EVar 5) 0 (p_k1_94189_98284_cfg0_3) (p_k1_94189_98284_cfgpos_5).

Definition s_k1_94189_98284 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_94189_98284 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 94189 98284) p_k1_94189_98284 = COk s_k1_94189_98284.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_94189_98284)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_98285_102380_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_98285_102380_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_98285_102380_cnt1) (p_k1_98285_102380_cnt1)).
Definition p_k1_98285_102380_cfg0_3 : plan :=
  PMmap (p_k1_98285_102380_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_98285_102380_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_98285_102380_cfgpos_5 : plan :=
  PMmap (p_k1_98285_102380_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_98285_102380_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_98285_102380_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_98285_102380_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_98285_102380 : plan :=
  PSplit (EVar 5) 0 (p_k1_98285_102380_cfg0_3) (p_k1_98285_102380_cfgpos_5).

Definition s_k1_98285_102380 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_98285_102380 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 98285 102380) p_k1_98285_102380 = COk s_k1_98285_102380.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_98285_102380)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_102381_104828_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_102381_104828_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_102381_104828_cnt1) (p_k1_102381_104828_cnt1)).
Definition p_k1_102381_104828_cfg0_3 : plan :=
  PMmap (p_k1_102381_104828_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_102381_104828_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_102381_104828_cfgpos_5 : plan :=
  PMmap (p_k1_102381_104828_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_102381_104828_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_102381_104828_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_102381_104828_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_102381_104828 : plan :=
  PSplit (EVar 5) 0 (p_k1_102381_104828_cfg0_3) (p_k1_102381_104828_cfgpos_5).

Definition s_k1_102381_104828 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_102381_104828 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 102381 104828) p_k1_102381_104828 = COk s_k1_102381_104828.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_102381_104828)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_104829_106476_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_104829_106476_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_104829_106476_cnt1) (p_k1_104829_106476_cnt1)).
Definition p_k1_104829_106476_cfg0_3 : plan :=
  PMmap (p_k1_104829_106476_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_104829_106476_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_104829_106476_cfgpos_5 : plan :=
  PMmap (p_k1_104829_106476_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_104829_106476_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_104829_106476_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_104829_106476_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_104829_106476 : plan :=
  PSplit (EVar 5) 0 (p_k1_104829_106476_cfg0_3) (p_k1_104829_106476_cfgpos_5).

Definition s_k1_104829_106476 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_104829_106476 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 104829 106476) p_k1_104829_106476 = COk s_k1_104829_106476.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_104829_106476)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_106477_110572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_106477_110572_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_106477_110572_cnt1) (p_k1_106477_110572_cnt1)).
Definition p_k1_106477_110572_cfg0_3 : plan :=
  PMmap (p_k1_106477_110572_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_106477_110572_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_106477_110572_cfgpos_5 : plan :=
  PMmap (p_k1_106477_110572_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_106477_110572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_106477_110572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_106477_110572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_106477_110572 : plan :=
  PSplit (EVar 5) 0 (p_k1_106477_110572_cfg0_3) (p_k1_106477_110572_cfgpos_5).

Definition s_k1_106477_110572 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_106477_110572 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 106477 110572) p_k1_106477_110572 = COk s_k1_106477_110572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_106477_110572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_110573_114668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_110573_114668_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_110573_114668_cnt1) (p_k1_110573_114668_cnt1)).
Definition p_k1_110573_114668_cfg0_3 : plan :=
  PMmap (p_k1_110573_114668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_110573_114668_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_110573_114668_cfgpos_5 : plan :=
  PMmap (p_k1_110573_114668_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_110573_114668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_110573_114668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_110573_114668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_110573_114668 : plan :=
  PSplit (EVar 5) 0 (p_k1_110573_114668_cfg0_3) (p_k1_110573_114668_cfgpos_5).

Definition s_k1_110573_114668 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_110573_114668 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 110573 114668) p_k1_110573_114668 = COk s_k1_110573_114668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_110573_114668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k1_114669_118764_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k1_114669_118764_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k1_114669_118764_cnt1) (p_k1_114669_118764_cnt1)).
Definition p_k1_114669_118764_cfg0_3 : plan :=
  PMmap (p_k1_114669_118764_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k1_114669_118764_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k1_114669_118764_cfgpos_5 : plan :=
  PMmap (p_k1_114669_118764_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k1_114669_118764_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k1_114669_118764_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k1_114669_118764_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k1_114669_118764 : plan :=
  PSplit (EVar 5) 0 (p_k1_114669_118764_cfg0_3) (p_k1_114669_118764_cfgpos_5).

Definition s_k1_114669_118764 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k1_114669_118764 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 1 114669 118764) p_k1_114669_118764 = COk s_k1_114669_118764.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k1_114669_118764)). Qed.

