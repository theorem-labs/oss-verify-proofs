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
Definition p_k2_126957_131051_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_126957_131051_exit3_2 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_126957_131051_oom3 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_126957_131051_cnt1) (p_k2_126957_131051_cnt1)).
Definition p_k2_126957_131051_cfgpos_4 : plan :=
  PMmap (p_k2_126957_131051_oom3) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_126957_131051_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_126957_131051_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_126957_131051_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_126957_131051 : plan :=
  PSplit (EVar 5) 0 (PContra) (p_k2_126957_131051_cfgpos_4).

Definition s_k2_126957_131051 : shape :=
  (SCase (EVar 5) 0 SNil (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_126957_131051 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 126957 131051) p_k2_126957_131051 = COk s_k2_126957_131051.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_126957_131051)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k2_131052_262137_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k2_131052_262137_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k2_131052_262137_cnt1) (p_k2_131052_262137_cnt1)).
Definition p_k2_131052_262137_cfg0_3 : plan :=
  PMmap (p_k2_131052_262137_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k2_131052_262137_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k2_131052_262137_cfgpos_5 : plan :=
  PMmap (p_k2_131052_262137_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k2_131052_262137_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k2_131052_262137_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k2_131052_262137_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k2_131052_262137 : plan :=
  PSplit (EVar 5) 0 (p_k2_131052_262137_cfg0_3) (p_k2_131052_262137_cfgpos_5).

Definition s_k2_131052_262137 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k2_131052_262137 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 2 131052 262137) p_k2_131052_262137 = COk s_k2_131052_262137.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k2_131052_262137)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k3_229371_524281_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k3_229371_524281_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k3_229371_524281_cnt1) (p_k3_229371_524281_cnt1)).
Definition p_k3_229371_524281_cfg0_3 : plan :=
  PMmap (p_k3_229371_524281_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k3_229371_524281_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k3_229371_524281_cfgpos_5 : plan :=
  PMmap (p_k3_229371_524281_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k3_229371_524281_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k3_229371_524281_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k3_229371_524281_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k3_229371_524281 : plan :=
  PSplit (EVar 5) 0 (p_k3_229371_524281_cfg0_3) (p_k3_229371_524281_cfgpos_5).

Definition s_k3_229371_524281 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k3_229371_524281 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 3 229371 524281) p_k3_229371_524281 = COk s_k3_229371_524281.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k3_229371_524281)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k4_491515_1048569_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k4_491515_1048569_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k4_491515_1048569_cnt1) (p_k4_491515_1048569_cnt1)).
Definition p_k4_491515_1048569_cfg0_3 : plan :=
  PMmap (p_k4_491515_1048569_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k4_491515_1048569_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k4_491515_1048569_cfgpos_5 : plan :=
  PMmap (p_k4_491515_1048569_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k4_491515_1048569_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k4_491515_1048569_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k4_491515_1048569_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k4_491515_1048569 : plan :=
  PSplit (EVar 5) 0 (p_k4_491515_1048569_cfg0_3) (p_k4_491515_1048569_cfgpos_5).

Definition s_k4_491515_1048569 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k4_491515_1048569 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 4 491515 1048569) p_k4_491515_1048569 = COk s_k4_491515_1048569.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k4_491515_1048569)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k5_1015803_2097145_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k5_1015803_2097145_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k5_1015803_2097145_cnt1) (p_k5_1015803_2097145_cnt1)).
Definition p_k5_1015803_2097145_cfg0_3 : plan :=
  PMmap (p_k5_1015803_2097145_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k5_1015803_2097145_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k5_1015803_2097145_cfgpos_5 : plan :=
  PMmap (p_k5_1015803_2097145_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k5_1015803_2097145_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k5_1015803_2097145_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k5_1015803_2097145_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k5_1015803_2097145 : plan :=
  PSplit (EVar 5) 0 (p_k5_1015803_2097145_cfg0_3) (p_k5_1015803_2097145_cfgpos_5).

Definition s_k5_1015803_2097145 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k5_1015803_2097145 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 5 1015803 2097145) p_k5_1015803_2097145 = COk s_k5_1015803_2097145.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k5_1015803_2097145)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k6_2064379_4194297_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k6_2064379_4194297_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k6_2064379_4194297_cnt1) (p_k6_2064379_4194297_cnt1)).
Definition p_k6_2064379_4194297_cfg0_3 : plan :=
  PMmap (p_k6_2064379_4194297_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k6_2064379_4194297_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k6_2064379_4194297_cfgpos_5 : plan :=
  PMmap (p_k6_2064379_4194297_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k6_2064379_4194297_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k6_2064379_4194297_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k6_2064379_4194297_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k6_2064379_4194297 : plan :=
  PSplit (EVar 5) 0 (p_k6_2064379_4194297_cfg0_3) (p_k6_2064379_4194297_cfgpos_5).

Definition s_k6_2064379_4194297 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k6_2064379_4194297 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 6 2064379 4194297) p_k6_2064379_4194297 = COk s_k6_2064379_4194297.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k6_2064379_4194297)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k7_4161531_8388601_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k7_4161531_8388601_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k7_4161531_8388601_cnt1) (p_k7_4161531_8388601_cnt1)).
Definition p_k7_4161531_8388601_cfg0_3 : plan :=
  PMmap (p_k7_4161531_8388601_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k7_4161531_8388601_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k7_4161531_8388601_cfgpos_5 : plan :=
  PMmap (p_k7_4161531_8388601_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k7_4161531_8388601_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k7_4161531_8388601_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k7_4161531_8388601_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k7_4161531_8388601 : plan :=
  PSplit (EVar 5) 0 (p_k7_4161531_8388601_cfg0_3) (p_k7_4161531_8388601_cfgpos_5).

Definition s_k7_4161531_8388601 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k7_4161531_8388601 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 7 4161531 8388601) p_k7_4161531_8388601 = COk s_k7_4161531_8388601.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k7_4161531_8388601)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k8_8355835_12566521_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k8_8355835_12566521_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k8_8355835_12566521_cnt1) (p_k8_8355835_12566521_cnt1)).
Definition p_k8_8355835_12566521_cfg0_3 : plan :=
  PMmap (p_k8_8355835_12566521_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k8_8355835_12566521_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k8_8355835_12566521_cfgpos_5 : plan :=
  PMmap (p_k8_8355835_12566521_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k8_8355835_12566521_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k8_8355835_12566521_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k8_8355835_12566521_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k8_8355835_12566521 : plan :=
  PSplit (EVar 5) 0 (p_k8_8355835_12566521_cfg0_3) (p_k8_8355835_12566521_cfgpos_5).

Definition s_k8_8355835_12566521 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k8_8355835_12566521 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 8 8355835 12566521) p_k8_8355835_12566521 = COk s_k8_8355835_12566521.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k8_8355835_12566521)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k8_12566522_16777209_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k8_12566522_16777209_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k8_12566522_16777209_cnt1) (p_k8_12566522_16777209_cnt1)).
Definition p_k8_12566522_16777209_cfg0_3 : plan :=
  PMmap (p_k8_12566522_16777209_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k8_12566522_16777209_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k8_12566522_16777209_cfgpos_5 : plan :=
  PMmap (p_k8_12566522_16777209_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k8_12566522_16777209_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k8_12566522_16777209_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k8_12566522_16777209_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k8_12566522_16777209 : plan :=
  PSplit (EVar 5) 0 (p_k8_12566522_16777209_cfg0_3) (p_k8_12566522_16777209_cfgpos_5).

Definition s_k8_12566522_16777209 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k8_12566522_16777209 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 8 12566522 16777209) p_k8_12566522_16777209 = COk s_k8_12566522_16777209.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k8_12566522_16777209)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k9_16744443_22347769_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k9_16744443_22347769_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k9_16744443_22347769_cnt1) (p_k9_16744443_22347769_cnt1)).
Definition p_k9_16744443_22347769_cfg0_3 : plan :=
  PMmap (p_k9_16744443_22347769_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k9_16744443_22347769_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k9_16744443_22347769_cfgpos_5 : plan :=
  PMmap (p_k9_16744443_22347769_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k9_16744443_22347769_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k9_16744443_22347769_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k9_16744443_22347769_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k9_16744443_22347769 : plan :=
  PSplit (EVar 5) 0 (p_k9_16744443_22347769_cfg0_3) (p_k9_16744443_22347769_cfgpos_5).

Definition s_k9_16744443_22347769 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k9_16744443_22347769 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 9 16744443 22347769) p_k9_16744443_22347769 = COk s_k9_16744443_22347769.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k9_16744443_22347769)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k9_22347770_27951096_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k9_22347770_27951096_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k9_22347770_27951096_cnt1) (p_k9_22347770_27951096_cnt1)).
Definition p_k9_22347770_27951096_cfg0_3 : plan :=
  PMmap (p_k9_22347770_27951096_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k9_22347770_27951096_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k9_22347770_27951096_cfgpos_5 : plan :=
  PMmap (p_k9_22347770_27951096_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k9_22347770_27951096_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k9_22347770_27951096_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k9_22347770_27951096_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k9_22347770_27951096 : plan :=
  PSplit (EVar 5) 0 (p_k9_22347770_27951096_cfg0_3) (p_k9_22347770_27951096_cfgpos_5).

Definition s_k9_22347770_27951096 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k9_22347770_27951096 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 9 22347770 27951096) p_k9_22347770_27951096 = COk s_k9_22347770_27951096.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k9_22347770_27951096)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k9_27951097_33554425_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k9_27951097_33554425_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k9_27951097_33554425_cnt1) (p_k9_27951097_33554425_cnt1)).
Definition p_k9_27951097_33554425_cfg0_3 : plan :=
  PMmap (p_k9_27951097_33554425_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k9_27951097_33554425_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k9_27951097_33554425_cfgpos_5 : plan :=
  PMmap (p_k9_27951097_33554425_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k9_27951097_33554425_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k9_27951097_33554425_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k9_27951097_33554425_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k9_27951097_33554425 : plan :=
  PSplit (EVar 5) 0 (p_k9_27951097_33554425_cfg0_3) (p_k9_27951097_33554425_cfgpos_5).

Definition s_k9_27951097_33554425 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k9_27951097_33554425 : check Plain.M.loaded_segments ITAB REF_ATB NX0k 20000%nat 400%nat (cs_Tk 9 27951097 33554425) p_k9_27951097_33554425 = COk s_k9_27951097_33554425.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k9_27951097_33554425)). Qed.

