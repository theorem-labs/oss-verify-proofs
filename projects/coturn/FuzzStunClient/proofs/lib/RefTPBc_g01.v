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
Definition p_k0_0_0_cfg0_1 : plan :=
  PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))).
Definition p_k0_0_0_exit3_2 : plan :=
  PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))).
Definition p_k0_0_0_cfgpos_3 : plan :=
  PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_0_0_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_0_0_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_0_0_exit3_2) (PCall SumF [] (PCall SumPrintf [] (PResume (PResume (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))).
Definition p_k0_0_0 : plan :=
  PSplit (EVar 5) 0 (p_k0_0_0_cfg0_1) (p_k0_0_0_cfgpos_3).

Definition s_k0_0_0 : shape :=
  (SCase (EVar 5) 0 (SEmit 1 [48; 10] (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0))))))).

Lemma chk_k0_0_0 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 0 0) p_k0_0_0 = COk s_k0_0_0.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_0_0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1_12_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1_12_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1_12_cnt1) (p_k0_1_12_cnt1)).
Definition p_k0_1_12_cfg0_3 : plan :=
  PMmap (p_k0_1_12_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_1_12_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1_12_cfgpos_5 : plan :=
  PMmap (p_k0_1_12_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_1_12_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_1_12_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_1_12_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_1_12 : plan :=
  PSplit (EVar 5) 0 (p_k0_1_12_cfg0_3) (p_k0_1_12_cfgpos_5).

Definition s_k0_1_12 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1_12 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 1 12) p_k0_1_12 = COk s_k0_1_12.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1_12)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_13_28_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_13_28_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_13_28_cnt1) (p_k0_13_28_cnt1)).
Definition p_k0_13_28_cfg0_3 : plan :=
  PMmap (p_k0_13_28_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_13_28_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_13_28_cfgpos_5 : plan :=
  PMmap (p_k0_13_28_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_13_28_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_13_28_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_13_28_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_13_28 : plan :=
  PSplit (EVar 5) 0 (p_k0_13_28_cfg0_3) (p_k0_13_28_cfgpos_5).

Definition s_k0_13_28 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_13_28 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 13 28) p_k0_13_28 = COk s_k0_13_28.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_13_28)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_29_44_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_29_44_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_29_44_cnt1) (p_k0_29_44_cnt1)).
Definition p_k0_29_44_cfg0_3 : plan :=
  PMmap (p_k0_29_44_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_29_44_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_29_44_cfgpos_5 : plan :=
  PMmap (p_k0_29_44_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_29_44_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_29_44_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_29_44_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_29_44 : plan :=
  PSplit (EVar 5) 0 (p_k0_29_44_cfg0_3) (p_k0_29_44_cfgpos_5).

Definition s_k0_29_44 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_29_44 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 29 44) p_k0_29_44 = COk s_k0_29_44.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_29_44)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_45_60_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_45_60_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_45_60_cnt1) (p_k0_45_60_cnt1)).
Definition p_k0_45_60_cfg0_3 : plan :=
  PMmap (p_k0_45_60_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_45_60_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_45_60_cfgpos_5 : plan :=
  PMmap (p_k0_45_60_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_45_60_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_45_60_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_45_60_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_45_60 : plan :=
  PSplit (EVar 5) 0 (p_k0_45_60_cfg0_3) (p_k0_45_60_cfgpos_5).

Definition s_k0_45_60 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_45_60 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 45 60) p_k0_45_60 = COk s_k0_45_60.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_45_60)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_61_76_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_61_76_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_61_76_cnt1) (p_k0_61_76_cnt1)).
Definition p_k0_61_76_cfg0_3 : plan :=
  PMmap (p_k0_61_76_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_61_76_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_61_76_cfgpos_5 : plan :=
  PMmap (p_k0_61_76_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_61_76_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_61_76_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_61_76_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_61_76 : plan :=
  PSplit (EVar 5) 0 (p_k0_61_76_cfg0_3) (p_k0_61_76_cfgpos_5).

Definition s_k0_61_76 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_61_76 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 61 76) p_k0_61_76 = COk s_k0_61_76.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_61_76)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_77_92_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_77_92_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_77_92_cnt1) (p_k0_77_92_cnt1)).
Definition p_k0_77_92_cfg0_3 : plan :=
  PMmap (p_k0_77_92_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_77_92_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_77_92_cfgpos_5 : plan :=
  PMmap (p_k0_77_92_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_77_92_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_77_92_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_77_92_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_77_92 : plan :=
  PSplit (EVar 5) 0 (p_k0_77_92_cfg0_3) (p_k0_77_92_cfgpos_5).

Definition s_k0_77_92 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_77_92 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 77 92) p_k0_77_92 = COk s_k0_77_92.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_77_92)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_93_108_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_93_108_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_93_108_cnt1) (p_k0_93_108_cnt1)).
Definition p_k0_93_108_cfg0_3 : plan :=
  PMmap (p_k0_93_108_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_93_108_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_93_108_cfgpos_5 : plan :=
  PMmap (p_k0_93_108_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_93_108_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_93_108_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_93_108_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_93_108 : plan :=
  PSplit (EVar 5) 0 (p_k0_93_108_cfg0_3) (p_k0_93_108_cfgpos_5).

Definition s_k0_93_108 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_93_108 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 93 108) p_k0_93_108 = COk s_k0_93_108.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_93_108)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_109_124_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_109_124_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_109_124_cnt1) (p_k0_109_124_cnt1)).
Definition p_k0_109_124_cfg0_3 : plan :=
  PMmap (p_k0_109_124_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_109_124_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_109_124_cfgpos_5 : plan :=
  PMmap (p_k0_109_124_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_109_124_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_109_124_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_109_124_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_109_124 : plan :=
  PSplit (EVar 5) 0 (p_k0_109_124_cfg0_3) (p_k0_109_124_cfgpos_5).

Definition s_k0_109_124 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_109_124 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 109 124) p_k0_109_124 = COk s_k0_109_124.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_109_124)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_125_140_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_125_140_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_125_140_cnt1) (p_k0_125_140_cnt1)).
Definition p_k0_125_140_cfg0_3 : plan :=
  PMmap (p_k0_125_140_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_125_140_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_125_140_cfgpos_5 : plan :=
  PMmap (p_k0_125_140_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_125_140_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_125_140_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_125_140_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_125_140 : plan :=
  PSplit (EVar 5) 0 (p_k0_125_140_cfg0_3) (p_k0_125_140_cfgpos_5).

Definition s_k0_125_140 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_125_140 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 125 140) p_k0_125_140 = COk s_k0_125_140.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_125_140)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_141_156_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_141_156_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_141_156_cnt1) (p_k0_141_156_cnt1)).
Definition p_k0_141_156_cfg0_3 : plan :=
  PMmap (p_k0_141_156_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_141_156_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_141_156_cfgpos_5 : plan :=
  PMmap (p_k0_141_156_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_141_156_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_141_156_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_141_156_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_141_156 : plan :=
  PSplit (EVar 5) 0 (p_k0_141_156_cfg0_3) (p_k0_141_156_cfgpos_5).

Definition s_k0_141_156 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_141_156 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 141 156) p_k0_141_156 = COk s_k0_141_156.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_141_156)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_157_188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_157_188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_157_188_cnt1) (p_k0_157_188_cnt1)).
Definition p_k0_157_188_cfg0_3 : plan :=
  PMmap (p_k0_157_188_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_157_188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_157_188_cfgpos_5 : plan :=
  PMmap (p_k0_157_188_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_157_188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_157_188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_157_188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_157_188 : plan :=
  PSplit (EVar 5) 0 (p_k0_157_188_cfg0_3) (p_k0_157_188_cfgpos_5).

Definition s_k0_157_188 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_157_188 : check Plain.M.loaded_segments ITAB REF_ATB NX0 20000%nat 400%nat (cs_T 157 188) p_k0_157_188 = COk s_k0_157_188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_157_188)). Qed.

