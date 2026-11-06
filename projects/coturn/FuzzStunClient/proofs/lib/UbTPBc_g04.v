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
Definition p_k0_12269_13084_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_12269_13084_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_12269_13084_cnt1) (p_k0_12269_13084_cnt1)).
Definition p_k0_12269_13084_cfg0_3 : plan :=
  PMmap (p_k0_12269_13084_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_12269_13084_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_12269_13084_cfgpos_5 : plan :=
  PMmap (p_k0_12269_13084_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_12269_13084_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_12269_13084_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_12269_13084_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_12269_13084 : plan :=
  PSplit (EVar 5) 0 (p_k0_12269_13084_cfg0_3) (p_k0_12269_13084_cfgpos_5).

Definition s_k0_12269_13084 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_12269_13084 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 12269 13084) p_k0_12269_13084 = COk s_k0_12269_13084.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_12269_13084)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_13085_16364_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_13085_16364_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_13085_16364_cnt1) (p_k0_13085_16364_cnt1)).
Definition p_k0_13085_16364_cfg0_3 : plan :=
  PMmap (p_k0_13085_16364_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_13085_16364_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_13085_16364_cfgpos_5 : plan :=
  PMmap (p_k0_13085_16364_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_13085_16364_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_13085_16364_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_13085_16364_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_13085_16364 : plan :=
  PSplit (EVar 5) 0 (p_k0_13085_16364_cfg0_3) (p_k0_13085_16364_cfgpos_5).

Definition s_k0_13085_16364 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_13085_16364 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 13085 16364) p_k0_13085_16364 = COk s_k0_13085_16364.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_13085_16364)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_16365_18700_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_16365_18700_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_16365_18700_cnt1) (p_k0_16365_18700_cnt1)).
Definition p_k0_16365_18700_cfg0_3 : plan :=
  PMmap (p_k0_16365_18700_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_16365_18700_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_16365_18700_cfgpos_5 : plan :=
  PMmap (p_k0_16365_18700_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_16365_18700_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_16365_18700_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_16365_18700_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_16365_18700 : plan :=
  PSplit (EVar 5) 0 (p_k0_16365_18700_cfg0_3) (p_k0_16365_18700_cfgpos_5).

Definition s_k0_16365_18700 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_16365_18700 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 16365 18700) p_k0_16365_18700 = COk s_k0_16365_18700.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_16365_18700)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_18701_20460_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_18701_20460_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_18701_20460_cnt1) (p_k0_18701_20460_cnt1)).
Definition p_k0_18701_20460_cfg0_3 : plan :=
  PMmap (p_k0_18701_20460_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_18701_20460_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_18701_20460_cfgpos_5 : plan :=
  PMmap (p_k0_18701_20460_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_18701_20460_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_18701_20460_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_18701_20460_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_18701_20460 : plan :=
  PSplit (EVar 5) 0 (p_k0_18701_20460_cfg0_3) (p_k0_18701_20460_cfgpos_5).

Definition s_k0_18701_20460 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_18701_20460 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 18701 20460) p_k0_18701_20460 = COk s_k0_18701_20460.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_18701_20460)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_20461_21820_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_20461_21820_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_20461_21820_cnt1) (p_k0_20461_21820_cnt1)).
Definition p_k0_20461_21820_cfg0_3 : plan :=
  PMmap (p_k0_20461_21820_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_20461_21820_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_20461_21820_cfgpos_5 : plan :=
  PMmap (p_k0_20461_21820_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_20461_21820_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_20461_21820_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_20461_21820_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_20461_21820 : plan :=
  PSplit (EVar 5) 0 (p_k0_20461_21820_cfg0_3) (p_k0_20461_21820_cfgpos_5).

Definition s_k0_20461_21820 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_20461_21820 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 20461 21820) p_k0_20461_21820 = COk s_k0_20461_21820.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_20461_21820)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_21821_24556_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_21821_24556_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_21821_24556_cnt1) (p_k0_21821_24556_cnt1)).
Definition p_k0_21821_24556_cfg0_3 : plan :=
  PMmap (p_k0_21821_24556_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_21821_24556_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_21821_24556_cfgpos_5 : plan :=
  PMmap (p_k0_21821_24556_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_21821_24556_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_21821_24556_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_21821_24556_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_21821_24556 : plan :=
  PSplit (EVar 5) 0 (p_k0_21821_24556_cfg0_3) (p_k0_21821_24556_cfgpos_5).

Definition s_k0_21821_24556 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_21821_24556 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 21821 24556) p_k0_21821_24556 = COk s_k0_21821_24556.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_21821_24556)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_24557_26188_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_24557_26188_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_24557_26188_cnt1) (p_k0_24557_26188_cnt1)).
Definition p_k0_24557_26188_cfg0_3 : plan :=
  PMmap (p_k0_24557_26188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_24557_26188_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_24557_26188_cfgpos_5 : plan :=
  PMmap (p_k0_24557_26188_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_24557_26188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_24557_26188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_24557_26188_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_24557_26188 : plan :=
  PSplit (EVar 5) 0 (p_k0_24557_26188_cfg0_3) (p_k0_24557_26188_cfgpos_5).

Definition s_k0_24557_26188 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_24557_26188 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 24557 26188) p_k0_24557_26188 = COk s_k0_24557_26188.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_24557_26188)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_26189_28652_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_26189_28652_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_26189_28652_cnt1) (p_k0_26189_28652_cnt1)).
Definition p_k0_26189_28652_cfg0_3 : plan :=
  PMmap (p_k0_26189_28652_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_26189_28652_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_26189_28652_cfgpos_5 : plan :=
  PMmap (p_k0_26189_28652_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_26189_28652_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_26189_28652_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_26189_28652_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_26189_28652 : plan :=
  PSplit (EVar 5) 0 (p_k0_26189_28652_cfg0_3) (p_k0_26189_28652_cfgpos_5).

Definition s_k0_26189_28652 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_26189_28652 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 26189 28652) p_k0_26189_28652 = COk s_k0_26189_28652.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_26189_28652)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_28653_32748_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_28653_32748_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_28653_32748_cnt1) (p_k0_28653_32748_cnt1)).
Definition p_k0_28653_32748_cfg0_3 : plan :=
  PMmap (p_k0_28653_32748_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_28653_32748_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_28653_32748_cfgpos_5 : plan :=
  PMmap (p_k0_28653_32748_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_28653_32748_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_28653_32748_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_28653_32748_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_28653_32748 : plan :=
  PSplit (EVar 5) 0 (p_k0_28653_32748_cfg0_3) (p_k0_28653_32748_cfgpos_5).

Definition s_k0_28653_32748 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_28653_32748 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 28653 32748) p_k0_28653_32748 = COk s_k0_28653_32748.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_28653_32748)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_32749_36844_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_32749_36844_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_32749_36844_cnt1) (p_k0_32749_36844_cnt1)).
Definition p_k0_32749_36844_cfg0_3 : plan :=
  PMmap (p_k0_32749_36844_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_32749_36844_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_32749_36844_cfgpos_5 : plan :=
  PMmap (p_k0_32749_36844_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_32749_36844_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_32749_36844_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_32749_36844_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_32749_36844 : plan :=
  PSplit (EVar 5) 0 (p_k0_32749_36844_cfg0_3) (p_k0_32749_36844_cfgpos_5).

Definition s_k0_32749_36844 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_32749_36844 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 32749 36844) p_k0_32749_36844 = COk s_k0_32749_36844.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_32749_36844)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_36845_37436_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_36845_37436_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_36845_37436_cnt1) (p_k0_36845_37436_cnt1)).
Definition p_k0_36845_37436_cfg0_3 : plan :=
  PMmap (p_k0_36845_37436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_36845_37436_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_36845_37436_cfgpos_5 : plan :=
  PMmap (p_k0_36845_37436_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_36845_37436_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_36845_37436_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_36845_37436_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_36845_37436 : plan :=
  PSplit (EVar 5) 0 (p_k0_36845_37436_cfg0_3) (p_k0_36845_37436_cfgpos_5).

Definition s_k0_36845_37436 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_36845_37436 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 36845 37436) p_k0_36845_37436 = COk s_k0_36845_37436.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_36845_37436)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_37437_40940_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_37437_40940_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_37437_40940_cnt1) (p_k0_37437_40940_cnt1)).
Definition p_k0_37437_40940_cfg0_3 : plan :=
  PMmap (p_k0_37437_40940_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_37437_40940_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_37437_40940_cfgpos_5 : plan :=
  PMmap (p_k0_37437_40940_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_37437_40940_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_37437_40940_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_37437_40940_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_37437_40940 : plan :=
  PSplit (EVar 5) 0 (p_k0_37437_40940_cfg0_3) (p_k0_37437_40940_cfgpos_5).

Definition s_k0_37437_40940 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_37437_40940 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 37437 40940) p_k0_37437_40940 = COk s_k0_37437_40940.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_37437_40940)). Qed.

