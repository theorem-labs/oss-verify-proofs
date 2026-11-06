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
Definition p_k10_33521659_40239097_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_33521659_40239097_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_33521659_40239097_cnt1) (p_k10_33521659_40239097_cnt1)).
Definition p_k10_33521659_40239097_cfg0_3 : plan :=
  PMmap (p_k10_33521659_40239097_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_33521659_40239097_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_33521659_40239097_cfgpos_5 : plan :=
  PMmap (p_k10_33521659_40239097_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k10_33521659_40239097_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k10_33521659_40239097_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k10_33521659_40239097_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_33521659_40239097 : plan :=
  PSplit (EVar 5) 0 (p_k10_33521659_40239097_cfg0_3) (p_k10_33521659_40239097_cfgpos_5).

Definition s_k10_33521659_40239097 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_33521659_40239097 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 10 33521659 40239097) p_k10_33521659_40239097 = COk s_k10_33521659_40239097.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_33521659_40239097)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_40239098_46956536_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_40239098_46956536_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_40239098_46956536_cnt1) (p_k10_40239098_46956536_cnt1)).
Definition p_k10_40239098_46956536_cfg0_3 : plan :=
  PMmap (p_k10_40239098_46956536_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_40239098_46956536_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_40239098_46956536_cfgpos_5 : plan :=
  PMmap (p_k10_40239098_46956536_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k10_40239098_46956536_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k10_40239098_46956536_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k10_40239098_46956536_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_40239098_46956536 : plan :=
  PSplit (EVar 5) 0 (p_k10_40239098_46956536_cfg0_3) (p_k10_40239098_46956536_cfgpos_5).

Definition s_k10_40239098_46956536 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_40239098_46956536 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 10 40239098 46956536) p_k10_40239098_46956536 = COk s_k10_40239098_46956536.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_40239098_46956536)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_46956537_53673975_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_46956537_53673975_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_46956537_53673975_cnt1) (p_k10_46956537_53673975_cnt1)).
Definition p_k10_46956537_53673975_cfg0_3 : plan :=
  PMmap (p_k10_46956537_53673975_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_46956537_53673975_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_46956537_53673975_cfgpos_5 : plan :=
  PMmap (p_k10_46956537_53673975_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k10_46956537_53673975_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k10_46956537_53673975_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k10_46956537_53673975_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_46956537_53673975 : plan :=
  PSplit (EVar 5) 0 (p_k10_46956537_53673975_cfg0_3) (p_k10_46956537_53673975_cfgpos_5).

Definition s_k10_46956537_53673975 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_46956537_53673975 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 10 46956537 53673975) p_k10_46956537_53673975 = COk s_k10_46956537_53673975.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_46956537_53673975)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_53673976_60391414_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_53673976_60391414_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_53673976_60391414_cnt1) (p_k10_53673976_60391414_cnt1)).
Definition p_k10_53673976_60391414_cfg0_3 : plan :=
  PMmap (p_k10_53673976_60391414_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_53673976_60391414_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_53673976_60391414_cfgpos_5 : plan :=
  PMmap (p_k10_53673976_60391414_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k10_53673976_60391414_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k10_53673976_60391414_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k10_53673976_60391414_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_53673976_60391414 : plan :=
  PSplit (EVar 5) 0 (p_k10_53673976_60391414_cfg0_3) (p_k10_53673976_60391414_cfgpos_5).

Definition s_k10_53673976_60391414 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_53673976_60391414 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 10 53673976 60391414) p_k10_53673976_60391414 = COk s_k10_53673976_60391414.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_53673976_60391414)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k10_60391415_67108857_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k10_60391415_67108857_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k10_60391415_67108857_cnt1) (p_k10_60391415_67108857_cnt1)).
Definition p_k10_60391415_67108857_cfg0_3 : plan :=
  PMmap (p_k10_60391415_67108857_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k10_60391415_67108857_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k10_60391415_67108857_cfgpos_5 : plan :=
  PMmap (p_k10_60391415_67108857_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k10_60391415_67108857_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k10_60391415_67108857_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k10_60391415_67108857_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k10_60391415_67108857 : plan :=
  PSplit (EVar 5) 0 (p_k10_60391415_67108857_cfg0_3) (p_k10_60391415_67108857_cfgpos_5).

Definition s_k10_60391415_67108857 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k10_60391415_67108857 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0k 20000%nat 400%nat (cs_Tk 10 60391415 67108857) p_k10_60391415_67108857 = COk s_k10_60391415_67108857.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k10_60391415_67108857)). Qed.

