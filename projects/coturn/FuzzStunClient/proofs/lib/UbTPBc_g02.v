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
Definition p_k0_189_236_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_189_236_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_189_236_cnt1) (p_k0_189_236_cnt1)).
Definition p_k0_189_236_cfg0_3 : plan :=
  PMmap (p_k0_189_236_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))).
Definition p_k0_189_236_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_189_236_cfgpos_5 : plan :=
  PMmap (p_k0_189_236_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_189_236_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_189_236_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_189_236_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))))).
Definition p_k0_189_236 : plan :=
  PSplit (EVar 5) 0 (p_k0_189_236_cfg0_3) (p_k0_189_236_cfgpos_5).

Definition s_k0_189_236 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_189_236 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 189 236) p_k0_189_236 = COk s_k0_189_236.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_189_236)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_237_284_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_237_284_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_237_284_cnt1) (p_k0_237_284_cnt1)).
Definition p_k0_237_284_cfg0_3 : plan :=
  PMmap (p_k0_237_284_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_237_284_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_237_284_cfgpos_5 : plan :=
  PMmap (p_k0_237_284_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_237_284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_237_284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_237_284_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_237_284 : plan :=
  PSplit (EVar 5) 0 (p_k0_237_284_cfg0_3) (p_k0_237_284_cfgpos_5).

Definition s_k0_237_284 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_237_284 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 237 284) p_k0_237_284 = COk s_k0_237_284.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_237_284)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_285_316_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_285_316_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_285_316_cnt1) (p_k0_285_316_cnt1)).
Definition p_k0_285_316_cfg0_3 : plan :=
  PMmap (p_k0_285_316_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_285_316_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_285_316_cfgpos_5 : plan :=
  PMmap (p_k0_285_316_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_285_316_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_285_316_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_285_316_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_285_316 : plan :=
  PSplit (EVar 5) 0 (p_k0_285_316_cfg0_3) (p_k0_285_316_cfgpos_5).

Definition s_k0_285_316 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_285_316 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 285 316) p_k0_285_316 = COk s_k0_285_316.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_285_316)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_317_396_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_317_396_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_317_396_cnt1) (p_k0_317_396_cnt1)).
Definition p_k0_317_396_cfg0_3 : plan :=
  PMmap (p_k0_317_396_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_317_396_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_317_396_cfgpos_5 : plan :=
  PMmap (p_k0_317_396_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_317_396_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_317_396_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_317_396_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_317_396 : plan :=
  PSplit (EVar 5) 0 (p_k0_317_396_cfg0_3) (p_k0_317_396_cfgpos_5).

Definition s_k0_317_396 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_317_396 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 317 396) p_k0_317_396 = COk s_k0_317_396.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_317_396)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_397_492_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_397_492_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_397_492_cnt1) (p_k0_397_492_cnt1)).
Definition p_k0_397_492_cfg0_3 : plan :=
  PMmap (p_k0_397_492_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))).
Definition p_k0_397_492_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_397_492_cfgpos_5 : plan :=
  PMmap (p_k0_397_492_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_397_492_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_397_492_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_397_492_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))))).
Definition p_k0_397_492 : plan :=
  PSplit (EVar 5) 0 (p_k0_397_492_cfg0_3) (p_k0_397_492_cfgpos_5).

Definition s_k0_397_492 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_397_492 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 397 492) p_k0_397_492 = COk s_k0_397_492.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_397_492)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_493_572_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_493_572_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_493_572_cnt1) (p_k0_493_572_cnt1)).
Definition p_k0_493_572_cfg0_3 : plan :=
  PMmap (p_k0_493_572_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_493_572_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_493_572_cfgpos_5 : plan :=
  PMmap (p_k0_493_572_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_493_572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_493_572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_493_572_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_493_572 : plan :=
  PSplit (EVar 5) 0 (p_k0_493_572_cfg0_3) (p_k0_493_572_cfgpos_5).

Definition s_k0_493_572 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_493_572 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 493 572) p_k0_493_572 = COk s_k0_493_572.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_493_572)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_573_668_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_573_668_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_573_668_cnt1) (p_k0_573_668_cnt1)).
Definition p_k0_573_668_cfg0_3 : plan :=
  PMmap (p_k0_573_668_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_573_668_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_573_668_cfgpos_5 : plan :=
  PMmap (p_k0_573_668_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_573_668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_573_668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_573_668_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_573_668 : plan :=
  PSplit (EVar 5) 0 (p_k0_573_668_cfg0_3) (p_k0_573_668_cfgpos_5).

Definition s_k0_573_668 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_573_668 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 573 668) p_k0_573_668 = COk s_k0_573_668.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_573_668)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_669_796_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_669_796_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_669_796_cnt1) (p_k0_669_796_cnt1)).
Definition p_k0_669_796_cfg0_3 : plan :=
  PMmap (p_k0_669_796_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_669_796_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_669_796_cfgpos_5 : plan :=
  PMmap (p_k0_669_796_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_669_796_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_669_796_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_669_796_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_669_796 : plan :=
  PSplit (EVar 5) 0 (p_k0_669_796_cfg0_3) (p_k0_669_796_cfgpos_5).

Definition s_k0_669_796 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_669_796 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 669 796) p_k0_669_796 = COk s_k0_669_796.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_669_796)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_797_1004_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_797_1004_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_797_1004_cnt1) (p_k0_797_1004_cnt1)).
Definition p_k0_797_1004_cfg0_3 : plan :=
  PMmap (p_k0_797_1004_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))).
Definition p_k0_797_1004_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_797_1004_cfgpos_5 : plan :=
  PMmap (p_k0_797_1004_oom2) (PCall SumEnframe [] (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_797_1004_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_797_1004_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_797_1004_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall)))))))))))))))))))))))))))))))).
Definition p_k0_797_1004 : plan :=
  PSplit (EVar 5) 0 (p_k0_797_1004_cfg0_3) (p_k0_797_1004_cfgpos_5).

Definition s_k0_797_1004 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_797_1004 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 797 1004) p_k0_797_1004 = COk s_k0_797_1004.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_797_1004)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1005_1148_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1005_1148_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1005_1148_cnt1) (p_k0_1005_1148_cnt1)).
Definition p_k0_1005_1148_cfg0_3 : plan :=
  PMmap (p_k0_1005_1148_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1005_1148_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1005_1148_cfgpos_5 : plan :=
  PMmap (p_k0_1005_1148_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_1005_1148_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_1005_1148_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_1005_1148_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1005_1148 : plan :=
  PSplit (EVar 5) 0 (p_k0_1005_1148_cfg0_3) (p_k0_1005_1148_cfgpos_5).

Definition s_k0_1005_1148 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1005_1148 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 1005 1148) p_k0_1005_1148 = COk s_k0_1005_1148.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1005_1148)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1149_1340_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1149_1340_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1149_1340_cnt1) (p_k0_1149_1340_cnt1)).
Definition p_k0_1149_1340_cfg0_3 : plan :=
  PMmap (p_k0_1149_1340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1149_1340_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1149_1340_cfgpos_5 : plan :=
  PMmap (p_k0_1149_1340_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_1149_1340_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_1149_1340_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_1149_1340_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1149_1340 : plan :=
  PSplit (EVar 5) 0 (p_k0_1149_1340_cfg0_3) (p_k0_1149_1340_cfgpos_5).

Definition s_k0_1149_1340 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1149_1340 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 1149 1340) p_k0_1149_1340 = COk s_k0_1149_1340.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1149_1340)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p_k0_1341_1628_cnt1 : plan :=
  PCall SumFreePro [] (PMunmap (PExitCall)).
Definition p_k0_1341_1628_oom2 : plan :=
  PResume (PSplit (EVar 7) 127 (p_k0_1341_1628_cnt1) (p_k0_1341_1628_cnt1)).
Definition p_k0_1341_1628_cfg0_3 : plan :=
  PMmap (p_k0_1341_1628_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))).
Definition p_k0_1341_1628_exit3_4 : plan :=
  PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))).
Definition p_k0_1341_1628_cfgpos_5 : plan :=
  PMmap (p_k0_1341_1628_oom2) (PCall SumEnframe [] (PCall SumMemcpy [] (PCall SumF [] (PResume (PResume (PResume (PResume (PResume (PResume (PIoctl (PStdioWrite (PResume (PResume (PSplit (XC) 0 (p_k0_1341_1628_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 1 (p_k0_1341_1628_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PSplit (XC) 2 (p_k0_1341_1628_exit3_4) (PCall SumF [] (PCall SumPrintf [] (PResume (PCall SumFreePro [] (PMunmap (PCall SumMainRet [] (PCall SumFreePro [] (PMunmap (PExitCall))))))))))))))))))))))))))))))).
Definition p_k0_1341_1628 : plan :=
  PSplit (EVar 5) 0 (p_k0_1341_1628_cfg0_3) (p_k0_1341_1628_cfgpos_5).

Definition s_k0_1341_1628 : shape :=
  (SCase (EVar 5) 0 (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SExit 0))) (SAlt2 (SCase (EVar 7) 127 (SExit 2) (SExit 0)) (SEmit 1 [48; 10] (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 1 (SEmit 1 [48; 10] (SExit 0)) (SCase (EAlu ALU_AND (EBlob false 0 2 1) (ELit 3)) 2 (SEmit 1 [48; 10; 48; 10] (SExit 0)) (SEmit 1 [48; 10; 48; 10; 48; 10] (SExit 0)))))))).

Lemma chk_k0_1341_1628 : check Ubsan.M.loaded_segments ITAB UB_ATB NX0 20000%nat 400%nat (cs_T 1341 1628) p_k0_1341_1628 = COk s_k0_1341_1628.
Proof. vm_cast_no_check (@eq_refl cres (COk s_k0_1341_1628)). Qed.

