(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: splits cert_202 into per-reservation cases cert_202_0 and cert_202_1 combined by lia, checking a register-shifted planK_202_k (vsh_202) against handoff tables HS_as0 collected by collect_handoffs, and adds the LIMIT reservation argument; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0CertK_202.v, lines 6, 143-148, 153-164. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Ja0DefsK Ja0ResK Ja0CertK_201 PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_202 : plan :=
PSys YBrk
(PRun [] (PSplit (EVar 5) 0x7fff5
(PBrk2
(PRun [] (PMmap PContra
(PFact (KDisj (SA (ELit 0x7fff7000) 0) (ELit 0x100000001000) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 442)) (ELit 4096)) 0) (ELit 4096)) (PRun [] (PMprotect PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemset []
(PRun [0x9a0a4] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun [] (PMmapIn PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemset []
(PRun [0x9a0a4] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 475)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 475)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) PContra)))
(PSys YBrk
(PRun [] (PMmap PContra
(PFact (KDisj (SA (ELit 0x7fff7000) 0) (ELit 0x100000001000) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 442)) (ELit 4096)) 0) (ELit 4096)) (PRun [] (PMprotect PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemset []
(PRun [0x9a0a4] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(PRun [0x5f698] (PJoin e_sp0 (-2280) 8
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [0xa71ac] (PJoin (ELit 0) 3497168 4 (PJoin (ELit 0) 5998180 4 (PAbsWord (ELit 0) 2149320 8 2 3 (PAbsWord (ELit 0) 2149344 4 2 3 (PAbsWord (ELit 0) 3497168 4 0 1 (PAbsWord (ELit 0) 5998180 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition shape_202 : shape := (SCase (EVar 5) 524277 (SAlt2 (SHole 1) (SHole 0)) (SHole 1)).
Definition vsh_202 (v : nat) : nat := if Nat.ltb v 12 then v else v + 6.
Definition planK_202_k : plan := psh vsh_202 planK_202.
Definition HSL_202_0 : list (nat * acs) := Eval vm_compute in
collect_handoffs 8 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_202 0) planK_202_k) [].
Definition HSL_202_1 : list (nat * acs) := Eval vm_compute in
collect_handoffs 8 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_202 1) planK_202_k) [].
Definition HS_as0_0 (h : nat) : option acs := match h with 0%nat | 1%nat => hlookup HSL_202_0 h | _ => None end.
Definition HS_as0_1 (h : nat) : option acs := match h with 0%nat | 1%nat => hlookup HSL_202_1 h | _ => None end.
Definition HS_as0 (r : Z) : nat -> option acs := if Z.eqb r 1 then HS_as0_1 else HS_as0_0.
Lemma cert_202_0 :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 (HS_as0 0) KC0 BFUEL FUEL None (HS_202 0) planK_202_k = COk shape_202.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_202)). Qed.
Lemma cert_202_1 :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 (HS_as0 1) KC0 BFUEL FUEL None (HS_202 1) planK_202_k = COk shape_202.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_202)). Qed.
Lemma cert_202 : forall r, 0 <= r <= 1 ->
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT r XN0 XE0 XB0 (HS_as0 r) KC0 BFUEL FUEL None (HS_202 r) planK_202_k = COk shape_202.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_202_0 | exact cert_202_1]. Qed.
