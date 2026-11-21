(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's Pm4CertK_root.v, Pm4CertK_201.v and Pm4CertK_202.v for LPS 727298f3: their recorded start-up plans moved here unchanged as planK_root_rec, planK_201_rec and planK_202_rec, checked as their renumbering by PlanRegenK.psh (variables from 11 up moved by 4), with the checker chkK and the hand-off table solver tlook, kmeet, solve, tget and shape_of added; taken from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8PlanK.v, lines 5-13, 21-729. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanNodesExtraDefsK AsanInitK Pm4DefsK Pm4ResK PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* The start-up plans, moved here from Pm4CertK_root / _201 / _202 so the hand-off
   states (Pm4HSK_* ) can be computed from them.  [planK_root_rec], [planK_201_rec]
   and [planK_202_rec] are the recorded plans as main has them in Pm4CertK_*, text
   unchanged; the checked plans are their renumbering by [PlanRegenK.psh vsh]
   (OSSV-343's method: a recorded plan is renumbered where it is checked, never
   rewritten).
   THE MAP, read from runs at 727298f3: NX0 is 15 (it was 11; V_EHDR/V_GID/V_EXECFN
   appended), so every variable at or above the old NX0 moves by 4 and the launch's
   own (below 11) keep their numbers.  The run's counter at hand-off 201 is 380 and
   at hand-off 202 is 446 at both CONFIG_RSEQ flags (the recorded plans name 376 and
   442 there), and with this map the root and 201 plans reach their hand-offs at
   both flags.  The 202 plan is main's: an earlier port had put in its place the
   plan of another unit's binary (fuzz_json_cursor's, 91 memset nodes per branch
   where this binary's start-up makes 69), which the run refuses at both flags. *)
Definition planK_root_rec : plan :=
  PRun [] (PX XIMemset [] 
  (PRun [] (PX XEnvScan [] 
  (PRun [] (PX XPnScan [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PSys YSetTid 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0x141620] (PExt 98 [ELit 0; ELit 0x6be010; ELit 8] 
  (PRun [0x95070] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x93e38] (PX XIStrncpy [] 
  (PRun [0x93e38] (PX XIStrncpy [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0x89474] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x8949c] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x95070] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x9be98] (PFresh 9 12 None 
  (PRun [] (PMmapIn PContra 
  (PRun [0x8313c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x8313c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XMemIsZero [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PSys YMunmap 
  (PRun [0x9c3cc] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition planK_201_rec : plan :=
  PSplit (EVar 6) 10
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x8313c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202))))))))))))))))
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x8313c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202)))))))))))))))).

Definition planK_202_rec : plan :=
  PSys YBrk
 (PRun [] (PSplit (EVar 5) 0x7fff5
 (PBrk2
  (PRun [] (PMmap PContra 
  (PFact (KDisj (SA (ELit 0x7fff7000) 0) (ELit 0x100000001000) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 442)) (ELit 4096)) 0) (ELit 4096)) (PRun [] (PMprotect PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemset [] 
  (PRun [0xa2fa8] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (PRun [] (PMmapIn PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemset [] 
  (PRun [0xa2fa8] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 475)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 475)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) PContra)))
 (PSys YBrk
  (PRun [] (PMmap PContra 
  (PFact (KDisj (SA (ELit 0x7fff7000) 0) (ELit 0x100000001000) (SA (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 442)) (ELit 4096)) 0) (ELit 4096)) (PRun [] (PMprotect PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemset [] 
  (PRun [0xa2fa8] (PCase2 (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 4030
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   (PRun [0x6859c] (PJoin e_sp0 (-2280) 8 
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
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [0xb00b0] (PJoin (ELit 0) 4054672 4 (PJoin (ELit 0) 4067256 4 (PAbsWord (ELit 0) 2342344 8 2 3 (PAbsWord (ELit 0) 2342368 4 2 3 (PAbsWord (ELit 0) 4054672 4 0 1 (PAbsWord (ELit 0) 4067256 4 0 1 (PAbsWord (EMd Instr.M_MUL (ELit 4096) (EVar 476)) 16 8 0 18446744073709551615 (PHavoc [5; 6; 7; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat (PFact (KRange (EVar 376) 0 1) (PHandoff 1))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition vsh (v : nat) : nat := if Nat.ltb v 11 then v else v + 4.
Definition planK_root : plan := psh vsh planK_root_rec.
Definition planK_201 : plan := psh vsh planK_201_rec.
Definition planK_202 : plan := psh vsh planK_202_rec.

(* the checker at a flag, a hand-off table and a start state *)
Definition chkK (r : Z) (HS : nat -> option acs) (cs : acs) (p : plan) : cres :=
  APKF.check_fast ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT r XN0 XE0 XB0 HS KC0 BFUEL FUEL None cs p.

(* THE HAND-OFF TABLE SOLVER.  A run stops at the first hand-off it cannot pass:
   CErr 4 = no entry for hole h yet (record the state that reached it); CErr 3 at
   PHandoff h = the entry is not entailed by another branch's state (keep only the
   knowledge both carry).  [entails] (AsanPlanCoreK) compares every other field for
   EQUALITY, so a hole two branches reach with different registers or maps cannot
   be solved here and the certificate below it fails loudly. *)
Fixpoint tlook (T : list (nat * acs)) (h : nat) : option acs :=
  match T with [] => None | (h', c) :: T' => if Nat.eqb h h' then Some c else tlook T' h end.
Definition kmeet (ch cs : acs) : acs := set_kn ch (filter (fun K => existsb (kentry_eqb K) (kn cs)) (kn ch)).
Fixpoint solve (n : nat) (r : Z) (cs0 : acs) (p : plan) (T : list (nat * acs)) : list (nat * acs) :=
  match n with
  | O => T
  | S n' =>
      match chkK r (tlook T) cs0 p with
      | CErr 4 (PHandoff h) cs => solve n' r cs0 p ((h, cs) :: T)
      | CErr 3 (PHandoff h) cs =>
          solve n' r cs0 p (map (fun hc => if Nat.eqb (fst hc) h then (h, kmeet (snd hc) cs) else hc) T)
      | _ => T
      end
  end.
Definition tget (T : list (nat * acs)) (h : nat) : acs :=
  match tlook T h with Some c => c | None => init_acs_of 0 ASAN0 end.
Definition shape_of (c : cres) : shape := match c with COk s => s | _ => SHole 999 end.
