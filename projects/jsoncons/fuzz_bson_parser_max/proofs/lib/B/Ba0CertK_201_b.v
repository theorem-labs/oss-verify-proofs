(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed JS_as0_201, cert_201; added HSL_201_0, HSL_201_1, HS_202 and 6 more; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0CertK_201.v, lines 6, 42-61. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK PlanRegenK. From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0ResK_b Ba0CertK_root_b.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_201 : plan :=
  PSplit (EVar 6) 10
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x7ab90] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202))))))))))))))))
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x7ab90] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202)))))))))))))))).

Definition shape_201 : shape := (SCase (EVar 6) 10 (SHole 202) (SHole 202)).
(* At LPS 727298f3 the 201 run starts from the computed [HS_201 r]
   ([Ba0CertK_root_b.v]) at each rz, and the state it hands off at 202 is
   computed here, not recorded.  The plan names one fresh variable of the root
   run, [EVar 376]; the root run now allocates 6 more ([HS_201 r]'s counter is 382, the recorded state's was 376,
   in a probe run), so [v >= 12 -> v + 6].  The plan splits into two arms and the
   state at 202 is the join of the two arms' states
   ([PlanRegenK.collect_handoffs], [join_states]). *)
Definition vsh_201 (v : nat) : nat := if Nat.ltb v 12 then v else v + 6.
Definition planK_201_k : plan := psh vsh_201 planK_201.

Definition HSL_201_0 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 6 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_201 0) planK_201_k) [].
Definition HS_202_0 : acs := hstate HSL_201_0 (HS_201 0) 202.
Definition HSL_201_1 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 6 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_201 1) planK_201_k) [].
Definition HS_202_1 : acs := hstate HSL_201_1 (HS_201 1) 202.
Definition HS_202 (r : Z) : acs := if Z.eqb r 1 then HS_202_1 else HS_202_0.
Definition JS_as0_201 (r : Z) (h : nat) : option acs := if Nat.eqb h 202 then Some (HS_202 r) else None.
Lemma cert_201_0 :
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 (JS_as0_201 0) KC0 BFUEL FUEL None (HS_201 0) planK_201_k = COk shape_201.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_201)). Qed.
Lemma cert_201_1 :
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 (JS_as0_201 1) KC0 BFUEL FUEL None (HS_201 1) planK_201_k = COk shape_201.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_201)). Qed.
Lemma cert_201 : forall r, 0 <= r <= 1 ->
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT r XN0 XE0 XB0 (JS_as0_201 r) KC0 BFUEL FUEL None (HS_201 r) planK_201_k = COk shape_201.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_201_0 | exact cert_201_1]. Qed.
