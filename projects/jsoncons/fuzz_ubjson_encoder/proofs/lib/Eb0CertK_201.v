(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the certificate is checked at each value of the run's CONFIG_RSEQ flag, its plan's fresh variables are renumbered by a map read from a probe of this unit's run, and its hand-off states are computed in the build; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0CertK_201.v, lines 43-61. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Eb0DefsK Eb0ResK Eb0CertK_root PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_201 : plan :=
  PSplit (EVar 6) 10
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x7bd3c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202))))))))))))))))
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x7bd3c] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202)))))))))))))))).

Definition shape_201 : shape := (SCase (EVar 6) 10 (SHole 202) (SHole 202)).
(* The plan names a fresh variable of the root run ([EVar 376]); that run now
   allocates six more, so [v >= 11 -> v + 6].  Read from this unit's probe of the run. *)
Definition vsh_201 (v : nat) : nat := if Nat.ltb v 11 then v else v + 6.
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
