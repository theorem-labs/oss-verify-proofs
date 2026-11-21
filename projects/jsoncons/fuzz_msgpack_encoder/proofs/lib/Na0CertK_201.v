(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the certificate is checked at both values of the kernel's rseq flag, the recorded plan is renumbered in the build by a map read from a probe of the run, and the hand-off states are computed in the build from the run instead of recorded; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0CertK_201.v, lines 6-10, 42-61. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0129 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PlanRegenK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0CertK_root.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.AsanPlanFastK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0129.AsanPlanFastXK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanNodesExtraDefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0ResK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0CertK_root OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_201 : plan :=
  PSplit (EVar 6) 10
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x81ab8] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202))))))))))))))))
 (PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
  (PRun [0x81ab8] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XMemcpy [] 
  (PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202)))))))))))))))).
Definition shape_201 : shape := (SCase (EVar 6) 10 (SHole 202) (SHole 202)).
Definition vsh_201 (v : nat) : nat := if Nat.ltb v 12 then v else v + 6.
Definition planK_201_k : plan := psh vsh_201 planK_201.
Definition HSL_201_0 : list (nat * acs) := Eval vm_compute in
collect_handoffs 6 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_201 0) planK_201_k) [].
Definition HS_202_0 : acs := hstate HSL_201_0 (HS_201 0) 202.
Definition HSL_201_1 : list (nat * acs) := Eval vm_compute in
collect_handoffs 6 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (HS_201 1) planK_201_k) [].
Definition HS_202_1 : acs := hstate HSL_201_1 (HS_201 1) 202.
Definition HS_202 (r : Z) : acs := if Z.eqb r 1 then HS_202_1 else HS_202_0.
Definition JS_as0_201 (r : Z) (h : nat) : option acs := if Nat.eqb h 202 then Some (HS_202 r) else None.
Lemma cert_201_0 :
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 0 XN0 XE0 XB0 (JS_as0_201 0) KC0 BFUEL FUEL None (HS_201 0) planK_201_k = COk shape_201.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_201)). Qed.
Lemma cert_201_1 :
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 1 XN0 XE0 XB0 (JS_as0_201 1) KC0 BFUEL FUEL None (HS_201 1) planK_201_k = COk shape_201.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_201)). Qed.
Lemma cert_201 : forall r, 0 <= r <= 1 ->
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT r XN0 XE0 XB0 (JS_as0_201 r) KC0 BFUEL FUEL None (HS_201 r) planK_201_k = COk shape_201.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_201_0 | exact cert_201_1]. Qed.
