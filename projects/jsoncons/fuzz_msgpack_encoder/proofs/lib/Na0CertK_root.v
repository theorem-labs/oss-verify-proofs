(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the certificate is checked at both values of the kernel's rseq flag, the recorded plan is renumbered in the build by a map read from a probe of the run, and the hand-off states are computed in the build from the run instead of recorded; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0CertK_root.v, lines 6-10, 72-92. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0129 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PlanRegenK.
Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.AsanPlanFastK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0129.AsanPlanFastXK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanNodesExtraDefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0ResK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_root : plan :=
  PRun [] (PX XIMemset [] 
  (PRun [] (PX XEnvScan [] 
  (PRun [] (PX XPnScan [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PSys YSetTid 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0x1378d4] (PExt 98 [ELit 0; ELit 0x6b3b40; ELit 8] 
  (PRun [0x939ec] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x927b4] (PX XIStrncpy [] 
  (PRun [0x927b4] (PX XIStrncpy [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0x87df0] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x87e18] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x939ec] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x9a814] (PFresh 9 12 None 
  (PRun [] (PMmapIn PContra 
  (PRun [0x81ab8] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x81ab8] (PExt 95 [] 
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
  (PRun [0x9ad48] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition shape_root : shape := (SHole 201).
Definition vsh_root (v : nat) : nat := if Nat.ltb v 12 then v else v + 4.
Definition planK_root_k : plan := psh vsh_root planK_root.
Definition HSL_root_0 : list (nat * acs) := Eval vm_compute in
collect_handoffs 4 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 0) planK_root_k) [].
Definition HS_201_0 : acs := hstate HSL_root_0 (asan0_init 0) 201.
Definition HSL_root_1 : list (nat * acs) := Eval vm_compute in
collect_handoffs 4 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 1) planK_root_k) [].
Definition HS_201_1 : acs := hstate HSL_root_1 (asan0_init 1) 201.
Definition HS_201 (r : Z) : acs := if Z.eqb r 1 then HS_201_1 else HS_201_0.
Definition JS_as0_root (r : Z) (h : nat) : option acs := if Nat.eqb h 201 then Some (HS_201 r) else None.
Lemma cert_root_0 :
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 0 XN0 XE0 XB0 (JS_as0_root 0) KC0 BFUEL FUEL None (asan0_init 0) planK_root_k = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root_1 :
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT 1 XN0 XE0 XB0 (JS_as0_root 1) KC0 BFUEL FUEL None (asan0_init 1) planK_root_k = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root : forall r, 0 <= r <= 1 ->
check ASEGS0 IT0 ASAN0 NX0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK.LIMIT r XN0 XE0 XB0 (JS_as0_root r) KC0 BFUEL FUEL None (asan0_init r) planK_root_k = COk shape_root.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_root_0 | exact cert_root_1]. Qed.
