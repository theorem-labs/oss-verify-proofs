(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Eb0DefsK Eb0HSK_201 Eb0ResK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition JS_as0_root (h : nat) : option acs := if Nat.eqb h 201 then Some HS_201 else None.
Definition planK_root : plan :=
  PRun [] (PX XIMemset []
  (PRun [] (PX XEnvScan []
  (PRun [] (PX XPnScan []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PSys YSetTid
  (PRun [] (PX XIMemcpy []
  (PRun [0x11e7b0] (PExt 98 [ELit 0; ELit 0x69a1c0; ELit 8]
  (PRun [0x8dc70] (PExt 97 []
  (PRun [] (PMmap PContra
  (PRun [] (PMmap PContra
  (PRun [] (PMmap PContra
  (PRun [0x8ca38] (PX XIStrncpy []
  (PRun [0x8ca38] (PX XIStrncpy []
  (PRun [] (PMmap PContra
  (PRun [] (PX XIMemset []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PX XIMemset []
  (PRun [] (PX XIMemcpy []
  (PRun [] (PX XIMemcpy []
  (PRun [0x82074] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
  (PRun [0x8209c] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
  (PRun [0x8dc70] (PExt 97 []
  (PRun [] (PMmap PContra
  (PRun [] (PMmap PContra
  (PRun [0x94a98] (PFresh 9 12 None
  (PRun [] (PMmapIn PContra
  (PRun [0x7bd3c] (PExt 95 []
  (PRun [] (PX XMemset []
  (PRun [] (PMmap PContra
  (PRun [] (PMmap PContra
  (PRun [] (PMmap PContra
  (PRun [0x7bd3c] (PExt 95 []
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
  (PRun [0x94fcc] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition shape_root : shape := (SHole 201).
Lemma cert_root :
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT XN0 XE0 XB0 JS_as0_root KC0 BFUEL FUEL None asan0_init planK_root = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
