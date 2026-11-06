(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Ja0DefsK Ja0HSK_201 Ja0ResK.
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
(PRun [0x113530] (PExt 98 [ELit 0; ELit 0x68edc0; ELit 8]
(PRun [0x8c16c] (PExt 97 []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x8af34] (PX XIStrncpy []
(PRun [0x8af34] (PX XIStrncpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [0x80570] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
(PRun [0x80598] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
(PRun [0x8c16c] (PExt 97 []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x92f94] (PFresh 9 12 None
(PRun [] (PMmapIn PContra
(PRun [0x7a238] (PExt 95 []
(PRun [] (PX XMemset []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x7a238] (PExt 95 []
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
(PRun [0x934c8] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition shape_root : shape := (SHole 201).
Lemma cert_root :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT XN0 XE0 XB0 JS_as0_root KC0 BFUEL FUEL None asan0_init planK_root = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
