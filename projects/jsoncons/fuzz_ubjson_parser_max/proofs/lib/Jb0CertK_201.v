(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Jb0DefsK Jb0HSK_201 Jb0HSK_202 Jb0ResK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition JS_as0_201 (h : nat) : option acs := if Nat.eqb h 202 then Some HS_202 else None.
Definition planK_201 : plan :=
PSplit (EVar 6) 10
(PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
(PRun [0x7a508] (PExt 95 []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PMmap PContra
(PRun [] (PX XMemcpy []
(PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202))))))))))))))))
(PFresh 10 12 (Some (eadd (escale 32768 (EVar 0)) (escale 4096 (EVar 10))))
(PRun [0x7a508] (PExt 95 []
(PRun [] (PX XMemset []
(PRun [] (PX XMemset []
(PRun [] (PMmap PContra
(PRun [] (PX XMemcpy []
(PRun [] (PFact (KRange (eaddz (esub (escale 16 (EVar 6)) (escale 4096 (EVar 376))) 3935) 0 4095) (PFact (KRange (EVar 376) 0 1) (PHavoc [1; 5; 6; 7; 28; 29; 30; 31]%nat (PHandoff 202)))))))))))))))).
Definition shape_201 : shape := (SCase (EVar 6) 10 (SHole 202) (SHole 202)).
Lemma cert_201 :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT XN0 XE0 XB0 JS_as0_201 KC0 BFUEL FUEL None HS_201 planK_201 = COk shape_201.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_201)). Qed.
