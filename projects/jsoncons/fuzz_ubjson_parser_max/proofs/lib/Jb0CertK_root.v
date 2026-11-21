(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: cert_root now quantifies over a mode parameter r in {0,1} via cert_root_0/cert_root_1, using a node-shifted planK_root_k and handoff states HS_201 recomputed by collect_handoffs instead of importing Jb0HSK_201; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0CertK_root.v, lines 6, 72-92. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanPlanFastXK AsanNodesExtraDefsK AsanInitK Jb0DefsK Jb0ResK PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_root : plan :=
PRun [] (PX XIMemset []
(PRun [] (PX XEnvScan []
(PRun [] (PX XPnScan []
(PRun [] (PX XIMemcpy []
(PRun [] (PSys YSetTid
(PRun [] (PX XIMemcpy []
(PRun [0x115368] (PExt 98 [ELit 0; ELit 0x690b00; ELit 8]
(PRun [0x8c43c] (PExt 97 []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x8b204] (PX XIStrncpy []
(PRun [0x8b204] (PX XIStrncpy []
(PRun [] (PMmap PContra
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemset []
(PRun [] (PX XIMemcpy []
(PRun [] (PX XIMemcpy []
(PRun [0x80840] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
(PRun [0x80868] (PDropRange (escale 4096 (EVar 94)) (ELit 65536)
(PRun [0x8c43c] (PExt 97 []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x93264] (PFresh 9 12 None
(PRun [] (PMmapIn PContra
(PRun [0x7a508] (PExt 95 []
(PRun [] (PX XMemset []
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [] (PMmap PContra
(PRun [0x7a508] (PExt 95 []
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
(PRun [0x93798] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition shape_root : shape := (SHole 201).
Definition vsh_root (v : nat) : nat := if Nat.ltb v 12 then v else v + 4.
Definition planK_root_k : plan := psh vsh_root planK_root.
Definition HSL_root_0 : list (nat * acs) := Eval vm_compute in
collect_handoffs 4 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 0) planK_root_k) [].
Definition HS_201_0 : acs := hstate HSL_root_0 (asan0_init 0) 201.
Definition HSL_root_1 : list (nat * acs) := Eval vm_compute in
collect_handoffs 4 (fun js => APKX.check_fastx ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 1) planK_root_k) [].
Definition HS_201_1 : acs := hstate HSL_root_1 (asan0_init 1) 201.
Definition HS_201 (r : Z) : acs := if Z.eqb r 1 then HS_201_1 else HS_201_0.
Definition JS_as0_root (r : Z) (h : nat) : option acs := if Nat.eqb h 201 then Some (HS_201 r) else None.
Lemma cert_root_0 :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 (JS_as0_root 0) KC0 BFUEL FUEL None (asan0_init 0) planK_root_k = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root_1 :
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 (JS_as0_root 1) KC0 BFUEL FUEL None (asan0_init 1) planK_root_k = COk shape_root.
Proof. rewrite <- APKX.check_fastx_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root : forall r, 0 <= r <= 1 ->
check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT r XN0 XE0 XB0 (JS_as0_root r) KC0 BFUEL FUEL None (asan0_init r) planK_root_k = COk shape_root.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_root_0 | exact cert_root_1]. Qed.
