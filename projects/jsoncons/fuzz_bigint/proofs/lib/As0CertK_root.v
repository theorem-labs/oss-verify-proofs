(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the root run is checked at each value of the run's CONFIG_RSEQ flag, with the plan's fresh variables renumbered for the longer run (vsh_root), and the state it hands off at 201 is computed from that run (PlanRegenK.collect_handoffs), not recorded. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AxSymExec3K AsanPlanCoreK AsanPlanK AsanPlanFastK AsanNodesExtraDefsK AsanInitK As0DefsK As0ResK PlanRegenK.
Import ListNotations. Import AX2K. Import APCK. Import APK.
Open Scope Z_scope.
Definition planK_root : plan :=
  PRun [] (PX XIMemset [] 
  (PRun [] (PX XEnvScan [] 
  (PRun [] (PX XPnScan [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PSys YSetTid 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0xbd138] (PExt 98 [ELit 0; ELit 0x630d48; ELit 8] 
  (PRun [0x729a8] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x7178c] (PX XIStrncpy [] 
  (PRun [0x7178c] (PX XIStrncpy [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemset [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [] (PX XIMemcpy [] 
  (PRun [0x66dc8] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x66df0] (PDropRange (escale 4096 (EVar 94)) (ELit 65536) 
  (PRun [0x729a8] (PExt 97 [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x797d0] (PFresh 9 12 None 
  (PRun [] (PMmapIn PContra 
  (PRun [0x60fd0] (PExt 95 [] 
  (PRun [] (PX XMemset [] 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [] (PMmap PContra 
  (PRun [0x60fd0] (PExt 95 [] 
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
  (PRun [0x79d04] (PHandoff 201)))))))))))))))))))))))))))))))))))) PContra))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

Definition shape_root : shape := (SHole 201).
(* At LPS 727298f3 the root run is checked at each value
   [rz] of the run's CONFIG_RSEQ flag, and the state it hands off at 201 is
   computed here from that run, not recorded.

   The plan's one fresh-variable literal, [EVar 94], is four below the run's:
   [V_GID] and the readable auxv values add four fresh variables before it, so
   [vsh_root] maps [v >= 12 -> v + 4].  Where the plan names [EVar 94], the run's one mapping
   is [4096 * EVar 98], at both rz; with this map the run reaches handoff 201 at
   both rz. *)
Definition vsh_root (v : nat) : nat := if Nat.ltb v 12 then v else v + 4.
Definition planK_root_k : plan := psh vsh_root planK_root.

(* the state the root run hands off at 201, per rz *)
Definition HSL_root_0 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 4 (fun js => APKF.check_fast ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 0) planK_root_k) [].
Definition HS_201_0 : acs := hstate HSL_root_0 (asan0_init 0) 201.
Definition HSL_root_1 : list (nat * acs) := Eval vm_compute in
  collect_handoffs 4 (fun js => APKF.check_fast ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 js KC0 BFUEL FUEL None (asan0_init 1) planK_root_k) [].
Definition HS_201_1 : acs := hstate HSL_root_1 (asan0_init 1) 201.
Definition HS_201 (r : Z) : acs := if Z.eqb r 1 then HS_201_1 else HS_201_0.
Definition JS_as0_root (r : Z) (h : nat) : option acs := if Nat.eqb h 201 then Some (HS_201 r) else None.
Lemma cert_root_0 :
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 0 XN0 XE0 XB0 (JS_as0_root 0) KC0 BFUEL FUEL None (asan0_init 0) planK_root_k = COk shape_root.
Proof. rewrite <- APKF.check_fast_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root_1 :
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT 1 XN0 XE0 XB0 (JS_as0_root 1) KC0 BFUEL FUEL None (asan0_init 1) planK_root_k = COk shape_root.
Proof. rewrite <- APKF.check_fast_eq. vm_cast_no_check (@eq_refl cres (COk shape_root)). Qed.
Lemma cert_root : forall r, 0 <= r <= 1 ->
  check ASEGS0 IT0 ASAN0 NX0 AsanInitK.LIMIT r XN0 XE0 XB0 (JS_as0_root r) KC0 BFUEL FUEL None (asan0_init r) planK_root_k = COk shape_root.
Proof. intros r Hr. assert (r = 0 \/ r = 1) as [-> | ->] by lia; [exact cert_root_0 | exact cert_root_1]. Qed.
