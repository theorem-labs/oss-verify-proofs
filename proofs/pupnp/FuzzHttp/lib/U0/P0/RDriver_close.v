(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib Startup RefImpl Stdio_iface Exit RDriver_kit RDriver_ctx RDriver_iface RF_main.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require F_printf_diag F_fwrite F_vfprintf F_stdio_exit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require RF_malloc_spec RF_free_spec.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import H_fuzz_stmt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma ps_get_set : forall (s : PState) so, ps_so (set_so_ps so s) = so.
Proof. intros [] so. reflexivity. Qed.
Lemma ps_set_set : forall (s : PState) so so', set_so_ps so' (set_so_ps so s) = set_so_ps so' s.
Proof. intros [] so so'. reflexivity. Qed.
Lemma ps_set_get : forall (s : PState), set_so_ps (ps_so s) s = s.
Proof. intros []. reflexivity. Qed.

Theorem exit_k_proof : exit_k_stmt.
Proof.
  unfold exit_k_stmt. intros A code s Q ms RX.
  destruct RX as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
                  & F & fc & m & lo & t & td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1
                  & -> & ST & TD & EXL & GF & FA & FIN & GCX & LC & DSO & [reg AX] & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Etp & Ea0 & Ht & LO & LOLO & SP47).
  unfold exit_k. eapply implM_bind with (Q1 := fun _ _ _ => False).
  - eapply (Exit.exit_spec ps_so set_so_ps (F_stdio_exit.stdio_exit_proof ps_so set_so_ps ps_get_set ps_set_set ps_set_get));
      [exact ST| exact TD| exact EXL| exact GF| exact FA| exact FIN| exact GCX | exact DSO | exact LC | exact AX| exact OFL| exact SIN| exact SOU| exact SEU
      | exact SOF| exact SEF| exact GG| exact GU| exact MI| exact Etp| exact Ea0| exact Ht| exact LO| exact LOLO| exact SP47].
  - intros e s' ms' X. destruct X.
Qed.

Theorem rmain_pre_closed {HGW : HasGuard} {HCEIL : HasCeiling} : rmain_pre_stmt.
Proof.
  exact (rmain_pre_proof
           RF_malloc_spec.rmalloc_spec
           RF_free_spec.rfree_spec_proof
           rauxv_init_proof
           (@F_printf_diag.fprintf_diag_proof PState)
           exit_k_proof
           (@F_fwrite.fwrite_diag_proof PState)
           F_vfprintf.towrite_proof).
Qed.
