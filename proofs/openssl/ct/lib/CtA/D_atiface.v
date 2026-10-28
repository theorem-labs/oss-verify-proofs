(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Nodes RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Canon Stdio.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_iface D_defs D_trpro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ATX_W : list (Z * Z) := [(0xbc9448, 0xbc944c); (0xbc9468, 0xbc9470); (0xbc9568, 0xbc9570)].

Section DAt.
Variable RT : rt_sig.
Variable XENV XENV1 : mem -> Prop.

Definition atexit_contract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  a0 = Z_to_bv 64 AEF_GUARD ->
  stk ctasegs m lo (bv_unsigned sp) -> lo + 128 <= bv_unsigned sp -> rt_sp0 RT Σ - STACK_WIN <= lo ->
  XENV m -> ART RT Σ m -> mem_inv ctasegs m ->
  cps ctasegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_atexit m)))
    (fun c => exists m',
        ASTA RT Σ (PMfd F0 fs0)
           (fun ms => ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
              /\ musl_after RT Σ (bv_unsigned sp) lo ATX_W m m' /\ XENV1 m') c).

End DAt.
