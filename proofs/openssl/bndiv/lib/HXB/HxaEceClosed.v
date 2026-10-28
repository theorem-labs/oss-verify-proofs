(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs W_fuzzA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaEceIface HxaEceMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ECE_STACK : Z := HxaEceIface.ECE_STACK.   (* [comment removed for export] *)
Definition ECE_COST : Z := HxaEceIface.ECE_COST.     (* [comment removed for export] *)

Lemma ECE_STACK_bounds : (0 <= ECE_STACK <= 0x18000)%Z.
Proof. unfold ECE_STACK, HxaEceIface.ECE_STACK. lia. Qed.
Lemma ECE_COST_nonneg : (0 <= ECE_COST)%Z.
Proof. unfold ECE_COST, HxaEceIface.ECE_COST. lia. Qed.

Theorem ece_cpsA_closed : forall AR : ARun, @W_fuzzA.ERR_clear_error_cpsA_stmt AR ECE_STACK ECE_COST.
Proof.
  intros AR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ ls OW LB EA lo
         HAH Hstk Hceil Hlo2 Hsp47 Hsp16 Hmi Etp Era Hs0 HCS HERR _ _ Hcred.
  exact (@ece_cps_AR AR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m Σ OW LB EA lo
           HAH Hstk Hceil Hlo2 Hsp47 Hsp16 Hmi Etp Era Hs0 HCS HERR Hcred).
Qed.
