(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface I_qck F_achk I_vprintfw I_vprintf I_vsnfront I_vsnstmt I_vsnlift
     RT_state RT_rep RT_closed RT_iclifts R_isPoisoned TopA_iodefs TopA_io RT_io.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rta_vsn : forall Σ m, ART RTA Σ m -> vsncells m.
Proof.
  intros Σ m HA. pose proof (rta_io Σ m HA) as IO.
  pose proof (io_ro_at m IO 0x5ac318 _ ltac:(io_in)) as V1. apply ro_split1 in V1 as [_ V2]. apply ro_split1 in V2 as [_ V3].
  exact V3.
Qed.

Theorem printf_contracts_A : printf_contracts RTA.
Proof.
  exact (printf_contracts_ok RTA (rc_facts RTA rta_contracts_all) rip_proof rta_shw (rta_pf rta_io) rta_vsn).
Qed.

Theorem vsnprintf_contract_A : vsnprintf_icontract RTA.
Proof. exact (rc_vsnprintf RTA printf_contracts_A). Qed.

Theorem snprintf_contract_A : snprintf_icontract RTA.
Proof. exact (rc_snprintf RTA printf_contracts_A). Qed.
