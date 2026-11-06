(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv ASec AQuar AHeap ALedger AHeap2 ALinkPg ALinkVm ALink AVaOf AHeapLaws AHeapInst AFsEnv ABudgetL8.
Import ListNotations.
Open Scope Z_scope.

Section BI.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv) (FI : fs_if) (Bs : vmbase).
Hypothesis AO : alayout_ok AL.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis SP0S : alloc_ceiling + 2^23 + 184 <= 2^47.
Hypothesis FSEI : forall m, thread_env (al_thread AL) m -> fs_tls_env (at_thr (al_thread AL)) A0_DTV A0_TLSB (al_dtls AL) (al_fsb AL) m -> FSENV FI m.

#[using="Type"] Lemma am_budget_AI_B : forall s LB n, am_budget FI (AI_B AL E FI Bs AO FSBE SP0S FSEI) s LB n = budgetZ s LB n.
Proof. reflexivity. Qed.
End BI.
