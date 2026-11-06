(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0PlanImage H0Atable H0Sinv H0CheckG H0Chain H0Chain2 H0Hop H0Batch H0Fam.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Fam2 H0BatchF R2GS0 R2GCDc0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Lemma bB : (let it := APC.mk_itab_ranges HSEGS R2G_ranges in hbatch_ok LIM 100000 400 it (map jB ops)) = true.
Proof. apply hbatch_f_intro. ltac2:(cert_refl_vm constr:(true)). Qed.
