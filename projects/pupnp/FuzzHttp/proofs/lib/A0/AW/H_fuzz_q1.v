(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.AW Require Import HttpAllocA HObjA HCount H_phdr PZDef.
Import ListNotations.
Open Scope Z_scope.

Section Q.
Context {HCEIL : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.

#[using="Type"] Lemma hdrs_mem_pure : forall (m : mem) (hs : list (HObjA.hdr FI AI)), HObjA.hdrs_mem FI AI m hs -> Forall (HObjA.hdro_pure FI AI) hs.
Proof.
  intros m hs. induction hs as [|h hs IH]; intros HM; [apply Forall_nil|].
  cbn [HObjA.hdrs_mem] in HM. destruct HM as (_ & HP & HM'). apply Forall_cons; [exact HP| exact (IH HM')].
Qed.

#[using="Type"] Lemma fuzz_q1 : forall (m : mem) (hs : list (HObjA.hdr FI AI)) (N0 Na N2 k c : Z),
  HObjA.hdrs_mem FI AI m hs -> Na <= N0 + 1 -> 0 <= k <= 2 * PZ_GMAX + 5 -> 0 <= c <= 2^26 - 1 ->
  H_phdr.hsumA FI AI hs <= c ->
  5 * (N2 - (k + 1)) <= 5 * Na - HCount.phiH FI AI [] + HCount.phiH FI AI hs ->
  N2 <= N0 + 13552000.
Proof.
  intros m hs N0 Na N2 k c HM HNa Hk Hc HS TG7.
  pose proof (HCount.phiH_le FI AI hs (hdrs_mem_pure m hs HM)) as PL.
  change (HCount.phiH FI AI []) with 0 in TG7.
  rewrite (H_phdr.hsumA_hlenA FI AI hs) in HS.
  clear HM. lia.
Qed.
End Q.
