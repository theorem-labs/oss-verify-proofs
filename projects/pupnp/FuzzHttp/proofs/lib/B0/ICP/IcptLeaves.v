(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit M_ctype M_htons M_errno_location.
Import ListNotations.
Open Scope Z_scope.

Section L.
Context {HC : HasCeiling}.

#[using="Type"] Lemma ic_tolower_proof : tolower_stmt_A.
Proof.
  intros until c. intros Hc -> MI. unfold A0_tolower.
  assert (E : bv_unsigned (Z_to_bv 64 c) = c) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply tolower_spec; [rewrite E; lia| exact MI]. }
  intros ms' Q. unfold ctype_post in Q. rewrite E in Q. exact Q.
Qed.

#[using="Type"] Lemma ic_htons_proof : htons_stmt_A.
Proof.
  intros until m. intros Hc MI. unfold A0_htons.
  eapply evt_mono.
  { eapply htons_spec; [exact Hc| exact MI]. }
  intros ms' Q. exact Q.
Qed.

#[using="Type"] Lemma ic_errno_location_proof : errno_location_stmt_A.
Proof.
  intros until m. intros Htp MI. unfold A0_errno_location.
  eapply evt_mono.
  { eapply errno_location_spec; [exact Htp| exact MI]. }
  intros ms' Q. exact Q.
Qed.
End L.
