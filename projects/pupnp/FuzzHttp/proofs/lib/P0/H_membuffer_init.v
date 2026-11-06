(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac STRW_tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Lemma membuffer_init_spec : membuffer_init_stmt rsegs PA.
Proof.
  unfold membuffer_init_stmt. intros until m. intros MBC AL MI Ha0.
  pose proof (munch_refl [(MB, MB + 32)%Z] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ MBC) as BND. cbn [cells_size csize] in BND.
  subst a0. cbn [ha_membuffer_init PA].
  step.
  step. fix_lit_store.
  step. fix_lit_store.
  step. fix_lit_store.
  step. fix_lit_store.
  step.
  finish.
Qed.
