(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac STRW_tac.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs HU_list_kit.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Lemma membuffer_init_spec : forall (MB : Z) (junk : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells rsegs m MB [CB 32%nat junk] -> (MB mod 8 = 0)%Z -> (0 < MB)%Z ->
  mem_inv rsegs m -> a0 = wz MB ->
  evt rsegs (membuffer_init_post rsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MB m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz (ha_membuffer_init UA)) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MBC AL NZ MI Ha0.
  pose proof (munch_refl [(MB, MB + 32)%Z] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (rw_cells_bound rsegs _ _ _ MBC) as BND. cbn [cells_size csize] in BND.
  subst a0. cbn [ha_membuffer_init UA].
  ub_null. ub_align.
  step.
  step. fix_lit_store.
  step. fix_lit_store.
  step. fix_lit_store.
  step. fix_lit_store.
  step.
  finish.
Qed.
