(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec CatExec CatSim StoreOk AgentLib.
Import ListNotations.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
(* [comment removed for export] *)
Definition bs_clob (r : bv 5) : bool := (bv_eqb r 11%bv || bv_eqb r 13%bv)%bool.

Definition bysizelog_spec (SEGS : list Segment) (entry exit_ : Z) : Prop :=
  forall mem (regs : bvmap 5 word) (i s : Z),
    0 <= i <= 63 -> 0 <= s -> s + 616 < 2 ^ 64 ->
    getr regs 11%bv = Z_to_bv 64 i -> getr regs 9%bv = Z_to_bv 64 s ->
    (forall a, s + 96 <= a < s + 616 -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true) ->
    exists regs' mem',
      msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
                  (mkst regs' (Z_to_bv 64 exit_) mem' (seg_rom SEGS))
      /\ (forall r, bs_clob r = false -> getr regs' r = getr regs r)
      /\ (forall x : word, bv_unsigned x < s + 96 \/ s + 616 <= bv_unsigned x -> mem' x = mem x)
      /\ mem_grows mem mem'.
End WithFP1.

