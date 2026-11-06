(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Tac InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells ABase AU_steptac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import ShadowTac.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac b2z_lia K :=
  exfalso;
  rewrite ?Z.add_0_l, ?Z.add_0_r, ?Z.sub_0_r in K;
  repeat match type of K with context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end;
  cbn [Z.b2z] in K;
  repeat match type of K with context [Z.lxor ?a ?b] => is_Zlit a; is_Zlit b; let v := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with v in K end;
  try (change 7 with (Z.ones 3) in K; rewrite !Z.land_ones in K by lia; change (2^3) with 8 in K);
  rewrite ?unsigned_lit in K by lia;
  first [lia | Z.div_mod_to_equations; lia].
Ltac ubf := let K := fresh "K" in if_cases K; zify_cond K; [solve [b2z_lia K]| clear K].
Ltac ubt := let K := fresh "K" in if_cases K; zify_cond K; [clear K| solve [b2z_lia K]].
Ltac bdec := first [ubf | ubt].
Ltac bshow := let K := fresh "K" in if_cases K; zify_cond K; [let T := type of K in idtac "KTRUE:" T| let T := type of K in idtac "KFALSE:" T].
Ltac unorm := progress (rewrite ?Z.add_0_l, ?Z.sub_0_r, ?Z.add_0_r).
Ltac usteps_to p := repeat (tryif at_pc p then fail else first [astep | bdec | unorm]);
  tryif at_pc p then idtac else (match goal with |- ?G => idtac "STUCK:" G end; try bshow; fail 1 "usteps_to: stuck before" p).
(* [comment removed for export] *)
Ltac showst := match goal with |- ?G => idtac G end; repeat match goal with H : rw_cells _ _ _ _ |- _ => let T := type of H in idtac "CELLS:" T; clear H end.
