(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pcA : N := Asan.M.init_pc.
Definition phA : PhdrInfo := Asan.M.phdrs.
Definition imgA : Image := mkImage segsA pcA phA.
(* [comment removed for export] *)
Definition dataA_lo : Z := 0xe4000.
Definition dataA_hi : Z := 0x646000.

Definition S0_A : sstate := S0 (Z.of_N pcA) phA dataA_lo dataA_hi.

(* [comment removed for export] *)
Definition c0A (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) : config :=
  init_config segsA pcA phA sp brk mb draw lim inp.

Lemma dataA_ok' : data_ok_b segsA dataA_lo dataA_hi = true.
Proof. exact dataA_ok. Qed.

Lemma segs_topA : segs_top segsA = 0x646000.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma pcA_val : Z.of_N pcA = 0x3af9c.
Proof. reflexivity. Qed.

Theorem init_smatch_A : forall sp brk mb draw lim inp,
  valid_entry48 imgA (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  exists rho, smatch segsA rho S0_A (w0 (c0A sp brk mb draw lim inp)) /\ Jinit segsA pcA phA sp draw inp rho.
Proof.
  intros sp brk mb draw lim inp [Hsp [_ [_ Hfit]]] Hinp.
  exists (rho0 segsA pcA phA sp draw inp). split.
  - apply (init_smatch0 segsA pcA phA dataA_lo dataA_hi dataA_ok').
    + unfold dataA_hi. lia.
    + rewrite segs_topA. lia.
    + exact Hsp.
    + exact Hinp.
    + exact Hfit.
  - apply Jinit_rho0.
Qed.
