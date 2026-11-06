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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition segsU : list Segment := Ubsan.M.loaded_segments.
Definition pcU : N := Ubsan.M.init_pc.
Definition phU : PhdrInfo := Ubsan.M.phdrs.
Definition imgU : Image := mkImage segsU pcU phU.
(* [comment removed for export] *)
Definition dataU_lo : Z := 0x28000.
Definition dataU_hi : Z := 0x5b000.

Definition S0_U : sstate := S0 (Z.of_N pcU) phU dataU_lo dataU_hi.

(* [comment removed for export] *)
Definition c0U (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) : config :=
  init_config segsU pcU phU sp brk mb draw lim inp.

Lemma dataU_ok : data_ok_b segsU dataU_lo dataU_hi = true.
Proof. vm_compute. reflexivity. Qed.

Lemma segs_topU : segs_top segsU = 0x5b000.
Proof. vm_compute. reflexivity. Qed.

Lemma pcU_val : Z.of_N pcU = 0x13338.
Proof. reflexivity. Qed.

Theorem init_smatch_U : forall sp brk mb draw lim inp,
  valid_entry48 imgU (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  exists rho, smatch segsU rho S0_U (w0 (c0U sp brk mb draw lim inp)) /\ Jinit segsU pcU phU sp draw inp rho.
Proof.
  intros sp brk mb draw lim inp [Hsp [_ [_ Hfit]]] Hinp.
  exists (rho0 segsU pcU phU sp draw inp). split.
  - apply (init_smatch0 segsU pcU phU dataU_lo dataU_hi dataU_ok).
    + unfold dataU_hi. lia.
    + rewrite segs_topU. lia.
    + exact Hsp.
    + exact Hinp.
    + exact Hfit.
  - apply Jinit_rho0.
Qed.
