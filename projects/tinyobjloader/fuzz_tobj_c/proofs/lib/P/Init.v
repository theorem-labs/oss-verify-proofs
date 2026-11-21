(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start state per CONFIG_RSEQ, taken at the run's flag; the launch conjunct in place of the entry-stack fit; the initial valuation and Jinit taking the mmap base). *)
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
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Plain.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition segsP : list Segment := Plain.M.loaded_segments.
Definition pcP : N := Plain.M.init_pc.
Definition phP : PhdrInfo := Plain.M.phdrs.
Definition imgP : Image := mkImage segsP pcP phP.
(* [comment removed for export] *)
Definition dataP_lo : Z := 0x28000.
Definition dataP_hi : Z := 0x5b000.

(* LPS 727298f3: the start state depends on the run's CONFIG_RSEQ (the auxv's length). *)
Definition S0_P (rs : bool) : sstate := S0 (Z.of_N pcP) phP dataP_lo dataP_hi rs.

(* [comment removed for export] *)
Definition c0P (sp brk mb : word) (draw : EntryDraw) (lim : Z) (inp : ProcInput) : config :=
  init_config segsP pcP phP sp brk mb draw lim inp.

Lemma dataP_ok : data_ok_b segsP dataP_lo dataP_hi = true.
Proof. vm_compute. reflexivity. Qed.

Lemma segs_topP : segs_top segsP = 0x5b000.
Proof. vm_compute. reflexivity. Qed.

Lemma pcP_val : Z.of_N pcP = 0x13268.
Proof. reflexivity. Qed.

Theorem init_smatch_P : forall sp brk mb draw lim inp,
  valid_entry48 imgP (mkEntry sp brk mb draw) inp -> valid_input_either inp ->
  exists rho, smatch segsP rho (S0_P (kb_rseq (in_kernel inp))) (w0 (c0P sp brk mb draw lim inp))
    /\ Jinit segsP pcP phP sp mb draw inp rho.
Proof.
  intros sp brk mb draw lim inp (Hsp & _ & _ & _ & Hlau) Hinp.
  exists (rho0 segsP pcP phP sp mb draw inp). split.
  - apply (init_smatch0 segsP pcP phP dataP_lo dataP_hi dataP_ok).
    + unfold dataP_hi. lia.
    + rewrite segs_topP. lia.
    + exact Hsp.
    + exact Hinp.
    + exact Hlau.
  - apply Jinit_rho0.
Qed.
