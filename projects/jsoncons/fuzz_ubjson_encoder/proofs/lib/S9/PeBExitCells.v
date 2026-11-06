(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmStatics PmStaticsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCStaticsA Eb0ExitCells.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEBXC.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Definition axmap (e : bool) : axv := if e then AXc else AX0.

Lemma atexit_cells_of_st M e : PESTA.atexit_stA RSEGS AD AAD EE M e -> atexit_cellsA M (axmap e).
Proof.
  unfold PESTA.atexit_stA, HAJ.atexit_cells.
  cbn [pa_atexit paa_atexit_f0 paa_atexit_a0 paa_at_cxa_atexit pe_drv_call pe_drv_guard pa_errcat_dtor pa_errcat_obj AD AAD EE PeCLayoutB.CADDR_B PeCLayoutB.CAADDR_B PeCLayoutB.EADDR_B].
  unfold atexit_cellsA, AX_CELLS, ax_cell, axmap.
  destruct e; cbn [PESTA.ax_list length Z.of_nat Z.mul Z.add Pos.of_succ_nat Pos.mul Pos.add Pos.succ];
    intros (_ & C4 & C8 & C16 & C24 & C32 & C288 & C40 & C296 & EXT).
  - destruct (EXT 0%nat _ _ eq_refl) as (E1 & E2 & E3 & E4). cbn [Z.of_nat Z.mul Z.add] in E1, E2, E3, E4.
    repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
  - repeat apply Forall_cons; cbn [fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; try apply Forall_nil; assumption.
Qed.

Theorem lsx_atexit : forall (g : PMST.st) (M : word -> option byte),
  LibIface.ls_ok (PESTA.TopLSA RSEGS AD AAD EE) g M -> exists ax : axv, atexit_cellsA M ax.
Proof.
  intros g M OK. exists (axmap (PMST.st_err g)). apply atexit_cells_of_st. exact (PESTA.pe_statics_exitA RSEGS AD AAD EE g M OK).
Qed.
End PEBXC.
