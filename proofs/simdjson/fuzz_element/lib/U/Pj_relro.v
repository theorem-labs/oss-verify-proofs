(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import InitMem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Sj_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma pj_relro_cells : forall (m : word -> option byte) A bs,
  pj_relro m ->
  (PJ_RELRO_LO <= A /\ A + Z.of_nat (length bs) <= PJ_RELRO_SSP \/ PJ_RELRO_SSP + 8 <= A /\ A + Z.of_nat (length bs) <= PJ_RELRO_HI) ->
  InitMem.rw_bytes_b Image.usegs A bs = true ->
  rw_cells Image.usegs m A [CB (length bs) bs].
Proof.
  intros m A bs RN HA HB. apply (InitMem.rw_cells_image0 Image.usegs m A bs); [| exact HB| lia| lia].
  intros a Ha. pose proof (RN (bv_unsigned a) ltac:(lia)) as E. unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Ltac relro_chunk RN m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells Image.usegs m A cs);
  [ apply (InitMem.rw_cells_recast Image.usegs m A [CB (length bs) bs] cs);
    [ apply (pj_relro_cells m A bs RN); [cbn [length]; lia | vm_compute; reflexivity]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma pj_relro_selftest : forall m, pj_relro m ->
  rw_cells Image.usegs m PJ_WIDEN_SLOT [C8 (Z_to_bv 64 PJ_DO_WIDEN)] /\ rw_cells Image.usegs m PJ_NULSB_VT [C8 (Z_to_bv 64 PJ_XSPUTN)].
Proof.
  intros m RN.
  relro_chunk RN m constr:(PJ_WIDEN_SLOT) [C8 (Z_to_bv 64 PJ_DO_WIDEN)] H1.
  relro_chunk RN m constr:(PJ_NULSB_VT) [C8 (Z_to_bv 64 PJ_XSPUTN)] H2.
  exact (conj H1 H2).
Qed.
