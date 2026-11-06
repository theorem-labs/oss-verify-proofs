(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Do. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QoSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Module OM := QZDE.
Module OS := QEpW.
Module OC := QbVh.
Module OF := QWxq_c1.
Module OT := QlEo_c1.
Module DM := QCUT.
Module DS := QUcd.
Module DC := QMow.
Module DF := Q0Do.
Module DT := QoSL.

Definition cellD (c : OC.cell) : DC.cell :=
match c with OC.C8 v => DC.C8 v | OC.C4 v => DC.C4 v | OC.C2 v => DC.C2 v | OC.C1 b => DC.C1 b | OC.CB n bs => DC.CB n bs end.
Definition cellO (c : DC.cell) : OC.cell :=
match c with DC.C8 v => OC.C8 v | DC.C4 v => OC.C4 v | DC.C2 v => OC.C2 v | DC.C1 b => OC.C1 b | DC.CB n bs => OC.CB n bs end.

Lemma cells_size_D : forall cs, DC.cells_size (map cellD cs) = OC.cells_size cs.
Proof. induction cs as [|c cs IH]; [reflexivity|]. cbn [map DC.cells_size OC.cells_size]. rewrite IH. destruct c; reflexivity. Qed.

Lemma cells_bytes_D : forall cs, DC.cells_bytes (map cellD cs) = OC.cells_bytes cs.
Proof. induction cs as [|c cs IH]; [reflexivity|]. cbn [map DC.cells_bytes OC.cells_bytes]. rewrite IH. destruct c; reflexivity. Qed.

Lemma cells_wf_D : forall cs, OC.cells_wf cs <-> DC.cells_wf (map cellD cs).
Proof.
induction cs as [|c cs IH]; [reflexivity|]. cbn [map OC.cells_wf DC.cells_wf]. rewrite IH. destruct c; reflexivity.
Qed.

Lemma cells_at_D : forall segs m A cs, OC.cells_at segs m A cs <-> DC.cells_at segs m A (map cellD cs).
Proof.
intros segs m A cs. unfold OC.cells_at, DC.cells_at. rewrite cells_bytes_D, <- cells_wf_D. reflexivity.
Qed.

Theorem ro_cells_D : forall segs m A cs, OT.ro_cells segs m A cs <-> DT.ro_cells segs m A (map cellD cs).
Proof. intros. unfold OT.ro_cells, DT.ro_cells. apply cells_at_D. Qed.

Theorem rw_cells_D : forall segs m A cs, OT.rw_cells segs m A cs <-> DT.rw_cells segs m A (map cellD cs).
Proof. intros. unfold OT.rw_cells, DT.rw_cells. rewrite cells_size_D, <- cells_at_D. reflexivity. Qed.
