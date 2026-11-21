(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import InitMem Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz RefDeflateInitLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).

Definition Z_CFG_TABLEG : Z := 0x29388.

Definition cfg_faddr (lv : Z) : Z := if lv =? 0 then 0x17de4 else if lv <=? 3 then 0x18f8c else 0x19614.

Ltac cfg_row :=
  lazymatch goal with |- rw_cells _ ?m ?a ?cs0 =>
    let cs := fresh "cs" in pose (cs := cs0); change (rw_cells psegs m a cs);
    apply (InitMem.rw_cells_recast psegs m a [CB 16 (cells_bytes cs)] cs);
    [ apply (InitMem.rw_cells_image0 psegs m a (cells_bytes cs));
      [ intros x Hx; match goal with RC : _ |- _ => apply RC end; change (Z.of_nat (length (cells_bytes cs))) with 16 in Hx; lia
      | vm_compute; reflexivity | lia | change (Z.of_nat (length (cells_bytes cs))) with 16; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  end.

Lemma configG_relro : forall m lv, relro_clean m -> 0 <= lv <= 9 ->
  rw_cells psegs m (Z_CFG_TABLEG + 16 * lv)
    [C2 (wq (cfg_good lv)); C2 (wq (cfg_lazy lv)); C2 (wq (cfg_nice lv)); C2 (wq (cfg_chain lv)); C8 (wq (cfg_faddr lv))].
Proof.
  intros m lv RC H. unfold Z_CFG_TABLEG. unfold relro_clean, RELRO_LO, RELRO_HI in RC.
  assert (C : lv = 0 \/ lv = 1 \/ lv = 2 \/ lv = 3 \/ lv = 4 \/ lv = 5 \/ lv = 6 \/ lv = 7 \/ lv = 8 \/ lv = 9) by lia.
  destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]; cbn; cfg_row.
Qed.
