(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface D_defs Sj_akit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma fc_relayout : forall (m : mem) A cs1 cs2,
  rw_cells asegs m A cs1 -> cells_wf cs2 -> cells_bytes cs2 = cells_bytes cs1 -> cells_size cs2 = cells_size cs1 -> rw_cells asegs m A cs2.
Proof.
  intros m A cs1 cs2 ((W1 & B1) & WR) W2 EB ES. split; [split; [exact W2| rewrite EB; exact B1]| rewrite ES; exact WR].
Qed.

Lemma fc_le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Definition fc_einv (spq f A OUT lo : Z) (txt : list byte) (m0 : mem) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 : word) (pnsc : list cell) (mm : mem) : Prop :=
  rw_cells asegs mm spq (fc_spill f c0 c8 c16 c24 c32 c40 c48 c56 c64 c80) /\
  rw_cells asegs mm (f + 608) pnsc /\
  (exists jz, rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz]) /\
  rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] /\
  (exists v, rw_cells asegs mm OUT [C8 v]) /\
  bytes_at asegs mm A txt /\ mem_inv asegs mm /\ munch (fc_W lo spq f OUT) m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo spq.

Ltac fc_eopen H :=
  let jz := fresh "jz" in let v := fresh "v" in
  destruct H as (SPILL & PNS & (jz & BSH) & PSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fc_spill in SPILL; unfold fc_W in MU.
Ltac fc_eclose :=
  unfold fc_einv, fc_spill, fc_W;
  split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Definition FC_ERR2 : list Z := [0xe989c; 0xe9e08; 0xe9a80; 0xea37c; 0xea578].
