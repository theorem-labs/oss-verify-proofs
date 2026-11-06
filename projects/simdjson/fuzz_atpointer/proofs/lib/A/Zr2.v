(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs Zpm Zr0 Zr1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition fc_inv3 (spq f A OUT lo : Z) (txt : list byte) (m0 : mem) (c0 c8 c16 c24 c32 c40 c64 c80 : word)
    (qw ww lmw : word) (negb vb tmb : byte) (ipw ilw fptw flw errw : word) (mm : mem) : Prop :=
  rw_cells asegs mm spq (fc_spill f c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80) /\
  (exists j5, rw_cells asegs mm (f + 608) (fc_pns qw ww lmw negb vb tmb j5 ipw ilw fptw flw errw)) /\
  rw_cells asegs mm (f / 8 + 2147450884) [CB 63 (repeat (Z_to_bv 8 0) 63)] /\
  rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] /\
  (exists v, rw_cells asegs mm OUT [C8 v]) /\
  bytes_at asegs mm A txt /\ mem_inv asegs mm /\ munch (fc_W lo spq f OUT) m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo spq.

Ltac fc_open3 H :=
  let j5 := fresh "j5" in let v := fresh "v" in
  destruct H as (SPILL & (j5 & PNS) & BSH & PSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fc_spill in SPILL; unfold fc_pns in PNS; unfold fc_W in MU.
Ltac fc_close3 :=
  unfold fc_inv3, fc_spill, fc_pns, fc_W;
  split; [eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.
