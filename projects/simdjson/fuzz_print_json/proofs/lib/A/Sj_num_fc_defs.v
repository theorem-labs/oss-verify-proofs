(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition fc_W (lo spq f OUT : Z) : list (Z * Z) :=
  [(lo, spq + 88); (f + 32, f + 536); (f + 608, f + 680); (f / 8 + 2147450884, f / 8 + 2147450947); (OUT, OUT + 8)].

Definition fc_spill (f : Z) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 : word) : list cell :=
  [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 (Z_to_bv 64 f); C8 c80].

Definition fc_pinv (spq f A OUT lo : Z) (txt : list byte) (m0 : mem) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 : word) (mm : mem) : Prop :=
  rw_cells asegs mm spq (fc_spill f c0 c8 c16 c24 c32 c40 c48 c56 c64 c80) /\
  (exists jp, rw_cells asegs mm (f + 608) [CB 72 jp]) /\
  (exists jz, rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz]) /\
  rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] /\
  (exists v, rw_cells asegs mm OUT [C8 v]) /\
  bytes_at asegs mm A txt /\ mem_inv asegs mm /\ munch (fc_W lo spq f OUT) m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo spq.

Ltac fc_popen H :=
  let jp := fresh "jp" in let jz := fresh "jz" in let v := fresh "v" in
  destruct H as (SPILL & (jp & PNS) & (jz & BSH) & PSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fc_spill in SPILL; unfold fc_W in MU.
Ltac fc_pclose :=
  unfold fc_pinv, fc_spill, fc_W;
  split; [eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Definition FC_ERRA : list Z := [0xe4654; 0xe4bc0].

Definition FC_ERRB : list Z := [0xe4838; 0xe5134; 0xe5330].
