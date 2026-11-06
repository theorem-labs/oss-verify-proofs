(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface D_defs Sj_akit Sj_num_fc_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition fc_pns (qw ww lmw : word) (negb vb tmb : byte) (j5 : list byte) (ipw ilw fptw flw errw : word) : list cell :=
  [C8 qw; C8 ww; C8 lmw; C1 negb; C1 vb; C1 tmb; CB 5 j5; C8 ipw; C8 ilw; C8 fptw; C8 flw; C8 errw].

Definition fc_inv2g (spq f A OUT lo : Z) (txt : list byte) (m0 : mem) (c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 : word)
    (qw ww lmw : word) (negb vb tmb : byte) (ipw ilw fptw flw errw : word) (mm : mem) : Prop :=
  rw_cells asegs mm spq (fc_spill f c0 c8 c16 c24 c32 c40 c48 c56 c64 c80) /\
  (exists j5, rw_cells asegs mm (f + 608) (fc_pns qw ww lmw negb vb tmb j5 ipw ilw fptw flw errw)) /\
  (exists jz, rw_cells asegs mm (f / 8 + 2147450884) [CB 63 jz]) /\
  rw_cells asegs mm (f / 8 + 2147450956) [CB 9 (repeat (Z_to_bv 8 0) 9)] /\
  (exists v, rw_cells asegs mm OUT [C8 v]) /\
  bytes_at asegs mm A txt /\ mem_inv asegs mm /\ munch (fc_W lo spq f OUT) m0 mm /\ wmono asegs m0 mm /\ stk asegs mm lo spq.
Definition fc_inv2 (spq f A OUT lo : Z) (txt : list byte) (m0 : mem) (c0 c8 c16 c24 c32 c40 c64 c80 : word)
    (qw ww lmw : word) (negb vb tmb : byte) (ipw ilw fptw flw errw : word) (mm : mem) : Prop :=
  fc_inv2g spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 qw ww lmw negb vb tmb ipw ilw fptw flw errw mm.

Ltac fc_open2 H :=
  unfold fc_inv2, fc_inv2g in H;
  let j5 := fresh "j5" in let jz := fresh "jz" in let v := fresh "v" in
  destruct H as (SPILL & (j5 & PNS) & (jz & BSH) & PSH & (v & OUTC) & TXT & MI & MU & WM & ST);
  unfold fc_spill in SPILL; unfold fc_pns in PNS; unfold fc_W in MU.
Ltac fc_close2 :=
  unfold fc_inv2, fc_inv2g, fc_spill, fc_pns, fc_W;
  split; [eassumption|]; split; [eexists; eassumption|]; split; [eexists; eassumption|]; split; [eassumption|]; split; [eexists; eassumption|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.

Lemma fc_inv2g_pinv : forall spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 qw ww lmw negb vb tmb ipw ilw fptw flw errw mm,
  fc_inv2g spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 qw ww lmw negb vb tmb ipw ilw fptw flw errw mm ->
  fc_pinv spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm.
Proof.
  intros until mm. intros (H1 & (j5 & H2) & H3).
  split; [exact H1|]. split; [| exact H3].
  destruct (rw_cells_forget asegs mm _ _ H2) as [j Hj]. exists j. exact Hj.
Qed.
Lemma fc_inv2_pinv : forall spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb ipw ilw fptw flw errw mm,
  fc_inv2 spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 c64 c80 qw ww lmw negb vb tmb ipw ilw fptw flw errw mm ->
  fc_pinv spq f A OUT lo txt m0 c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm.
Proof. intros until mm. intros H. exact (fc_inv2g_pinv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H). Qed.
