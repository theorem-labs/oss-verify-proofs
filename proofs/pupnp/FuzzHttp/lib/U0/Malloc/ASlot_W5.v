(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp MallocKit_A2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_A3 ASlot_W1.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition clr (r : meta) : meta := m_set_prev None (m_set_next None r).

Lemma dequeue_self_eq sc g st :
  m_next (get_meta_rec st g) = Some g ->
  dequeue (LActive sc) g st = put_meta g (clr (get_meta_rec st g)) (set_active sc None st).
Proof.
  intros GN. unfold dequeue. rewrite GN. cbn [optr_eqb negb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbn [negb set_head].
  rewrite upd_meta_put. reflexivity.
Qed.

Lemma dequeue_other_eq sc g nx pv st :
  m_next (get_meta_rec st g) = Some nx -> m_prev (get_meta_rec st g) = Some pv -> nx <> g -> pv <> g ->
  active st sc = Some g ->
  dequeue (LActive sc) g st =
    let st1 := put_meta pv (m_set_next (Some nx) (get_meta_rec st pv)) st in
    let st2 := put_meta nx (m_set_prev (Some pv) (get_meta_rec st1 nx)) st1 in
    let st3 := set_active sc (Some nx) st2 in
    put_meta g (clr (get_meta_rec st g)) st3.
Proof.
  intros GN GP NEn NEp HA. unfold dequeue. rewrite GN, GP. cbn [optr_eqb negb]. rewrite (aptr_eqb_neq nx g NEn). cbn [negb get_head set_head].
  rewrite !upd_meta_put.
  match goal with |- context [optr_eqb (active ?s sc) (Some g)] => change (active s sc) with (active st sc) end.
  rewrite HA. cbn [optr_eqb]. rewrite (proj2 (aptr_eqb_eq g g) eq_refl). cbv zeta.
  f_equal. f_equal. rewrite rec_set_active. rewrite (get_meta_rec_put_other _ nx) by (intros E; apply NEn; symmetry; exact E).
  rewrite (get_meta_rec_put_other _ pv) by (intros E; apply NEp; symmetry; exact E). reflexivity.
Qed.

Section DEQ.
Variables (st : mstate) (m : mem) (g : aptr) (sc : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis HA : active st sc = Some g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis FR0 : m_freed mr = 0.
End DEQ.