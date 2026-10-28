(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr Bytes.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import Malloc_fp MallocKit_A2 F_malloc_big.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import MallocKit_A3.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.

Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).

Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => as_fm_link st0 g head
  | None => as_fm_single st0 h g
  end.

Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.

Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).

Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
  intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.

Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
  destruct HI as [E|HI]; [inversion E; subst; LiaTuning.ctauto|]. apply IH; LiaTuning.ctauto.
Qed.

Lemma sub_fp_single W lo hi : In (lo, hi) W -> sub_fp [(lo, hi)] W.
Proof. intros HI x HO. cbn. split; [exact (outside_In W x lo hi HO HI)| exact I]. Qed.

Section FAILM.
Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.

Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.
End FAILM.