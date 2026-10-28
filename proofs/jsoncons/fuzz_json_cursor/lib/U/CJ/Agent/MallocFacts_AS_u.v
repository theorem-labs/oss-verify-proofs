(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import F_syscalls_u MallocRep_u MallocTree_u MallocFacts_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.Agent Require Import MallocNat_u.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import RunP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

Definition ta_fail (sc : Z) (st st1 : mstate) : Prop :=
  try_avail sc st kS bS = SRet (Some (st1, 0)).

Definition req_ok (sc req : Z) : Prop := 0 <= req /\ req + IB <= UNIT * size_class sc.

Inductive IST (st0 : mstate) : mstate -> Prop :=
| ist_top : forall t, (s_tick st0 < t)%N -> IST st0 (set_tick t st0)
| ist_am : forall o st sc st1 st2 m,
    IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 ->
    leaf_of o (alloc_meta st1 kS bS) (Some (st2, Some m)) ->
    IST st0 st2.

Definition ISTR (st0 st3 : mstate) : Prop :=
  exists o st f sc req idx,
    IST st0 st /\ 0 <= sc < 48 /\ req_ok sc req /\
    leaf_of o (alloc_slot full_lay f st sc req kS bS) (Some (st3, idx)).

Definition lmem (cs : mstate) (g : aptr) : Prop :=
  m_mem (get_meta_rec cs g) <> None /\ m_next (get_meta_rec cs g) <> None /\ m_prev (get_meta_rec cs g) <> None.

Definition fact_lists (cs : mstate) : Prop :=
  (forall sc g, active cs sc = Some g -> lmem cs g)
  /\ (forall g n, m_mem (get_meta_rec cs g) <> None -> m_next (get_meta_rec cs g) = Some n ->
        lmem cs n /\ m_sizeclass (get_meta_rec cs n) = m_sizeclass (get_meta_rec cs g))
  /\ (forall g p, m_mem (get_meta_rec cs g) <> None -> m_prev (get_meta_rec cs g) = Some p ->
        lmem cs p /\ m_sizeclass (get_meta_rec cs p) = m_sizeclass (get_meta_rec cs g)).

Definition fact_freelist (cs : mstate) : Prop :=
  forall h, c_free_meta_head (ctx cs) = Some h ->
    meta_slot cs h /\ m_mem (get_meta_rec cs h) = None /\ m_next (get_meta_rec cs h) <> None
    /\ exists p, m_prev (get_meta_rec cs h) = Some p /\ meta_slot cs p /\ m_mem (get_meta_rec cs p) = None
                 /\ m_next (get_meta_rec cs p) <> None.

Definition mw_ok (mr : meta) : Prop :=
  0 <= m_last_idx mr <= 31 /\ 0 <= m_freeable mr <= 1 /\ 0 <= m_sizeclass mr <= 63 /\ 0 <= m_maplen mr < 2^52.

Definition fact_mw (cs : mstate) : Prop :=
  forall g, mw_ok (get_meta_rec cs g) /\ 0 <= m_avail (get_meta_rec cs g) < 2^32 /\ 0 <= m_freed (get_meta_rec cs g) < 2^32.

Definition fact_host_stride (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> 0 <= m_sizeclass (get_meta_rec cs g) <= 27 ->
    get_stride (get_meta_rec cs g) = UNIT * size_class (m_sizeclass (get_meta_rec cs g)).

Definition fact_links (cs : mstate) : Prop :=
  forall g, lmem cs g ->
    (forall n, m_next (get_meta_rec cs g) = Some n -> m_prev (get_meta_rec cs n) = Some g)
    /\ (forall p, m_prev (get_meta_rec cs g) = Some p -> m_next (get_meta_rec cs p) = Some g).

Definition fact_sc0_full (cs : mstate) : Prop :=
  forall g b gh, m_mem (get_meta_rec cs g) = Some b -> (s_groups cs) !! b = Some gh ->
    m_sizeclass (get_meta_rec cs g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec cs g).

Definition fact_ghdr_unk (st : mstate) : Prop :=
  forall b gh o, (s_groups st) !! b = Some gh -> 0 <= o < 9 ->
    exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h.

Definition fact_bit_stride (cs : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i ->
    Z.testbit (m_avail (get_meta_rec cs g)) i || Z.testbit (m_freed (get_meta_rec cs g)) i = true ->
    m_sizeclass (get_meta_rec cs g) < 48 ->
    UNIT * size_class (m_sizeclass (get_meta_rec cs g)) <= get_stride (get_meta_rec cs g).

Record LFACTS (cs : mstate) : Prop := mkLF {
  lf_lists : fact_lists cs;
  lf_freelist : fact_freelist cs;
  lf_mw : fact_mw cs;
  lf_host_stride : fact_host_stride cs;
  lf_links : fact_links cs;
  lf_sc0_full : fact_sc0_full cs;
  lf_bit_stride : fact_bit_stride cs
}.

Record ISTF_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkISTF {
  isf_mf : @MFACTS_g resv st LB;
  isf_lf : LFACTS (strip st);
  isf_ghdr : fact_ghdr_unk st
}.

Definition nest_ok (m : aptr) (st3 : mstate) : Prop :=
  get_meta_rec st3 m = meta0
  /\ forall h, c_free_meta_head (ctx st3) = Some h -> h <> m /\ m_prev (get_meta_rec st3 h) <> Some m.

Definition AMP_AS_g (resv : list (Z * Z)) (am_pre : mstate -> Prop) : Prop :=
  forall st0 LB st sc st1, AREACH_from resv st0 LB -> IST st0 st -> 0 <= sc < 48 -> ta_fail sc st st1 -> am_pre st1.
End CEIL_WRAP_1.

