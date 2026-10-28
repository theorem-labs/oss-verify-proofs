(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocTree.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Export MallocBlocks MallocHINV.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Record block_ok (st : mstate) (b : block) : Prop := mkBO {
  (* [comment removed for export] *)
  bo_slot : exists g idx, (s_slots st) !! (blk_slot b) = Some (g, idx)
            /\ Z.testbit (m_avail (get_meta_rec st g)) idx = false
            /\ Z.testbit (m_freed (get_meta_rec st g)) idx = false
            /\ 0 <= idx <= m_last_idx (get_meta_rec st g)
            (* [comment removed for export] *)
            /\ (exists off, 0 <= off /\ blk_addr b = conc st (blk_slot b) + UNIT * off
                           /\ UNIT * off + blk_size b <= get_stride (get_meta_rec st g) - IB);
  (* [comment removed for export] *)
  bo_region : exists r, (s_regions st) !! (fst (blk_slot b)) = Some r /\ r_kind r = RKGroup;
  bo_size : 0 <= blk_size b
}.

(* [comment removed for export] *)

Definition sstart_of (mr : meta) (i : Z) : Z := snd (default (0%N, 0) (m_mem mr)) + UNIT + get_stride mr * i.

Definition fact_ctx (cs : mstate) : Prop :=
  0 <= c_mmap_counter (ctx cs) < 2^32 /\ 0 <= c_secret (ctx cs) < 2^64
  /\ (c_init_done (ctx cs) = 0 \/ c_init_done (ctx cs) = 1)
  /\ 0 <= c_seq (ctx cs) < 256
  /\ (forall i, 0 <= bounces cs i < 256) /\ (forall i, 0 <= unmap_seq cs i < 256).

Definition fact_active (cs : mstate) : Prop :=
  forall sc g, active cs sc = Some g ->
    0 <= sc < 48 /\ m_sizeclass (get_meta_rec cs g) = sc /\ m_mem (get_meta_rec cs g) <> None.

Definition fact_gmeta (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b ->
    let mr := get_meta_rec cs g in
    meta_slot cs g
    /\ 0 <= m_avail mr < 2^32 /\ 0 <= m_freed mr < 2^32
    /\ 0 <= m_last_idx mr <= 31 /\ m_freeable mr = 1
    /\ ((0 <= m_sizeclass mr < 48 /\ 0 <= m_maplen mr < 2^19) \/ (m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ 0 < m_maplen mr))
    /\ 0 <= m_maplen mr
    /\ (exists ai, (s_groups cs) !! b = Some (mkGhdr (Some g) ai) /\ 0 <= ai <= m_last_idx mr
                   /\ forall i, 0 <= i -> Z.testbit (m_avail mr) i = true -> i <= ai)
    /\ (exists r, (s_regions cs) !! (fst b) = Some r /\ r_kind r = RKGroup
                  /\ 0 <= snd b /\ snd b mod 16 = 0
                  /\ sstart_of mr (m_last_idx mr + 1) <= round_up_pg (r_len r))
    /\ UNIT <= get_stride mr /\ get_stride mr mod UNIT = 0
    (* [comment removed for export] *)
    /\ (m_sizeclass mr < 48 -> get_stride mr < 2^31)
    /\ (m_sizeclass mr < 48 -> forall i, 0 <= i -> Z.testbit (m_avail mr) i = true ->
          UNIT * size_class (m_sizeclass mr) <= get_stride mr)
    (* [comment removed for export] *)
    /\ (m_sizeclass mr < 48 -> get_stride mr * (m_last_idx mr + 1) < 2^20).

Definition fact_avail_clear (cs : mstate) (LB : list block) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i -> Z.testbit (m_avail (get_meta_rec cs g)) i = true ->
    let mr := get_meta_rec cs g in
    let lo := sstart_of mr i - IB in
    let hi := sstart_of mr i + get_stride mr - IB in
    (forall b' gh, (s_groups cs) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= lo \/ hi <= snd b')
    /\ (forall blk, In blk LB -> fst (blk_slot blk) = fst b ->
          exists r, (s_regions cs) !! (fst b) = Some r /\
          (blk_addr blk + blk_size blk <= r_base r + lo \/ r_base r + hi <= blk_addr blk)).

(* [comment removed for export] *)
Definition fact_free_clear (cs : mstate) (LB : list block) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i ->
    Z.testbit (m_avail (get_meta_rec cs g)) i = true \/ Z.testbit (m_freed (get_meta_rec cs g)) i = true ->
    let mr := get_meta_rec cs g in
    let lo := sstart_of mr i - IB in
    let hi := sstart_of mr i + get_stride mr - IB in
    (forall b' gh, (s_groups cs) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= lo \/ hi <= snd b')
    /\ (forall blk, In blk LB -> fst (blk_slot blk) = fst b ->
          exists r, (s_regions cs) !! (fst b) = Some r /\
          (blk_addr blk + blk_size blk <= r_base r + lo \/ r_base r + hi <= blk_addr blk)).

(* [comment removed for export] *)
Definition fact_hdr_clear (cs : mstate) (LB : list block) : Prop :=
  forall b gh blk r, (s_groups cs) !! b = Some gh -> In blk LB -> fst (blk_slot blk) = fst b ->
    (s_regions cs) !! (fst b) = Some r ->
    blk_addr blk + blk_size blk <= r_base r + snd b \/ r_base r + snd b + 16 <= blk_addr blk.

(* [comment removed for export] *)
Definition fact_usage (cs : mstate) : Prop := forall i, 0 <= usage cs i < 2^60.

(* [comment removed for export] *)
Definition fact_masks (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b ->
    let mr := get_meta_rec cs g in
    (forall i, 0 <= i -> Z.testbit (m_avail mr) i = true -> i <= m_last_idx mr)
    /\ (forall i, 0 <= i -> Z.testbit (m_freed mr) i = true -> i <= m_last_idx mr)
    /\ Z.land (m_avail mr) (m_freed mr) = 0.

(* [comment removed for export] *)
Definition fact_maplen (cs : mstate) : Prop :=
  forall g b, m_mem (get_meta_rec cs g) = Some b -> m_maplen (get_meta_rec cs g) < 2^40.

(* [comment removed for export] *)
Definition fact_slots (cs : mstate) : Prop :=
  forall p g idx, (s_slots cs) !! p = Some (g, idx) ->
    exists b, m_mem (get_meta_rec cs g) = Some b /\ fst p = fst b
              /\ snd p = sstart_of (get_meta_rec cs g) idx /\ 0 <= idx <= m_last_idx (get_meta_rec cs g).

(* [comment removed for export] *)
Definition fact_slots_complete (cs : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec cs g) = Some b -> 0 <= i <= m_last_idx (get_meta_rec cs g) ->
    (s_slots cs) !! (fst b, sstart_of (get_meta_rec cs g) i) = Some (g, i).

(* [comment removed for export] *)
Definition fact_ptrs (st : mstate) : Prop :=
  ptrs_in (fun rid => (rid < s_next_rid st)%N) st
  /\ (forall rid, (s_next_rid st <= rid)%N -> (s_regions st) !! rid = None /\ (s_shadow st) !! rid = None).

(* [comment removed for export] *)
Definition fact_blk_unknown (st : mstate) (LB : list block) : Prop :=
  forall blk r, In blk LB -> (s_regions st) !! (fst (blk_slot blk)) = Some r ->
    forall a, blk_addr blk <= a < blk_addr blk + blk_size blk ->
      exists h, cell_read (get_shadow st (fst (blk_slot blk))) (a - r_base r) = Unknown h.

(* [comment removed for export] *)
Definition fact_blocks_disjoint (st : mstate) (LB : list block) : Prop :=
  forall b1 b2, In b1 LB -> In b2 LB -> fst (blk_slot b1) = fst (blk_slot b2) -> blk_slot b1 <> blk_slot b2 ->
    blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

(* [comment removed for export] *)
Definition fact_hdr0 (st : mstate) : Prop :=
  forall g b i, m_mem (get_meta_rec st g) = Some b -> 0 <= i <= m_last_idx (get_meta_rec st g) + 1 ->
    cell_read (get_shadow st (fst b)) (sstart_of (get_meta_rec st g) i - IB) = Known 0.

(* [comment removed for export] *)
Definition fact_cell_ticks (st : mstate) : Prop :=
  forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t <= s_tick st)%N.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record MFACTS_g {resv : list (Z * Z)} (st : mstate) (LB : list block) : Prop := mkMF {
  mf_blocks : Forall (block_ok st) LB;
  (* [comment removed for export] *)
  mf_nodup : List.NoDup (map blk_slot LB);
  (* [comment removed for export] *)
  mf_ticks : ticks_ok st;
  (* [comment removed for export] *)
  mf_reserved : s_reserved st = resv;
  mf_ctx : fact_ctx (strip st);
  mf_active : fact_active (strip st);
  mf_gmeta : fact_gmeta (strip st);
  mf_avail_clear : fact_avail_clear (strip st) LB;
  mf_hdr0 : fact_hdr0 st;
  (* [comment removed for export] *)
  mf_free_clear : fact_free_clear (strip st) LB;
  mf_hdr_clear : fact_hdr_clear (strip st) LB;
  mf_usage : fact_usage (strip st);
  mf_masks : fact_masks (strip st);
  mf_maplen : fact_maplen (strip st);
  mf_slots : fact_slots (strip st);
  mf_slots_complete : fact_slots_complete (strip st);
  (* [comment removed for export] *)
  mf_ptrs : fact_ptrs st;
  mf_blk_unknown : fact_blk_unknown st LB;
  mf_blocks_disjoint : fact_blocks_disjoint st LB;
  (* [comment removed for export] *)
  mf_cell_ticks : fact_cell_ticks st
}.
End ACeilS1.


(* [comment removed for export] *)
Notation MFACTS := (@MFACTS_g agent_reserved).


(* [comment removed for export] *)
