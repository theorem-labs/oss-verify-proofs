(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import MallocRep MallocTree MallocBlocks.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition sstart_of (mr : meta) (i : Z) : Z := snd (default (0%N, 0) (m_mem mr)) + UNIT + get_stride mr * i.
End ACeilS1.


(* [comment removed for export] *)
(* [comment removed for export] *)

Notation rec st m := (get_meta_rec st m) (only parsing).
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Definition hosts (st : mstate) (b g : aptr) : Prop := exists ai, (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Definition is_gm (st : mstate) (g : aptr) : Prop := exists b, hosts st b g.

Definition slot_free (mr : meta) (i : Z) : Prop :=
  Z.testbit (m_freed mr) i = true \/ Z.testbit (m_avail mr) i = true.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record ci_links_t (st : mstate) : Prop := mkCL {
  cl_next : forall m nx, m_next (get_meta_rec st m) = Some nx ->
              m_prev (get_meta_rec st nx) = Some m /\ meta_slot st nx;
  cl_prev : forall m pv, m_prev (get_meta_rec st m) = Some pv ->
              m_next (get_meta_rec st pv) = Some m /\ meta_slot st pv;
  cl_none : forall m, m_next (get_meta_rec st m) = None <-> m_prev (get_meta_rec st m) = None;
  (* [comment removed for export] *)
  cl_self : forall m, m_next (get_meta_rec st m) <> None -> meta_slot st m
}.

(* [comment removed for export] *)
Record ci_heads_t (st : mstate) : Prop := mkCH {
  ch_free : forall h, c_free_meta_head (ctx st) = Some h ->
              m_next (get_meta_rec st h) <> None /\ m_mem (get_meta_rec st h) = None;
  ch_active : forall sc a, active st sc = Some a ->
              0 <= sc < 48 /\ m_next (get_meta_rec st a) <> None /\ is_gm st a /\ m_sizeclass (get_meta_rec st a) = sc
}.

(* [comment removed for export] *)
Definition ci_homog (st : mstate) : Prop :=
  forall m nx, m_next (get_meta_rec st m) = Some nx ->
    (is_gm st m <-> is_gm st nx)
    /\ (is_gm st m -> m_sizeclass (get_meta_rec st nx) = m_sizeclass (get_meta_rec st m)).

(* [comment removed for export] *)
Definition hdr_known (st : mstate) (p b1 : aptr) (i1 : Z) : Prop :=
  exists v3 lo hi,
    cell_read (get_shadow st (fst p)) (snd p - 3) = Known v3 /\ Z.land v3 31 = i1
    /\ cell_read (get_shadow st (fst p)) (snd p - 2) = Known lo
    /\ cell_read (get_shadow st (fst p)) (snd p - 1) = Known hi
    /\ 16 * (lo + 256 * hi) = snd p - snd b1 - 16.

(* [comment removed for export] *)
Record gmeta_ok (st : mstate) (g b : aptr) : Prop := mkGO {
  go_slot : meta_slot st g;
  go_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  go_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  go_li : 0 <= m_last_idx (get_meta_rec st g) <= 31;
  go_freeable : m_freeable (get_meta_rec st g) = 1;
  go_sc : (0 <= m_sizeclass (get_meta_rec st g) < 48)
          \/ (m_sizeclass (get_meta_rec st g) = 63 /\ m_last_idx (get_meta_rec st g) = 0 /\ 0 < m_maplen (get_meta_rec st g));
  go_maplen : 0 <= m_maplen (get_meta_rec st g) < 2^35;
  (* [comment removed for export] *)
  go_bits : forall i, 0 <= i ->
      (Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g))
      /\ (Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g));
  go_mem : m_mem (get_meta_rec st g) = Some b;
  go_region : exists r, (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup
      /\ 0 <= snd b /\ snd b mod 16 = 0
      /\ sstart_of (get_meta_rec st g) (m_last_idx (get_meta_rec st g) + 1) <= round_up_pg (r_len r)   (* [comment removed for export] *)
      /\ (m_maplen (get_meta_rec st g) <> 0 -> snd b = 0 /\ m_maplen (get_meta_rec st g) * 4096 = round_up_pg (r_len r));
  go_stride : UNIT <= get_stride (get_meta_rec st g) /\ get_stride (get_meta_rec st g) mod UNIT = 0;
  (* [comment removed for export] *)
  go_nest : m_maplen (get_meta_rec st g) = 0 ->
      exists g1 i1 b1, (s_slots st) !! b = Some (g1, i1) /\ hosts st b1 g1 /\ fst b1 = fst b
        /\ b = slot_start' (get_meta_rec st g1) i1 /\ 0 <= i1 <= m_last_idx (get_meta_rec st g1)
        /\ ~ slot_free (get_meta_rec st g1) i1
        /\ m_sizeclass (get_meta_rec st g) < m_sizeclass (get_meta_rec st g1)
        (* [comment removed for export] *)
        /\ hdr_known st b b1 i1
}.

Definition ci_gmeta (st : mstate) : Prop := forall b g, hosts st b g -> gmeta_ok st g b.

(* [comment removed for export] *)
Definition ci_groups (st : mstate) : Prop :=
  forall b gh, (s_groups st) !! b = Some gh ->
    exists g, g_meta gh = Some g /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g).

(* [comment removed for export] *)
Definition ci_group_inj (st : mstate) : Prop :=
  forall b1 b2 g, hosts st b1 g -> hosts st b2 g -> b1 = b2.

(* [comment removed for export] *)
Definition ci_slots (st : mstate) : Prop :=
  forall s g i, (s_slots st) !! s = Some (g, i) ->
    is_gm st g /\ s = slot_start' (get_meta_rec st g) i /\ 0 <= i <= m_last_idx (get_meta_rec st g).
Definition ci_slots_total (st : mstate) : Prop :=
  forall b g i, hosts st b g -> 0 <= i <= m_last_idx (get_meta_rec st g) ->
    (s_slots st) !! (slot_start' (get_meta_rec st g) i) = Some (g, i).

(* [comment removed for export] *)
Definition ci_ghdr_unk (st : mstate) : Prop :=
  forall b gh o, (s_groups st) !! b = Some gh -> 0 <= o < 12 ->
    exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h.

(* [comment removed for export] *)
Definition ci_hdr0 (st : mstate) : Prop :=
  forall g b i, hosts st b g -> 0 <= i <= m_last_idx (get_meta_rec st g) ->
    cell_read (get_shadow st (fst b)) (sstart_of (get_meta_rec st g) i - IB) = Known 0.

(* [comment removed for export] *)
Record blk_ok (st : mstate) (blk : block) : Prop := mkBK {
  bk_slot : exists g i b, (s_slots st) !! (blk_slot blk) = Some (g, i) /\ hosts st b g /\ fst b = fst (blk_slot blk)
            /\ 0 <= i <= m_last_idx (get_meta_rec st g)
            /\ ~ slot_free (get_meta_rec st g) i
            /\ (exists off, 0 <= off /\ blk_addr blk = conc st (blk_slot blk) + UNIT * off
                           /\ UNIT * off + blk_size blk <= get_stride (get_meta_rec st g) - IB
                           /\ cell_read (get_shadow st (fst (blk_slot blk))) (snd (blk_slot blk) + UNIT * off - IB) = Known 0
                           /\ hdr_known st (aadd (blk_slot blk) (UNIT * off)) b i);
  (* [comment removed for export] *)
  bk_nogroup : (s_groups st) !! (blk_slot blk) = None;
  bk_size : 0 <= blk_size blk
}.

Definition ci_ctx (st : mstate) : Prop :=
  0 <= c_seq (ctx st) < 256
  /\ (forall i, 0 <= bounces st i < 256) /\ (forall i, 0 <= unmap_seq st i < 256)
  /\ (forall sc, 0 <= usage st sc < 2^64)
  /\ 0 <= c_secret (ctx st) < 2^64.

Definition ci_brk (st : mstate) : Prop :=
  forall rid off, c_brk (ctx st) = BrkLive rid off ->
    exists r, (s_regions st) !! rid = Some r /\ r_kind r = RKBrk.


(* [comment removed for export] *)
Definition ci_mem_hosts (st : mstate) : Prop :=
  forall q b, m_mem (get_meta_rec st q) = Some b -> hosts st b q.

(* [comment removed for export] *)
Definition ng_ptr (st : mstate) (p : optr) : Prop :=
  match p with
  | Some q => exists r, (s_regions st) !! (fst q) = Some r /\ r_kind r <> RKGroup
  | None => True
  end.
(* [comment removed for export] *)
Definition ci_mptrs (st : mstate) : Prop :=
  ng_ptr st (c_avail_meta (ctx st)) /\ ng_ptr st (c_meta_area_head (ctx st)) /\ ng_ptr st (c_meta_area_tail (ctx st))
  /\ ng_ptr st (c_avail_meta_areas (ctx st))
  /\ forall a ar, (s_areas st) !! a = Some ar -> ng_ptr st (a_next ar).

(* [comment removed for export] *)
Record blk_clear (st : mstate) (LB : list block) (blk : block) : Prop := mkBC {
  bc_region : exists r, (s_regions st) !! (fst (blk_slot blk)) = Some r /\ r_kind r = RKGroup
     /\ r_base r + 16 <= blk_addr blk /\ blk_addr blk + blk_size blk <= r_base r + round_up_pg (r_len r)
     /\ blk_addr blk mod 16 = 0
     /\ (forall a, blk_addr blk <= a < blk_addr blk + blk_size blk ->
           exists h, cell_read (get_shadow st (fst (blk_slot blk))) (a - r_base r) = Unknown h);
  bc_hdrs : forall b gh, (s_groups st) !! b = Some gh -> fst b = fst (blk_slot blk) ->
     blk_addr blk + blk_size blk <= conc st b - IB \/ conc st b + 16 <= blk_addr blk;
  bc_blocks : forall blk', In blk' LB -> blk_slot blk' <> blk_slot blk -> fst (blk_slot blk') = fst (blk_slot blk) ->
     blk_addr blk' + blk_size blk' <= blk_addr blk - 4 \/ blk_addr blk + blk_size blk <= blk_addr blk' - 4
}.

Record CINV (st : mstate) (LB : list block) : Prop := mkCI {
  ci_links : ci_links_t st;
  ci_heads : ci_heads_t st;
  ci_hom : ci_homog st;
  ci_gmetas : ci_gmeta st;
  ci_grps : ci_groups st;
  ci_ginj : ci_group_inj st;
  ci_slts : ci_slots st;
  ci_sltt : ci_slots_total st;
  ci_unk : ci_ghdr_unk st;
  ci_h0 : ci_hdr0 st;
  ci_blks : Forall (blk_ok st) LB;
  ci_nodup : List.NoDup (map blk_slot LB);
  ci_cx : ci_ctx st;
  ci_bk : ci_brk st;
  ci_ticks : ticks_ok st;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ci_memh : ci_mem_hosts st;
  ci_mp : ci_mptrs st;
  ci_bclr : Forall (blk_clear st LB) LB
}.


End ACeilS2.
