(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record aenv := mkAEnv {
  ae_ic        : aimg_consts;    (* [comment removed for export] *)
  ae_sp0       : Z;              (* [comment removed for export] *)
  ae_tp        : Z;              (* [comment removed for export] *)
  ae_thread    : Z;              (* [comment removed for export] *)
  ae_space_beg : Z;              (* [comment removed for export] *)
  ae_resv_beg  : Z;              (* [comment removed for export] *)
  ae_ptr_array : Z;              (* [comment removed for export] *)
  ae_depot_nodes : Z;            (* [comment removed for export] *)
  ae_store_blk : Z;              (* [comment removed for export] *)
  ae_keys0     : list (list Z);  (* [comment removed for export] *)
  ae_frames0   : Z;              (* [comment removed for export] *)
  ae_reserved  : list (Z * Z);   (* [comment removed for export] *)
  ae_fs_beg    : Z;              (* [comment removed for export] *)
  ae_fs_len    : Z;
  ae_iarena    : Z;              (* [comment removed for export] *)
  ae_img       : Z * Z           (* [comment removed for export] *)
}.

Definition ae_instance (E : aenv) : Z := aic_instance (ae_ic E).
Definition ae_region_info (E : aenv) : Z := ae_space_beg E + kSpaceSize.
Definition ae_stack_top (E : aenv) : Z := round_up (ae_sp0 E - kStackAnchorDelta) kPageSize.
Definition ae_stack_bottom (E : aenv) : Z := ae_stack_top E - kStackSizeForThread.
Definition ae_cache (E : aenv) : Z := ae_thread E + kThrCache.          (* [comment removed for export] *)
Definition ae_qcache (E : aenv) : Z := ae_thread E + kThrQCache.        (* [comment removed for export] *)
Definition ae_tstats (E : aenv) : Z := ae_thread E + kThrStats.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record region := mkRegion {
  rg_mapped_user : Z;       (* [comment removed for export] *)
  rg_alloc_user  : Z;       (* [comment removed for export] *)
  rg_free        : list Z;  (* [comment removed for export] *)
  rg_mapped_fa   : Z;       (* [comment removed for export] *)
  rg_n_allocated : Z;       (* [comment removed for export] *)
  rg_n_freed     : Z        (* [comment removed for export] *)
}.
Definition region0 : region := mkRegion 0 0 [] 0 0 0.
Definition rg_num_freed (r : region) : Z := Z.of_nat (length (rg_free r)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Record secchunk := mkSec {
  sc_map_beg  : Z;
  sc_map_size : Z;
  sc_needed   : Z           (* [comment removed for export] *)
}.

Record secstats := mkSecStats {
  ss_n_allocs : Z; ss_n_frees : Z; ss_cur : Z; ss_max : Z;
  ss_by_size_log : gmap Z Z   (* [comment removed for export] *)
}.
Definition secstats0 : secstats := mkSecStats 0 0 0 0 ∅.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive cstate := CAllocated (alloc_id : Z) | CQuarantined (alloc_id free_id : Z).

Record chunkmeta := mkCM {
  cm_alloc_beg : Z;         (* [comment removed for export] *)
  cm_rz_log    : Z;         (* [comment removed for export] *)
  cm_n         : Z;         (* [comment removed for export] *)
  cm_prim      : option Z;  (* [comment removed for export] *)
  cm_state     : cstate
}.
Definition cm_user_beg (m : chunkmeta) : Z := cm_alloc_beg m + 16 * 2 ^ (cm_rz_log m).
Definition cm_chunk_beg (m : chunkmeta) : Z := cm_user_beg m - kChunkHeaderSize.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record batch := mkBatch {
  b_addr  : Z;              (* [comment removed for export] *)
  b_items : list Z;         (* [comment removed for export] *)
  b_size  : Z               (* [comment removed for export] *)
}.
Definition qbytes (l : list batch) : Z := fold_right (fun b acc => b_size b + acc) 0 l.
Definition qcount (l : list batch) : Z := Z.of_nat (length l).

(* [comment removed for export] *)
(* [comment removed for export] *)

Record tstats := mkTS {
  ts_mallocs : Z; ts_malloced : Z; ts_malloced_redzones : Z;
  ts_frees : Z; ts_freed : Z; ts_real_frees : Z; ts_really_freed : Z;
  ts_reallocs : Z; ts_realloced : Z;
  ts_mmaps : Z; ts_mmaped : Z; ts_munmaps : Z; ts_munmaped : Z;
  ts_malloc_large : Z;
  ts_by_size : gmap Z Z     (* [comment removed for export] *)
}.
Definition tstats0 : tstats := mkTS 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ∅.

(* [comment removed for export] *)
(* [comment removed for export] *)

Record astate := mkAS {
  (* [comment removed for export] *)
  as_regions      : gmap Z region;     (* [comment removed for export] *)
  as_cache_inited : bool;              (* [comment removed for export] *)
  as_cache        : gmap Z (list Z);   (* [comment removed for export] *)
  as_cache_stale  : gmap Z (gmap Z Z); (* [comment removed for export] *)
  as_cache_allocated : Z;              (* [comment removed for export] *)
  as_cache_mapped : Z;                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_ptr_committed : Z;                (* [comment removed for export] *)
  as_sec          : list secchunk;     (* [comment removed for export] *)
  as_sec_stale    : gmap Z Z;          (* [comment removed for export] *)
  as_sec_stats    : secstats;
  as_glob_allocated : Z; as_glob_mapped : Z;   (* [comment removed for export] *)
  as_oom          : bool;              (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_chunks       : gmap Z chunkmeta;  (* [comment removed for export] *)
  as_dead         : gmap Z Z;          (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_tq           : list batch;        (* [comment removed for export] *)
  as_gq           : list batch;        (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_keys         : list (list Z);     (* [comment removed for export] *)
  as_frames       : Z;                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_ia_inited    : bool;              (* [comment removed for export] *)
  as_ts           : tstats;
  (* [comment removed for export] *)
  as_residue      : list Z;
  (* [comment removed for export] *)
  as_nprim_ever   : Z;
  (* [comment removed for export] *)
  as_node_blocks  : list Z;
  as_store_blocks : list Z;
  as_store_stored : gmap Z Z;
  as_ndepot_ins   : Z;
  (* [comment removed for export] *)
  as_everc        : gmap Z Z
}.

Definition astate0 (E : aenv) : astate :=
  mkAS ∅ false ∅ ∅ 0 0  0 [] ∅ secstats0 0 0 false  ∅ ∅  [] []  [] (ae_frames0 E)  false tstats0 [] 0 [] [] ∅ 0 ∅.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition get_region (s : astate) (c : Z) : region :=
  match as_regions s !! c with Some r => r | None => region0 end.
Definition set_region (c : Z) (r : region) (s : astate) : astate :=
  mkAS (<[c := r]> (as_regions s)) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).

Definition get_cache (s : astate) (c : Z) : list Z :=
  match as_cache s !! c with Some l => l | None => [] end.
Definition set_cache (c : Z) (l : list Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (<[c := l]> (as_cache s)) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).

(* [comment removed for export] *)
Definition upd_cache_inited (v : bool) (s : astate) : astate :=
  mkAS (as_regions s) v (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_cache_stale (f : gmap Z (gmap Z Z) -> gmap Z (gmap Z Z)) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (f (as_cache_stale s)) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_cache_allocated (f : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (f (as_cache_allocated s)) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_cache_mapped (f : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (f (as_cache_mapped s))
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_ptr_committed (v : Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       v (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_sec (f : list secchunk -> list secchunk) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (f (as_sec s)) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_sec_stale (f : gmap Z Z -> gmap Z Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (f (as_sec_stale s)) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_sec_stats (f : secstats -> secstats) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (f (as_sec_stats s)) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_glob (fa fm : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (fa (as_glob_allocated s)) (fm (as_glob_mapped s)) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_oom (v : bool) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) v
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_chunks (f : gmap Z chunkmeta -> gmap Z chunkmeta) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (f (as_chunks s)) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_dead (f : gmap Z Z -> gmap Z Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (f (as_dead s)) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_tq (f : list batch -> list batch) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (f (as_tq s)) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_gq (f : list batch -> list batch) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (f (as_gq s)) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_keys (f : list (list Z) -> list (list Z)) (fr : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (f (as_keys s)) (fr (as_frames s)) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_ia_inited (v : bool) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) v (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_ts (f : tstats -> tstats) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (f (as_ts s)) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_residue (f : list Z -> list Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (f (as_residue s)) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_nprim (f : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (f (as_nprim_ever s)) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
(* [comment removed for export] *)
Definition everc (s : astate) (c : Z) : Z := match as_everc s !! c with Some v => v | None => 0 end.
Definition upd_nprimc (prim : bool) (c : Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s)
       (if prim then as_nprim_ever s + 1 else as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s)
       (if prim then <[c := everc s c + 1]> (as_everc s) else as_everc s).
Definition upd_node_blocks (f : list Z -> list Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (f (as_node_blocks s)) (as_store_blocks s) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_store_blocks (f : list Z -> list Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (f (as_store_blocks s)) (as_store_stored s) (as_ndepot_ins s) (as_everc s).
Definition upd_store_stored (f : gmap Z Z -> gmap Z Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (f (as_store_stored s)) (as_ndepot_ins s) (as_everc s).
Definition upd_ndepot (f : Z -> Z) (s : astate) : astate :=
  mkAS (as_regions s) (as_cache_inited s) (as_cache s) (as_cache_stale s) (as_cache_allocated s) (as_cache_mapped s)
       (as_ptr_committed s) (as_sec s) (as_sec_stale s) (as_sec_stats s) (as_glob_allocated s) (as_glob_mapped s) (as_oom s)
       (as_chunks s) (as_dead s) (as_tq s) (as_gq s) (as_keys s) (as_frames s) (as_ia_inited s) (as_ts s) (as_residue s) (as_nprim_ever s) (as_node_blocks s) (as_store_blocks s) (as_store_stored s) (f (as_ndepot_ins s)) (as_everc s).

(* [comment removed for export] *)
Definition ts_upd_mallocs (f : Z -> Z) (t : tstats) := mkTS (f (ts_mallocs t)) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t) (ts_freed t) (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t) (ts_malloc_large t) (ts_by_size t).
Definition ts_on_malloc (n' needed' : Z) (large : bool) (cls : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t + 1) (ts_malloced t + n') (ts_malloced_redzones t + (needed' - n')) (ts_frees t) (ts_freed t)
       (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t)
       (if large then ts_malloc_large t + 1 else ts_malloc_large t)
       (if large then ts_by_size t else <[cls := match ts_by_size t !! cls with Some k => k + 1 | None => 1 end]> (ts_by_size t)).
Definition ts_on_free (n : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t + 1) (ts_freed t + n)
       (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t)
       (ts_malloc_large t) (ts_by_size t).
Definition ts_on_real_free (n : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t) (ts_freed t)
       (ts_real_frees t + 1) (ts_really_freed t + n) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t)
       (ts_malloc_large t) (ts_by_size t).
Definition ts_on_realloc (n : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t) (ts_freed t)
       (ts_real_frees t) (ts_really_freed t) (ts_reallocs t + 1) (ts_realloced t + n) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t) (ts_munmaped t)
       (ts_malloc_large t) (ts_by_size t).
Definition ts_on_mmap (sz : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t) (ts_freed t)
       (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t + 1) (ts_mmaped t + sz) (ts_munmaps t) (ts_munmaped t)
       (ts_malloc_large t) (ts_by_size t).
Definition ts_on_munmap (sz : Z) (t : tstats) : tstats :=
  mkTS (ts_mallocs t) (ts_malloced t) (ts_malloced_redzones t) (ts_frees t) (ts_freed t)
       (ts_real_frees t) (ts_really_freed t) (ts_reallocs t) (ts_realloced t) (ts_mmaps t) (ts_mmaped t) (ts_munmaps t + 1) (ts_munmaped t + sz)
       (ts_malloc_large t) (ts_by_size t).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition tq_bytes (s : astate) : Z := qbytes (as_tq s).   (* [comment removed for export] *)
Definition gq_bytes (s : astate) : Z := qbytes (as_gq s).   (* [comment removed for export] *)
Definition n_chunks (s : astate) : Z := Z.of_nat (length (as_sec s)).

(* [comment removed for export] *)
Fixpoint index_of (h : Z) (l : list (list Z)) (i : Z) : option Z :=
  match l with
  | [] => None
  | k' :: l' => if depot_hash k' =? h then Some i else index_of h l' (i + 1)
  end.
Definition depot_lookup (E : aenv) (s : astate) (k : list Z) : option Z :=
  index_of (depot_hash k) (ae_keys0 E ++ as_keys s) 1.
Definition depot_n_ids (E : aenv) (s : astate) : Z := Z.of_nat (length (ae_keys0 E) + length (as_keys s)).

(* [comment removed for export] *)
Definition chunk_used_size (s : astate) (chunk_beg : Z) : Z :=
  match as_chunks s !! chunk_beg with Some m => cm_n m | None => 0 end.

(* [comment removed for export] *)
Definition classes30 : list Z := map Z.of_nat (seq 1 30).
Definition regions_bytes (s : astate) : Z :=
  fold_right (fun c acc => rg_mapped_user (get_region s c) + rg_mapped_fa (get_region s c) + acc) 0 classes30.
Definition sec_bytes (s : astate) : Z := fold_right (fun c acc => sc_map_size c + acc) 0 (as_sec s).
Definition a_eager_bytes (s : astate) : Z :=
  regions_bytes s + sec_bytes s + (if as_ptr_committed s =? 0 then 0 else kPtrArrayCommit).
