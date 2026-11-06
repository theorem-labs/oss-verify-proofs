(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc Realloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Record rk_data := mkRK {
  rk_st0 : mstate;      (* [comment removed for export] *)
  rk_g : aptr; rk_idx : Z; rk_old : Z;
  rk_stride : Z; rk_start : aptr; rk_e : aptr; rk_avail : Z;
  rk_base : Z; rk_needed : Z; rk_maplen4096 : Z; rk_gmem : aptr }.

Definition rk_of (st : mstate) (p : aptr) (n : Z) (g : aptr) (idx old : Z) : rk_data :=
  let st0 := set_tick (N.succ (s_tick st)) st in
  let mr := get_meta_rec st0 g in
  let stride := get_stride mr in
  let start := slot_start' mr idx in
  let e := aadd start (stride - IB) in
  mkRK st0 g idx old stride start e (snd e - snd p)
       (snd p - snd start) (round_up_pg (n + (snd p - snd start) + UNIT + IB)) (m_maplen mr * 4096)
       (default (0%N, 0) (m_mem mr)).

Definition realloc_keep (st : mstate) (p : aptr) (n : Z) (st' : mstate) : Prop :=
  size_overflows n = false /\
  exists g idx old,
    realloc_hdr (set_tick (N.succ (s_tick st)) st) p = SRet (Some (g, idx, old)) /\
    let d := rk_of st p n g idx old in
    let mr := get_meta_rec (rk_st0 d) g in
    ( (* [comment removed for export] *)
      ((n <=? rk_avail d) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) = true
       /\ st' = havoc p n (set_size p (rk_e d) n idx (rk_st0 d)))
    \/ ((n <=? rk_avail d) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1) = false
       /\ (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n) = true /\ m_sizeclass mr = 63
       /\ ( (* [comment removed for export] *)
            (rk_maplen4096 d = rk_needed d
             /\ st' = fst (realloc_big_tail (rk_st0 d) (rk_gmem d) (rk_base d) idx (rk_needed d) n))
          \/ (* [comment removed for export] *)
            (rk_maplen4096 d <> rk_needed d /\ rk_needed d < PTRDIFF_MAX
             /\ exists r, mremap_answer_ok (live_ranges (rk_st0 d)) (conc (rk_st0 d) (rk_gmem d)) (rk_maplen4096 d) (rk_needed d) r = true
                /\ is_err r = false
                /\ st' = fst (realloc_big_tail (remap_region (fst (rk_gmem d)) g r (rk_needed d) (rk_st0 d)) (rk_gmem d) (rk_base d) idx (rk_needed d) n))))).

(* [comment removed for export] *)
End RC__1.
