(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import gmap.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSTree.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

Definition aptr : Type := (N * Z)%type.
Definition optr : Type := option aptr.

Definition aptr_eqb (a b : aptr) : bool :=
  N.eqb (fst a) (fst b) && Z.eqb (snd a) (snd b).
Definition optr_eqb (a b : optr) : bool :=
  match a, b with
  | None, None => true
  | Some x, Some y => aptr_eqb x y
  | _, _ => false
  end.
Definition aadd (p : aptr) (d : Z) : aptr := (fst p, snd p + d).

Inductive undef_reason := UAssert (tag : Z) | UFuel | UBadPtr | UBadAnswer.

Inductive ev : Type :=
| EBrk (addr : Z)
| EMmap (addr len prot flags : Z)
| EMunmap (addr len : Z)
| EMprotect (addr len prot : Z)
| EPeek (p : aptr) (caddr : Z) (hint : Z)
| EUndef (why : undef_reason).

Definition M (R : Type) := stree ev Z R.
Definition ret {R} (r : R) : M R := SRet r.

Definition PROT_NONE : Z := 0.
Definition PROT_RW : Z := 3.
Definition MAP_PRIVATE : Z := 2.
Definition MAP_FIXED : Z := 16.
Definition MAP_ANON : Z := 32.
Definition ENOSYS : Z := 38.
Definition TWO64 : Z := 2^64.

Definition is_err (r : Z) : bool := (TWO64 - 4096 <? r).

Definition UNIT : Z := 16.
Definition IB : Z := 4.
Definition MMAP_THRESHOLD : Z := 131052.
Definition PGSZ : Z := 4096.
Definition META_SIZE : Z := 40.
Definition AREA_HDR : Z := 24.
Definition NSLOTS : Z := 101.

Definition size_classes : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8;
   9; 10; 12; 15;
   18; 20; 25; 31;
   36; 42; 50; 63;
   72; 84; 102; 127;
   146; 170; 204; 255;
   292; 340; 409; 511;
   584; 682; 818; 1023;
   1169; 1364; 1637; 2047;
   2340; 2730; 3276; 4095;
   4680; 5460; 6552; 8191].
Definition size_class (i : Z) : Z := nth (Z.to_nat i) size_classes 0.

Definition small_cnt_tab : list (list Z) :=
  [[30;30;30]; [31;15;15]; [20;10;10]; [31;15;7]; [25;12;6];
   [21;10;5]; [18;8;4]; [31;15;7]; [28;14;6]].
Definition small_cnt (sc i : Z) : Z := nth (Z.to_nat i) (nth (Z.to_nat sc) small_cnt_tab []) 0.
Definition med_cnt_tab : list Z := [28; 24; 20; 32].
Definition med_cnt (i : Z) : Z := nth (Z.to_nat i) med_cnt_tab 0.

Definition u32 (z : Z) : Z := z mod 2^32.
Definition bit (i : Z) : Z := 2^i.
Definition mask_upto (k : Z) : Z := 2^(k+1) - 1.
Definition lowbit (m : Z) : Z := Z.land m (- m).
Definition ctz32 (m : Z) : Z := Z.log2 (lowbit m).
Definition clz32 (m : Z) : Z := 31 - Z.log2 m.
Definition testbit (m i : Z) : bool := Z.testbit m i.

Definition round_up_pg (x : Z) : Z := x + Z.land (- x) (PGSZ - 1).

Definition alloc_ceiling : Z := 0x7fffff800000.
Definition is_errno_form (r : Z) : bool := (TWO64 - 4095 <=? r) && (r <? TWO64).

Definition brk0_answer_ok (r : Z) : bool := (0 <? r) && (r mod PGSZ =? 0) && (r <? TWO64).

Definition brk_answer_ok (old new r : Z) : bool := (r =? new) || (r =? old).

Definition iv_disjoint (a n b m : Z) : bool := (a + n <=? b) || (b + m <=? a).
Definition ranges_free (l : list (Z * Z)) (a n : Z) : bool :=
  forallb (fun bm : Z * Z => iv_disjoint a n (fst bm) (snd bm)) l.

Definition mmap_answer_ok (live : list (Z * Z)) (len r : Z) : bool :=
  is_errno_form r ||
  ((0 <? r) && (r mod PGSZ =? 0) && (r + round_up_pg len <=? alloc_ceiling)
   && ranges_free live r (round_up_pg len)).

Definition mmap_fixed_answer_ok (a r : Z) : bool := is_errno_form r || (r =? a).

Definition munmap_answer_ok (r : Z) : bool := (r =? 0) || is_errno_form r.
Definition mprotect_answer_ok (r : Z) : bool := (r =? 0) || is_errno_form r.
Definition peek_answer_ok (r : Z) : bool := (0 <=? r) && (r <? 256).

Inductive rkind := RKBrk | RKMeta | RKGroup.

Record region := mkRegion {
  r_kind  : rkind;
  r_base  : Z;
  r_len   : Z
}.

Record shadow := mkShadow {
  r_cells : gmap Z (Z * N);
  r_hav   : gmap Z (list (Z * N));
  r_havp  : gmap Z N
}.
Definition shadow0 : shadow := mkShadow ∅ ∅ ∅.

Record meta := mkMeta {
  m_prev : optr; m_next : optr; m_mem : optr;
  m_avail : Z; m_freed : Z;
  m_last_idx : Z; m_freeable : Z; m_sizeclass : Z; m_maplen : Z
}.
Definition meta0 : meta := mkMeta None None None 0 0 0 0 0 0.

Record area := mkArea { a_check : Z; a_next : optr; a_nslots : Z }.

Record ghdr := mkGhdr { g_meta : optr; g_active_idx : Z }.

Inductive brkstate := BrkUntried | BrkDead | BrkLive (rid : N) (off : Z).

Record mctx := mkCtx {
  c_secret : Z;
  c_init_done : Z;
  c_mmap_counter : Z;
  c_free_meta_head : optr;
  c_avail_meta : optr;
  c_avail_meta_count : Z;
  c_avail_meta_area_count : Z;
  c_meta_alloc_shift : Z;
  c_meta_area_head : optr;
  c_meta_area_tail : optr;
  c_avail_meta_areas : optr;
  c_active : gmap Z aptr;
  c_usage : gmap Z Z;
  c_unmap_seq : gmap Z Z;
  c_bounces : gmap Z Z;
  c_seq : Z;
  c_brk : brkstate
}.
Definition ctx0 : mctx :=
  mkCtx 0 0 0 None None 0 0 0 None None None ∅ ∅ ∅ ∅ 0 BrkUntried.

Record mstate := mkState {
  s_ctx : mctx;
  s_regions : gmap N region;
  s_shadow : gmap N shadow;
  s_next_rid : N;
  s_metas : gmap aptr meta;
  s_areas : gmap aptr area;
  s_groups : gmap aptr ghdr;
  s_slots : gmap aptr (aptr * Z);
  s_tick : N;
  s_secret : Z;
  s_reserved : list (Z * Z)
}.

Definition minit (secret : Z) (reserved : list (Z * Z)) : mstate :=
  mkState ctx0 ∅ ∅ 0%N ∅ ∅ ∅ ∅ 0%N secret reserved.

Definition upd_ctx (f : mctx -> mctx) (st : mstate) : mstate :=
  mkState (f (s_ctx st)) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_regions (v : gmap N region) (st : mstate) : mstate :=
  mkState (s_ctx st) v (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_shadow (v : gmap N shadow) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) v (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_next_rid (v : N) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) v (s_metas st) (s_areas st) (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_metas (v : gmap aptr meta) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) v (s_areas st) (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_areas (v : gmap aptr area) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) v (s_groups st) (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_groups (v : gmap aptr ghdr) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) v (s_slots st) (s_tick st) (s_secret st) (s_reserved st).
Definition set_slots (v : gmap aptr (aptr * Z)) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) v (s_tick st) (s_secret st) (s_reserved st).
Definition set_tick (v : N) (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) (s_shadow st) (s_next_rid st) (s_metas st) (s_areas st) (s_groups st) (s_slots st) v (s_secret st) (s_reserved st).

Definition set_secret (v : Z) (c : mctx) := mkCtx v (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_init_done (v : Z) (c : mctx) := mkCtx (c_secret c) v (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_mmap_counter (v : Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) v (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_free_meta_head (v : optr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) v (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_avail_meta (v : optr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) v (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_avail_meta_count (v : Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) v (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_avail_meta_area_count (v : Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) v (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_meta_alloc_shift (v : Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) v (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_meta_area_head (v : optr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) v (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_meta_area_tail (v : optr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) v (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_avail_meta_areas (v : optr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) v (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_active_map (v : gmap Z aptr) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) v (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_usage_map (v : gmap Z Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) v (c_unmap_seq c) (c_bounces c) (c_seq c) (c_brk c).
Definition set_unmap_seq_map (v : gmap Z Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) v (c_bounces c) (c_seq c) (c_brk c).
Definition set_bounces_map (v : gmap Z Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) v (c_seq c) (c_brk c).
Definition set_seq (v : Z) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) v (c_brk c).
Definition set_brk (v : brkstate) (c : mctx) := mkCtx (c_secret c) (c_init_done c) (c_mmap_counter c) (c_free_meta_head c) (c_avail_meta c) (c_avail_meta_count c) (c_avail_meta_area_count c) (c_meta_alloc_shift c) (c_meta_area_head c) (c_meta_area_tail c) (c_avail_meta_areas c) (c_active c) (c_usage c) (c_unmap_seq c) (c_bounces c) (c_seq c) v.

Definition ctx (st : mstate) : mctx := s_ctx st.

Definition active (st : mstate) (sc : Z) : optr := (c_active (ctx st)) !! sc.
Definition set_active (sc : Z) (v : optr) (st : mstate) : mstate :=
  upd_ctx (fun c => set_active_map (match v with Some p => <[sc := p]> (c_active c) | None => delete sc (c_active c) end) c) st.
Definition usage (st : mstate) (sc : Z) : Z := default 0 ((c_usage (ctx st)) !! sc).
Definition set_usage (sc : Z) (v : Z) (st : mstate) : mstate :=
  upd_ctx (fun c => set_usage_map (<[sc := v]> (c_usage c)) c) st.
Definition unmap_seq (st : mstate) (i : Z) : Z := default 0 ((c_unmap_seq (ctx st)) !! i).
Definition bounces (st : mstate) (i : Z) : Z := default 0 ((c_bounces (ctx st)) !! i).
Definition set_bounce (i v : Z) (st : mstate) : mstate :=
  upd_ctx (fun c => set_bounces_map (<[i := v]> (c_bounces c)) c) st.

Definition get_meta_rec (st : mstate) (m : aptr) : meta := default meta0 ((s_metas st) !! m).
Definition put_meta (m : aptr) (r : meta) (st : mstate) : mstate := set_metas (<[m := r]> (s_metas st)) st.
Definition upd_meta (m : aptr) (f : meta -> meta) (st : mstate) : mstate := put_meta m (f (get_meta_rec st m)) st.
Definition m_set_prev v r := mkMeta v (m_next r) (m_mem r) (m_avail r) (m_freed r) (m_last_idx r) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_next v r := mkMeta (m_prev r) v (m_mem r) (m_avail r) (m_freed r) (m_last_idx r) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_mem v r := mkMeta (m_prev r) (m_next r) v (m_avail r) (m_freed r) (m_last_idx r) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_avail v r := mkMeta (m_prev r) (m_next r) (m_mem r) v (m_freed r) (m_last_idx r) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_freed v r := mkMeta (m_prev r) (m_next r) (m_mem r) (m_avail r) v (m_last_idx r) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_last_idx v r := mkMeta (m_prev r) (m_next r) (m_mem r) (m_avail r) (m_freed r) (Z.land v 31) (m_freeable r) (m_sizeclass r) (m_maplen r).
Definition m_set_freeable v r := mkMeta (m_prev r) (m_next r) (m_mem r) (m_avail r) (m_freed r) (m_last_idx r) (Z.land v 1) (m_sizeclass r) (m_maplen r).
Definition m_set_sizeclass v r := mkMeta (m_prev r) (m_next r) (m_mem r) (m_avail r) (m_freed r) (m_last_idx r) (m_freeable r) (Z.land v 63) (m_maplen r).
Definition m_set_maplen v r := mkMeta (m_prev r) (m_next r) (m_mem r) (m_avail r) (m_freed r) (m_last_idx r) (m_freeable r) (m_sizeclass r) (Z.land v (2^52 - 1)).

Definition get_group (st : mstate) (g : aptr) : option ghdr := (s_groups st) !! g.
Definition group_active_idx (st : mstate) (g : aptr) : Z :=
  match get_group st g with Some h => Z.land (g_active_idx h) 31 | None => 0 end.

Definition put_group (g : aptr) (m : optr) (ai : Z) (st : mstate) : mstate :=
  set_groups (<[g := mkGhdr m (Z.land ai 31)]> (s_groups st)) st.

Definition set_group_active_idx (g : aptr) (ai : Z) (st : mstate) : mstate :=
  match get_group st g with
  | Some h => set_groups (<[g := mkGhdr (g_meta h) (Z.land ai 31)]> (s_groups st)) st
  | None => st
  end.

Definition get_region (st : mstate) (rid : N) : option region := (s_regions st) !! rid.
Definition conc (st : mstate) (p : aptr) : Z :=
  match get_region st (fst p) with Some r => r_base r + snd p | None => 0 end.
Definition oconc (st : mstate) (p : optr) : Z := match p with Some q => conc st q | None => 0 end.

Definition region_live_range (r : region) : Z * Z :=
  match r_kind r with
  | RKBrk => (r_base r + PGSZ, round_up_pg (r_len r) - PGSZ)
  | _ => (r_base r, round_up_pg (r_len r))
  end.
Definition live_ranges (st : mstate) : list (Z * Z) :=
  s_reserved st ++ map (fun kr : N * region => region_live_range (snd kr)) (map_to_list (s_regions st)).
Definition bad_answer {R} (bail : M R) : M R := SVis (EUndef UBadAnswer) (fun _ => bail).

Definition brk_pages_ok (st : mstate) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? alloc_ceiling) && ranges_free (live_ranges st) lo len.

Definition new_region (k : rkind) (base len : Z) (st : mstate) : mstate * N :=
  let rid := s_next_rid st in
  (set_next_rid (N.succ rid) (set_regions (<[rid := mkRegion k base len]> (s_regions st)) st), rid).

Definition drop_region (rid : N) (st : mstate) : mstate :=
  set_shadow (delete rid (s_shadow st)) (set_regions (delete rid (s_regions st)) st).
Definition del_group (g : aptr) (st : mstate) : mstate :=
  set_groups (delete g (s_groups st)) st.

Definition add_slots (m p : aptr) (stride : Z) (cnt : Z) (st : mstate) : mstate :=
  set_slots (snd (Z.iter cnt (fun acc : Z * gmap aptr (aptr * Z) =>
               let (i, tb) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> tb))
             (0, s_slots st))) st.
Definition del_slots (p : aptr) (stride : Z) (cnt : Z) (st : mstate) : mstate :=
  set_slots (snd (Z.iter cnt (fun acc : Z * gmap aptr (aptr * Z) =>
               let (i, tb) := acc in (i + 1, delete (aadd p (UNIT + stride * i)) tb))
             (0, s_slots st))) st.

Inductive cellval := Known (v : Z) | Unknown (hint : Z).

Definition stale (hl : list (Z * N)) (b : Z) (t : option N) : bool :=
  existsb (fun ch : Z * N => (b <? fst ch) && match t with Some t => (t <? snd ch)%N | None => true end) hl.

Definition stale_pg (hp : option N) (t : option N) : bool :=
  match hp, t with
  | Some h, Some t => (t <? h)%N
  | Some _, None => true
  | None, _ => false
  end.

Definition cell_read (r : shadow) (off : Z) : cellval :=
  let hl := default [] ((r_hav r) !! (off / 16)) in
  let hp := (r_havp r) !! (off / 4096) in
  match (r_cells r) !! off with
  | Some (v, t) => if stale_pg hp (Some t) || stale hl (off mod 16) (Some t) then Unknown v else Known v
  | None => if stale_pg hp None || stale hl (off mod 16) None then Unknown 0 else Known 0
  end.

Definition get_shadow (st : mstate) (rid : N) : shadow := default shadow0 ((s_shadow st) !! rid).
Definition rd8 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  match cell_read (get_shadow st (fst p)) (snd p) with
  | Known v => k v
  | Unknown hint => SVis (EPeek p (conc st p) hint) (fun v => if peek_answer_ok v then k v else bad_answer (k hint))
  end.

Definition rd16 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  rd8 st p (fun b0 => rd8 st (aadd p 1) (fun b1 => k (b0 + 256 * b1))).
Definition rd32 {R} (st : mstate) (p : aptr) (k : Z -> M R) : M R :=
  rd8 st p (fun b0 => rd8 st (aadd p 1) (fun b1 =>
  rd8 st (aadd p 2) (fun b2 => rd8 st (aadd p 3) (fun b3 =>
  k (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3))))).

Definition upd_region (rid : N) (f : region -> region) (st : mstate) : mstate :=
  match get_region st rid with
  | Some r => set_regions (<[rid := f r]> (s_regions st)) st
  | None => st
  end.
Definition upd_shadow (rid : N) (f : shadow -> shadow) (st : mstate) : mstate :=
  set_shadow (<[rid := f (get_shadow st rid)]> (s_shadow st)) st.

Definition wr8 (p : aptr) (v : Z) (st : mstate) : mstate :=
  upd_shadow (fst p) (fun r =>
    mkShadow (<[snd p := (Z.land v 255, s_tick st)]> (r_cells r)) (r_hav r) (r_havp r)) st.
Definition wr16 (p : aptr) (v : Z) (st : mstate) : mstate :=
  wr8 (aadd p 1) (Z.shiftr v 8) (wr8 p v st).
Definition wr32 (p : aptr) (v : Z) (st : mstate) : mstate :=
  wr8 (aadd p 3) (Z.shiftr v 24) (wr8 (aadd p 2) (Z.shiftr v 16) (wr8 (aadd p 1) (Z.shiftr v 8) (wr8 p v st))).

Definition hav_add (cov : Z) (t : N) (hl : list (Z * N)) : list (Z * N) :=
  (cov, t) :: filter (fun ch : Z * N => cov <? fst ch) hl.

Definition havoc_units (x y : Z) (t : N) (h : gmap Z (list (Z * N))) : gmap Z (list (Z * N)) :=
  let u0 := x / 16 in
  let u1 := (y - 1) / 16 in
  let lastcov := let r := y mod 16 in if r =? 0 then 16 else r in
  snd (Z.iter (u1 - u0 + 1)
         (fun acc : Z * gmap Z (list (Z * N)) =>
            let (u, h) := acc in
            let cov := if u =? u1 then lastcov else 16 in
            (u + 1, <[u := hav_add cov t (default [] (h !! u))]> h))
         (u0, h)).

Definition havoc_pages (p0 p1 : Z) (t : N) (h : gmap Z N) : gmap Z N :=
  snd (Z.iter (p1 - p0) (fun acc : Z * gmap Z N => let (pg, h) := acc in (pg + 1, <[pg := t]> h)) (p0, h)).

Definition havoc (p : aptr) (n : Z) (st : mstate) : mstate :=
  if n <=? 0 then st else
  let a := snd p in
  let b := a + n in
  let t := s_tick st in
  let fp := (a + 4095) / 4096 in
  let lp := b / 4096 in
  upd_shadow (fst p) (fun r =>
    let '(hav, havp) :=
      if fp <? lp then

        let hav1 := if a <? fp * 4096 then havoc_units a (fp * 4096) t (r_hav r) else r_hav r in
        let hav2 := if lp * 4096 <? b then havoc_units (lp * 4096) b t hav1 else hav1 in
        (hav2, havoc_pages fp lp t (r_havp r))
      else (havoc_units a b t (r_hav r), r_havp r) in
    mkShadow (r_cells r) hav havp) st.

Definition guard {R} (tag : Z) (c : bool) (k : M R) (bail : M R) : M R :=
  if c then k else SVis (EUndef (UAssert tag)) (fun _ => bail).

Definition step_seq (st : mstate) : mstate :=
  if c_seq (ctx st) =? 255
  then upd_ctx (fun c => set_seq 1 (set_unmap_seq_map ∅ c)) st
  else upd_ctx (fun c => set_seq (c_seq c + 1) c) st.

Definition sc_in_seq_range (sc : Z) : bool := (7 <=? sc) && (sc <? 39).

Definition record_seq (sc : Z) (st : mstate) : mstate :=
  if sc_in_seq_range sc
  then upd_ctx (fun c => set_unmap_seq_map (<[sc - 7 := c_seq c]> (c_unmap_seq c)) c) st
  else st.

Definition account_bounce (sc : Z) (st : mstate) : mstate :=
  if sc_in_seq_range sc then
    let seq := unmap_seq st (sc - 7) in
    if negb (seq =? 0) && (c_seq (ctx st) - seq <? 10) then
      if bounces st (sc - 7) + 1 <? 100
      then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st
      else set_bounce (sc - 7) 150 st
    else st
  else st.

Definition decay_bounces (sc : Z) (st : mstate) : mstate :=
  if sc_in_seq_range sc && negb (bounces st (sc - 7) =? 0)
  then set_bounce (sc - 7) (bounces st (sc - 7) - 1) st
  else st.

Definition is_bouncing (sc : Z) (st : mstate) : bool :=
  sc_in_seq_range sc && (100 <=? bounces st (sc - 7)).

Definition size_to_class (n : Z) : Z :=
  let n := Z.shiftr (n + IB - 1) 4 in
  if n <? 10 then n else
  let n := n + 1 in
  let i := (28 - clz32 n) * 4 + 8 in
  let i := if size_class (i + 1) <? n then i + 2 else i in
  if size_class i <? n then i + 1 else i.

Definition size_overflows (n : Z) : bool := (2^63 - 1 - 4096 <=? n).

Inductive lhead := LActive (sc : Z) | LFree.
Definition get_head (st : mstate) (h : lhead) : optr :=
  match h with LActive sc => active st sc | LFree => c_free_meta_head (ctx st) end.
Definition set_head (h : lhead) (v : optr) (st : mstate) : mstate :=
  match h with LActive sc => set_active sc v st | LFree => upd_ctx (set_free_meta_head v) st end.

Definition queue {R} (h : lhead) (m : aptr) (st : mstate) (k : mstate -> M R) (bail : M R) : M R :=
  let mr := get_meta_rec st m in
  guard 1 (optr_eqb (m_next mr) None) (
  guard 2 (optr_eqb (m_prev mr) None) (
  match get_head st h with
  | Some head =>
      let hprev := m_prev (get_meta_rec st head) in

      let st1 := upd_meta m (fun r => m_set_prev hprev (m_set_next (Some head) r)) st in

      let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some m)) st1 | None => st1 end in
      let st3 := upd_meta head (m_set_prev (Some m)) st2 in
      k st3
  | None =>
      let st1 := upd_meta m (fun r => m_set_prev (Some m) (m_set_next (Some m) r)) st in
      k (set_head h (Some m) st1)
  end) bail) bail.

Definition dequeue (h : lhead) (m : aptr) (st : mstate) : mstate :=
  let mr := get_meta_rec st m in
  let st1 :=
    if negb (optr_eqb (m_next mr) (Some m)) then

      let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
      let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
      if optr_eqb (get_head st2 h) (Some m) then set_head h (m_next mr) st2 else st2
    else set_head h None st in

  upd_meta m (fun r => m_set_prev None (m_set_next None r)) st1.

Definition free_meta {R} (m : aptr) (st : mstate) (k : mstate -> M R) (bail : M R) : M R :=
  queue LFree m (put_meta m meta0 st) k bail.

Definition activate_group {R} (m : aptr) (st : mstate) (k : mstate -> Z -> M R) (bail : M R) : M R :=
  let mr := get_meta_rec st m in
  guard 3 (m_avail mr =? 0) (
    let act := match m_mem mr with Some _ => mask_upto (group_active_idx st (default (0%N,-1) (m_mem mr))) | None => 0 end in
    let mask := m_freed mr in
    let st1 := upd_meta m (fun r => m_set_avail (Z.land mask act) (m_set_freed (Z.ldiff mask act) r)) st in
    k st1 (Z.land mask act)) bail.

Definition get_stride (mr : meta) : Z :=
  if (m_last_idx mr =? 0) && negb (m_maplen mr =? 0)
  then m_maplen mr * 4096 - UNIT
  else UNIT * size_class (m_sizeclass mr).

Definition area_of (m : aptr) : aptr := (fst m, snd m - (snd m) mod 4096).

Definition get_meta {R} (st : mstate) (p : aptr) (k : aptr -> Z -> Z -> M R) (bail : M R) : M R :=
  guard 10 (snd p mod 16 =? 0) (
  rd16 st (aadd p (-2)) (fun offset16 =>
  rd8 st (aadd p (-3)) (fun b3 =>
  let index := Z.land b3 31 in
  rd8 st (aadd p (-4)) (fun b4 =>
  let cont (offset : Z) :=
    let base := aadd p (- (UNIT * offset) - UNIT) in
    match get_group st base with
    | None => SVis (EUndef UBadPtr) (fun _ => bail)
    | Some gh =>
      match g_meta gh with
      | None => SVis (EUndef UBadPtr) (fun _ => bail)
      | Some m =>
        let mr := get_meta_rec st m in
        guard 11 (optr_eqb (m_mem mr) (Some base)) (
        guard 12 (index <=? m_last_idx mr) (
        guard 13 (negb (testbit (m_avail mr) index)) (
        guard 14 (negb (testbit (m_freed mr) index)) (
        let ar := (s_areas st) !! (area_of m) in
        guard 15 (match ar with Some a => a_check a =? c_secret (ctx st) | None => false end) (
        let sc := m_sizeclass mr in
        guard 16 (if sc <? 48 then (size_class sc * index <=? offset) && (offset <? size_class sc * (index + 1))
                  else sc =? 63) (
        guard 17 (if negb (m_maplen mr =? 0) then offset <=? m_maplen mr * 4096 / UNIT - 1 else true) (
        k m offset index) bail) bail) bail) bail) bail) bail) bail
      end
    end in
  if negb (b4 =? 0) then
    guard 18 (offset16 =? 0) (
    rd32 st (aadd p (-8)) (fun offset32 =>
    guard 19 (65535 <? offset32) (cont offset32) bail)) bail
  else cont offset16)))) bail.

Definition get_nominal_size {R} (st : mstate) (p e : aptr) (k : Z -> M R) (bail : M R) : M R :=
  rd8 st (aadd p (-3)) (fun b3 =>
  let reserved := Z.shiftr b3 5 in
  let cont (reserved : Z) :=
    guard 22 (reserved <=? snd e - snd p) (
    rd8 st (aadd e (- reserved)) (fun cb =>
    guard 23 (cb =? 0) (
    rd8 st e (fun eb =>
    guard 24 (eb =? 0) (k (snd e - reserved - snd p)) bail)) bail)) bail in
  if 5 <=? reserved then
    guard 20 (reserved =? 5) (
    rd32 st (aadd e (-4)) (fun r32 =>
    guard 21 (5 <=? r32) (
    rd8 st (aadd e (-5)) (fun b5 =>
    guard 25 (b5 =? 0) (cont r32) bail)) bail)) bail
  else cont reserved).

Definition set_size (p e : aptr) (n : Z) (b3 : Z) (st : mstate) : mstate :=
  let reserved := snd e - snd p - n in
  let st1 := if negb (reserved =? 0) then wr8 (aadd e (- reserved)) 0 st else st in
  let '(st2, reserved) :=
    if 5 <=? reserved then (wr8 (aadd e (-5)) 0 (wr32 (aadd e (-4)) reserved st1), 5)
    else (st1, reserved) in
  wr8 (aadd p (-3)) (Z.land b3 31 + Z.shiftl reserved 5) st2.

Fixpoint zero_hdrs (p : aptr) (size : Z) (i : Z) (cnt : nat) (st : mstate) : mstate :=
  match cnt with
  | O => st
  | S c => zero_hdrs p size (i + 1) c (wr8 (aadd p (UNIT + i * size - 4)) 0 st)
  end.

Definition fold_off (off slack : Z) : Z :=
  if slack <? off then
    let m := slack in
    let m := Z.lor m (Z.shiftr m 1) in
    let m := Z.lor m (Z.shiftr m 2) in
    let m := Z.lor m (Z.shiftr m 4) in
    let off := Z.land off m in
    if slack <? off then off - (slack + 1) else off
  else off.

Definition slot_start (mr : meta) (idx : Z) : optr :=
  match m_mem mr with
  | Some g => Some (aadd g (UNIT + get_stride mr * idx))
  | None => None
  end.

Definition slot_start' (mr : meta) (idx : Z) : aptr :=
  aadd (default (0%N, 0) (m_mem mr)) (UNIT + get_stride mr * idx).
Definition slot_of (st : mstate) (g : aptr) (idx : Z) : aptr := slot_start' (get_meta_rec st g) idx.

Definition enframe_read_off {R} (st : mstate) (g : aptr) (idx n ctr : Z) (k : Z -> M R) : M R :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let slack := (stride - IB - n) / UNIT in
  let p := slot_start' mr idx in
  rd8 st (aadd p (-3)) (fun b3 =>
    if negb (b3 =? 0) then rd16 st (aadd p (-2)) (fun o16 => k (fold_off (Z.land (o16 + 1) 255) slack))
    else k (fold_off (Z.land ctr 255) slack)).

Definition enframe_at (st : mstate) (g : aptr) (idx n off : Z) : mstate * aptr :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let gm := default (0%N, 0) (m_mem mr) in
  let p := aadd gm (UNIT + stride * idx) in
  let e := aadd p (stride - IB) in
  let '(st1, p) :=
    if negb (off =? 0) then
      let st1 := wr16 (aadd p (-2)) off st in
      let st2 := wr8 (aadd p (-3)) 224 st1 in
      let p' := aadd p (UNIT * off) in
      (wr8 (aadd p' (-4)) 0 st2, p')
    else (st, p) in
  let st2 := wr16 (aadd p (-2)) ((snd p - (snd gm + UNIT)) / UNIT) st1 in
  let st3 := wr8 (aadd p (-3)) idx st2 in
  (set_size p e n idx st3, p).

Definition enframe_full {R} (st : mstate) (g : aptr) (idx n ctr : Z) (k : mstate -> aptr -> M R) : M R :=
  enframe_read_off st g idx n ctr (fun off => let '(st1, p) := enframe_at st g idx n off in k st1 p).

Definition nest_layout (st : mstate) (g : aptr) (idx j : Z) (size cnt : Z) : mstate :=
  let '(st1, p) := enframe_at st g idx (UNIT * size_class j - IB) 0 in
  let st2 := wr8 (aadd p (-3)) (Z.lor (Z.land idx 31) 192) st1 in
  zero_hdrs p size 0 (Z.to_nat (cnt + 1)) st2.

Definition am_take {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_avail_meta (ctx st) with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some m =>
    let st1 := upd_ctx (fun c => set_avail_meta (Some (aadd m META_SIZE)) (set_avail_meta_count (c_avail_meta_count c - 1) c)) st in
    let st2 := upd_meta m (fun r => m_set_prev None (m_set_next None r)) st1 in
    k st2 (Some m)
  end.

Definition am_carve {R} (st : mstate) (p : aptr) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096))
                                (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  let st4 := set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3 in
  let st5 := upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) st4 in
  am_take st5 k bail.

Definition am_finish {R} (st : mstate) (need_unprotect : bool) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  match c_avail_meta_areas (ctx st) with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let need_unprotect := if negb (snd p mod PGSZ =? 0) then false else need_unprotect in
    if need_unprotect then
      SVis (EMprotect (conc st p) PGSZ PROT_RW) (fun r =>
        if negb (mprotect_answer_ok r) then bad_answer bail else
        if (r =? 0) || (r =? TWO64 - ENOSYS) then am_carve st p k bail else k st None)
    else am_carve st p k bail
  end.

Definition am_after_brk {R} (st : mstate) (need_unprotect : bool) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  if c_avail_meta_area_count (ctx st) =? 0 then
    let n := Z.shiftl 2 (c_meta_alloc_shift (ctx st)) in
    SVis (EMmap 0 (n * PGSZ) PROT_NONE (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) (n * PGSZ) r) then bad_answer bail else
      if is_err r then k st None else
      let '(st1, rid) := new_region RKMeta r (n * PGSZ) st in
      let st2 := upd_ctx (fun c => set_meta_alloc_shift (c_meta_alloc_shift c + 1)
                                    (set_avail_meta_area_count (n - 1)
                                    (set_avail_meta_areas (Some (rid, PGSZ)) c))) st1 in
      am_finish st2 need_unprotect k bail)
  else am_finish st need_unprotect k bail.

Definition alloc_meta {R} (st : mstate) (k : mstate -> optr -> M R) (bail : M R) : M R :=

  let st := if c_init_done (ctx st) =? 0
            then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st
            else st in

  match c_free_meta_head (ctx st) with
  | Some m => k (dequeue LFree m st) (Some m)
  | None =>

    if negb (c_avail_meta_count (ctx st) =? 0) then am_take st k bail else

    let brk_dead := match c_brk (ctx st) with BrkDead => true | _ => false end in
    if (c_avail_meta_area_count (ctx st) =? 0) && negb brk_dead then
      match c_brk (ctx st) with
      | BrkUntried =>

        SVis (EBrk 0) (fun cur =>
          if negb (brk0_answer_ok cur) then bad_answer bail else
          let base := round_up_pg cur in
          let new := base + 2 * PGSZ in
          SVis (EBrk new) (fun r =>
            if negb (brk_answer_ok cur new r) then bad_answer bail else
            if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
            else if negb (brk_pages_ok st base (2 * PGSZ)) then bad_answer bail
            else

              SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
                if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else

                let '(st1, rid) := new_region RKBrk base (2 * PGSZ) st in
                let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                              (set_avail_meta_areas (Some (rid, PGSZ))
                                              (set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
                am_after_brk st2 false k bail)))
      | BrkLive rid off =>

        let old := conc st (rid, off) in
        let new := old + PGSZ in
        SVis (EBrk new) (fun r =>
          if negb (brk_answer_ok old new r) then bad_answer bail else
          if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) st) true k bail
          else if negb (brk_pages_ok st old PGSZ) then bad_answer bail
          else
            let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + PGSZ)) st in
            let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
                                          (set_avail_meta_areas (Some (rid, off))
                                          (set_brk (BrkLive rid (off + PGSZ)) c))) st1 in
            am_after_brk st2 false k bail)
      | BrkDead => am_after_brk st true k bail
      end
    else am_after_brk st true k bail
  end.

Fixpoint span_loop (fuel : nat) (cnt span size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_loop f (cnt + 1) (span + size) size else cnt
  end.

Definition ta_fin {R} (st : mstate) (m : aptr) (mask : Z) (k : mstate -> Z -> M R) : M R :=
  let first := lowbit mask in
  k (upd_meta m (m_set_avail (mask - first)) st) first.

Definition try_avail {R} (sc : Z) (st : mstate) (k : mstate -> Z -> M R) (bail : M R) : M R :=
  match active st sc with
  | None => k st 0
  | Some m =>
    let mask := m_avail (get_meta_rec st m) in
    let fin (st : mstate) (m : aptr) (mask : Z) : M R := ta_fin st m mask k in
    if negb (mask =? 0) then fin st m mask else

    let step1 : option (mstate * aptr) :=
      if m_freed (get_meta_rec st m) =? 0 then
        let st1 := dequeue (LActive sc) m st in
        match active st1 sc with None => None | Some m1 => Some (st1, m1) end
      else
        match m_next (get_meta_rec st m) with
        | Some m1 => Some (set_active sc (Some m1) st, m1)
        | None => None
        end in
    match step1 with
    | None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
              else SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (st1, m1) =>
      let mask := m_freed (get_meta_rec st1 m1) in

      let '(st2, m2, mask) :=
        let mr := get_meta_rec st1 m1 in
        if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
          match m_next mr with
          | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
          | None => (st1, m1, mask)
          end
        else (st1, m1, mask) in

      let mr2 := get_meta_rec st2 m2 in
      let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
      let '(st3, m3) :=
        if Z.land mask (mask_upto gai) =? 0 then
          if negb (optr_eqb (m_next mr2) (Some m2)) then
            match m_next mr2 with
            | Some mn => (set_active sc (Some mn) st2, mn)
            | None => (st2, m2)
            end
          else
            let cnt := gai + 2 in
            let size := size_class (m_sizeclass mr2) * UNIT in
            let span := UNIT + size * cnt in
            let cnt := span_loop 300%nat cnt span size in
            let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
            match m_mem mr2 with
            | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
            | None => (st2, m2)
            end
        else (st2, m2) in

      activate_group m3 st3 (fun st4 mask =>
        guard 40 (negb (mask =? 0)) (
          fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask) bail) bail
    end
  end.

Definition small_cnt_pick (sc usage : Z) : Z :=
  if negb (usage <? 4 * small_cnt sc 0) then small_cnt sc 0
  else if negb (usage <? 4 * small_cnt sc 1) then small_cnt sc 1
  else small_cnt sc 2.

Fixpoint halve_even (fuel : nat) (cnt usage : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if (Z.even cnt) && (usage <? 4 * cnt) then halve_even f (Z.shiftr cnt 1) usage else cnt
  end.

Fixpoint halve_big (fuel : nat) (cnt size : Z) : Z :=
  match fuel with
  | O => cnt
  | S f => if 65536 * UNIT <=? size * cnt then halve_big f (Z.shiftr cnt 1) size else cnt
  end.

Definition hdr_havoc (b : aptr) (st : mstate) : mstate :=
  upd_shadow (fst b) (fun r =>
    mkShadow (r_cells r) (<[snd b / 16 := hav_add 12 (s_tick st) (default [] ((r_hav r) !! (snd b / 16)))]> (r_hav r)) (r_havp r)) st.

Record layout_hook : Type := mkLay {
  lh_nest : mstate -> aptr -> Z -> Z -> Z -> Z -> mstate;
  lh_hdr : mstate -> aptr -> mstate
}.
Definition lay_none : layout_hook := mkLay (fun st _ _ _ _ _ => st) (fun st _ => st).
Definition full_lay : layout_hook := mkLay nest_layout (fun st b => hdr_havoc b st).

Definition ag_tail {R} (lay : layout_hook) (st : mstate) (sc : Z) (m : aptr) (p : aptr) (cnt active_idx : Z) (k : mstate -> optr -> M R) : M R :=
  let st := lh_hdr lay st p in
  let st1 := set_usage sc (usage st sc + cnt) st in
  let avail := mask_upto active_idx in
  let freed := mask_upto (cnt - 1) - avail in
  let st2 := upd_meta m (fun r =>
               m_set_sizeclass sc (m_set_freeable 1 (m_set_last_idx (cnt - 1)
               (m_set_mem (Some p) (m_set_freed freed (m_set_avail avail r)))))) st1 in
  let st3 := put_group p (Some m) active_idx st2 in

  let st4 := add_slots m p (get_stride (get_meta_rec st3 m)) cnt st3 in
  k st4 (Some m).

Section ALLOC_GROUP.
Variable R : Type.
Variable lay : layout_hook.
Variable alloc_slot_rec : mstate -> Z -> Z -> (mstate -> Z -> M R) -> M R -> M R.

Definition alloc_group (st : mstate) (sc req : Z) (k : mstate -> optr -> M R) (bail : M R) : M R :=
  let size := UNIT * size_class sc in

  alloc_meta st (fun st mo =>
  match mo with
  | None => k st None
  | Some m =>
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in

    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : M R := ag_tail lay st sc m p cnt active_idx k in
    if PGSZ / 2 <? size * cnt + UNIT then

      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => k st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in

          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else

      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot_rec st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => k st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>

            let p := slot_of st1 g idx in
            let st2 := lh_nest lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail
  end) bail.
End ALLOC_GROUP.

Fixpoint alloc_slot {R} (lay : layout_hook) (fuel : nat) (st : mstate) (sc req : Z) (k : mstate -> Z -> M R) (bail : M R) {struct fuel} : M R :=
  match fuel with
  | O => SVis (EUndef UFuel) (fun _ => bail)
  | S f =>

    try_avail sc st (fun st1 first =>
      if negb (first =? 0) then k st1 (ctz32 first) else

      alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
        match go with
        | None => k st2 (-1)
        | Some g =>
          let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
          queue (LActive sc) g st3 (fun st4 => k st4 0) bail
        end) bail) bail
  end.

Definition FUEL : nat := 64%nat.

Definition malloc_small_ctrl {R} (lay : layout_hook) (st : mstate) (n : Z) (k : mstate -> option (aptr * Z) -> M R) (bail : M R) : M R :=
  let sc := size_to_class n in

  let g := active st sc in

  let sc :=
    match g with
    | Some _ => sc
    | None =>
      if (4 <=? sc) && (sc <? 32) && negb (sc =? 6) && Z.even sc && (usage st sc =? 0) then
        let usage1 := usage st (Z.lor sc 1) in
        let usage1 := match active st (Z.lor sc 1) with
                      | None => usage1 + 3
                      | Some _ => let ar := get_meta_rec st (default (0%N,-1) (active st (Z.lor sc 1))) in
                                  if (m_avail ar =? 0) && (m_freed ar =? 0) then usage1 + 3 else usage1
                      end in
        if usage1 <=? 12 then Z.lor sc 1 else sc
      else sc
    end in
  let g := active st sc in

  let mask := match g with Some gp => m_avail (get_meta_rec st gp) | None => 0 end in
  let first := lowbit mask in
  match g, negb (first =? 0) with
  | Some gp, true => k (upd_meta gp (m_set_avail (mask - first)) st) (Some (gp, ctz32 first))
  | _, _ =>

    alloc_slot lay FUEL st sc n (fun st1 idx =>
      if idx <? 0 then k st1 None
      else match active st1 sc with
           | Some gp => k st1 (Some (gp, idx))
           | None => SVis (EUndef UBadPtr) (fun _ => bail)
           end) bail
  end.

Definition malloc_core (lay : layout_hook) (st : mstate) (n : Z) : M (mstate * option (aptr * Z)) :=
  let bail := ret (st, @None (aptr * Z)) in

  if size_overflows n then ret (st, None) else
  if MMAP_THRESHOLD <=? n then

    let needed := n + IB + UNIT in
    SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st) needed r) then bad_answer bail else
      if is_err r then ret (st, None) else
      let '(st1, rid) := new_region RKGroup r needed st in

      let st2 := step_seq st1 in
      alloc_meta st2 (fun st3 go =>
        match go with
        | None =>

          SVis (EMunmap r needed) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, None) else bad_answer bail)
        | Some g =>

          let st4 := upd_meta g (fun mr =>
                       m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
                       (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
          let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr lay st4 (rid, 0)) in
          let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
          let st7 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6 in
          ret (st7, Some (g, 0))
        end) bail)
  else
    malloc_small_ctrl lay st n (fun st1 r => ret (st1, r)) bail.

Definition malloc (st0 : mstate) (n : Z) : M (mstate * optr) :=
  let st := set_tick (N.succ (s_tick st0)) st0 in
  '(st1, r) <-- malloc_core full_lay st n ;;
  match r with
  | None => ret (st1, None)
  | Some (g, idx) =>

    enframe_full st1 g idx n (c_mmap_counter (ctx st1)) (fun st2 p => ret (havoc p n st2, Some p))
  end.

Definition okay_to_free (st : mstate) (g : aptr) : bool :=
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if m_freeable mr =? 0 then false
  else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
  else if m_maplen mr =? 0 then true
  else if negb (optr_eqb (m_next mr) (Some g)) then true
  else if negb (is_bouncing sc st) then true
  else
    let cnt := m_last_idx mr + 1 in
    let usg := usage st sc in
    if (9 * cnt <=? usg) && (cnt <? 20) then true else false.

Definition mapinfo : Type := option (aptr * Z).

Definition decoder (R : Type) := mstate -> aptr -> (aptr -> Z -> M R) -> M R -> M R.
Definition dec_hdr {R} : decoder R := fun st p k bail => get_meta st p (fun m _ idx => k m idx) bail.
Definition dec_slots {R} : decoder R := fun st p k bail =>
  match (s_slots st) !! p with
  | Some (m, idx) => k m idx
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  end.

Section FREE_GROUP.
Variable R : Type.
Variable dec : decoder R.
Variable nontrivial_free_rec : mstate -> aptr -> Z -> (mstate -> mapinfo -> M R) -> M R -> M R.

Definition free_group (st : mstate) (g : aptr) (k : mstate -> mapinfo -> M R) (bail : M R) : M R :=
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in

  let st1 := if sc <? 48 then set_usage sc (usage st sc - (m_last_idx mr + 1)) st else st in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>

    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then

      let st2 := record_seq sc (step_seq st1) in
      free_meta g st2 (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else

      dec st1 p (fun m idx =>
        nontrivial_free_rec st1 m idx (fun st3 mi =>
          free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
End FREE_GROUP.

Fixpoint nontrivial_free {R} (dec : decoder R) (fuel : nat) (st : mstate) (g : aptr) (i : Z) (k : mstate -> mapinfo -> M R) (bail : M R) {struct fuel} : M R :=
  match fuel with
  | O => SVis (EUndef UFuel) (fun _ => bail)
  | S f =>
    let mr := get_meta_rec st g in
    let self := bit i in
    let sc := m_sizeclass mr in
    let mask := Z.lor (m_freed mr) (m_avail mr) in
    if (mask + self =? mask_upto (m_last_idx mr)) && okay_to_free st g then

      match m_next mr with
      | Some _ =>
        guard 50 (sc <? 48) (
          let activate_new := optr_eqb (active st sc) (Some g) in
          let st1 := dequeue (LActive sc) g st in
          match activate_new, active st1 sc with
          | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
          | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
          end) bail
      | None => free_group R dec (nontrivial_free dec f) st g k bail
      end
    else if mask =? 0 then

      guard 51 (sc <? 48) (
        let aor (st : mstate) := k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None in
        if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st aor bail
        else aor st) bail
    else

      k (upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) self) r) st) None
  end.

Definition free_tail (dec : decoder mstate) (st : mstate) (g : aptr) (idx : Z) : M mstate :=
  let mr := get_meta_rec st g in
  let self := bit idx in
  let all := mask_upto (m_last_idx mr) in

  let freed := m_freed mr in
  let avail := m_avail mr in
  let mask := Z.lor freed avail in
  guard 60 (negb (testbit mask idx)) (
    if negb ((freed =? 0) || (mask + self =? all)) then
      ret (upd_meta g (m_set_freed (freed + self)) st)
    else

      nontrivial_free dec FUEL st g idx (fun st2 mi =>
        match mi with
        | Some (base, len) =>
          if negb (len =? 0) then
            SVis (EMunmap (conc st2 base) len) (fun ru => if munmap_answer_ok ru then ret (drop_region (fst base) st2) else bad_answer (ret st))
          else ret st2
        | None => ret st2
        end) (ret st)) (ret st).

Definition free_hdr (st : mstate) (p : aptr) : M (option (mstate * aptr * Z)) :=
  let bail := ret (@None (mstate * aptr * Z)) in

  get_meta st p (fun g _ idx =>
    let mr := get_meta_rec st g in
    match slot_start mr idx with
    | None => SVis (EUndef UBadPtr) (fun _ => bail)
    | Some start =>
      let e := aadd start (get_stride mr - IB) in
      get_nominal_size st p e (fun _ =>
        let st1 := wr16 (aadd p (-2)) 0 (wr8 (aadd p (-3)) 255 st) in
        ret (Some (st1, g, idx))) bail
    end) bail.

Definition free (st : mstate) (p : optr) : M mstate :=
  match p with
  | None => ret st
  | Some p =>
    r <-- free_hdr st p ;;
    match r with
    | None => ret st
    | Some (st1, g, idx) => free_tail dec_hdr st1 g idx
    end
  end.

Definition cptr : Type := aptr.

Definition strip (st : mstate) : mstate :=
  mkState (s_ctx st) (s_regions st) ∅ (s_next_rid st) (s_metas st) (s_areas st)
          (s_groups st) (s_slots st) 0%N (s_secret st) (s_reserved st).

Definition cmalloc (cs : mstate) (n : Z) : M (mstate * option cptr) :=
  '(st1, r) <-- malloc_core lay_none cs n ;;
  ret (strip st1, match r with Some (g, idx) => Some (slot_of st1 g idx) | None => None end).

Definition cfree (cs : mstate) (p : option cptr) : M mstate :=
  match p with
  | None => ret cs
  | Some s =>
    match (s_slots cs) !! s with
    | None => SVis (EUndef UBadPtr) (fun _ => ret cs)
    | Some (g, idx) => '(st1) <-- free_tail dec_slots cs g idx ;; ret (strip st1)
    end
  end.
