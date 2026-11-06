(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From Stdlib Require Import FMapPositive.
Import ListNotations.
Open Scope Z_scope.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition kShadowOffset      : Z := 0x7fff8000.
Definition kHighMemEnd        : Z := 0x7fffffffffff.
Definition kHighMemBeg        : Z := 0x10007fff8000.
Definition kLowMemEnd         : Z := kShadowOffset - 1.
Definition kSpaceSize         : Z := 2^37.
Definition kRegionSizeLog     : Z := 32.
Definition kRegionSize        : Z := 2^32.
Definition kFreeArrayOffset   : Z := 0xE0000000.
Definition kFreeArraySize     : Z := 0x20000000.
Definition kUserMapSize       : Z := 0x40000.
Definition kFreeArrayMapSize  : Z := 0x40000.
Definition kNumClasses        : Z := 32.
Definition kMaxSize           : Z := 0x10000.
Definition kCompactPtrScale   : Z := 4.
Definition kPageSize          : Z := 4096.
Definition kChunkHeaderSize   : Z := 16.
Definition kChunkHeader2Size  : Z := 8.
Definition kMinRedzoneLog     : Z := 0.
Definition kMaxRedzoneLog     : Z := 7.
Definition kMaxAllowedMalloc  : Z := 2^40.
Definition kMaxMallocFillSize : Z := 4096.
Definition kMallocFillByte    : Z := 0xbe.
Definition kClearShadowMmapThreshold : Z := 0x10000.
Definition kQuarantineMaxSize : Z := 0x10000000.
Definition kQuarantineMinSize : Z := 0xE666661.
Definition kMaxCacheSize      : Z := 0x100000.
Definition kBatchSize         : Z := 8192.
Definition kBatchCount        : Z := 1021.
Definition kBatchClass        : Z := 24.
Definition kChunksBlockCount  : Z := 0x4000.
Definition kMaxNumChunks      : Z := 2^20.
Definition kPtrArrayReserve   : Z := 0x800000.

Definition kAsanHeapLeftRedzoneMagic : Z := 0xfa.
Definition kAsanHeapFreeMagic        : Z := 0xfd.

Definition PROT_NONE : Z := 0.  Definition PROT_RW : Z := 3.
Definition MAP_PA    : Z := 0x22.
Definition MAP_PAF   : Z := 0x32.
Definition MAP_PAFN  : Z := 0x4032.

Definition round_up (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition round_down (x a : Z) : Z := (x / a) * a.
Definition mem_to_shadow (a : Z) : Z := kShadowOffset + a / 8.
Definition addr_is_in_mem (a : Z) : bool :=
  ((0 <=? a) && (a <=? kLowMemEnd)) || ((kHighMemBeg <=? a) && (a <=? kHighMemEnd)).

Definition msb (x : Z) : Z := Z.log2 x.

Fixpoint znth {A} (l : list A) (i : nat) (d : A) : A :=
  match l, i with
  | [], _ => d
  | x :: _, O => x
  | _ :: r, S i' => znth r i' d
  end.
Fixpoint upd_nth {A} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: upd_nth r i' x
  end.
Definition zidx (i : Z) : nat := Z.to_nat i.
Fixpoint zrepeat {A} (x : A) (n : nat) : list A := match n with O => [] | S n' => x :: zrepeat x n' end.
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).

Definition class_size (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let t := Z.shiftl 512 ((c - 16) / 2) in
       if Z.odd (c - 16) then t + t / 2 else t.

Definition class_id (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := msb s in
       let hbits := Z.land (Z.shiftr s (l - 1)) 1 in
       let lbits := Z.land s (Z.shiftl 1 (l - 1) - 1) in
       16 + Z.shiftl (l - 9) 1 + hbits + (if 0 <? lbits then 1 else 0).

Definition max_cached_hint (sz : Z) : Z :=
  if sz =? 0 then 0 else let n := 1024 / sz in Z.max 1 (Z.min 8 n).
Definition max_count (c : Z) : Z := 2 * max_cached_hint (class_size c).

Definition class_size_table : list Z :=
  [0;32;64;96;128;160;192;224;256;288;320;352;384;416;448;480;512;
   768;1024;1536;2048;3072;4096;6144;8192;12288;16384;24576;32768;49152;65536;64].
Definition max_count_table : list Z :=
  [0;16;16;16;16;12;10;8;8;6;6;4;4;4;4;4;4;2;2;2;2;2;2;2;2;2;2;2;2;2;2;16].

Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := Z.shiftl 16 (Z.min (Z.max (rz_log n) kMinRedzoneLog) kMaxRedzoneLog).

Record req := mkReq {
  rq_n        : Z;
  rq_size     : Z;
  rq_rz       : Z;
  rq_rounded  : Z;
  rq_needed   : Z;
  rq_primary  : bool
}.

Definition compute_req (n : Z) : req :=
  let size' := if n =? 0 then 1 else n in
  let rz := rz_size n in
  let rounded := round_up (Z.max n 8) 8 in
  let needed0 := rounded + rz in
  let prim := needed0 <=? kMaxSize in
  let needed := if prim then needed0 else needed0 + rz in
  mkReq n size' rz rounded needed prim.

Definition size_too_big (r : req) : bool :=
  (kMaxAllowedMalloc <? rq_n r) || (kMaxAllowedMalloc <? rq_needed r) || (kMaxAllowedMalloc <? rq_size r).

Record region := mkRegion {
  rg_mapped_user       : Z;
  rg_allocated_user    : Z;
  rg_num_freed         : Z;
  rg_free_array        : list Z;
  rg_mapped_free_array : Z
}.
Definition region0 := mkRegion 0 0 0 [] 0.

Record pclass := mkPC { pc_count : Z; pc_chunks : list Z   }.
Definition pclass0 := mkPC 0 [].

Record schunk := mkSC { sc_map_beg : Z; sc_map_size : Z; sc_size : Z }.

Inductive cstate := CAllocated | CQuarantine.
Record chunk := mkChunk {
  ch_alloc_beg : Z;
  ch_user_beg  : Z;
  ch_used      : Z;
  ch_rz        : Z;
  ch_class     : Z;
  ch_state     : cstate
}.
Definition ch_primary (c : chunk) : bool := negb (ch_class c =? 0).
Definition ch_chunk_beg (c : chunk) : Z := ch_user_beg c - kChunkHeaderSize.

Record qbatch := mkQB { qb_addr : Z; qb_size : Z; qb_count : Z; qb_chunks : list Z   }.

Record qcache := mkQC { qc_list : list qbatch; qc_bytes : Z }.
Definition qcache0 := mkQC [] 0.

Inductive mkind :=
  | MkPrimaryReservation
  | MkRegionInfo
  | MkUserMap (cls : Z)
  | MkFreeArrayMap (cls : Z)
  | MkPtrArrayReservation
  | MkPtrArrayCommit
  | MkSecondary
  | MkShadowRemap.
Record mapping := mkMap { mp_base : Z; mp_size : Z; mp_kind : mkind; mp_prot : Z; mp_lazy : bool }.

Inductive effect :=
  | EMmap (hint len prot flags ret : Z)
  | EMunmap (addr len : Z)
  | EPoison (addr size val : Z)
  | EShadow1 (app_addr val : Z)
  | EFill (addr n byte : Z)
  | EStore64 (addr val : Z)
  | EInternalAllocInit.

Record astate := mkState {
  as_space_beg     : Z;
  as_ptr_array     : Z;
  as_regions       : list region;
  as_cache_inited  : bool;
  as_cache         : list pclass;
  as_n_reserved    : Z;
  as_sec           : list schunk;
  as_chunks        : PositiveMap.t chunk;
  as_tq            : qcache;
  as_gq            : qcache;
  as_internal_init : bool;
  as_maps          : list mapping;
  as_shadow        : list (Z * Z * Z);
  as_env           : list Z;
  as_track_shadow  : bool;
  as_qmax          : Z;
  as_qmin          : Z;
  as_qcache        : Z

}.

Definition get_region (st : astate) (c : Z) : region := znth (as_regions st) (zidx c) region0.
Definition set_region (st : astate) (c : Z) (r : region) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (upd_nth (as_regions st) (zidx c) r) (as_cache_inited st)
          (as_cache st) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
          (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition get_pc (st : astate) (c : Z) : pclass := znth (as_cache st) (zidx c) pclass0.
Definition set_pc (st : astate) (c : Z) (p : pclass) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st)
          (upd_nth (as_cache st) (zidx c) p) (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st)
          (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_cache_inited (st : astate) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) true (as_cache st) (as_n_reserved st)
          (as_sec st) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_sec (st : astate) (nres : Z) (s : list schunk) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st) nres s
          (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_chunks (st : astate) (l : PositiveMap.t chunk) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) l (as_tq st) (as_gq st) (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_tq (st : astate) (q : qcache) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) q (as_gq st) (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_gq (st : astate) (q : qcache) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) q (as_internal_init st) (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition set_internal_init (st : astate) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st) true (as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition add_map (st : astate) (m : mapping) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st)
          (m :: as_maps st) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition remove_map (st : astate) (base : Z) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st)
          (filter (fun m => negb (mp_base m =? base)) (as_maps st)) (as_shadow st) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition paint (st : astate) (lo hi v : Z) : astate :=
  mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st)
          (as_maps st) (if as_track_shadow st then (lo, hi, v) :: as_shadow st else []) (as_env st) (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st).
Definition pop_env (st : astate) : Z * astate :=
  match as_env st with
  | [] => (0, st)
  | k :: r => (k, mkState (as_space_beg st) (as_ptr_array st) (as_regions st) (as_cache_inited st) (as_cache st)
                          (as_n_reserved st) (as_sec st) (as_chunks st) (as_tq st) (as_gq st) (as_internal_init st)
                          (as_maps st) (as_shadow st) r (as_track_shadow st) (as_qmax st) (as_qmin st) (as_qcache st))
  end.

Fixpoint shadow_lookup (ps : list (Z * Z * Z)) (a : Z) : option Z :=
  match ps with
  | [] => None
  | (lo, hi, v) :: r => if (lo <=? a) && (a <? hi) then Some v else shadow_lookup r a
  end.
Definition shadow_at (st : astate) (a : Z) : option Z := shadow_lookup (as_shadow st) (round_down a 8).

Definition ckey (user : Z) : positive := Z.to_pos user.
Definition find_chunk (m : PositiveMap.t chunk) (user : Z) : option chunk :=
  if user <=? 0 then None else PositiveMap.find (ckey user) m.
Definition remove_chunk (m : PositiveMap.t chunk) (user : Z) : PositiveMap.t chunk := PositiveMap.remove (ckey user) m.
Definition upd_chunk (st : astate) (c : chunk) : astate :=
  set_chunks st (PositiveMap.add (ckey (ch_user_beg c)) c (as_chunks st)).
Definition chunk_list (st : astate) : list chunk := map snd (PositiveMap.elements (as_chunks st)).

Definition region_beg (st : astate) (c : Z) : Z := as_space_beg st + Z.shiftl c kRegionSizeLog.
Definition free_array_base (st : astate) (c : Z) : Z := region_beg st c + kFreeArrayOffset.
Definition compact_to_addr (st : astate) (c : Z) (cp : Z) : Z := region_beg st c + Z.shiftl cp kCompactPtrScale.
Definition addr_to_compact (st : astate) (c : Z) (a : Z) : Z := Z.shiftr (a - region_beg st c) kCompactPtrScale.
Definition in_primary (st : astate) (a : Z) : bool := (as_space_beg st <=? a) && (a <? as_space_beg st + kSpaceSize).
Definition class_of_addr (st : astate) (a : Z) : Z := Z.land (Z.shiftr (a - as_space_beg st) kRegionSizeLog) 31.

Definition poison_shadow (st : astate) (addr size val : Z) : option (astate * list effect) :=
  if negb (Z.land addr 7 =? 0) then None else
  if negb (addr_is_in_mem addr) then None else
  if negb (Z.land size 7 =? 0) then None else
  if negb (addr_is_in_mem (addr + size - 8)) then None else
  let shadow_beg := mem_to_shadow addr in
  let shadow_end := mem_to_shadow (addr + size - 8) + 1 in
  let len := shadow_end - shadow_beg in
  let st' := if 0 <? size then paint st addr (addr + size) val else st in
  let ev := EPoison addr size val in
  if negb (val =? 0) then Some (st', [ev])
  else if len <? kClearShadowMmapThreshold then Some (st', [ev])
  else
    let page_beg := round_up shadow_beg kPageSize in
    let page_end := round_down shadow_end kPageSize in
    if page_end <=? page_beg then Some (st', [ev])
    else

      Some (st', [ev; EMmap page_beg (page_end - page_beg) PROT_RW MAP_PAFN page_beg]).

Definition ensure_cache_inited (st : astate) : astate :=
  if as_cache_inited st then st else set_cache_inited st.

Definition map_fixed (st : astate) (addr size : Z) (k : mkind) : astate * list effect :=
  (add_map st (mkMap addr size k PROT_RW false), [EMmap addr size PROT_RW MAP_PAF addr]).

Definition ensure_free_array_space (st : astate) (c : Z) (num_freed : Z) : option (astate * list effect) :=
  let r := get_region st c in
  let needed := num_freed * 4 in
  if needed <=? rg_mapped_free_array r then Some (st, [])
  else
    let new_mapped := round_up needed kFreeArrayMapSize in
    if kFreeArraySize <? new_mapped then None else
    let cur_end := free_array_base st c + rg_mapped_free_array r in
    let sz := new_mapped - rg_mapped_free_array r in
    let (st1, ev1) := map_fixed st cur_end sz (MkFreeArrayMap c) in
    match poison_shadow st1 cur_end sz kAsanHeapLeftRedzoneMagic with
    | None => None
    | Some (st2, ev2) =>
        let r' := mkRegion (rg_mapped_user r) (rg_allocated_user r) (rg_num_freed r) (rg_free_array r) new_mapped in
        Some (set_region st2 c r', ev1 ++ ev2)
    end.

Fixpoint carve_asc (base size : Z) (i : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => Z.shiftr (base + i * size) kCompactPtrScale :: carve_asc base size (i + 1) k'
  end.

Definition populate_free_array (st : astate) (c : Z) (requested : Z) : option (astate * list effect) :=
  let r := get_region st c in
  let size := class_size c in
  let total_user_bytes := rg_allocated_user r + requested * size in
  let step1 : option (astate * region * list effect) :=
    if total_user_bytes <=? rg_mapped_user r then Some (st, r, [])
    else

      let user_map_size := round_up (total_user_bytes - rg_mapped_user r) kUserMapSize in
      if kFreeArrayOffset <? rg_mapped_user r + 0   + user_map_size then None
      else
        let beg := region_beg st c + rg_mapped_user r in
        let (st1, ev1) := map_fixed st beg user_map_size (MkUserMap c) in
        match poison_shadow st1 beg user_map_size kAsanHeapLeftRedzoneMagic with
        | None => None
        | Some (st2, ev2) =>
            let r' := mkRegion (rg_mapped_user r + user_map_size) (rg_allocated_user r) (rg_num_freed r)
                               (rg_free_array r) (rg_mapped_free_array r) in
            Some (set_region st2 c r', r', ev1 ++ ev2)
        end in
  match step1 with
  | None => None
  | Some (st1, r1, ev1) =>
      let new_chunks := (rg_mapped_user r1 - rg_allocated_user r1) / size in
      let total_freed := rg_num_freed r1 + new_chunks in
      match ensure_free_array_space st1 c total_freed with
      | None => None
      | Some (st2, ev2) =>
          let r2 := get_region st2 c in

          let seg := carve_asc (rg_allocated_user r2) size 0 (Z.to_nat new_chunks) in
          let r3 := mkRegion (rg_mapped_user r2) (rg_allocated_user r2 + new_chunks * size) total_freed
                             (seg ++ rg_free_array r2) (rg_mapped_free_array r2) in
          if rg_mapped_user r3 <? rg_allocated_user r3 then None
          else Some (set_region st2 c r3, ev1 ++ ev2)
      end
  end.

Definition get_from_allocator (st : astate) (c : Z) (n : Z) : option (astate * list Z * list effect) :=
  let r := get_region st c in
  let step : option (astate * list effect) :=
    if rg_num_freed r <? n then
      match populate_free_array st c (n - rg_num_freed r) with
      | None => None
      | Some (st1, ev1) => if rg_num_freed (get_region st1 c) <? n then None   else Some (st1, ev1)
      end
    else Some (st, []) in
  match step with
  | None => None
  | Some (st1, ev1) =>
      let r1 := get_region st1 c in
      let k := Z.to_nat n in

      let taken := firstn k (rg_free_array r1) in
      let r2 := mkRegion (rg_mapped_user r1) (rg_allocated_user r1) (rg_num_freed r1 - n) (skipn k (rg_free_array r1)) (rg_mapped_free_array r1) in
      Some (set_region st1 c r2, taken, ev1)
  end.

Definition cache_alloc (st : astate) (c : Z) : option (astate * Z * list effect) :=
  if (c =? 0) || (kNumClasses <=? c) then None else
  let pc := get_pc st c in
  let step : option (astate * pclass * list effect) :=
    if pc_count pc =? 0 then
      let st1 := ensure_cache_inited st in
      let n := max_count c / 2 in
      match get_from_allocator st1 c n with
      | None => None
      | Some (st2, taken, ev) => Some (st2, mkPC n taken, ev)
      end
    else Some (st, pc, []) in
  match step with
  | None => None
  | Some (st1, pc1, ev) =>
      match pc_chunks pc1 with
      | [] => None
      | cp :: rest =>
          let st2 := set_pc st1 c (mkPC (pc_count pc1 - 1) rest) in
          Some (st2, compact_to_addr st2 c cp, ev)
      end
  end.

Definition return_to_allocator (st : astate) (c : Z) (n : Z) (cps_tf : list Z) : option (astate * list effect) :=
  let r := get_region st c in
  let new_num := rg_num_freed r + n in
  match ensure_free_array_space st c new_num with
  | None => None
  | Some (st1, ev) =>
      let r1 := get_region st1 c in
      let r2 := mkRegion (rg_mapped_user r1) (rg_allocated_user r1) new_num (cps_tf ++ rg_free_array r1) (rg_mapped_free_array r1) in
      Some (set_region st1 c r2, ev)
  end.

Definition cache_dealloc (st : astate) (c : Z) (p : Z) : option (astate * list effect) :=
  if (c =? 0) || (kNumClasses <=? c) then None else
  let st0 := ensure_cache_inited st in
  let pc := get_pc st0 c in
  let step : option (astate * pclass * list effect) :=
    if pc_count pc =? max_count c then
      let cnt := max_count c / 2 in
      if pc_count pc <? cnt then None else
      let k := Z.to_nat cnt in
      let ret := firstn k (pc_chunks pc) in
      let keep := skipn k (pc_chunks pc) in
      let pck := mkPC (pc_count pc - cnt) keep in
      match return_to_allocator (set_pc st0 c pck) c cnt ret with
      | None => None
      | Some (st1, ev) => Some (st1, pck, ev)
      end
    else Some (st0, pc, []) in
  match step with
  | None => None
  | Some (st1, pc1, ev) =>
      let pc2 := mkPC (pc_count pc1 + 1) (addr_to_compact st1 c p :: pc_chunks pc1) in
      Some (set_pc st1 c pc2, ev)
  end.

Definition large_allocate (st : astate) (needed : Z) (kaddr : Z) : option (astate * Z * list effect) :=
  let map_size := round_up needed kPageSize + kPageSize in
  if map_size <? needed then None else
  let map_beg := kaddr in
  if negb (Z.land map_beg (kPageSize - 1) =? 0) then None else
  let ev0 := [EMmap 0 map_size PROT_RW MAP_PA map_beg] in
  let st0 := add_map st (mkMap map_beg map_size MkSecondary PROT_RW false) in
  let map_end := map_beg + map_size in
  let res := map_beg + kPageSize in

  match poison_shadow st0 map_beg (round_up res 8 - map_beg) kAsanHeapLeftRedzoneMagic with
  | None => None
  | Some (st1, ev1) =>
    let tail := round_down (res + needed) 8 in
    match poison_shadow st1 tail (map_end - tail) kAsanHeapLeftRedzoneMagic with
    | None => None
    | Some (st2, ev2) =>
      if map_end <? res + needed then None else

      let n := zlen (as_sec st2) in
      if kMaxNumChunks <=? n then None else
      let '(st3, nres, ev3) :=
        if n =? as_n_reserved st2 then
          let (st', ev') := map_fixed st2 (as_ptr_array st2 + as_n_reserved st2 * 8) (kChunksBlockCount * 8) MkPtrArrayCommit in
          (st', as_n_reserved st2 + kChunksBlockCount, ev')
        else (st2, as_n_reserved st2, []) in
      let st4 := set_sec st3 nres (as_sec st3 ++ [mkSC map_beg map_size needed]) in
      Some (st4, res, ev0 ++ ev1 ++ ev2 ++ ev3)
    end
  end.

Fixpoint nearest_le (l : list schunk) (m : Z) (best : option schunk) : option schunk :=
  match l with
  | [] => best
  | h :: r =>
      if m <? sc_map_beg h then nearest_le r m best
      else match best with
           | None => nearest_le r m (Some h)
           | Some b => if m - sc_map_beg h <? m - sc_map_beg b then nearest_le r m (Some h) else nearest_le r m best
           end
  end.
Definition large_get_block_begin (st : astate) (m : Z) : option Z :=
  match nearest_le (as_sec st) m None with
  | None => Some 0
  | Some h => if sc_map_beg h + sc_map_size h <=? m then Some 0 else Some (sc_map_beg h + kPageSize)
  end.

Fixpoint find_sec_idx (l : list schunk) (map_beg : Z) (i : nat) : option nat :=
  match l with [] => None | h :: r => if sc_map_beg h =? map_beg then Some i else find_sec_idx r map_beg (S i) end.

Definition large_deallocate (st : astate) (p : Z) : option (astate * list effect) :=
  if negb (Z.land p (kPageSize - 1) =? 0) then None else
  let map_beg := p - kPageSize in
  match find_sec_idx (as_sec st) map_beg 0%nat with
  | None => None
  | Some idx =>
      let h := znth (as_sec st) idx (mkSC 0 0 0) in
      let n := length (as_sec st) in
      let last := znth (as_sec st) (n - 1)%nat (mkSC 0 0 0) in

      let l1 := firstn (n - 1)%nat (upd_nth (as_sec st) idx last) in
      let st1 := set_sec st (as_n_reserved st) l1 in
      match poison_shadow st1 map_beg (sc_map_size h) 0 with
      | None => None
      | Some (st2, ev2) =>

          if negb (addr_is_in_mem map_beg && addr_is_in_mem (map_beg + sc_map_size h)) then None else
          let st3 := remove_map st2 map_beg in
          Some (st3, ev2 ++ [EMunmap map_beg (sc_map_size h)])
      end
  end.

Definition actually_allocated_size (st : astate) (allocated : Z) : option Z :=
  if in_primary st allocated then Some (class_size (class_of_addr st allocated))
  else if negb (Z.land allocated (kPageSize - 1) =? 0) then None
  else match nearest_le (as_sec st) allocated None with
       | Some h => if sc_map_beg h =? allocated - kPageSize then Some (round_up (sc_size h) kPageSize) else None
       | None => None
       end.

Definition am_malloc_k (st : astate) (n : Z) (kaddr : Z) : option (Z * astate * list effect) :=
  if n <? 0 then None else
  let r := compute_req n in
  if size_too_big r then None else

  let needed := rq_needed r in
  let alloc : option (astate * Z * Z * list effect) :=
    if (kMaxSize <? needed) then
      match large_allocate st needed kaddr with
      | None => None
      | Some (st1, res, ev) => Some (st1, res, 0, ev)
      end
    else
      let c := class_id needed in
      match cache_alloc st c with
      | None => None
      | Some (st1, a, ev) => Some (st1, a, c, ev)
      end in
  match alloc with
  | None => None
  | Some (st1, allocated, cls, ev1) =>
    let user_beg := allocated + rq_rz r in
    let user_end := user_beg + rq_size r in
    if allocated + needed <? user_end then None else

    let ch := mkChunk allocated user_beg (rq_size r) (rq_rz r) cls CAllocated in
    let st2 := upd_chunk st1 ch in

    let do_rz := negb (rq_primary r) in
    let step13 : option (astate * list effect) :=
      if do_rz then
        match actually_allocated_size st2 allocated with
        | None => None
        | Some asz =>
          let tail_beg := round_up user_end 8 in
          match poison_shadow st2 allocated (user_beg - allocated) kAsanHeapLeftRedzoneMagic with
          | None => None
          | Some (st3, e3) =>
            match poison_shadow st3 tail_beg (allocated + asz - tail_beg) kAsanHeapLeftRedzoneMagic with
            | None => None
            | Some (st4, e4) => Some (st4, e3 ++ e4)
            end
          end
        end
      else Some (st2, []) in
    match step13 with
    | None => None
    | Some (st3, ev3) =>

      let rd := Z.land (rq_size r) (Z.lnot 7) in
      let step14 := if 0 <? rd then poison_shadow st3 user_beg rd 0 else Some (st3, []) in
      match step14 with
      | None => None
      | Some (st4, ev4) =>

        let g := user_beg + rd in
        let step15 : option (astate * list effect) :=
          if negb (rq_size r =? rd) then
            if negb (addr_is_in_mem g) then None
            else Some (paint st4 g (g + 8) (Z.land (rq_size r) 7), [EShadow1 g (Z.land (rq_size r) 7)])
          else Some (st4, []) in
        match step15 with
        | None => None
        | Some (st5, ev5) =>

          let fill := [EFill user_beg (Z.min (rq_size r) kMaxMallocFillSize) kMallocFillByte] in
          if negb (user_beg - kChunkHeaderSize =? allocated) && (user_beg - kChunkHeaderSize <? allocated + 16) then None
          else Some (user_beg, st5, ev1 ++ ev3 ++ ev4 ++ ev5 ++ fill)
        end
      end
    end
  end.

Definition am_malloc_full (st : astate) (n : Z) : option (Z * astate * list effect) :=
  let r := compute_req n in
  if rq_primary r then am_malloc_k st n 0
  else let (k, st') := pop_env st in am_malloc_k st' n k.

Definition cb_recycle (st : astate) (m : Z) : option (astate * list effect) :=
  match find_chunk (as_chunks st) (m + kChunkHeaderSize) with
  | None => None
  | Some ch =>
    match ch_state ch with
    | CAllocated => None
    | CQuarantine =>
      if in_primary st m then

        let c := class_of_addr st m in
        let size := class_size c in
        if (c =? 0) then None else
        let off := m - region_beg st c in
        let beg := region_beg st c + (off / size) * size in
        let r := get_region st c in
        if rg_mapped_user r <? (off / size + 1) * size then None else
        let p := beg in
        if negb (p =? ch_alloc_beg ch) then None else

        match poison_shadow st (ch_user_beg ch) (round_up (ch_used ch) 8) kAsanHeapLeftRedzoneMagic with
        | None => None
        | Some (st1, ev1) =>
          let st2 := set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)) in
          match cache_dealloc st2 c p with
          | None => None
          | Some (st3, ev3) => Some (st3, ev1 ++ ev3)
          end
        end
      else
        match large_get_block_begin st m with
        | None => None
        | Some p =>
          if p =? 0 then None else
          if in_primary st p then None else
          if negb (p =? ch_alloc_beg ch) then None else
          let st1 := set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch)) in
          large_deallocate st1 p
        end
    end
  end.

Fixpoint cb_recycle_list (st : astate) (ms : list Z) (racc : list effect) : option (astate * list effect) :=
  match ms with
  | [] => Some (st, racc)
  | m :: r => match cb_recycle st m with
              | None => None
              | Some (st1, ev) => cb_recycle_list st1 r (rev_append ev racc)
              end
  end.

Fixpoint do_recycle (st : astate) (bs : list qbatch) (racc : list effect) : option (astate * list effect) :=
  match bs with
  | [] => Some (st, racc)
  | b :: r =>
    match cb_recycle_list st (qb_chunks b) racc with
    | None => None
    | Some (st1, racc1) =>

      if negb (in_primary st1 (qb_addr b)) then None else
      match cache_dealloc st1 (class_of_addr st1 (qb_addr b)) (qb_addr b) with
      | None => None
      | Some (st2, ev2) => do_recycle st2 r (rev_append ev2 racc1)
      end
    end
  end.

Fixpoint merge_batches_aux (fuel : nat) (cur : qbatch) (rest : list qbatch) (racc_done : list qbatch)
         (rextracted : list qbatch) (xbytes : Z) : option (list qbatch * list qbatch * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
    match rest with
    | [] => Some (rev (cur :: racc_done), rev rextracted, xbytes)
    | nx :: rest' =>
      if qb_count cur + qb_count nx <=? kBatchCount then
        if qb_size cur <? kBatchSize then None else
        let cur' := mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx)
                         (qb_chunks cur ++ qb_chunks nx) in
        let nx'  := mkQB (qb_addr nx) kBatchSize 0 [] in
        merge_batches_aux fuel' cur' rest' racc_done (nx' :: rextracted) (xbytes + kBatchSize)
      else merge_batches_aux fuel' nx rest' (cur :: racc_done) rextracted xbytes
    end
  end.
Definition merge_batches (q : qcache) : option (qcache * list qbatch * Z) :=
  match qc_list q with
  | [] => Some (q, [], 0)
  | b :: r =>
    match merge_batches_aux (S (length r)) b r [] [] 0 with
    | None => None
    | Some (l', ex, xb) => Some (mkQC l' (qc_bytes q - xb), ex, xb)
    end
  end.

Fixpoint pop_while (fuel : nat) (l : list qbatch) (bytes : Z) (min_size : Z) (acc : list qbatch)
  : option (list qbatch * Z * list qbatch) :=
  match fuel with
  | O => None
  | S f =>
    if bytes <=? min_size then Some (l, bytes, acc)
    else match l with
         | [] => None
         | b :: r => pop_while f r (bytes - qb_size b) min_size (b :: acc)
         end
  end.

Definition quarantine_recycle (st : astate) (min_size : Z) : option (astate * list effect) :=
  let g := as_gq st in
  let overhead := zlen (qc_list g) * kBatchSize in
  if qc_bytes g <? overhead then None else
  let merged : option (qcache * list qbatch) :=
    if (overhead <? qc_bytes g) && (qc_bytes g * 100 <? overhead * 200)
    then match merge_batches g with None => None | Some (g', ex, _) => Some (g', ex) end
    else Some (g, []) in
  match merged with
  | None => None
  | Some (g1, extracted) =>
    match pop_while (S (length (qc_list g1))) (qc_list g1) (qc_bytes g1) min_size [] with
    | None => None
    | Some (l2, bytes2, rpopped) =>
      let st1 := set_gq st (mkQC l2 bytes2) in
      match do_recycle st1 (extracted ++ rev rpopped) [] with
      | None => None
      | Some (st2, racc) => Some (st2, rev racc)
      end
    end
  end.

Definition quarantine_drain (st : astate) : option (astate * list effect) :=
  let t := as_tq st in let g := as_gq st in
  let g1 := mkQC (qc_list g ++ qc_list t) (qc_bytes g + qc_bytes t) in
  let st1 := set_gq (set_tq st qcache0) g1 in
  if as_qmax st <? qc_bytes g1 then quarantine_recycle st1 (as_qmin st)
  else Some (st1, []).

Definition quarantine_enqueue (st : astate) (m size : Z) : option (astate * list effect) :=
  let t := as_tq st in
  let need_new := match qc_list t with
                  | [] => true
                  | _ => kBatchCount <=? qb_count (last (qc_list t) (mkQB 0 0 0 []))
                  end in
  if need_new then
    match cache_alloc st kBatchClass with
    | None => None
    | Some (st1, b, ev) =>
      if b =? 0 then None else
      let nb := mkQB b (size + kBatchSize) 1 [m] in
      let t1 := mkQC (qc_list (as_tq st1) ++ [nb]) (qc_bytes (as_tq st1) + size + kBatchSize) in
      Some (set_tq st1 t1, ev)
    end
  else
    let l := qc_list t in
    let k := length l in
    let lb := last l (mkQB 0 0 0 []) in
    let lb' := mkQB (qb_addr lb) (qb_size lb + size) (qb_count lb + 1) (qb_chunks lb ++ [m]) in
    let t1 := mkQC (firstn (k - 1)%nat l ++ [lb']) (qc_bytes t + size) in
    Some (set_tq st t1, []).

Definition quarantine_put (st : astate) (ch : chunk) : option (astate * list effect) :=
  let size := ch_used ch in
  if (as_qcache st =? 0) || (as_qmax st <? size) then None else
  match poison_shadow st (ch_user_beg ch) (round_up size 8) kAsanHeapFreeMagic with
  | None => None
  | Some (st1, ev1) =>
    match quarantine_enqueue st1 (ch_chunk_beg ch) size with
    | None => None
    | Some (st2, ev2) =>
      if as_qcache st2 <? qc_bytes (as_tq st2) then
        match quarantine_drain st2 with
        | None => None
        | Some (st3, ev3) => Some (st3, ev1 ++ ev2 ++ ev3)
        end
      else Some (st2, ev1 ++ ev2)
    end
  end.

Definition am_free_full (st : astate) (p : Z) : option (astate * list effect) :=
  let '(st0, ev0) := if as_internal_init st then (st, []) else (set_internal_init st, [EInternalAllocInit]) in
  if p =? 0 then Some (st0, ev0) else
  match find_chunk (as_chunks st0) p with
  | None => None
  | Some ch =>
    match ch_state ch with
    | CQuarantine => None
    | CAllocated =>
      let ch' := mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine in
      let st1 := upd_chunk st0 ch' in
      let ev1 := [EStore64 p 0xFFFFFFFF00000000; EStore64 p 0  ] in
      match quarantine_put st1 ch' with
      | None => None
      | Some (st2, ev2) => Some (st2, ev0 ++ ev1 ++ ev2)
      end
    end
  end.

Inductive syscall_event :=
  | SysMmap (hint len prot flags ret : Z)
  | SysMunmap (addr len : Z).

Fixpoint syscalls_of (l : list effect) : list syscall_event :=
  match l with
  | [] => []
  | EMmap h n pr fl r :: t => SysMmap h n pr fl r :: syscalls_of t
  | EMunmap a n :: t => SysMunmap a n :: syscalls_of t
  | _ :: t => syscalls_of t
  end.

Definition am_malloc (st : astate) (n : Z) : option (Z * astate * list syscall_event) :=
  match am_malloc_full st n with
  | None => None
  | Some (p, st', ev) => Some (p, st', syscalls_of ev)
  end.

Definition am_free (st : astate) (p : Z) : option (astate * list syscall_event) :=
  match am_free_full st p with
  | None => None
  | Some (st', ev) => Some (st', syscalls_of ev)
  end.

Definition init_state_q (res_base space_beg ptr_array : Z) (env : list Z) (track_shadow : bool) (qmax qmin qcache : Z) : astate :=
  mkState space_beg ptr_array (zrepeat region0 32) false (zrepeat pclass0 32) 0 [] (PositiveMap.empty chunk)
          qcache0 qcache0 false
          [ mkMap res_base 0x2000011000 MkPrimaryReservation PROT_NONE true
          ; mkMap (space_beg + kSpaceSize) kPageSize MkRegionInfo PROT_RW false
          ; mkMap ptr_array kPtrArrayReserve MkPtrArrayReservation PROT_NONE true ]
          [] env track_shadow qmax qmin qcache.
Definition init_state (res_base space_beg ptr_array : Z) (env : list Z) (track_shadow : bool) : astate :=
  init_state_q res_base space_beg ptr_array env track_shadow kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize.

Definition malloc_class (n : Z) : Z := let r := compute_req n in if rq_primary r then class_id (rq_needed r) else 0.

Definition ex_state := init_state 0x2aaaaae49000 0x2aaaaae50000 0x2acaaae5a000 [0x2acaaca7a000] true.
Definition ex1 := am_malloc_full ex_state 65536.

Definition ex2 := match ex1 with Some (_, st, _) => am_malloc_full st 122 | None => None end.

Section WF.
  Fixpoint zforallb {A} (f : A -> bool) (l : list A) : bool :=
    match l with [] => true | x :: r => f x && zforallb f r end.
  Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.

  Fixpoint zmerge (a b : list Z) {struct a} : list Z :=
    match a with
    | [] => b
    | x :: a' => (fix inner (b : list Z) : list Z :=
                   match b with
                   | [] => a
                   | y :: b' => if x <=? y then x :: zmerge a' b else y :: inner b'
                   end) b
    end.
  Fixpoint zsplit (l : list Z) : list Z * list Z :=
    match l with [] => ([], []) | [x] => ([x], []) | x :: y :: r => let (a, b) := zsplit r in (x :: a, y :: b) end.
  Fixpoint zsort_fuel (fuel : nat) (l : list Z) : list Z :=
    match fuel with
    | O => l
    | S f => match l with [] | [_] => l | _ => let (a, b) := zsplit l in zmerge (zsort_fuel f a) (zsort_fuel f b) end
    end.
  Definition zsort (l : list Z) : list Z := zsort_fuel (length l) l.
  Fixpoint sorted_nodup (l : list Z) : bool :=
    match l with
    | [] | [_] => true
    | x :: (y :: _) as r => (x <? y) && sorted_nodup r
    end.
  Definition nodup (l : list Z) : bool := sorted_nodup (zsort l).

  Variable st : astate.

  Definition wf_region (c : Z) : bool :=
    let r := get_region st c in
    let size := class_size c in
    (0 <=? rg_allocated_user r) && (rg_allocated_user r <=? rg_mapped_user r)
    && (rg_mapped_user r mod kUserMapSize =? 0)
    && (rg_mapped_user r + kUserMapSize <=? kFreeArrayOffset)
    && (if size =? 0 then rg_mapped_user r =? 0
        else (rg_allocated_user r mod size =? 0) && (rg_mapped_user r - rg_allocated_user r <? size + (if rg_allocated_user r =? 0 then kUserMapSize else 0)))
    && (rg_num_freed r =? zlen (rg_free_array r)) && (0 <=? rg_num_freed r)
    && (4 * rg_num_freed r <=? rg_mapped_free_array r) && (rg_mapped_free_array r mod kFreeArrayMapSize =? 0)
    && (rg_mapped_free_array r <=? kFreeArraySize)
    && zforallb (fun cp => (0 <=? cp) && (Z.shiftl cp kCompactPtrScale <? rg_allocated_user r)
                           && (if size =? 0 then false else Z.shiftl cp kCompactPtrScale mod size =? 0)) (rg_free_array r).

  Definition wf_cache (c : Z) : bool :=
    let pc := get_pc st c in
    let r := get_region st c in
    let size := class_size c in
    (pc_count pc =? zlen (pc_chunks pc))
    && (if as_cache_inited st then pc_count pc <=? max_count c else pc_count pc =? 0)
    && zforallb (fun cp => (0 <=? cp) && (Z.shiftl cp kCompactPtrScale <? rg_allocated_user r)
                           && (if size =? 0 then false else Z.shiftl cp kCompactPtrScale mod size =? 0)) (pc_chunks pc).

  Definition classes : list Z := map Z.of_nat (seq 0 32).
  Definition all_chunks : list chunk := chunk_list st.
  Definition all_batches : list qbatch := qc_list (as_tq st) ++ qc_list (as_gq st).

  Definition carved_addrs : list Z :=
    flat_map (fun c => map (compact_to_addr st c) (rg_free_array (get_region st c))
                       ++ map (compact_to_addr st c) (pc_chunks (get_pc st c))) classes
    ++ map ch_alloc_beg (filter ch_primary all_chunks)
    ++ map qb_addr all_batches.
  Definition wf_partition : bool := nodup carved_addrs.

  Definition wf_chunk (ch : chunk) : bool :=
    let r := compute_req (ch_used ch) in
    (1 <=? ch_used ch) && (ch_used ch =? rq_size r) && (ch_rz ch =? rq_rz r)
    && (ch_user_beg ch =? ch_alloc_beg ch + ch_rz ch)
    && (if ch_primary ch then
          let c := ch_class ch in
          rq_primary r && (c =? class_id (rq_needed r)) && (c =? class_of_addr st (ch_alloc_beg ch))
          && in_primary st (ch_alloc_beg ch)
          && ((ch_alloc_beg ch - region_beg st c) mod class_size c =? 0)
          && (ch_alloc_beg ch - region_beg st c + class_size c <=? rg_allocated_user (get_region st c))
          && (rq_needed r <=? class_size c)
        else
          negb (rq_primary r) && negb (in_primary st (ch_alloc_beg ch))
          && match find_sec_idx (as_sec st) (ch_alloc_beg ch - kPageSize) 0%nat with
             | Some i => let h := znth (as_sec st) i (mkSC 0 0 0) in
                         (sc_size h =? rq_needed r) && (sc_map_size h =? round_up (sc_size h) kPageSize + kPageSize)
             | None => false
             end).
  Definition wf_chunks : bool :=
    zforallb wf_chunk all_chunks
    && (zlen (filter (fun ch => negb (ch_primary ch)) all_chunks) =? zlen (as_sec st))
    && nodup (map sc_map_beg (as_sec st))
    && (zlen (as_sec st) <=? as_n_reserved st) && ((as_n_reserved st =? 0) || (as_n_reserved st =? kChunksBlockCount)).

  Definition used_of (m : Z) : Z := match find_chunk (as_chunks st) (m + kChunkHeaderSize) with Some ch => ch_used ch | None => -1 end.
  Definition wf_batch (b : qbatch) : bool :=
    (qb_count b =? zlen (qb_chunks b)) && (1 <=? qb_count b) && (qb_count b <=? kBatchCount)
    && in_primary st (qb_addr b) && (class_of_addr st (qb_addr b) =? kBatchClass)
    && (qb_size b =? kBatchSize + zsum (map used_of (qb_chunks b)))
    && zforallb (fun m => match find_chunk (as_chunks st) (m + kChunkHeaderSize) with
                          | Some ch => match ch_state ch with CQuarantine => true | _ => false end
                          | None => false end) (qb_chunks b).
  Definition wf_qcache (q : qcache) : bool :=
    zforallb wf_batch (qc_list q) && (qc_bytes q =? zsum (map qb_size (qc_list q))).
  Definition quarantined_ms : list Z := flat_map qb_chunks all_batches.
  Definition wf_quarantine : bool :=
    wf_qcache (as_tq st) && wf_qcache (as_gq st)
    && (qc_bytes (as_tq st) <=? as_qcache st) && (qc_bytes (as_gq st) <=? as_qmax st)
    && nodup quarantined_ms
    && (zlen quarantined_ms =? zlen (filter (fun ch => match ch_state ch with CQuarantine => true | _ => false end) all_chunks)).

  Definition wf_state : bool :=
    zforallb wf_region classes && zforallb wf_cache classes && wf_partition && wf_chunks && wf_quarantine
    && (rg_mapped_user (get_region st 0) =? 0) && (rg_mapped_user (get_region st 31) =? 0)
    && (pc_count (get_pc st 0) =? 0) && (pc_count (get_pc st 31) =? 0).
End WF.

