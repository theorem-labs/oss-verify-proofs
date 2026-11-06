(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive aundef :=
| UBadAnswer      (* [comment removed for export] *)
| UBadPtr         (* [comment removed for export] *)
| USpin           (* [comment removed for export] *)
| UCheck (tag : Z)(* [comment removed for export] *)
| UUnmodeled.     (* [comment removed for export] *)

Inductive aev : Type :=
| ASetTid (addr : Z)                    (* [comment removed for export] *)
| ABrk (addr : Z)                       (* [comment removed for export] *)
| AMmap (addr len prot flags : Z)       (* [comment removed for export] *)
| AMunmap (addr len : Z)                (* [comment removed for export] *)
| AMprotect (addr len prot : Z)         (* [comment removed for export] *)
| AMadvise (addr len : Z)               (* [comment removed for export] *)
| AUndef (why : aundef).

Definition AM (R : Type) := stree aev Z R.
Definition aret {R} (r : R) : AM R := SRet r.
Definition aundef_ {R} (w : aundef) (k : AM R) : AM R := SVis (AUndef w) (fun _ => k).

(* [comment removed for export] *)
Definition PROT_NONE : Z := 0.
Definition PROT_RW : Z := 3.
Definition F_ANON : Z := 34.        (* [comment removed for export] *)
Definition F_FIXED : Z := 50.       (* [comment removed for export] *)
Definition F_NORES : Z := 16418.    (* [comment removed for export] *)
Definition F_FIXNORES : Z := 16434. (* [comment removed for export] *)
Definition PG : Z := 4096.
Definition TWO64 : Z := 2^64.
Definition ENOSYS : Z := 38.
(* [comment removed for export] *)
Definition ALLOC_TOP_MIN : Z := 0x7fff7f800000.
Definition STACK_MAX : Z := 2^23.
Definition atop_of_sp (sp0 : Z) : Z := sp0 - STACK_MAX.

Definition is_err (r : Z) : bool := (TWO64 - 4096 <? r).
Definition rup (x a : Z) : Z := ((x + a - 1) / a) * a.
Definition rdn (x a : Z) : Z := (x / a) * a.

(* [comment removed for export] *)
Definition mmap_answer_ok (atop len r : Z) : bool :=
  is_err r || ((0 <? r) && (r mod PG =? 0) && (r + rup len PG <=? atop) && (r <? TWO64)).
Definition fixed_answer_ok (a r : Z) : bool := is_err r || (r =? a).
Definition brk0_answer_ok (r : Z) : bool := (0 <? r) && (r <? TWO64).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SHADOW_OFF : Z := 0x7fff8000.          (* [comment removed for export] *)
Definition K_SPACE_SIZE : Z := 2^37.               (* [comment removed for export] *)
Definition K_SPACE_EXTRA : Z := 0x1000.            (* [comment removed for export] *)
Definition K_ALIGN : Z := 0x10000.                 (* [comment removed for export] *)
Definition K_REGION : Z := 2^32.                   (* [comment removed for export] *)
Definition K_FREEARR_OFF : Z := 0xE0000000.        (* [comment removed for export] *)
Definition K_FREEARR_MAX : Z := 0x20000000.        (* [comment removed for export] *)
Definition K_USER_MAP : Z := 0x40000.              (* [comment removed for export] *)
Definition K_FREEARR_MAP : Z := 0x40000.           (* [comment removed for export] *)
Definition K_MAX_SIZE : Z := 0x10000.              (* [comment removed for export] *)
Definition K_NUM_CLASSES : Z := 32.
Definition K_BATCH_CLASS : Z := 24.                (* [comment removed for export] *)
Definition K_PTRARR_RESERVE : Z := 0x800000.       (* [comment removed for export] *)
Definition K_PTRARR_COMMIT : Z := 0x20000.         (* [comment removed for export] *)
Definition K_CHUNKS_BLOCK : Z := 16384.
Definition Q_MAX : Z := 0x10000000.                (* [comment removed for export] *)
Definition Q_MIN : Z := 241591905.                 (* [comment removed for export] *)
Definition Q_CACHE : Z := 0x100000.                (* [comment removed for export] *)
Definition Q_BATCH : Z := 1021.                    (* [comment removed for export] *)
Definition Q_BATCH_BYTES : Z := 8192.              (* [comment removed for export] *)
Definition CLEAR_SHADOW_MMAP_THRESHOLD : Z := 0x10000.
Definition FAKESTACK_BYTES : Z := 0xb09000.        (* [comment removed for export] *)
Definition STACK_SIZE : Z := 0x800000.             (* [comment removed for export] *)
Definition LOW_SHADOW_ADDR : Z := 0x7fff7000.      (* [comment removed for export] *)
Definition LOW_SHADOW_LEN : Z := 0x10000000.
Definition HIGH_SHADOW_ADDR : Z := 0x2008fff7000.
Definition HIGH_SHADOW_LEN : Z := 0xdfff0001000.
Definition GAP_ADDR : Z := 0x8fff7000.
Definition GAP_LEN : Z := 0x20000000000.

(* [comment removed for export] *)
Definition size_of_class (c : Z) : Z :=
  if c <=? 16 then 32 * c
  else if c =? 31 then 64
  else let t := Z.shiftl 512 (Z.shiftr (c - 16) 1) in
       if Z.odd (c - 16) then t + Z.shiftr t 1 else t.

Definition class_id (s : Z) : Z :=
  if s <=? 512 then Z.shiftr (s + 31) 5
  else let l := Z.log2 s in
       let hbits := Z.land (Z.shiftr s (l - 1)) 1 in
       let lbits := Z.land s (Z.shiftl 1 (l - 1) - 1) in
       16 + Z.shiftl (l - 9) 1 + hbits + (if lbits =? 0 then 0 else 1).

(* [comment removed for export] *)
Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / size_of_class c)).

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := Z.shiftl 16 (rz_log n).

(* [comment removed for export] *)
Definition rounded_size (n : Z) : Z := rup (Z.max n 8) 8.
Definition needed0 (n : Z) : Z := rounded_size n + rz_size n.
Definition is_primary (n : Z) : bool := needed0 n <=? K_MAX_SIZE.
Definition needed_size (n : Z) : Z := if is_primary n then needed0 n else needed0 n + rz_size n.
(* [comment removed for export] *)
Definition sec_map_size (n : Z) : Z := rup (needed_size n) PG + PG.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record aclass := mkAClass {
  c_mapped_user : Z;        (* [comment removed for export] *)
  c_allocated_user : Z;     (* [comment removed for export] *)
  c_num_freed : Z;          (* [comment removed for export] *)
  c_mapped_free_array : Z;  (* [comment removed for export] *)
  c_count : Z               (* [comment removed for export] *)
}.
Definition aclass0 : aclass := mkAClass 0 0 0 0 0.

(* [comment removed for export] *)
Inductive achunk :=
| CPrim (c : Z) (n : Z)                          (* [comment removed for export] *)
| CSec (map_beg map_size : Z) (n : Z).           (* [comment removed for export] *)
Definition chunk_size (ch : achunk) : Z := match ch with CPrim _ n => n | CSec _ _ n => n end.

(* [comment removed for export] *)
Record abatch := mkABatch { b_count : Z; b_size : Z; b_chunks : list achunk }.

Definition aptr : Type := N.

Record astate := mkAState {
  a_space_beg : Z;              (* [comment removed for export] *)
  a_ptr_array : Z;              (* [comment removed for export] *)
  a_nres : Z;                   (* [comment removed for export] *)
  a_nsec : Z;                   (* [comment removed for export] *)
  a_cinit : bool;               (* [comment removed for export] *)
  a_cls : gmap Z aclass;        (* [comment removed for export] *)
  a_live : gmap N achunk;       (* [comment removed for export] *)
  a_next : N;                   (* [comment removed for export] *)
  a_qloc : list abatch;         (* [comment removed for export] *)
  a_qloc_bytes : Z;
  a_qglob : list abatch;        (* [comment removed for export] *)
  a_qglob_bytes : Z
}.

Definition ainit (space_beg ptr_array : Z) : astate :=
  mkAState space_beg ptr_array 0 0 false ∅ ∅ 0%N [] 0 [] 0.

(* [comment removed for export] *)
Definition set_nres v st := mkAState (a_space_beg st) (a_ptr_array st) v (a_nsec st) (a_cinit st) (a_cls st) (a_live st) (a_next st) (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_nsec v st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) v (a_cinit st) (a_cls st) (a_live st) (a_next st) (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_cinit v st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) v (a_cls st) (a_live st) (a_next st) (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_cls v st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) (a_cinit st) v (a_live st) (a_next st) (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_live v st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) (a_cinit st) (a_cls st) v (a_next st) (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_next v st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) (a_cinit st) (a_cls st) (a_live st) v (a_qloc st) (a_qloc_bytes st) (a_qglob st) (a_qglob_bytes st).
Definition set_qloc l b st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) (a_cinit st) (a_cls st) (a_live st) (a_next st) l b (a_qglob st) (a_qglob_bytes st).
Definition set_qglob l b st := mkAState (a_space_beg st) (a_ptr_array st) (a_nres st) (a_nsec st) (a_cinit st) (a_cls st) (a_live st) (a_next st) (a_qloc st) (a_qloc_bytes st) l b.

Definition get_cls (st : astate) (c : Z) : aclass := default aclass0 ((a_cls st) !! c).
Definition put_cls (c : Z) (r : aclass) (st : astate) : astate := set_cls (<[c := r]> (a_cls st)) st.
Definition cls_set_count v r := mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) v.
Definition cls_set_num_freed v r := mkAClass (c_mapped_user r) (c_allocated_user r) v (c_mapped_free_array r) (c_count r).
Definition cls_set_mapped_free_array v r := mkAClass (c_mapped_user r) (c_allocated_user r) (c_num_freed r) v (c_count r).
Definition cls_set_mapped_user v r := mkAClass v (c_allocated_user r) (c_num_freed r) (c_mapped_free_array r) (c_count r).
Definition cls_set_allocated_user v r := mkAClass (c_mapped_user r) v (c_num_freed r) (c_mapped_free_array r) (c_count r).

Definition max_count (st : astate) (c : Z) : Z := if a_cinit st then max_cached c else 0.
Definition region_beg (st : astate) (c : Z) : Z := a_space_beg st + c * K_REGION.

(* [comment removed for export] *)
Definition chunk_alloc_beg (ch : achunk) : Z := match ch with CSec mb _ _ => mb + PG | CPrim _ _ => 0 end.
Definition chunk_user_beg (ch : achunk) : Z := match ch with CSec mb _ n => mb + PG + rz_size n | CPrim _ _ => 0 end.
Definition aptr_addr (st : astate) (p : aptr) : Z :=
  match (a_live st) !! p with Some ch => chunk_user_beg ch | None => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition poison0 {R} (addr size : Z) (k : AM R) : AM R := k.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ev {R} (e : aev) (k : Z -> AM R) : AM R := SVis e k.

(* [comment removed for export] *)
Definition must_map {R} (atop len prot flags : Z) (k : Z -> AM R) : AM R :=
  ev (AMmap 0 len prot flags) (fun r =>
    if negb (mmap_answer_ok atop len r) then aundef_ UBadAnswer (k 0)
    else if is_err r then aundef_ USpin (k 0) else k r).
Definition must_map_fixed {R} (addr len prot flags : Z) (k : AM R) : AM R :=
  ev (AMmap addr len prot flags) (fun r =>
    if negb (fixed_answer_ok addr r) then aundef_ UBadAnswer k
    else if is_err r then aundef_ USpin k else k).

(* [comment removed for export] *)
Definition musl_startup_malloc {R} (atop : Z) (k : AM R) : AM R :=
  ev (ABrk 0) (fun b0 =>
    if negb (brk0_answer_ok b0) then aundef_ UBadAnswer k else
    let cur := rup b0 PG in
    let new := cur + 2 * PG in
    ev (ABrk new) (fun r =>
      let group := ev (AMmap 0 PG PROT_RW F_ANON) (fun _ => k) in   (* [comment removed for export] *)
      if r =? new then
        ev (AMmap cur PG PROT_NONE F_FIXED) (fun _ => group)         (* [comment removed for export] *)
      else if r =? b0 then
        ev (AMmap 0 (2 * PG) PROT_NONE F_ANON) (fun p =>              (* [comment removed for export] *)
          if negb (mmap_answer_ok atop (2 * PG) p) then aundef_ UBadAnswer k
          else if is_err p then k                                       (* [comment removed for export] *)
          else ev (AMprotect (p + PG) PG PROT_RW) (fun r2 =>
                 if (r2 =? 0) || (r2 =? TWO64 - ENOSYS) then group else k))
      else aundef_ UBadAnswer k)).

Definition astartup (tid_addr sp0 : Z) : AM astate :=
  let must_map {R} := @must_map R (atop_of_sp sp0) in
  ev (ASetTid tid_addr) (fun _ =>
  must_map 0x10000 PROT_RW F_ANON (fun _ =>                      (* [comment removed for export] *)
  must_map 0x38e000 PROT_RW F_ANON (fun _ =>                     (* [comment removed for export] *)
  must_map_fixed LOW_SHADOW_ADDR LOW_SHADOW_LEN PROT_RW F_FIXNORES ( (* [comment removed for export] *)
  must_map_fixed HIGH_SHADOW_ADDR HIGH_SHADOW_LEN PROT_RW F_FIXNORES ( (* [comment removed for export] *)
  must_map_fixed GAP_ADDR GAP_LEN PROT_NONE F_FIXNORES (          (* [comment removed for export] *)
  must_map (K_SPACE_SIZE + K_SPACE_EXTRA + K_ALIGN) PROT_NONE F_NORES (fun b6 =>  (* [comment removed for export] *)
  let space_beg := b6 + K_ALIGN - Z.land b6 (K_ALIGN - 1) in
  must_map_fixed (space_beg + K_SPACE_SIZE) 0x1000 PROT_RW F_FIXED ( (* [comment removed for export] *)
  must_map K_PTRARR_RESERVE PROT_NONE F_NORES (fun b8 =>          (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun _ =>                       (* [comment removed for export] *)
  must_map 0x10000 PROT_RW F_ANON (fun _ =>                      (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun _ =>                       (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun _ =>                       (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun v =>                       (* [comment removed for export] *)
  ev (AMunmap v 0x1000) (fun _ =>                                (* [comment removed for export] *)
  let top := rup (sp0 - 0xa0) PG in
  poison0 (top - STACK_SIZE) STACK_SIZE (                        (* [comment removed for export] *)
  must_map FAKESTACK_BYTES PROT_RW F_ANON (fun _ =>              (* [comment removed for export] *)
  musl_startup_malloc (atop_of_sp sp0) (                        (* [comment removed for export] *)
  must_map 0x100000 PROT_RW F_ANON (fun _ =>                     (* [comment removed for export] *)
  must_map 0x800000 PROT_RW F_NORES (fun _ =>                    (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun _ =>                       (* [comment removed for export] *)
  must_map 0x1000 PROT_RW F_ANON (fun _ =>                       (* [comment removed for export] *)
  aret (ainit space_beg b8))))))))))))))))))))))).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ensure_free_array {R} (st : astate) (c num_freed : Z) (k : astate -> bool -> AM R) : AM R :=
  let r := get_cls st c in
  let needed := num_freed * 4 in
  if needed <=? c_mapped_free_array r then k st true else
  let new_mapped := rup needed K_FREEARR_MAP in
  if K_FREEARR_MAX <? new_mapped then aundef_ (UCheck 751) (k st false) else
  let cur_end := region_beg st c + K_FREEARR_OFF + c_mapped_free_array r in
  ev (AMmap cur_end (new_mapped - c_mapped_free_array r) PROT_RW F_FIXED) (fun a =>
    if negb (fixed_answer_ok cur_end a) then aundef_ UBadAnswer (k st false)
    else if is_err a then k st false
    else k (put_cls c (cls_set_mapped_free_array new_mapped r) st) true).

(* [comment removed for export] *)
Definition populate_free_array {R} (st : astate) (c requested : Z) (k : astate -> bool -> AM R) : AM R :=
  let size := size_of_class c in
  let r := get_cls st c in
  let total_user := c_allocated_user r + requested * size in
  let after_map (st1 : astate) : AM R :=
    let r1 := get_cls st1 c in
    let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
    let total_freed := c_num_freed r1 + new_cnt in
    ensure_free_array st1 c total_freed (fun st2 ok =>
      if negb ok then k st2 false else
      let r2 := get_cls st2 c in
      k (put_cls c (cls_set_allocated_user (c_allocated_user r2 + new_cnt * size) (cls_set_num_freed total_freed r2)) st2) true) in
  if total_user <=? c_mapped_user r then after_map st else
  let ums := rup (total_user - c_mapped_user r) K_USER_MAP in
  if K_FREEARR_OFF <? c_mapped_user r + ums then aundef_ (UCheck 705) (k st false)   (* [comment removed for export] *)
  else
  let beg := region_beg st c + c_mapped_user r in
  ev (AMmap beg ums PROT_RW F_FIXED) (fun a =>
    if negb (fixed_answer_ok beg a) then aundef_ UBadAnswer (k st false)
    else if is_err a then k st false
    else after_map (put_cls c (cls_set_mapped_user (c_mapped_user r + ums) r) st)).

Definition init_cache (st : astate) : astate := if a_cinit st then st else set_cinit true st.

(* [comment removed for export] *)
Definition cache_alloc {R} (st : astate) (c : Z) (k : astate -> bool -> AM R) : AM R :=
  let r := get_cls st c in
  if 0 <? c_count r then k (put_cls c (cls_set_count (c_count r - 1) r) st) true else
  let st1 := init_cache st in
  let n := max_count st1 c / 2 in
  let r1 := get_cls st1 c in
  let take (st2 : astate) : AM R :=
    let r2 := get_cls st2 c in
    if c_num_freed r2 <? n then aundef_ (UCheck 229) (k st2 false)
    else k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed r2 - n) r2)) st2) true in
  if n <=? c_num_freed r1 then take st1
  else populate_free_array st1 c (n - c_num_freed r1) (fun st2 ok => if ok then take st2 else k st2 false).

(* [comment removed for export] *)
Definition cache_dealloc {R} (st : astate) (c : Z) (k : astate -> AM R) : AM R :=
  let st1 := init_cache st in
  let r := get_cls st1 c in
  let mc := max_count st1 c in
  if c_count r =? mc then
    let cnt := mc / 2 in
    ensure_free_array st1 c (c_num_freed r + cnt) (fun st2 ok =>
      if negb ok then aundef_ USpin (k st2) else
      let r2 := get_cls st2 c in
      k (put_cls c (cls_set_count (c_count r2 - cnt + 1) (cls_set_num_freed (c_num_freed r2 + cnt) r2)) st2))
  else k (put_cls c (cls_set_count (c_count r + 1) r) st1).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition K_HIGH_MEM : Z := 0x10007fff8000.      (* [comment removed for export] *)
Definition iv_clear (a n : Z) (iv : Z * Z) : bool := (a + n <=? fst iv) || (snd iv <=? a).
Definition avoids_all (a n : Z) (l : list (Z * Z)) : bool := forallb (iv_clear a n) l.

Definition sec_iv (ch : achunk) : list (Z * Z) :=
  match ch with CSec mb ms _ => [(mb, mb + ms)] | CPrim _ _ => [] end.
(* [comment removed for export] *)
Definition achunks (st : astate) : list achunk :=
  map snd (map_to_list (a_live st)) ++ flat_map b_chunks (a_qloc st ++ a_qglob st).
Definition asec_ranges (st : astate) : list (Z * Z) := flat_map sec_iv (achunks st).

Definition large_alloc {R} (ATOP : Z) (RESV : list (Z * Z)) (st : astate) (n : Z) (k : astate -> option achunk -> AM R) : AM R :=
  let map_size := sec_map_size n in
  ev (AMmap 0 map_size PROT_RW F_ANON) (fun mb =>
    if negb (mmap_answer_ok ATOP map_size mb) then aundef_ UBadAnswer (k st None)
    else if is_err mb then k st None                     (* [comment removed for export] *)
    else if negb (avoids_all mb map_size (RESV ++ asec_ranges st)) then aundef_ UBadAnswer (k st None)   (* [comment removed for export] *)
    else
    let ch := CSec mb map_size n in
    let st1 := set_nsec (a_nsec st + 1) st in
    if a_nsec st =? a_nres st then
      let a := a_ptr_array st + 8 * a_nres st in
      if K_PTRARR_RESERVE <? 8 * (a_nres st + K_CHUNKS_BLOCK) then aundef_ (UCheck 42) (k st None) else
      ev (AMmap a K_PTRARR_COMMIT PROT_RW F_FIXED) (fun r =>
        if negb (fixed_answer_ok a r) then aundef_ UBadAnswer (k st None)
        else if is_err r then aundef_ USpin (k st None)  (* [comment removed for export] *)
        else k (set_nres (a_nres st + K_CHUNKS_BLOCK) st1) (Some ch))
    else k st1 (Some ch)).

(* [comment removed for export] *)
Definition flush_beg (map_beg : Z) : Z := rup (SHADOW_OFF + Z.shiftr map_beg 3) PG.
Definition flush_end (map_beg map_size : Z) : Z := rdn (SHADOW_OFF + Z.shiftr (map_beg + map_size) 3) PG.

Definition large_dealloc {R} (st : astate) (map_beg map_size : Z) (k : astate -> AM R) : AM R :=
  let st1 := set_nsec (a_nsec st - 1) st in
  let sb := flush_beg map_beg in
  let se := flush_end map_beg map_size in
  let unmap : AM R :=
    ev (AMunmap map_beg map_size) (fun r =>
      if r =? 0 then k st1
      else if is_err r then aundef_ USpin (k st1)        (* [comment removed for export] *)
      else aundef_ UBadAnswer (k st1)) in
  poison0 map_beg map_size (
    if sb <? se then ev (AMadvise sb (se - sb)) (fun _ => unmap) else unmap).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition amalloc (ATOP : Z) (RESV : list (Z * Z)) (st : astate) (n : Z) : AM (astate * option aptr) :=
  if (2^40 <? n) || (2^40 <? needed_size n) then aret (st, None)   (* [comment removed for export] *)
  else
  let finish (st1 : astate) (ch : achunk) : AM (astate * option aptr) :=
    let id := a_next st1 in
    let st2 := set_next (N.succ id) (set_live (<[id := ch]> (a_live st1)) st1) in
    (* [comment removed for export] *)
    match ch with
    | CPrim _ _ => aret (st2, Some id)
    | CSec _ _ _ => poison0 (chunk_user_beg ch) (Z.land n (Z.lnot 7)) (aret (st2, Some id))
    end in
  if is_primary n then
    let c := class_id (needed_size n) in
    cache_alloc st c (fun st1 ok => if ok then finish st1 (CPrim c n) else aret (st1, None))
  else
    large_alloc ATOP RESV st n (fun st1 och => match och with Some ch => finish st1 ch | None => aret (st1, None) end).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition QCH := achunk.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition recycle_chunk {R} (st : astate) (ch : achunk) (k : astate -> AM R) : AM R :=
  match ch with
  | CPrim c _ => cache_dealloc st c k
  | CSec mb ms _ => large_dealloc st mb ms k
  end.

Fixpoint recycle_chunks {R} (st : astate) (l : list achunk) (k : astate -> AM R) {struct l} : AM R :=
  match l with
  | [] => k st
  | ch :: l' => recycle_chunk st ch (fun st1 => recycle_chunks st1 l' k)
  end.

(* [comment removed for export] *)
Fixpoint do_recycle {R} (st : astate) (bs : list abatch) (k : astate -> AM R) {struct bs} : AM R :=
  match bs with
  | [] => k st
  | b :: bs' => recycle_chunks st (rev (b_chunks b)) (fun st1 => cache_dealloc st1 K_BATCH_CLASS (fun st2 => do_recycle st2 bs' k))
  end.

(* [comment removed for export] *)
Fixpoint merge_batches (cur : abatch) (rest : list abatch) {struct rest} : list abatch * list abatch * Z :=
  match rest with
  | [] => ([cur], [], 0)
  | nx :: rest' =>
      if b_count cur + b_count nx <=? Q_BATCH then
        let cur' := mkABatch (b_count cur + b_count nx) (b_size cur + (b_size nx - Q_BATCH_BYTES)) (b_chunks nx ++ b_chunks cur) in
        let '(l, ex, exb) := merge_batches cur' rest' in
        (l, mkABatch 0 Q_BATCH_BYTES [] :: ex, exb + Q_BATCH_BYTES)
      else
        let '(l, ex, exb) := merge_batches nx rest' in
        (cur :: l, ex, exb)
  end.

(* [comment removed for export] *)
Fixpoint dequeue_while (l : list abatch) (bytes min_size : Z) {struct l} : list abatch * list abatch * Z :=
  match l with
  | [] => ([], [], bytes)
  | b :: l' => if min_size <? bytes
               then let '(taken, rest, bytes') := dequeue_while l' (bytes - b_size b) min_size in (b :: taken, rest, bytes')
               else ([], l, bytes)
  end.

(* [comment removed for export] *)
Definition recycle {R} (st : astate) (min_size : Z) (k : astate -> AM R) : AM R :=
  let cache_size := a_qglob_bytes st in
  let overhead := Q_BATCH_BYTES * Z.of_nat (length (a_qglob st)) in
  if cache_size <? overhead then aundef_ (UCheck 159) (k st) else
  let '(gl, extracted, exb) :=
    (if (overhead <? cache_size) && (cache_size * 100 <? overhead * 200)
     then match a_qglob st with
          | [] => ([], [], 0)
          | b :: rest => merge_batches b rest
          end
     else (a_qglob st, [], 0)) in
  let bytes1 := cache_size - exb in
  let '(taken, rest, bytes2) := dequeue_while gl bytes1 min_size in
  if (min_size <? bytes2) then aundef_ (UCheck 0) (k st)   (* [comment removed for export] *)
  else do_recycle (set_qglob rest bytes2 st) (extracted ++ taken) k.

(* [comment removed for export] *)
Definition drain {R} (st : astate) (k : astate -> AM R) : AM R :=
  let st1 := set_qglob (a_qglob st ++ a_qloc st) (a_qglob_bytes st + a_qloc_bytes st) (set_qloc [] 0 st) in
  if Q_MAX <? a_qglob_bytes st1 then recycle st1 Q_MIN k else k st1.

(* [comment removed for export] *)
Definition enqueue {R} (st : astate) (ch : achunk) (k : astate -> AM R) : AM R :=
  let n := chunk_size ch in
  let new_batch (st0 : astate) : AM R :=
    cache_alloc st0 K_BATCH_CLASS (fun st1 ok =>
      if negb ok then aundef_ USpin (k st1)          (* [comment removed for export] *)
      else k (set_qloc (a_qloc st1 ++ [mkABatch 1 (n + Q_BATCH_BYTES) [ch]]) (a_qloc_bytes st1 + n + Q_BATCH_BYTES) st1)) in
  match rev (a_qloc st) with
  | [] => new_batch st
  | b :: rl =>
      if b_count b =? Q_BATCH then new_batch st
      else k (set_qloc (rev (mkABatch (b_count b + 1) (b_size b + n) (ch :: b_chunks b) :: rl)) (a_qloc_bytes st + n) st)
  end.

(* [comment removed for export] *)
Definition afree (st : astate) (p : option aptr) : AM astate :=
  match p with
  | None => aret st
  | Some id =>
    match (a_live st) !! id with
    | None => aundef_ UBadPtr (aret st)
    | Some ch =>
      let st1 := set_live (delete id (a_live st)) st in
      let after (st2 : astate) : AM astate :=
        if Q_CACHE <? a_qloc_bytes st2 then drain st2 (fun st3 => aret st3) else aret st2 in
      if chunk_size ch <=? Q_MAX then enqueue st1 ch after
      else recycle_chunk st1 ch after
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aannotate (st : astate) (p : aptr) (cap old new : Z) : AM astate :=
  match (a_live st) !! p with
  | None => aundef_ UBadPtr (aret st)
  | Some ch =>
    if negb ((0 <=? old) && (old <=? cap) && (0 <=? new) && (new <=? cap)) then aundef_ UBadPtr (aret st)  (* [comment removed for export] *)
    else if 2^40 <? cap then aundef_ (UCheck 438) (aret st)
    else if old =? new then aret st
    else if negb (Z.land cap 7 =? 0) && (rdn cap 8 <? Z.min old new) then aundef_ UUnmodeled (aret st)  (* [comment removed for export] *)
    else if old <? new then
      match ch with
      | CPrim _ _ => aret st                                  (* [comment removed for export] *)
      | CSec _ _ _ => let beg := chunk_user_beg ch in
                      let a := rdn old 8 in let b1 := rdn new 8 in
                      if a <? b1 then poison0 (beg + a) (b1 - a) (aret st) else aret st
      end
    else aret st
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cls_mapped_bytes (r : aclass) : Z := c_mapped_user r + c_mapped_free_array r.
Definition batches_bytes (l : list abatch) : Z := fold_right (fun b acc => b_size b + acc) 0 l.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Examples.
  (* [comment removed for export] *)
  Definition toy_oracle (cur : Z) (e : aev) : Z * Z :=
    match e with
    | ASetTid _ => (1234, cur)
    | ABrk a => if a =? 0 then (0x6c7000, cur) else (a, cur)
    | AMmap a len _ _ => if a =? 0 then (cur, cur + rup len PG) else (a, cur)
    | AMunmap _ _ => (0, cur)
    | AMprotect _ _ _ => (0, cur)
    | AMadvise _ _ => (0, cur)
    | AUndef _ => (0, cur)
    end.
  Definition run {R} (t : AM R) (cur : Z) := srun toy_oracle cur t.

  Definition st0 := snd (run (astartup 0x6c4248 0x7fffc0000000) 0x2aaaaaaab000).
  Example startup_events :
    length (fst (fst (run (astartup 0x6c4248 0x7fffc0000000) 0x2aaaaaaab000))) = 24%nat.   (* [comment removed for export] *)
  Proof. vm_compute. reflexivity. Qed.
  Example startup_spacebeg : a_space_beg st0 = 0x2aaaaae50000 /\ a_ptr_array st0 = 0x2acaaae5a000.
  Proof. vm_compute. split; reflexivity. Qed.

  (* [comment removed for export] *)
  Example malloc_65536_events :
    map fst (fst (fst (run (amalloc ALLOC_TOP_MIN [] st0 65536) 0x2acaaca7a000)))
    = [AMmap 0 0x12000 PROT_RW F_ANON; AMmap 0x2acaaae5a000 0x20000 PROT_RW F_FIXED].
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition st1 := fst (snd (run (amalloc ALLOC_TOP_MIN [] st0 65536) 0x2acaaca7a000)).
  Example malloc_20_events :
    map fst (fst (fst (run (amalloc ALLOC_TOP_MIN [] st1 20) 0))) =
    [AMmap (0x2aaaaae50000 + 2 * 2^32) 0x40000 PROT_RW F_FIXED; AMmap (0x2aaaaae50000 + 2 * 2^32 + 0xE0000000) 0x40000 PROT_RW F_FIXED].
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition st2p := snd (run (amalloc ALLOC_TOP_MIN [] st1 20) 0).
  Example first_free_events :
    map fst (fst (fst (run (afree (fst st2p) (snd st2p)) 0))) =
    [AMmap (0x2aaaaae50000 + 24 * 2^32) 0x40000 PROT_RW F_FIXED; AMmap (0x2aaaaae50000 + 24 * 2^32 + 0xE0000000) 0x40000 PROT_RW F_FIXED].
  Proof. vm_compute. reflexivity. Qed.

  Example sizes : (class_id (needed_size 20), size_of_class 24, class_id 8192, needed_size 65536, sec_map_size 65536, is_primary 64512, is_primary 64513)
                  = (2, 8192, 24, 69632, 0x12000, true, false).
  Proof. vm_compute. reflexivity. Qed.
End Examples.
