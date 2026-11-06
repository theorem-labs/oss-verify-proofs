(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Inductive aev : Type :=
| AEvMmap (addr len prot flags : Z)
| AEvMunmap (addr len : Z).

Inductive aans : Type := AnsOk (r : Z) | AnsErr (e : Z).

Inductive aundef : Type :=
| UBadAnswer            (* [comment removed for export] *)
| UPlacement (r : Z)    (* [comment removed for export] *)
| UBadPtr (p : Z)       (* [comment removed for export] *)
| UDepot                (* [comment removed for export] *)
| UInternal (tag : Z).  (* [comment removed for export] *)

Inductive aout (R : Type) : Type := ONorm (r : R) | OSpin | OUndef (why : aundef).
End RC__1.
Arguments ONorm {R} r.
Arguments OSpin {R}.
Arguments OUndef {R} why.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AM (R : Type) : Type := astate -> stree aev aans (astate * aout R).

Definition aret {R} (r : R) : AM R := fun s => SRet (s, ONorm r).
Definition abind {R S} (m : AM R) (f : R -> AM S) : AM S :=
  fun s => sbind (m s) (fun p => match snd p with
                                 | ONorm r => f r (fst p)
                                 | OSpin => SRet (fst p, OSpin)
                                 | OUndef w => SRet (fst p, OUndef w)
                                 end).
Definition aget : AM astate := fun s => SRet (s, ONorm s).
Definition aput (s' : astate) : AM unit := fun _ => SRet (s', ONorm tt).
Definition aupd (f : astate -> astate) : AM unit := fun s => SRet (f s, ONorm tt).
Definition aspin {R} : AM R := fun s => SRet (s, OSpin).
Definition aundef_ {R} (w : aundef) : AM R := fun s => SRet (s, OUndef w).
Definition acheck (b : bool) (tag : Z) : AM unit := if b then aret tt else aundef_ (UInternal tag).
Definition acall (e : aev) : AM aans := fun s => SVis e (fun a => SRet (s, ONorm a)).

End RC__2.
Declare Scope am_scope.
Notation "x <- m ;; k" := (abind m (fun x => k)) (at level 100, m at next level, right associativity) : am_scope.
Notation "m ;;; k" := (abind m (fun _ => k)) (at level 100, right associativity) : am_scope.
Open Scope am_scope.

(* [comment removed for export] *)
Section RC__3.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Fixpoint ziota (a : Z) (k : nat) : list Z := match k with O => [] | S k' => a :: ziota (a + 1) k' end.
Definition removelast {A} (l : list A) : list A := firstn (Nat.pred (length l)) l.
Fixpoint list_find_index {A} (f : A -> bool) (l : list A) (i : nat) : option nat :=
  match l with [] => None | x :: l' => if f x then Some i else list_find_index f l' (S i) end.
Fixpoint list_set {A} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: list_set t i' v
  end.
Definition zlog2 (x : Z) : Z := Z.log2 x.

Section OPS.
Variable E : aenv.
Let SB : Z := ae_space_beg E.
Let INST : Z := ae_instance E.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_mmap_fixed (addr len : Z) : AM bool :=
  a <- acall (AEvMmap addr len kProtRw kFlagsFixedRw) ;;
  match a with
  | AnsOk r => if r =? addr then aret true else aundef_ UBadAnswer
  | AnsErr e => if e =? ENOMEM then aret false else aundef_ UBadAnswer
  end.

(* [comment removed for export] *)
Definition known_ranges (s : astate) : list (Z * Z) :=
  ae_reserved E ++ map (fun c => (sc_map_beg c, sc_map_size c)) (as_sec s)
  ++ map (fun b => (b, kDepotNodeBlockBytes)) (as_node_blocks s) ++ map (fun b => (b, kStoreBlockBytes)) (as_store_blocks s).
Definition iv_disjoint (a n b m : Z) : bool := (a + n <=? b) || (b + m <=? a).
Definition ranges_free (l : list (Z * Z)) (a n : Z) : bool :=
  forallb (fun bm : Z * Z => iv_disjoint a n (fst bm) (snd bm)) l.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition call_mmap_anon (len : Z) : AM (option Z) :=
  s <- aget ;;
  a <- acall (AEvMmap 0 len kProtRw kFlagsAnonRw) ;;
  match a with
  | AnsErr e => if e =? ENOMEM then aret None else aundef_ UBadAnswer
  | AnsOk r =>
      if (r mod kPageSize =? 0) && (0 <? r) && (r + len <=? alloc_ceiling) && ranges_free (known_ranges s) r len then
        if app_mem_b r len && negb (in_primary SB r) && negb (in_primary SB (r + len - 1)) && (r + len <=? kHighMemEnd + 1)
        then aret (Some r) else aundef_ (UPlacement r)
      else aundef_ UBadAnswer
  end.

(* [comment removed for export] *)
Definition call_mmap_ordie (len flags : Z) : AM Z :=
  s <- aget ;;
  a <- acall (AEvMmap 0 len kProtRw flags) ;;
  match a with
  | AnsErr _ => aspin
  | AnsOk r =>
      if (r mod kPageSize =? 0) && (0 <? r) && (r + len <=? alloc_ceiling) && ranges_free (known_ranges s) r len then
        if app_mem_b r len && negb (in_primary SB r) && negb (in_primary SB (r + len - 1)) && (r + len <=? kHighMemEnd + 1)
        then aret r else aundef_ (UPlacement r)
      else aundef_ UBadAnswer
  end.

(* [comment removed for export] *)
Definition call_munmap (addr len : Z) : AM unit :=
  a <- acall (AEvMunmap addr len) ;;
  match a with
  | AnsOk r => if r =? 0 then aret tt else aundef_ UBadAnswer
  | AnsErr _ => aspin
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_alloc_once (count : Z) : AM (option Z) :=
  s <- aget ;;
  let start := as_frames s in
  aupd (upd_keys (fun ks => ks) (fun f => f + count)) ;;;
  let b := start / kStoreBlockFrames in
  let b' := (start + count - 1) / kStoreBlockFrames in
  if b =? b' then
    (* [comment removed for export] *)
    s1 <- aget ;;
    (if (0 <? b) && (zlen (as_store_blocks s1) <? b) then
       r <- call_mmap_ordie kStoreBlockBytes kFlagsNoReserveRw ;;
       aupd (upd_store_blocks (fun l => l ++ [r]))
     else aret tt) ;;;
    aret (Some start)
  else
    (* [comment removed for export] *)
    let in_first := kStoreBlockFrames - start mod kStoreBlockFrames in
    aupd (upd_store_stored (fun st => <[b' := (match st !! b' with Some v => v | None => 0 end) + (count - in_first)]>
                                      (<[b := (match st !! b with Some v => v | None => 0 end) + in_first]> st))) ;;;
    aret None.

Definition store_alloc (count : Z) : AM Z :=
  r <- store_alloc_once count ;;
  match r with
  | Some start => aret start
  | None => r2 <- store_alloc_once count ;;
            match r2 with Some start => aret start | None => aundef_ (UInternal 720) (* [comment removed for export] *) end
  end.

Definition depot_put (key : list Z) : AM Z :=
  s <- aget ;;
  aupd (upd_ndepot (fun k => k + 1)) ;;;                    (* [comment removed for export] *)
  match depot_lookup E s key with
  | Some id => aret id
  | None =>
      let id := depot_n_ids E s + 1 in
      acheck (id <? 2^31) 731 ;;;
      (* [comment removed for export] *)
      (if (id mod kDepotNodesPerBlock =? 0) then
         r <- call_mmap_ordie kDepotNodeBlockBytes kFlagsAnonRw ;;
         aupd (upd_node_blocks (fun l => l ++ [r]))
       else aret tt) ;;;
      _ <- store_alloc (zlen key + 1) ;;
      aupd (upd_keys (fun ks => ks ++ [key]) (fun f => f)) ;;;
      aret id
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ensure_free_array_space (c : Z) (num_freed : Z) : AM bool :=
  s <- aget ;;
  let r := get_region s c in
  let needed_fa := 4 * num_freed in
  if rg_mapped_fa r <? needed_fa then
    let new_fa := round_up needed_fa kFreeArrayMapSize in
    acheck (new_fa <=? kFreeArraySize) 751 ;;;
    let cur := free_array SB c + rg_mapped_fa r in
    let sz := new_fa - rg_mapped_fa r in
    ok <- call_mmap_fixed cur sz ;;
    if ok then
      aupd (fun s => upd_ts (ts_on_mmap sz) (set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r) new_fa (rg_n_allocated r) (rg_n_freed r)) s)) ;;;
      aret true
    else aret false
  else aret true.

(* [comment removed for export] *)
Definition populate_free_array (c : Z) (requested : Z) : AM bool :=
  s <- aget ;;
  let r := get_region s c in
  let size := class_size c in
  let rbeg := region_beg SB c in
  let total := rg_alloc_user r + requested * size in
  ok1 <- (if rg_mapped_user r <? total then
            let user_map := round_up (total - rg_mapped_user r) kUserMapSize in
            (* [comment removed for export] *)
            acheck (rg_mapped_user r + user_map <=? kFreeArrayOffset) 700 ;;;
            ok <- call_mmap_fixed (rbeg + rg_mapped_user r) user_map ;;
            if ok then
              aupd (fun s => upd_cache_mapped (fun m => m + user_map)
                               (upd_ts (ts_on_mmap user_map)
                                 (set_region c (mkRegion (rg_mapped_user r + user_map) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r)
                                                         (rg_n_allocated r) (rg_n_freed r)) s))) ;;;
              aret true
            else aret false
          else aret true) ;;
  if negb ok1 then aret false else
  s1 <- aget ;;
  let r1 := get_region s1 c in
  let new_chunks := (rg_mapped_user r1 - rg_alloc_user r1) / size in
  let total_freed := rg_num_freed r1 + new_chunks in
  ok2 <- ensure_free_array_space c total_freed ;;
  if negb ok2 then aret false else
  s2 <- aget ;;
  let r2 := get_region s2 c in
  (* [comment removed for export] *)
  let fresh := rev (map (fun i => (rg_alloc_user r2 + i * size) / 16) (ziota 0 (Z.to_nat new_chunks))) in
  aupd (set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + new_chunks * size) (rg_free r2 ++ fresh) (rg_mapped_fa r2)
                              (rg_n_allocated r2) (rg_n_freed r2))) ;;;
  aret true.

(* [comment removed for export] *)
Definition get_from_allocator (c : Z) (n : Z) : AM (option (list Z)) :=
  s <- aget ;;
  let r := get_region s c in
  ok <- (if rg_num_freed r <? n then populate_free_array c (n - rg_num_freed r) else aret true) ;;
  if negb ok then aret None else
  s1 <- aget ;;
  let r1 := get_region s1 c in
  acheck (n <=? rg_num_freed r1) 229 ;;;
  let keep := (length (rg_free r1) - Z.to_nat n)%nat in
  let lo := firstn keep (rg_free r1) in
  let hi := skipn keep (rg_free r1) in
  aupd (set_region c (mkRegion (rg_mapped_user r1) (rg_alloc_user r1) lo (rg_mapped_fa r1) (rg_n_allocated r1 + n) (rg_n_freed r1))) ;;;
  aret (Some hi).

(* [comment removed for export] *)
Definition init_cache : AM unit := aupd (upd_cache_inited true).

(* [comment removed for export] *)
Definition refill (c : Z) : AM bool :=
  init_cache ;;;
  r <- get_from_allocator c (hint c) ;;
  match r with
  | None => aret false
  | Some l =>
      aupd (fun s => upd_cache_stale (fun st => <[c := fold_right (fun i m => delete i m) (match st !! c with Some m => m | None => ∅ end)
                                                                 (map Z.of_nat (seq 0 (length l)))]> st)
                       (set_cache c l s)) ;;;
      aret true
  end.

(* [comment removed for export] *)
Definition cache_pop (c : Z) : AM (option Z) :=
  s <- aget ;;
  ok <- (match get_cache s c with [] => refill c | _ => aret true end) ;;
  if negb ok then aret None else
  s1 <- aget ;;
  match get_cache s1 c with
  | [] => aundef_ (UInternal 1)   (* [comment removed for export] *)
  | l => let x := List.last l 0 in
         let i := Z.of_nat (Nat.pred (length l)) in
         aupd (fun s => upd_cache_allocated (fun a => a + class_size c)
                          (upd_cache_stale (fun st => <[c := <[i := x]> (match st !! c with Some m => m | None => ∅ end)]> st)
                            (set_cache c (removelast l) s))) ;;;
         aret (Some (chunk_of_compact SB c x))
  end.

(* [comment removed for export] *)
Definition return_to_allocator (c : Z) (chunks : list Z) : AM unit :=
  s <- aget ;;
  let r := get_region s c in
  let new := rg_num_freed r + zlen chunks in
  ok <- ensure_free_array_space c new ;;
  if negb ok then aspin (* [comment removed for export] *) else
  s1 <- aget ;;
  let r1 := get_region s1 c in
  aupd (set_region c (mkRegion (rg_mapped_user r1) (rg_alloc_user r1) (rg_free r1 ++ chunks) (rg_mapped_fa r1)
                              (rg_n_allocated r1) (rg_n_freed r1 + zlen chunks))).
  (* [comment removed for export] *)

Definition local_dealloc (c : Z) (p : Z) : AM unit :=
  acheck ((1 <=? c) && (c <? kNumClasses)) 50 ;;;
  init_cache ;;;
  s <- aget ;;
  let l := get_cache s c in
  (if zlen l =? max_count c then
     let keep := (length l - Z.to_nat (hint c))%nat in
     aupd (set_cache c (firstn keep l)) ;;;
     return_to_allocator c (skipn keep l)
   else aret tt) ;;;
  s1 <- aget ;;
  let l1 := get_cache s1 c in
  let x := compact_of_chunk SB c p in
  let i := zlen l1 in
  aupd (fun s => upd_cache_allocated (fun a => a - class_size c)
                   (upd_cache_stale (fun st => <[c := delete i (match st !! c with Some m => m | None => ∅ end)]> st)
                     (set_cache c (l1 ++ [x]) s))).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition bump (m : gmap Z Z) (k d : Z) : gmap Z Z :=
  <[k := match m !! k with Some v => v + d | None => d end]> m.

(* [comment removed for export] *)
Definition sec_alloc (needed2 : Z) : AM (option Z) :=
  let msz := round_up needed2 kPageSize + kPageSize in
  r <- call_mmap_anon msz ;;
  match r with
  | None => aret None
  | Some map_beg =>
      aupd (upd_ts (ts_on_mmap msz)) ;;;
      s <- aget ;;
      acheck (n_chunks s <? 2^20) 42 ;;;
      (if n_chunks s =? as_ptr_committed s then
         ok <- call_mmap_fixed (ae_ptr_array E + 8 * as_ptr_committed s) kPtrArrayCommit ;;
         if ok then aupd (fun s => upd_ptr_committed (as_ptr_committed s + kChunksBlockCount) s)
         else aspin   (* [comment removed for export] *)
       else aret tt) ;;;
      aupd (fun s =>
        let idx := n_chunks s in
        upd_glob (fun a => a + msz) (fun m => m + msz)
          (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st + 1) (ss_n_frees st) (ss_cur st + msz) (Z.max (ss_max st) (ss_cur st + msz))
                                               (bump (ss_by_size_log st) (zlog2 msz) 1))
            (upd_sec_stale (delete idx)
              (upd_sec (fun l => l ++ [mkSec map_beg msz needed2])
                (upd_residue (fun r => r ++ residue_pages map_beg msz) s))))) ;;;   (* [comment removed for export] *)
      aret (Some (map_beg + kPageSize))
  end.

(* [comment removed for export] *)
Definition sec_block_begin (s : astate) (m : Z) : Z :=
  let nearest := fold_left (fun acc c => if (sc_map_beg c <=? m) && (acc <? sc_map_beg c) then sc_map_beg c else acc) (as_sec s) 0 in
  if nearest =? 0 then 0
  else match list_find_index (fun c => sc_map_beg c =? nearest) (as_sec s) 0 with
       | Some i => match nth_error (as_sec s) i with
                   | Some c => if m <? sc_map_beg c + sc_map_size c then sc_map_beg c + kPageSize else 0
                   | None => 0
                   end
       | None => 0
       end.

(* [comment removed for export] *)
Definition remap_range (u L : Z) : Z * Z :=
  let sbeg := mem_to_shadow u in
  let send := sbeg + L / 8 in
  let pb := round_up sbeg kPageSize in
  let pe := round_down send kPageSize in
  (pb, pe - pb).
Definition needs_remap (L : Z) : bool := kClearShadowMmapThreshold <=? L / 8.

Definition poison_zero (u L : Z) : AM unit := aret tt.

(* [comment removed for export] *)
Definition large_dealloc (p : Z) : AM unit :=
  s <- aget ;;
  let map_beg := p - kPageSize in
  match list_find_index (fun c => sc_map_beg c =? map_beg) (as_sec s) 0 with
  | None => aundef_ (UInternal 139)
  | Some i =>
      match nth_error (as_sec s) i with
      | None => aundef_ (UInternal 140)
      | Some h =>
          let n := length (as_sec s) in
          let lastc := List.last (as_sec s) h in
          let sec' := removelast (list_set (as_sec s) i lastc) in
          let msz := sc_map_size h in
          aupd (fun s =>
            upd_glob (fun a => a - msz) (fun m => m - msz)
              (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st) (ss_n_frees st + 1) (ss_cur st - msz) (ss_max st) (ss_by_size_log st))
                (upd_sec_stale (fun st => <[Z.of_nat (Nat.pred n) := sc_map_beg lastc]> st)
                  (upd_sec (fun _ => sec') s)))) ;;;
          (* [comment removed for export] *)
          poison_zero map_beg msz ;;;
          aupd (upd_ts (ts_on_munmap msz)) ;;;
          call_munmap map_beg msz
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition amalloc_core (key : list Z) (n : Z) : AM (option Z) :=
  let n' := req n in
  let rzl := rz_log n in
  let rz := rz_size n in
  let prim := from_primary n in
  let need := needed n in                      (* [comment removed for export] *)
  acheck (n <? 2^40) 7 ;;;                     (* [comment removed for export] *)
  aupd (upd_nprimc prim (class_id (needed1 n))) ;;;   (* [comment removed for export] *)
  ab <- (if prim then cache_pop (class_id (needed1 n)) else sec_alloc need) ;;
  match ab with
  | None => aupd (upd_oom true) ;;; aret None
  | Some alloc_beg =>
      id <- depot_put key ;;
      let user_beg := alloc_beg + rz in
      let chunk_beg := user_beg - kChunkHeaderSize in
      (* [comment removed for export] *)
      sK <- aget ;;
      acheck (match as_chunks sK !! chunk_beg with None => true | Some _ => false end) 9 ;;;
      aupd (fun s => upd_dead (delete chunk_beg)
              (upd_chunks (fun cm => <[chunk_beg := mkCM alloc_beg rzl n' (if prim then Some (class_id (needed1 n)) else None) (CAllocated id)]> cm) s)) ;;;
      (* [comment removed for export] *)
      poison_zero user_beg ((n' / 8) * 8) ;;;
      (* [comment removed for export] *)
      aupd (upd_ts (ts_on_malloc n' need (kMaxSize <? need) (class_id need))) ;;;
      aret (Some user_beg)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition batch_alloc : AM Z :=
  r <- cache_pop kBatchClass ;;
  match r with
  | None => aspin
  | Some b => if b =? 0 then aspin else aret b
  end.

Definition enqueue (cb : Z) (n : Z) : AM unit :=
  s <- aget ;;
  let tq := as_tq s in
  let neednew := match tq with [] => true | _ => (zlen (b_items (List.last tq (mkBatch 0 [] 0))) =? kBatchCap) end in
  if neednew then
    b <- batch_alloc ;;
    aupd (upd_tq (fun l => l ++ [mkBatch b [cb] (kBatchSize + n)]))
  else
    aupd (upd_tq (fun l => let b := List.last l (mkBatch 0 [] 0) in
                           removelast l ++ [mkBatch (b_addr b) (b_items b ++ [cb]) (b_size b + n)])).

(* [comment removed for export] *)
Definition qcb_recycle (m : Z) : AM unit :=
  s <- aget ;;
  match as_chunks s !! m with
  | None => aundef_ (UInternal 694)
  | Some meta =>
      match cm_state meta with
      | CAllocated _ => aundef_ (UInternal 695)
      | CQuarantined _ _ =>
          let n := cm_n meta in
          p <- (if in_primary SB m then
                  let off := m - SB in
                  let c := (off / kRegionSize) mod kNumClasses in
                  acheck (negb (c =? 0) && negb (c =? 31)) 2 ;;;
                  let size := class_size c in
                  let idx := (off mod kRegionSize) / size in
                  let beg := region_beg SB (off / kRegionSize) + idx * size in
                  aret (if (idx + 1) * size <=? rg_mapped_user (get_region s c) then beg else 0)
                else aret (sec_block_begin s m)) ;;
          (if in_primary SB p then
             (* [comment removed for export] *)
             acheck (p =? cm_alloc_beg meta) 192 ;;;
             (* [comment removed for export] *)
             acheck (match cm_prim meta with Some c0 => c0 =? ((p - SB) / kRegionSize) mod kNumClasses | None => false end) 241
           else aret tt) ;;;
          aupd (upd_ts (ts_on_real_free n)) ;;;
          if p =? 0 then aundef_ (UInternal 3)   (* [comment removed for export] *)
          else if in_primary SB p then
            let c := ((p - SB) / kRegionSize) mod kNumClasses in
            aupd (fun s => upd_dead (fun d => <[m := n]> d) (upd_chunks (delete m) s)) ;;;
            local_dealloc c p
          else
            acheck (p =? cm_alloc_beg meta) 4 ;;;
            acheck (match cm_prim meta with None => true | Some _ => false end) 242 ;;;   (* [comment removed for export] *)
            aupd (upd_chunks (delete m)) ;;;
            large_dealloc p
      end
  end.

Fixpoint recycle_items (items : list Z) : AM unit :=
  match items with
  | [] => aret tt
  | m :: rest => qcb_recycle m ;;; recycle_items rest
  end.

(* [comment removed for export] *)
Fixpoint do_recycle (bs : list batch) : AM unit :=
  match bs with
  | [] => aret tt
  | b :: rest =>
      recycle_items (b_items b) ;;;
      (if in_primary SB (b_addr b) then
         (* [comment removed for export] *)
         acheck ((((b_addr b - SB) / kRegionSize) mod kNumClasses) =? kBatchClass) 6 ;;;
         local_dealloc (((b_addr b - SB) / kRegionSize) mod kNumClasses) (b_addr b)
       else aundef_ (UInternal 5)) ;;;
      do_recycle rest
  end.

(* [comment removed for export] *)
Fixpoint merge_batches_aux (cur : batch) (rest : list batch) (acc_out : list batch) : list batch * list batch :=
  match rest with
  | [] => ([cur], acc_out)
  | nx :: rest' =>
      if zlen (b_items cur) + zlen (b_items nx) <=? kBatchCap then
        merge_batches_aux (mkBatch (b_addr cur) (b_items cur ++ b_items nx) (b_size cur + (b_size nx - kBatchSize))) rest'
                          (acc_out ++ [mkBatch (b_addr nx) [] kBatchSize])
      else let '(l, o) := merge_batches_aux nx rest' acc_out in (cur :: l, o)
  end.
Definition merge_batches (gq : list batch) : list batch * list batch :=
  match gq with [] => ([], []) | b :: rest => merge_batches_aux b rest [] end.

(* [comment removed for export] *)
Fixpoint pop_prefix (gq : list batch) (bytes min : Z) : list batch * list batch :=
  match gq with
  | [] => ([], [])
  | b :: rest => if min <? bytes then let '(popped, kept) := pop_prefix rest (bytes - b_size b) min in (b :: popped, kept)
                 else ([], gq)
  end.

(* [comment removed for export] *)
Definition recycle : AM unit :=
  s <- aget ;;
  let gq := as_gq s in
  let cache_size := qbytes gq in
  let overhead := kBatchSize * zlen gq in
  acheck (overhead <=? cache_size) 159 ;;;
  let '(gq1, empties) := (if (overhead <? cache_size) && (cache_size * 100 <? overhead * 200) then merge_batches gq else (gq, [])) in
  let '(popped, kept) := pop_prefix gq1 (qbytes gq1) kQuarantineMin in
  aupd (upd_gq (fun _ => kept)) ;;;
  do_recycle (empties ++ popped).

(* [comment removed for export] *)
Definition drain_if_needed : AM unit :=
  s <- aget ;;
  if kThreadQuarantineMax <? tq_bytes s then
    aupd (fun s => upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq s) s)) ;;;
    s1 <- aget ;;
    if kQuarantineMax <? gq_bytes s1 then recycle else aret tt
  else aret tt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition afree_core (key : list Z) (p : Z) : AM unit :=
  s <- aget ;;
  let cb := p - kChunkHeaderSize in
  match as_chunks s !! cb with
  | None => aundef_ (UBadPtr p)
  | Some meta =>
      match cm_state meta with
      | CQuarantined _ _ => aundef_ (UBadPtr p)      (* [comment removed for export] *)
      | CAllocated aid =>
          if negb (cm_user_beg meta =? p) then aundef_ (UBadPtr p) else
          let n := cm_n meta in
          aupd (upd_ts (ts_on_free n)) ;;;
          fid <- depot_put key ;;
          aupd (upd_chunks (fun cm => <[cb := mkCM (cm_alloc_beg meta) (cm_rz_log meta) n (cm_prim meta) (CQuarantined aid fid)]> cm)) ;;;
          (* [comment removed for export] *)
          enqueue cb n ;;;
          drain_if_needed
      end
  end.

(* [comment removed for export] *)
Definition ia_init : AM unit := aupd (upd_ia_inited true).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amalloc (key : list Z) (n : Z) : AM (option Z) := amalloc_core key n.

(* [comment removed for export] *)
Definition afree (key : list Z) (p : Z) : AM unit :=
  ia_init ;;;
  if p =? 0 then aret tt else afree_core key p.

(* [comment removed for export] *)
Definition arealloc (key : list Z) (p n : Z) : AM (option Z) :=
  ia_init ;;;
  if p =? 0 then amalloc_core key n
  else if n =? 0 then (afree_core key p ;;; aret None)     (* [comment removed for export] *)
  else
    aupd (upd_ts (ts_on_realloc n)) ;;;
    r <- amalloc_core key n ;;
    match r with
    | None => aret None
    | Some q =>
        s <- aget ;;
        match as_chunks s !! (p - kChunkHeaderSize) with
        | Some meta => match cm_state meta with
                       | CAllocated _ => if cm_user_beg meta =? p then
                                           (* [comment removed for export] *)
                                           afree_core key p ;;; aret (Some q)
                                         else aundef_ (UBadPtr p)
                       | _ => aundef_ (UBadPtr p)
                       end
        | None => aundef_ (UBadPtr p)
        end
    end.

(* [comment removed for export] *)
Definition acalloc (key : list Z) (nmemb size : Z) : AM (option Z) :=
  if negb (size =? 0) && (2^64 <=? nmemb * size) then aret None   (* [comment removed for export] *)
  else amalloc_core key (nmemb * size).   (* [comment removed for export] *)

End OPS.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint arun {R} (fuel : nat) (t : stree aev aans (astate * aout R)) (oracle : list aans)
  : option (astate * aout R * list aev * list aans) :=
  match t with
  | SRet (s, o) => Some (s, o, [], oracle)
  | SVis e k => match oracle, fuel with
                | a :: rest, S f => match arun f (k a) rest with
                                    | Some (s, o, evs, orc) => Some (s, o, e :: evs, orc)
                                    | None => None
                                    end
                | _, _ => None
                end
  end.
End RC__3.
