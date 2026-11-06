(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition kMaxSize : Z := 65536.
Definition kNumClasses : Z := 32.
Definition kRegionSizeLog : Z := 32.
Definition kUserMapSize : Z := 262144.
Definition kFreeArrayOffset : Z := 3758096384.
Definition kFreeArrayMapSize : Z := 262144.
Definition kFreeArrayMax : Z := 536870912.
Definition kCompactPtrScale : Z := 4.
Definition kChunkHeaderSize : Z := 16.
Definition kChunkHeader2Size : Z := 8.
Definition kPage : Z := 4096.
Definition kSecRz : Z := 2048.
Definition kPtrArrayCommit : Z := 131072.
Definition kPtrArrayEntriesPerCommit : Z := 16384.
Definition kMaxNumChunks : Z := 1048576.
Definition kBatchClass : Z := 24.
Definition kBatchBytes : Z := 8192.
Definition kBatchSlots : Z := 1021.
Definition kQuarantineMax : Z := 268435456.
Definition kQuarantineMin : Z := 241591905.
Definition kQuarantineCacheMax : Z := 1048576.
Definition kClearShadowMmapThreshold : Z := 2 ^ 64 - 1.
Definition kMallocFill : Z := 4096.
Definition kMaxAllowedMalloc : Z := 2 ^ 40.
Definition kStackSizeLog : Z := 20.
Definition kDepotIdsPerBlock : Z := 65536.
Definition kStoreFramesPerBlock : Z := 1048576.
Definition kUnwindMax : nat := 30%nat.
Definition EV_MAX : Z := 8192.
Definition MALLOC_MAX : Z := 2 ^ 28.
Definition shAddressable : Z := 0.
Definition shHeapLeftRz : Z := 250.
Definition shHeapFreed : Z := 253.
Definition shStackAfterReturn : Z := 245.
Definition class_size (c : Z) : Z :=
if c =? 31 then 64
else if c <=? 16 then 32 * c
else let t := Z.shiftl 512 ((c - 16) / 2) in
if Z.odd c then t + t / 2 else t.
Definition class_id (s : Z) : Z :=
if s <=? 512 then (s + 31) / 32
else let l := Z.log2 s in
let hbit := (Z.shiftr s (l - 1)) mod 2 in
let lbits := s mod 2 ^ (l - 1) in
16 + 2 * (l - 9) + hbit + (if lbits =? 0 then 0 else 1).
Fixpoint first_class (s : Z) (c : Z) (fuel : nat) : Z :=
match fuel with
| O => c
| S f => if s <=? class_size c then c else first_class s (c + 1) f
end.
Definition class_id' (s : Z) : Z := first_class s 1 29%nat.
Definition max_cached (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / class_size c)).
Definition rz_log (n : Z) : Z :=
if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := Z.shiftl 16 (rz_log n).
Definition round_up (x a : Z) : Z := (x + a - 1) / a * a.
Definition round_down (x a : Z) : Z := x / a * a.
Definition req_size (n : Z) : Z := if n =? 0 then 1 else n.
Definition rounded_size (n : Z) : Z := round_up (Z.max n 8) 8.
Definition needed_primary (n : Z) : Z := rounded_size n + rz_size n.
Definition from_primary (n : Z) : bool := needed_primary n <=? kMaxSize.
Definition needed_size (n : Z) : Z :=
if from_primary n then needed_primary n else needed_primary n + rz_size n.
Definition sec_map_size (n : Z) : Z := round_up (needed_size n) kPage + kPage.
Definition chunk_class (n : Z) : Z := class_id (needed_size n).
Inductive sptr :=
| PNull
| PPrim (off : Z)
| PSec (r : nat) (off : Z)
| PFake (cid : Z) (pos : Z).
Definition sptr_eqb (p q : sptr) : bool :=
match p, q with
| PNull, PNull => true
| PPrim a, PPrim b => a =? b
| PSec r a, PSec s b => Nat.eqb r s && (a =? b)
| PFake c a, PFake d b => (c =? d) && (a =? b)
| _, _ => false
end.
Definition padd (p : sptr) (d : Z) : sptr :=
match p with
| PPrim off => PPrim (off + d)
| PSec r off => PSec r (off + d)
| q => q
end.
Definition prim_class (off : Z) : Z := Z.shiftr off 32.
Definition region_off (c : Z) : Z := Z.shiftl c 32.
Inductive kreq :=
| KMapUser (c : Z) (off len : Z)
| KMapFreeArray (c : Z) (off len : Z)
| KMapPtrArray (off len : Z)
| KMmapSec (len : Z)
| KMunmapSec (r : nat) (len : Z)
| KShadowRemap (base : sptr) (len : Z)
| KDepot (trace : list Z).
Definition aGranted (z : Z) : bool := z =? 1.
Definition aDestroyed (z : Z) : bool := z =? 2.
Inductive failure :=
| FCheck (pc : Z)
| FModel (tag : Z)
| FFuel.
Inductive itree (S A : Type) : Type :=
| IRet (a : A)
| IAsk (q : kreq) (snap : S) (k : Z -> itree S A)
| ISpin (pc : Z)
| IFail (f : failure).
Arguments IRet {S A}. Arguments IAsk {S A}. Arguments ISpin {S A}. Arguments IFail {S A}.
Fixpoint ibind {S A B : Type} (t : itree S A) (k : A -> itree S B) : itree S B :=
match t with
| IRet a => k a
| IAsk q snap c => IAsk q snap (fun b => ibind (c b) k)
| ISpin pc => ISpin pc
| IFail f => IFail f
end.
Inductive fseg := FRun (lo k : Z) | FOne (off : Z).
Record region := mkRegion {
rg_mapped_user : Z;
rg_alloc_user : Z;
rg_mapped_fa : Z;
rg_free : list fseg;
rg_holes : list (Z * Z)
}.
Definition region0 : region := mkRegion 0 0 0 [] [].
Record pclass := mkPC { pc_max : Z; pc_chunks : list Z   }.
Definition pclass0 : pclass := mkPC 0 [].
Inductive cstate := CAllocated | CQuarantined.
Record chunk := mkChunk {
ck_beg : sptr;
ck_req : Z;
ck_state : cstate
}.
Definition ck_rz (k : chunk) : Z := rz_size (ck_req k).
Definition ck_n (k : chunk) : Z := req_size (ck_req k).
Definition ck_user (k : chunk) : sptr := padd (ck_beg k) (ck_rz k).
Definition ck_hdr (k : chunk) : sptr := padd (ck_beg k) (ck_rz k - kChunkHeaderSize).
Definition ck_extent (k : chunk) : Z :=
if from_primary (ck_req k) then class_size (chunk_class (ck_req k)) else sec_map_size (ck_req k) - kPage.
Record secmap := mkSec { sm_len : Z; sm_size : Z  ; sm_live : bool }.
Record batch := mkBatch { b_self : Z  ;
b_items : list chunk   }.
Definition b_bytes (b : batch) : Z := kBatchBytes + fold_right (fun k acc => ck_n k + acc) 0 (b_items b).
Record qcache := mkQC { qc_list : list batch   ; qc_bytes : Z }.
Definition qc0 : qcache := mkQC [] 0.
Record fakestack := mkFS { fs_hint : list Z  ; fs_live : list (Z * Z)   }.
Record astate := mkA {
st_regions : list region;
st_cache_inited : bool;
st_cache : list pclass;
st_chunks : list chunk;
st_secs : list secmap;
st_sec_arr : list nat;
st_sec_reserved : Z;
st_qthread : qcache;
st_qglobal : qcache;
st_fs : fakestack;
st_depot : list (list Z);
st_internal_inited : bool;
st_nev : Z
}.
Definition init_state : astate :=
mkA (repeat region0 32) false (repeat pclass0 32) [] [] [] 0 qc0 qc0
(mkFS (repeat 0 11) []) [] false 0.
Definition M (A : Type) : Type := astate -> itree astate (A * astate).
Definition ret {A} (a : A) : M A := fun s => IRet (a, s).
Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
fun s => ibind (m s) (fun '(a, s') => k a s').
Definition fail {A} (f : failure) : M A := fun _ => IFail f.
Definition spin {A} (pc : Z) : M A := fun _ => ISpin pc.
Definition get : M astate := fun s => IRet (s, s).
Definition put (s : astate) : M unit := fun _ => IRet (tt, s).
Definition modify (f : astate -> astate) : M unit := fun s => IRet (tt, f s).
Definition askz (q : kreq) : M Z := fun s => IAsk q s (fun z => IRet (z, s)).
Definition mcheck (b : bool) (pc : Z) : M unit := if b then ret tt else fail (FCheck pc).
Declare Scope am_scope.
Notation "x <- m ;; k" := (bind m (fun x => k))
(at level 100, m at next level, k at level 200, right associativity) : am_scope.
Notation "m ;; k" := (bind m (fun _ => k))
(at level 100, k at level 200, right associativity) : am_scope.
Local Open Scope am_scope.
Section e.
Implicit Types (s : astate).
Definition set_regions v s := mkA v (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_cache_inited v s := mkA (st_regions s) v (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_cache v s := mkA (st_regions s) (st_cache_inited s) v (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_chunks v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) v (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_secs v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) v (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_sec_arr v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) v (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_sec_reserved v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) v (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_qthread v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) v (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_qglobal v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) v (st_fs s) (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_fs v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) v (st_depot s) (st_internal_inited s) (st_nev s).
Definition set_depot v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) v (st_internal_inited s) (st_nev s).
Definition set_internal_inited v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) v (st_nev s).
Definition set_nev v s := mkA (st_regions s) (st_cache_inited s) (st_cache s) (st_chunks s) (st_secs s) (st_sec_arr s) (st_sec_reserved s) (st_qthread s) (st_qglobal s) (st_fs s) (st_depot s) (st_internal_inited s) v.
End e.
Fixpoint lupd {X : Type} (l : list X) (i : nat) (v : X) : list X :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: lupd t i' v
end.
Definition znth {X} (d : X) (i : Z) (l : list X) : X := nth (Z.to_nat i) l d.
Definition zupd {X} (i : Z) (v : X) (l : list X) : list X := lupd l (Z.to_nat i) v.
Fixpoint removelast {X} (l : list X) : list X :=
match l with [] => [] | [x] => [] | x :: t => x :: removelast t end.
Definition get_region (c : Z) : M region := s <- get ;; ret (znth region0 c (st_regions s)).
Definition set_region (c : Z) (r : region) : M unit := modify (fun s => set_regions (zupd c r (st_regions s)) s).
Definition get_pc (c : Z) : M pclass := s <- get ;; ret (znth pclass0 c (st_cache s)).
Definition set_pc (c : Z) (p : pclass) : M unit := modify (fun s => set_cache (zupd c p (st_cache s)) s).
Fixpoint find_user (l : list chunk) (p : sptr) : option chunk :=
match l with
| [] => None
| k :: t => if sptr_eqb (ck_user k) p then Some k else find_user t p
end.
Fixpoint upd_chunk (l : list chunk) (k : chunk) : list chunk :=
match l with
| [] => [k]
| k' :: t => if sptr_eqb (ck_beg k') (ck_beg k) then k :: t else k' :: upd_chunk t k
end.
Fixpoint del_chunk (l : list chunk) (beg : sptr) : list chunk :=
match l with
| [] => []
| k :: t => if sptr_eqb (ck_beg k) beg then t else k :: del_chunk t beg
end.
Definition tick : M unit := modify (fun s => set_nev (st_nev s + 1) s).
Fixpoint fa_len (l : list fseg) : Z :=
match l with [] => 0 | FRun _ k :: t => k + fa_len t | FOne _ :: t => 1 + fa_len t end.
Fixpoint fa_pop (size : Z) (l : list fseg) : option (Z * list fseg) :=
match l with
| [] => None
| FOne off :: t => Some (off, t)
| FRun lo k :: t =>
if k <=? 0 then fa_pop size t
else Some (lo, if k =? 1 then t else FRun (lo + size) (k - 1) :: t)
end.
Fixpoint fa_pop_n (fuel : nat) (size : Z) (n : Z) (l : list fseg) (acc : list Z) : option (list Z * list fseg) :=
match fuel with
| O => None
| S f => if n <=? 0 then Some (rev acc, l)
else match fa_pop size l with
| None => None
| Some (off, l') => fa_pop_n f size (n - 1) l' (off :: acc)
end
end.
Definition cache_fill_order (popped_top_first : list Z) : list Z := rev popped_top_first.
Fixpoint fa_push_list (l : list fseg) (offs : list Z) : list fseg :=
match offs with [] => l | o :: t => fa_push_list (FOne o :: l) t end.
Definition add_hole (h : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
h :: filter (fun h' => negb (fst h' =? fst h)) l.
Definition del_hole (off : Z) (l : list (Z * Z)) : list (Z * Z) :=
filter (fun h' => negb (fst h' =? off)) l.
Definition ensure_free_array (c : Z) (need : Z) (spin_on_fail : bool) : M bool :=
r <- get_region c ;;
let needed := 4 * need in
if needed <=? rg_mapped_fa r then ret true
else
let new_mapped := round_up needed kFreeArrayMapSize in
mcheck (new_mapped <=? kFreeArrayMax) 212388   ;;
z <- askz (KMapFreeArray c (rg_mapped_fa r) (new_mapped - rg_mapped_fa r)) ;;
if aGranted z then
set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) new_mapped (rg_free r)
(del_hole (kFreeArrayOffset + rg_mapped_fa r) (rg_holes r))) ;;
ret true
else
(if aDestroyed z
then set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(add_hole (kFreeArrayOffset + rg_mapped_fa r, new_mapped - rg_mapped_fa r) (rg_holes r)))
else ret tt) ;;
if spin_on_fail then spin 213516   else ret false.
Definition map_more_user (c : Z) (need : Z) : M bool :=
r <- get_region c ;;
let size := class_size c in
let total := rg_alloc_user r + need * size in
if rg_mapped_user r <? total then
let map_size := round_up (total - rg_mapped_user r) kUserMapSize in
mcheck (rg_mapped_user r + map_size <=? kFreeArrayOffset) 222820   ;;
z <- askz (KMapUser c (rg_mapped_user r) map_size) ;;
if aGranted z then
set_region c (mkRegion (rg_mapped_user r + map_size) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(del_hole (rg_mapped_user r) (rg_holes r))) ;; ret true
else
(if aDestroyed z
then set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r)
(add_hole (rg_mapped_user r, map_size) (rg_holes r)))
else ret tt) ;; ret false
else ret true.
Definition populate (c : Z) (need : Z) : M bool :=
ok <- map_more_user c need ;;
if negb ok then ret false
else
r <- get_region c ;;
let size := class_size c in
let new_cnt := (rg_mapped_user r - rg_alloc_user r) / size in
let total_freed := fa_len (rg_free r) + new_cnt in
ok2 <- ensure_free_array c total_freed false ;;
if negb ok2 then ret false
else
r2 <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + new_cnt * size) (rg_mapped_fa r2)
(FRun (rg_alloc_user r2) new_cnt :: rg_free r2) (rg_holes r2)) ;;
ret true.
Definition get_from_allocator (c : Z) (n : Z) : M (option (list Z)) :=
r <- get_region c ;;
ok <- (if fa_len (rg_free r) <? n then populate c (n - fa_len (rg_free r)) else ret true) ;;
if negb ok then ret None
else
r2 <- get_region c ;;
if fa_len (rg_free r2) <? n then ret None
else match fa_pop_n 10000%nat (class_size c) n (rg_free r2) [] with
| None => fail (FModel 1)
| Some (tops, rest) =>
set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2) (rg_mapped_fa r2) rest (rg_holes r2)) ;;
ret (Some tops)
end.
Definition init_caches (l : list pclass) : list pclass :=
map (fun c => mkPC (max_cached (Z.of_nat c)) (pc_chunks (nth c l pclass0))) (seq 0 32).
Definition init_cache_if_needed : M unit :=
s <- get ;;
if st_cache_inited s then ret tt
else put (set_cache_inited true (set_cache (init_caches (st_cache s)) s)).
Definition refill_if_empty (c : Z) : M unit :=
p <- get_pc c ;;
match pc_chunks p with
| [] => got <- get_from_allocator c (pc_max p / 2) ;;
match got with
| None => ret tt
| Some tops => set_pc c (mkPC (pc_max p) (cache_fill_order tops))
end
| _ => ret tt
end.
Definition cache_alloc (c : Z) : M (option Z) :=
init_cache_if_needed ;;
refill_if_empty c ;;
p <- get_pc c ;;
match pc_chunks p with
| [] => ret None
| l => let off := last l 0 in
set_pc c (mkPC (pc_max p) (removelast l)) ;;
ret (Some (region_off c + off))
end.
Definition sec_alloc (n : Z) : M (option sptr) :=
let map_size := sec_map_size n in
z <- askz (KMmapSec map_size) ;;
if z =? 0 then ret None
else
s <- get ;;
let r := length (st_secs s) in
let idx := Z.of_nat (length (st_sec_arr s)) in
mcheck (idx <? kMaxNumChunks) 221048   ;;
put (set_secs (st_secs s ++ [mkSec map_size (needed_size n) true]) s) ;;
(if idx =? st_sec_reserved s then
z2 <- askz (KMapPtrArray (8 * idx) kPtrArrayCommit) ;;
if aGranted z2 then modify (fun s => set_sec_reserved (st_sec_reserved s + kPtrArrayEntriesPerCommit) s)
else spin 391236
else ret tt) ;;
modify (fun s => set_sec_arr (st_sec_arr s ++ [r]) s) ;;
ret (Some (PSec r kPage)).
Definition bad_next (fp top nfp : Z) : bool := (nfp <=? fp) || (top - 16 <=? nfp) || negb (nfp mod 8 =? 0).
Fixpoint fpchain (load : Z -> option Z) (bp top : Z) (ch : list (Z * Z * Z)) : Prop :=
match ch with
| [] => exists r, load (bp - 8) = Some r /\ 0 <= r < 4096
| (fp, ra, nfp) :: rest =>
fp = bp /\ fp mod 8 = 0 /\ load (fp - 8) = Some ra /\ load (fp - 16) = Some nfp /\ 4096 <= ra /\
(if bad_next fp top nfp then rest = [] else fpchain load nfp top rest)
end.
Definition unwind_of_chain (pc0 : Z) (ch : list (Z * Z * Z)) : list Z :=
firstn kUnwindMax (pc0 :: flat_map (fun r => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end) ch).
Fixpoint unwind_loop (fuel : nat) (pc0 : Z) (top : Z) (bp : Z) (chain : list (Z * Z * Z)) (acc : list Z) : list Z :=
match fuel, chain with
| O, _ | _, [] => rev acc
| S f, (b, ra, s0) :: rest =>
if negb (b =? bp) then rev acc
else if ra <? 4096 then rev acc
else let acc' := if ra =? pc0 then acc else ra :: acc in
if bad_next bp top s0 then rev acc'
else unwind_loop f pc0 top s0 rest acc'
end.
Definition unwind_trace (pc0 bp top bottom : Z) (chain : list (Z * Z * Z)) : list Z :=
if (bp <=? bottom) || (top - 16 <=? bp) || negb (bp mod 8 =? 0) then [pc0]
else unwind_loop 29%nat pc0 top bp chain [pc0].
Fixpoint trace_eqb (a b : list Z) : bool :=
match a, b with
| [], [] => true
| x :: a', y :: b' => (x =? y) && trace_eqb a' b'
| _, _ => false
end.
Fixpoint mem_trace (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => trace_eqb t u || mem_trace t l' end.
Definition depot_ids (s : astate) : Z := 1 + Z.of_nat (length (st_depot s)).
Definition depot_frames (s : astate) : Z :=
fold_right (fun t acc => Z.of_nat (length t) + 1 + acc) 0 (st_depot s).
Definition kStartFramesMax : Z := 32.
Definition depot_put (trace : list Z) : M unit :=
z <- askz (KDepot trace) ;;
if z =? 0 then ret tt
else
s <- get ;;
mcheck (depot_ids s + 1 <? kDepotIdsPerBlock) 469488   ;;
mcheck (kStartFramesMax + depot_frames s + Z.of_nat (length trace) + 1 <? kStoreFramesPerBlock) 460508   ;;
put (set_depot (st_depot s ++ [trace]) s).
Definition needs_remap (n' : Z) : bool := kClearShadowMmapThreshold <=? n' / 8.
Definition malloc (n : Z) (trace : list Z) : M sptr :=
tick ;;
mcheck (n <? kMaxAllowedMalloc - kPage) 202260   ;;
ob <- (if from_primary n
then o <- cache_alloc (chunk_class n) ;;
ret (match o with Some off => Some (PPrim off) | None => None end)
else sec_alloc n) ;;
match ob with
| None => ret PNull
| Some beg =>
depot_put trace ;;
let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin 449860
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)
end.
Definition qc_push (q : qcache) (k : chunk) (newb : option Z) : qcache :=
match newb with
| Some b => mkQC (qc_list q ++ [mkBatch b [k]]) (qc_bytes q + ck_n k + kBatchBytes)
| None => mkQC (match rev (qc_list q) with
| [] => []
| lastb :: initr => rev initr ++ [mkBatch (b_self lastb) (b_items lastb ++ [k])]
end) (qc_bytes q + ck_n k)
end.
Definition need_new_batch (q : qcache) : bool :=
match rev (qc_list q) with
| [] => true
| lastb :: _ => Z.of_nat (length (b_items lastb)) =? kBatchSlots
end.
Definition enqueue (k : chunk) : M unit :=
s <- get ;;
nb <- (if need_new_batch (st_qthread s) then
ob <- cache_alloc kBatchClass ;;
match ob with
| None => spin 219184
| Some off => ret (Some off)
end
else ret None) ;;
modify (fun s => set_qthread (qc_push (st_qthread s) k nb) s).
Definition return_to_allocator (c : Z) (offs : list Z) : M unit :=
r <- get_region c ;;
let newlen := fa_len (rg_free r) + Z.of_nat (length offs) in
_ <- ensure_free_array c newlen true ;;
r <- get_region c ;;
set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (fa_push_list (rg_free r) offs) (rg_holes r)).
Definition cache_dealloc (c : Z) (off_in_space : Z) : M unit :=
init_cache_if_needed ;;
p <- get_pc c ;;
let rel := off_in_space - region_off c in
(if Z.of_nat (length (pc_chunks p)) =? pc_max p then
let n := pc_max p / 2 in
let keep := firstn (length (pc_chunks p) - Z.to_nat n) (pc_chunks p) in
let drained := skipn (length (pc_chunks p) - Z.to_nat n) (pc_chunks p) in
return_to_allocator c drained ;; set_pc c (mkPC (pc_max p) keep)
else ret tt) ;;
p <- get_pc c ;;
set_pc c (mkPC (pc_max p) (pc_chunks p ++ [rel])).
Fixpoint index_of (l : list nat) (r : nat) (i : nat) : option nat :=
match l with [] => None | x :: t => if Nat.eqb x r then Some i else index_of t r (S i) end.
Definition sec_dealloc (r : nat) : M unit :=
s <- get ;;
match nth_error (st_secs s) r, index_of (st_sec_arr s) r 0%nat with
| Some sm, Some i =>
(if needs_remap (sm_len sm) then
z <- askz (KShadowRemap (PSec r 0) (sm_len sm)) ;;
if aGranted z then ret tt else spin 449860
else ret tt) ;;
_ <- askz (KMunmapSec r (sm_len sm)) ;;
modify (fun s =>
let arr := st_sec_arr s in
let lastr := last arr r in
let arr' := removelast (lupd arr i lastr) in
set_sec_arr arr' (set_secs (lupd (st_secs s) r (mkSec (sm_len sm) (sm_size sm) false)) s))
| _, _ => fail (FModel 2)
end.
Fixpoint mem_chunk (k : chunk) (l : list chunk) : bool :=
match l with
| [] => false
| k' :: t => (sptr_eqb (ck_beg k') (ck_beg k) && (ck_req k' =? ck_req k) &&
match ck_state k', ck_state k with CQuarantined, CQuarantined | CAllocated, CAllocated => true | _, _ => false end)
|| mem_chunk k t
end.
Definition recycle_chunk (k : chunk) : M unit :=
s <- get ;;
mcheck (mem_chunk k (st_chunks s)) 210276   ;;
put (set_chunks (del_chunk (st_chunks s) (ck_beg k)) s) ;;
match ck_beg k with
| PPrim off => cache_dealloc (prim_class off) off
| PSec r _ => sec_dealloc r
| _ => fail (FModel 4)
end.
Fixpoint recycle_items (fuel : nat) (items : list chunk) : M unit :=
match fuel, items with
| _, [] => ret tt
| O, _ => fail FFuel
| S f, k :: t => recycle_chunk k ;; recycle_items f t
end.
Fixpoint do_recycle (fuel : nat) (bs : list batch) : M unit :=
match fuel, bs with
| _, [] => ret tt
| O, _ => fail FFuel
| S f, b :: t => recycle_items 1100%nat (b_items b) ;;
cache_dealloc kBatchClass (b_self b) ;;
do_recycle f t
end.
Fixpoint pop_batches (fuel : nat) (q : qcache) (acc : list batch) : qcache * list batch :=
match fuel with
| O => (q, rev acc)
| S f => if qc_bytes q <=? kQuarantineMin then (q, rev acc)
else match qc_list q with
| [] => (q, rev acc)
| b :: t => pop_batches f (mkQC t (qc_bytes q - b_bytes b)) (b :: acc)
end
end.
Definition maybe_drain : M unit :=
s <- get ;;
if qc_bytes (st_qthread s) <=? kQuarantineCacheMax then ret tt
else
let g := mkQC (qc_list (st_qglobal s) ++ qc_list (st_qthread s)) (qc_bytes (st_qglobal s) + qc_bytes (st_qthread s)) in
put (set_qglobal g (set_qthread qc0 s)) ;;
if qc_bytes g <=? kQuarantineMax then ret tt
else
mcheck (2 * (kBatchBytes * Z.of_nat (length (qc_list g))) <=? qc_bytes g) 209280   ;;
let '(g', popped) := pop_batches 100000%nat g [] in
modify (set_qglobal g') ;;
do_recycle 100000%nat popped.
Definition free (p : sptr) (trace : list Z) : M unit :=
tick ;;
s <- get ;;
(if st_internal_inited s then ret tt else modify (set_internal_inited true)) ;;
match p with
| PNull => ret tt
| _ =>
s <- get ;;
match find_user (st_chunks s) p with
| None => fail (FCheck 201376)
| Some k =>
mcheck (match ck_state k with CAllocated => true | _ => false end) 201364   ;;
depot_put trace ;;
let k' := mkChunk (ck_beg k) (ck_req k) CQuarantined in
modify (fun s => set_chunks (upd_chunk (st_chunks s) k') s) ;;
enqueue k' ;;
maybe_drain
end
end.
Definition fs_frames (cid : Z) : Z := Z.shiftl 1 (kStackSizeLog - 6 - cid).
Definition fs_frame_bytes (cid : Z) : Z := Z.shiftl 64 cid.
Fixpoint mem_pos (l : list (Z * Z)) (cid pos : Z) : bool :=
match l with [] => false | (c, p) :: t => ((c =? cid) && (p =? pos)) || mem_pos t cid pos end.
Fixpoint fs_probe (fuel : nat) (live : list (Z * Z)) (cid : Z) (hint : Z) : option (Z * Z) :=
match fuel with
| O => None
| S f => let pos := hint mod fs_frames cid in
if mem_pos live cid pos then fs_probe f live cid (hint + 1)
else Some (pos, hint + 1)
end.
Definition stack_malloc (cid : Z) : M sptr :=
s <- get ;;
let fs := st_fs s in
let hint := znth 0 cid (fs_hint fs) in
match fs_probe (Z.to_nat (fs_frames cid)) (fs_live fs) cid hint with
| None => ret PNull
| Some (pos, hint') =>
put (set_fs (mkFS (zupd cid hint' (fs_hint fs)) ((cid, pos) :: fs_live fs)) s) ;;
ret (PFake cid pos)
end.
Fixpoint del_pos (l : list (Z * Z)) (cid pos : Z) : list (Z * Z) :=
match l with [] => [] | (c, p) :: t => if (c =? cid) && (p =? pos) then t else (c, p) :: del_pos t cid pos end.
Definition stack_free (cid pos : Z) : M unit :=
modify (fun s => set_fs (mkFS (fs_hint (st_fs s)) (del_pos (fs_live (st_fs s)) cid pos)) s).
Definition chunk_granule (k : chunk) (j : Z) : Z :=
let u := ck_rz k / 8 in
let full := ck_n k / 8 in
let part := ck_n k mod 8 in
if j <? u then shHeapLeftRz
else match ck_state k with
| CQuarantined => if j <? u + (ck_n k + 7) / 8 then shHeapFreed else shHeapLeftRz
| CAllocated =>
if j <? u + full then shAddressable
else if (j =? u + full) && negb (part =? 0) then part
else shHeapLeftRz
end.
Definition aok (s : astate) (q : kreq) (z : Z) : Prop :=
match q with
| KMapUser _ _ _ | KMapFreeArray _ _ _ | KMapPtrArray _ _ | KShadowRemap _ _ => z = 0 \/ z = 1
| KMmapSec _ => z = 0 \/ z = 1
| KMunmapSec _ _ => z = 1
| KDepot tr => z = 0 \/ (z = 1 /\ mem_trace tr (st_depot s) = false)
end.
Fixpoint asafe {A : Type} (t : itree astate A) : Prop :=
match t with
| IRet _ => True
| ISpin _ => True
| IFail _ => False
| IAsk q s k => forall z, aok s q z -> asafe (k z)
end.
Fixpoint apath {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
match t, tr with
| IRet a', [] => a' = a
| IAsk q s k, (q', z) :: tr' => q' = q /\ aok s q z /\ apath (k z) tr' a
| _, _ => False
end.
Fixpoint aspins {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (pc : Z) : Prop :=
match t, tr with
| ISpin pc', [] => pc' = pc
| IAsk q s k, (q', z) :: tr' => q' = q /\ aok s q z /\ aspins (k z) tr' pc
| _, _ => False
end.
Fixpoint irun {S A} (fuel : nat) (t : itree S A) (ans : list Z) : option (A + Z) :=
match fuel with
| O => None
| S f =>
match t with
| IRet a => Some (inl a)
| ISpin pc => Some (inr pc)
| IFail _ => None
| IAsk _ _ k => match ans with
| [] => irun f (k 1) []
| z :: rest => irun f (k z) rest
end
end
end.
Example class_table_ok :
map class_size [1;16;17;18;24;30] = [32;512;768;1024;8192;65536] /\
map class_id [24;488;584;6152;49160;8192] = [1;16;17;24;30;24] /\
(from_primary 64512, from_primary 64513, sec_map_size 65536, sec_map_size 100000000)
= (true, false, 73728, 100012032).
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition run_malloc (n : Z) (s : astate) : option (sptr * astate) :=
match irun 1000 (malloc n [1;2] s) [] with Some (inl r) => Some r | _ => None end.
Definition run_free (p : sptr) (s : astate) : option astate :=
match irun 100000 (free p [3;4] s) [] with Some (inl r) => Some (snd r) | _ => None end.
Example malloc_free_cycle :
match run_malloc 46 init_state with
| Some (p, s1) =>
match run_free p s1 with
| Some s2 => (p, Z.of_nat (length (st_chunks s2)), qc_bytes (st_qthread s2),
Z.of_nat (length (pc_chunks (znth pclass0 2 (st_cache s2)))),
Z.of_nat (length (pc_chunks (znth pclass0 24 (st_cache s2)))), st_nev s2)
| None => (PNull, -1, -1, -1, -1, -1)
end
| None => (PNull, -2, -2, -2, -2, -2)
end = (PPrim (8589934592 + 16), 1, 46 + 8192, 7, 0, 2).
Proof. vm_compute. reflexivity. Qed.
Example secondary_cycle :
match run_malloc 65536 init_state with
| Some (p, s1) => (p, st_sec_reserved s1, Z.of_nat (length (st_sec_arr s1)))
| None => (PNull, -1, -1)
end = (PSec 0 (4096 + 2048), 16384, 1).
Proof. vm_compute. reflexivity. Qed.
Example big_cycle :
match irun 1000 (malloc 1048576 [1;2] init_state) [] with
| Some (inl (p, s1)) => (p, Z.of_nat (length (st_chunks s1)))
| _ => (PNull, -1)
end = (PSec 0 (4096 + 2048), 1).
Proof. vm_compute. reflexivity. Qed.
