(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition UNIT : Z := 16.
Definition IB : Z := 4.
Definition PGSZ : Z := 4096.
Definition MMAP_THRESHOLD : Z := 131052.
Definition METAS_PER_AREA : Z := 101.
Definition META_SIZE : Z := 40.
Definition AREA_HDR : Z := 24.
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
Definition small_cnt_tab : list (list Z) :=
[[30; 30; 30]; [31; 15; 15]; [20; 10; 10]; [31; 15; 7]; [25; 12; 6];
[21; 10; 5]; [18; 8; 4]; [31; 15; 7]; [28; 14; 6]].
Definition med_cnt_tab : list Z := [28; 24; 20; 32].
Definition znth (i : Z) (l : list Z) : Z := nth (Z.to_nat i) l 0.
Fixpoint zupd (l : list Z) (i : nat) (v : Z) : list Z :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: zupd t i' v
end.
Definition zset (i : Z) (v : Z) (l : list Z) : list Z := zupd l (Z.to_nat i) v.
Definition class_size (sc : Z) : Z := UNIT * znth sc size_classes.
Definition lowbit (m : Z) : Z := Z.land m (- m).
Definition ctz32 (m : Z) : Z := Z.log2 (lowbit m).
Definition clz32 (x : Z) : Z := 31 - Z.log2 x.
Definition ones (k : Z) : Z := 2 ^ (k + 1) - 1.
Definition bit (k : Z) : Z := 2 ^ k.
Definition page_round (x : Z) : Z := (x + PGSZ - 1) / PGSZ * PGSZ.
Definition class_of_units (k : Z) : Z :=
if k <? 10 then k else
let k := k + 1 in
let i := (28 - clz32 k) * 4 + 8 in
let i := if znth (i + 1) size_classes <? k then i + 2 else i in
if znth i size_classes <? k then i + 1 else i.
Definition size_to_class (n : Z) : Z := class_of_units (Z.shiftr (n + IB - 1) 4).
Definition size_overflows (n : Z) : bool := 2 ^ 63 - 4096 <=? n.
Inductive sptr := SP (r : nat) (off : Z).
Definition sptr_eqb (p q : sptr) : bool :=
match p, q with SP r o, SP r' o' => Nat.eqb r r' && Z.eqb o o' end.
Definition osptr_eqb (p q : option sptr) : bool :=
match p, q with
| None, None => true
| Some p, Some q => sptr_eqb p q
| _, _ => false
end.
Definition padd (p : sptr) (d : Z) : sptr := match p with SP r o => SP r (o + d) end.
Definition prid (p : sptr) : nat := match p with SP r _ => r end.
Definition poff (p : sptr) : Z := match p with SP _ o => o end.
Inductive rkind :=
| RkBrk
| RkMetaRes
| RkMap.
Record region := mkRegion {
rg_kind : rkind;
rg_len  : Z;
rg_rw   : list Z;
rg_live : bool
}.
Inductive kreq :=
| KBrkQuery
| KBrkGrow (npages : Z)
| KGuard
| KMmapRW (len : Z)
| KMmapNone (len : Z)
| KMprotect (page : sptr)
| KMunmap (r : nat) (len : Z)
| KMremap (r : nat) (old_len new_len : Z)
| KJunk (pristine : Z).
Inductive failure :=
| FAssert (site : Z)
| FFuel
| FModel (tag : Z).
Inductive itree (S A : Type) : Type :=
| IRet (a : A)
| IAsk (q : kreq) (snap : S) (k : Z -> itree S A)
| IFail (f : failure).
Arguments IRet {S A}. Arguments IAsk {S A}. Arguments IFail {S A}.
Fixpoint ibind {S A B : Type} (t : itree S A) (k : A -> itree S B) : itree S B :=
match t with
| IRet a => k a
| IAsk q snap c => IAsk q snap (fun b => ibind (c b) k)
| IFail f => IFail f
end.
Inductive fkind := FUser | FGroup.
Record frame := mkFrame {
fr_off  : Z;
fr_n    : Z;
fr_kind : fkind
}.
Record slotst := mkSlot { ss_hdr : option (Z * Z); ss_fr : option frame }.
Definition slot_zero : slotst := mkSlot (Some (0, 0)) None.
Definition slot_junk : slotst := mkSlot None None.
Record ameta := mkAMeta {
am_prev   : option sptr;
am_next   : option sptr;
am_mem    : sptr;
am_avail  : Z;
am_freed  : Z;
am_last   : Z;
am_sc     : Z;
am_maplen : Z;
am_aidx   : Z;
am_slots  : list slotst
}.
Inductive mslot :=
| MFree (prev next : option sptr)
| MRaw
| MUsed (m : ameta).
Inductive brkst :=
| BrkNever
| BrkDead
| BrkCur (r : nat) (pages : Z).
Record astate := mkA {
st_init_done : bool;
st_mmap_counter : Z;
st_free_meta_head : option sptr;
st_avail_meta : sptr;
st_avail_meta_count : Z;
st_avail_meta_area_count : Z;
st_meta_alloc_shift : Z;
st_area_head : option sptr;
st_area_tail : option sptr;
st_avail_meta_areas : sptr;
st_active : list (option sptr);
st_usage : list Z;
st_unmap_seq : list Z;
st_bounces : list Z;
st_seq : Z;
st_brk : brkst;
st_metas : list (sptr * mslot);
st_regions : list region;
st_areas : list sptr
}.
Definition init_state : astate :=
mkA false 0 None (SP 0 0) 0 0 0 None None (SP 0 0)
(repeat None 48) (repeat 0 48) (repeat 0 32) (repeat 0 32) 0 BrkNever
[] [] [].
Definition M (A : Type) : Type := astate -> itree astate (A * astate).
Definition ret {A} (a : A) : M A := fun s => IRet (a, s).
Definition bind {A B} (m : M A) (k : A -> M B) : M B :=
fun s => ibind (m s) (fun '(a, s') => k a s').
Definition fail {A} (f : failure) : M A := fun _ => IFail f.
Definition get : M astate := fun s => IRet (s, s).
Definition put (s : astate) : M unit := fun _ => IRet (tt, s).
Definition modify (f : astate -> astate) : M unit := fun s => IRet (tt, f s).
Definition askz (q : kreq) : M Z := fun s => IAsk q s (fun z => IRet (z, s)).
Definition ask (q : kreq) : M bool := fun s => IAsk q s (fun z => IRet (negb (z =? 0), s)).
Definition massert (b : bool) (site : Z) : M unit :=
if b then ret tt else fail (FAssert site).
Definition mcheck (b : bool) (tag : Z) : M unit :=
if b then ret tt else fail (FModel tag).
Declare Scope mm_scope.
Notation "x <- m ;; k" := (bind m (fun x => k))
(at level 100, m at next level, k at level 200, right associativity) : mm_scope.
Notation "m ;; k" := (bind m (fun _ => k))
(at level 100, k at level 200, right associativity) : mm_scope.
Local Open Scope mm_scope.
Section w.
Implicit Types (s : astate).
Definition set_init_done (v : bool) s : astate := mkA v (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_mmap_counter (v : Z) s : astate := mkA (st_init_done s) v (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_free_meta_head (v : option sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) v (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_avail_meta (v : sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) v (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_avail_meta_count (v : Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) v (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_avail_meta_area_count (v : Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) v (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_meta_alloc_shift (v : Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) v (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_area_head (v : option sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) v (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_area_tail (v : option sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) v (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_avail_meta_areas (v : sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) v (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_active (v : list (option sptr)) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) v (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_usage (v : list Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) v (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_unmap_seq (v : list Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) v (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_bounces (v : list Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) v (st_seq s) (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_seq (v : Z) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) v (st_brk s) (st_metas s) (st_regions s) (st_areas s).
Definition set_brk (v : brkst) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) v (st_metas s) (st_regions s) (st_areas s).
Definition set_metas (v : list (sptr * mslot)) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) v (st_regions s) (st_areas s).
Definition set_regions (v : list region) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) v (st_areas s).
Definition set_areas (v : list sptr) s : astate := mkA (st_init_done s) (st_mmap_counter s) (st_free_meta_head s) (st_avail_meta s) (st_avail_meta_count s) (st_avail_meta_area_count s) (st_meta_alloc_shift s) (st_area_head s) (st_area_tail s) (st_avail_meta_areas s) (st_active s) (st_usage s) (st_unmap_seq s) (st_bounces s) (st_seq s) (st_brk s) (st_metas s) (st_regions s) v.
End w.
Fixpoint lupd {X : Type} (l : list X) (i : nat) (v : X) : list X :=
match l, i with
| [], _ => []
| _ :: t, O => v :: t
| h :: t, S i' => h :: lupd t i' v
end.
Fixpoint mlookup (l : list (sptr * mslot)) (p : sptr) : option mslot :=
match l with
| [] => None
| (q, x) :: t => if sptr_eqb p q then Some x else mlookup t p
end.
Fixpoint mupdate (l : list (sptr * mslot)) (p : sptr) (x : mslot) : list (sptr * mslot) :=
match l with
| [] => [(p, x)]
| (q, y) :: t => if sptr_eqb p q then (q, x) :: t else (q, y) :: mupdate t p x
end.
Definition getm (p : sptr) : M ameta :=
s <- get ;;
match mlookup (st_metas s) p with
| Some (MUsed am) => ret am
| _ => fail (FModel 1)
end.
Definition setm (p : sptr) (am : ameta) : M unit :=
modify (fun s => set_metas (mupdate (st_metas s) p (MUsed am)) s).
Definition setslot (p : sptr) (x : mslot) : M unit :=
modify (fun s => set_metas (mupdate (st_metas s) p x) s).
Definition am_set_links (pr nx : option sptr) (m : ameta) : ameta :=
mkAMeta pr nx (am_mem m) (am_avail m) (am_freed m) (am_last m) (am_sc m) (am_maplen m) (am_aidx m) (am_slots m).
Definition am_set_prev (pr : option sptr) (m : ameta) : ameta :=
mkAMeta pr (am_next m) (am_mem m) (am_avail m) (am_freed m) (am_last m) (am_sc m) (am_maplen m) (am_aidx m) (am_slots m).
Definition am_set_next (nx : option sptr) (m : ameta) : ameta :=
mkAMeta (am_prev m) nx (am_mem m) (am_avail m) (am_freed m) (am_last m) (am_sc m) (am_maplen m) (am_aidx m) (am_slots m).
Definition am_set_avail (v : Z) (m : ameta) : ameta :=
mkAMeta (am_prev m) (am_next m) (am_mem m) v (am_freed m) (am_last m) (am_sc m) (am_maplen m) (am_aidx m) (am_slots m).
Definition am_set_freed (v : Z) (m : ameta) : ameta :=
mkAMeta (am_prev m) (am_next m) (am_mem m) (am_avail m) v (am_last m) (am_sc m) (am_maplen m) (am_aidx m) (am_slots m).
Definition am_set_aidx (v : Z) (m : ameta) : ameta :=
mkAMeta (am_prev m) (am_next m) (am_mem m) (am_avail m) (am_freed m) (am_last m) (am_sc m) (am_maplen m) v (am_slots m).
Definition am_set_slots (v : list slotst) (m : ameta) : ameta :=
mkAMeta (am_prev m) (am_next m) (am_mem m) (am_avail m) (am_freed m) (am_last m) (am_sc m) (am_maplen m) (am_aidx m) v.
Definition links_of (x : mslot) : option sptr * option sptr :=
match x with
| MFree pr nx => (pr, nx)
| MRaw => (None, None)
| MUsed am => (am_prev am, am_next am)
end.
Definition with_links (x : mslot) (pr nx : option sptr) : mslot :=
match x with
| MFree _ _ => MFree pr nx
| MRaw => MFree pr nx
| MUsed am => MUsed (am_set_links pr nx am)
end.
Definition get_links (p : sptr) : M (option sptr * option sptr) :=
s <- get ;;
match mlookup (st_metas s) p with
| Some x => ret (links_of x)
| None => fail (FModel 2)
end.
Definition set_links (p : sptr) (pr nx : option sptr) : M unit :=
s <- get ;;
match mlookup (st_metas s) p with
| Some x => setslot p (with_links x pr nx)
| None => fail (FModel 3)
end.
Definition set_prev (p : sptr) (pr : option sptr) : M unit :=
l <- get_links p ;; set_links p pr (snd l).
Definition set_next (p : sptr) (nx : option sptr) : M unit :=
l <- get_links p ;; set_links p (fst l) nx.
Inductive headloc := HActive (sc : Z) | HFreeMeta.
Definition get_head (h : headloc) : M (option sptr) :=
s <- get ;;
match h with
| HActive sc => ret (nth (Z.to_nat sc) (st_active s) None)
| HFreeMeta => ret (st_free_meta_head s)
end.
Definition set_head (h : headloc) (v : option sptr) : M unit :=
match h with
| HActive sc => modify (fun s => set_active (lupd (st_active s) (Z.to_nat sc) v) s)
| HFreeMeta => modify (set_free_meta_head v)
end.
Definition queue (h : headloc) (m : sptr) : M unit :=
l <- get_links m ;;
massert (osptr_eqb (fst l) None && osptr_eqb (snd l) None) 1 ;;
hd <- get_head h ;;
match hd with
| Some head =>
lh <- get_links head ;;
match fst lh with
| None => fail (FModel 4)
| Some hprev =>
set_links m (Some hprev) (Some head) ;;
set_next hprev (Some m) ;;
set_prev head (Some m)
end
| None =>
set_links m (Some m) (Some m) ;;
set_head h (Some m)
end.
Definition dequeue (h : headloc) (m : sptr) : M unit :=
l <- get_links m ;;
(if osptr_eqb (snd l) (Some m) then set_head h None
else
match fst l, snd l with
| Some pr, Some nx =>
set_next pr (Some nx) ;;
set_prev nx (Some pr) ;;
hd <- get_head h ;;
if osptr_eqb hd (Some m) then set_head h (Some nx) else ret tt
| _, _ => fail (FModel 5)
end) ;;
set_links m None None.
Definition dequeue_head (h : headloc) : M (option sptr) :=
hd <- get_head h ;;
match hd with
| Some m => dequeue h m ;; ret (Some m)
| None => ret None
end.
Definition free_meta (m : sptr) : M unit :=
setslot m (MFree None None) ;; queue HFreeMeta m.
Definition usage_of (s : astate) (sc : Z) : Z := znth sc (st_usage s).
Definition set_usage_of (sc : Z) (v : Z) : M unit :=
modify (fun s => set_usage (zset sc v (st_usage s)) s).
Definition bounce_idx (sc : Z) : option Z :=
if (7 <=? sc) && (sc <? 39) then Some (sc - 7) else None.
Definition step_seq : M unit :=
modify (fun s =>
if st_seq s =? 255 then set_seq 1 (set_unmap_seq (repeat 0 32) s)
else set_seq (st_seq s + 1) s).
Definition record_seq (sc : Z) : M unit :=
match bounce_idx sc with
| Some k => modify (fun s => set_unmap_seq (zset k (st_seq s) (st_unmap_seq s)) s)
| None => ret tt
end.
Definition account_bounce (sc : Z) : M unit :=
match bounce_idx sc with
| Some k =>
modify (fun s =>
let useq := znth k (st_unmap_seq s) in
let b := znth k (st_bounces s) in
if negb (useq =? 0) && (st_seq s - useq <? 10)
then set_bounces (zset k (if b + 1 <? 100 then b + 1 else 150) (st_bounces s)) s
else s)
| None => ret tt
end.
Definition decay_bounces (sc : Z) : M unit :=
match bounce_idx sc with
| Some k =>
modify (fun s =>
let b := znth k (st_bounces s) in
if b =? 0 then s else set_bounces (zset k (b - 1) (st_bounces s)) s)
| None => ret tt
end.
Definition is_bouncing (s : astate) (sc : Z) : bool :=
match bounce_idx sc with
| Some k => 100 <=? znth k (st_bounces s)
| None => false
end.
Definition new_region (k : rkind) (len : Z) : M nat :=
s <- get ;;
let r := length (st_regions s) in
put (set_regions (st_regions s ++ [mkRegion k len [] true]) s) ;;
ret r.
Definition upd_region (r : nat) (f : region -> region) : M unit :=
modify (fun s =>
set_regions (lupd (st_regions s) r (f (nth r (st_regions s) (mkRegion RkMap 0 [] false)))) s).
Definition area_from_brk : M bool :=
s <- get ;;
if (st_avail_meta_area_count s =? 0) &&
match st_brk s with BrkDead => false | _ => true end
then
match st_brk s with
| BrkNever =>
_ <- ask KBrkQuery ;;
ok <- ask (KBrkGrow 2) ;;
if ok then
r <- new_region RkBrk (2 * PGSZ) ;;
modify (fun s => set_avail_meta_area_count 1
(set_avail_meta_areas (SP r PGSZ)
(set_brk (BrkCur r 2) s))) ;;
_ <- ask KGuard ;;
ret false
else modify (set_brk BrkDead) ;; ret true
| BrkCur r pages =>
ok <- ask (KBrkGrow 1) ;;
if ok then
upd_region r (fun rg => mkRegion RkBrk (rg_len rg + PGSZ) [] true) ;;
modify (fun s => set_avail_meta_area_count 1
(set_avail_meta_areas (SP r (PGSZ * pages))
(set_brk (BrkCur r (pages + 1)) s))) ;;
ret false
else modify (set_brk BrkDead) ;; ret true
| BrkDead => ret true
end
else ret true.
Definition area_from_mmap : M bool :=
s <- get ;;
if st_avail_meta_area_count s =? 0 then
let n := Z.shiftl 2 (st_meta_alloc_shift s) in
ok <- ask (KMmapNone (n * PGSZ)) ;;
if ok then
r <- new_region RkMetaRes (n * PGSZ) ;;
modify (fun s => set_meta_alloc_shift (st_meta_alloc_shift s + 1)
(set_avail_meta_area_count (n - 1)
(set_avail_meta_areas (SP r PGSZ) s))) ;;
ret true
else ret false
else ret true.
Definition open_area (need_unprotect : bool) : M bool :=
s <- get ;;
let p := st_avail_meta_areas s in
prot_ok <- (if need_unprotect then ask (KMprotect p) else ret true) ;;
if negb prot_ok then ret false
else
(if need_unprotect
then upd_region (prid p) (fun rg => mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [poff p]) (rg_live rg))
else ret tt) ;;
modify (fun s =>
set_avail_meta_area_count (st_avail_meta_area_count s - 1)
(set_avail_meta_areas (padd p 4096)
(set_area_tail (Some p)
(set_area_head (match st_area_head s with None => Some p | h => h end)
(set_areas (st_areas s ++ [p])
(set_avail_meta_count METAS_PER_AREA
(set_avail_meta (padd p AREA_HDR) s))))))) ;;
ret true.
Definition alloc_meta : M (option sptr) :=
modify (set_init_done true) ;;
fm <- dequeue_head HFreeMeta ;;
match fm with
| Some m => ret (Some m)
| None =>
s <- get ;;
ok <- (if 0 <? st_avail_meta_count s then ret true
else nu <- area_from_brk ;;
rs <- area_from_mmap ;;
if rs then open_area nu else ret false) ;;
if negb ok then ret None
else
s <- get ;;
let m := st_avail_meta s in
put (set_avail_meta (padd m META_SIZE)
(set_avail_meta_count (st_avail_meta_count s - 1) s)) ;;
setslot m MRaw ;;
ret (Some m)
end.
Definition stride_of (am : ameta) : Z :=
if (am_last am =? 0) && negb (am_maplen am =? 0)
then am_maplen am * 4096 - UNIT
else class_size (am_sc am).
Definition nth_slot (am : ameta) (i : Z) : slotst := nth (Z.to_nat i) (am_slots am) slot_junk.
Definition upd_slot (am : ameta) (i : Z) (x : slotst) : ameta :=
am_set_slots (lupd (am_slots am) (Z.to_nat i) x) am.
Definition slot_start (am : ameta) (i : Z) : sptr := padd (am_mem am) (UNIT + stride_of am * i).
Definition slot_user (am : ameta) (i : Z) : option sptr :=
match ss_fr (nth_slot am i) with
| Some fr => Some (padd (slot_start am i) (UNIT * fr_off fr))
| None => None
end.
Definition activate_group (m : sptr) : M Z :=
am <- getm m ;;
massert (am_avail am =? 0) 2 ;;
let act := ones (am_aidx am) in
let mask := am_freed am in
setm m (am_set_avail (Z.land mask act) (am_set_freed (Z.ldiff mask act) am)) ;;
ret (Z.land mask act).
Fixpoint span_loop (fuel : nat) (cnt span size : Z) : Z :=
match fuel with
| O => cnt
| S f => if Z.lxor span (span + size - 1) <? 4096
then span_loop f (cnt + 1) (span + size) size
else cnt
end.
Definition try_avail (sc : Z) : M Z :=
hd <- get_head (HActive sc) ;;
match hd with
| None => ret 0
| Some m0 =>
am0 <- getm m0 ;;
if negb (am_avail am0 =? 0) then
let first := lowbit (am_avail am0) in
setm m0 (am_set_avail (am_avail am0 - first) am0) ;; ret first
else
om1 <- (if am_freed am0 =? 0
then dequeue (HActive sc) m0 ;; get_head (HActive sc)
else set_head (HActive sc) (am_next am0) ;; ret (am_next am0)) ;;
match om1 with
| None => ret 0
| Some m1 =>
am1 <- getm m1 ;;
m2 <- (if am_freed am1 =? ones (am_last am1)
then match am_next am1 with
| Some nx => set_head (HActive sc) (Some nx) ;; ret nx
| None => fail (FModel 6)
end
else ret m1) ;;
am2 <- getm m2 ;;
let mask := am_freed am2 in
m3 <- (if Z.land mask (ones (am_aidx am2)) =? 0 then
if negb (osptr_eqb (am_next am2) (Some m2)) then
match am_next am2 with
| Some nx => set_head (HActive sc) (Some nx) ;; ret nx
| None => fail (FModel 7)
end
else
let size := class_size (am_sc am2) in
let cnt0 := am_aidx am2 + 2 in
let cnt1 := span_loop 300%nat cnt0 (UNIT + size * cnt0) size in
let cnt := if am_last am2 + 1 <? cnt1 then am_last am2 + 1 else cnt1 in
setm m2 (am_set_aidx (cnt - 1) am2) ;; ret m2
else ret m2) ;;
mask <- activate_group m3 ;;
massert (negb (mask =? 0)) 3 ;;
am3 <- getm m3 ;;
decay_bounces (am_sc am3) ;;
let first := lowbit mask in
am3 <- getm m3 ;;
setm m3 (am_set_avail (mask - first) am3) ;;
ret first
end
end.
Definition enframe (g : sptr) (idx n ctr : Z) (k : fkind) : M sptr :=
am <- getm g ;;
mcheck ((0 <=? idx) && (idx <=? am_last am)) 12 ;;
let stride := stride_of am in
let slack := (stride - IB - n) / UNIT in
let sl := nth_slot am idx in
off0 <- (if slack =? 0 then ret 0
else match ss_hdr sl with
| Some (h3, h16) => ret (Z.land (if h3 =? 0 then ctr else h16 + 1) 255)
| None => z <- askz (KJunk (Z.land ctr 255)) ;; ret (z mod 256)
end) ;;
let off :=
if slack <? off0 then
let m1 := Z.lor slack (Z.shiftr slack 1) in
let m2 := Z.lor m1 (Z.shiftr m1 2) in
let m3 := Z.lor m2 (Z.shiftr m2 4) in
let off1 := Z.land off0 m3 in
if slack <? off1 then off1 - (slack + 1) else off1
else off0 in
massert (off <=? slack) 4 ;;
let reserved := stride - IB - UNIT * off - n in
let rsv := if 5 <=? reserved then 5 else reserved in
let hdr := if off =? 0
then (match k with FUser => idx + rsv * 32 | FGroup => idx + 192 end, (stride * idx) / UNIT)
else (224, off) in
setm g (upd_slot am idx (mkSlot (Some hdr) (Some (mkFrame off n k)))) ;;
ret (padd (slot_start am idx) (UNIT * off)).
Definition small_cnt (sc usage : Z) : Z :=
let row := nth (Z.to_nat sc) small_cnt_tab [] in
if negb (usage <? 4 * znth 0 row) then znth 0 row
else if negb (usage <? 4 * znth 1 row) then znth 1 row
else znth 2 row.
Fixpoint halve_while_even (fuel : nat) (cnt usage : Z) : Z :=
match fuel with
| O => cnt
| S f => if (Z.even cnt) && (usage <? 4 * cnt) then halve_while_even f (cnt / 2) usage else cnt
end.
Fixpoint halve_while_big (fuel : nat) (cnt size : Z) : Z :=
match fuel with
| O => cnt
| S f => if 65536 * UNIT <=? size * cnt then halve_while_big f (cnt / 2) size else cnt
end.
Definition initial_cnt (sc usage : Z) : Z :=
let size := class_size sc in
let cnt :=
if sc <? 9 then small_cnt sc usage
else halve_while_big 8%nat (halve_while_even 8%nat (znth (Z.land sc 3) med_cnt_tab) usage) size in
if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.
Definition mmap_plan (s : astate) (sc req cnt0 usage0 : Z) : Z * Z :=
let size := class_size sc in
let nosmall := is_bouncing s sc in
let usage := if (Z.even sc) && (sc <? 32) then usage0 + usage_of s (sc + 1) else usage0 in
let cnt :=
if (usage <? 4 * cnt0) && negb nosmall then
if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt0) then 2
else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt0) then 3
else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt0) then 3
else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt0) then 5
else cnt0
else cnt0 in
let needed := page_round (size * cnt + UNIT) in
if negb nosmall && (cnt <=? 7) then
let rq := page_round (req + IB + UNIT) in
if (rq <? size + UNIT) || ((4 * PGSZ <=? rq) && (usage <? 2 * cnt))
then (1, rq) else (cnt, needed)
else (cnt, needed).
Definition install_group (m : sptr) (sc cnt aidx maplen : Z) (mem : sptr) (sl : slotst) : M unit :=
s <- get ;;
set_usage_of sc (usage_of s sc + cnt) ;;
let avail := ones aidx in
let freed := ones (cnt - 1) - avail in
setm m (mkAMeta None None mem (avail - 1) freed (cnt - 1) sc maplen aidx
(repeat sl (Z.to_nat cnt))) ;;
queue (HActive sc) m.
Fixpoint alloc_slot (fuel : nat) (sc req : Z) : M Z :=
match fuel with
| O => fail FFuel
| S fuel' =>
first <- try_avail sc ;;
if negb (first =? 0) then ret (ctz32 first)
else
og <- alloc_group fuel' sc req ;;
match og with
| None => ret (-1)
| Some g => ret 0
end
end
with alloc_group (fuel : nat) (sc req : Z) : M (option sptr) :=
match fuel with
| O => fail FFuel
| S fuel' =>
om <- alloc_meta ;;
match om with
| None => ret None
| Some m =>
s <- get ;;
let size := class_size sc in
let usage := usage_of s sc in
let cnt0 := initial_cnt sc usage in
if PGSZ / 2 <? size * cnt0 + UNIT then
let plan := mmap_plan s sc req cnt0 usage in
account_bounce sc ;;
step_seq ;;
ok <- ask (KMmapRW (snd plan)) ;;
if negb ok then free_meta m ;; ret None
else
r <- new_region RkMap (page_round (snd plan)) ;;
s <- get ;;
put (set_mmap_counter (Z.land (st_mmap_counter s + 1) (2^32 - 1)) s) ;;
let cnt := fst plan in
let a0 := (4096 - UNIT) / size - 1 in
let a1 := if cnt - 1 <? a0 then cnt - 1 else a0 in
let aidx := if a1 <? 0 then 0 else a1 in
install_group m sc cnt aidx (snd plan / 4096) (SP r 0) slot_zero ;;
ret (Some m)
else
let total := UNIT + cnt0 * size - IB in
let j := size_to_class total in
idx <- alloc_slot fuel' j total ;;
if idx <? 0 then free_meta m ;; ret None
else
hj <- get_head (HActive j) ;;
match hj with
| None => fail (FModel 8)
| Some g =>
amg <- getm g ;;
mcheck (stride_of amg =? class_size j) 11 ;;
s <- get ;;
p <- enframe g idx (class_size j - IB) (st_mmap_counter s) FGroup ;;
install_group m sc cnt0 (cnt0 - 1) 0 p slot_junk ;;
ret (Some m)
end
end
end.
Definition NEST_FUEL : nat := 64%nat.
Definition malloc (n : Z) : M (option sptr) :=
if size_overflows n then ret None
else if MMAP_THRESHOLD <=? n then
let needed := n + IB + UNIT in
ok <- ask (KMmapRW needed) ;;
if negb ok then ret None
else
r <- new_region RkMap (page_round needed) ;;
step_seq ;;
og <- alloc_meta ;;
match og with
| None => _ <- ask (KMunmap r needed) ;;
upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) ;;
ret None
| Some g =>
setm g (mkAMeta None None (SP r 0) 0 0 0 63 (page_round needed / 4096) 0 [slot_zero]) ;;
s <- get ;;
let ctr := Z.land (st_mmap_counter s + 1) (2^32 - 1) in
put (set_mmap_counter ctr s) ;;
p <- enframe g 0 n ctr FUser ;;
ret (Some p)
end
else
s <- get ;;
let sc0 := size_to_class n in
let g0 := nth (Z.to_nat sc0) (st_active s) None in
let sc :=
if (osptr_eqb g0 None) && (4 <=? sc0) && (sc0 <? 32) && negb (sc0 =? 6)
&& Z.even sc0 && (usage_of s sc0 =? 0)
then
let u := usage_of s (sc0 + 1) in
let head_full :=
match nth (Z.to_nat (sc0 + 1)) (st_active s) None with
| None => true
| Some h => match mlookup (st_metas s) h with
| Some (MUsed am) => (am_avail am =? 0) && (am_freed am =? 0)
| _ => true
end
end in
let u := if head_full then u + 3 else u in
if u <=? 12 then sc0 + 1 else sc0
else sc0 in
let g := nth (Z.to_nat sc) (st_active s) None in
r <- (match g with
| None => ret None
| Some gm =>
am <- getm gm ;;
if am_avail am =? 0 then ret None
else let first := lowbit (am_avail am) in
setm gm (am_set_avail (am_avail am - first) am) ;;
ret (Some (gm, ctz32 first))
end) ;;
gi <- (match r with
| Some gi => ret (Some gi)
| None =>
idx <- alloc_slot NEST_FUEL sc n ;;
if idx <? 0 then ret None
else hd <- get_head (HActive sc) ;;
match hd with
| Some gm => ret (Some (gm, idx))
| None => fail (FModel 9)
end
end) ;;
match gi with
| None => ret None
| Some (gm, idx) =>
s <- get ;;
p <- enframe gm idx n (st_mmap_counter s) FUser ;;
ret (Some p)
end.
Fixpoint find_in_slots (sl : list slotst) (base : sptr) (stride : Z) (i : Z) (p : sptr)
: option Z :=
match sl with
| [] => None
| x :: t =>
match ss_fr x with
| Some fr => if sptr_eqb (padd base (stride * i + UNIT * fr_off fr)) p then Some i
else find_in_slots t base stride (i + 1) p
| None => find_in_slots t base stride (i + 1) p
end
end.
Fixpoint find_frame_in (l : list (sptr * mslot)) (p : sptr) : option (sptr * Z) :=
match l with
| [] => None
| (m, MUsed am) :: t =>
match find_in_slots (am_slots am) (padd (am_mem am) UNIT) (stride_of am) 0 p with
| Some i => Some (m, i)
| None => find_frame_in t p
end
| _ :: t => find_frame_in t p
end.
Definition find_frame (p : sptr) : M (sptr * Z) :=
s <- get ;;
match find_frame_in (st_metas s) p with
| Some x => ret x
| None => fail (FAssert 0)
end.
Definition okay_to_free (s : astate) (g : sptr) (am : ameta) : bool :=
let sc := am_sc am in
if (48 <=? sc) || (stride_of am <? class_size sc) then true
else if am_maplen am =? 0 then true
else if negb (osptr_eqb (am_next am) (Some g)) then true
else if negb (is_bouncing s sc) then true
else let cnt := am_last am + 1 in
(9 * cnt <=? usage_of s sc) && (cnt <? 20).
Definition forget_frame (g : sptr) (i : Z) : M unit :=
am <- getm g ;;
let sl := nth_slot am i in
setm g (upd_slot am i (mkSlot (ss_hdr sl) None)).
Definition slot_is_group (sl : slotst) : bool :=
match ss_fr sl with
| Some fr => match fr_kind fr with FGroup => true | FUser => false end
| None => false
end.
Fixpoint nontrivial_free (fuel : nat) (g : sptr) (i : Z) : M (option (nat * Z)) :=
match fuel with
| O => fail FFuel
| S fuel' =>
am <- getm g ;;
s <- get ;;
let self := bit i in
let sc := am_sc am in
let mask := Z.lor (am_freed am) (am_avail am) in
if (mask + self =? ones (am_last am)) && okay_to_free s g am then
(match am_next am with
| Some _ =>
massert (sc <? 48) 5 ;;
hd <- get_head (HActive sc) ;;
let activate_new := osptr_eqb hd (Some g) in
dequeue (HActive sc) g ;;
hd' <- get_head (HActive sc) ;;
match activate_new, hd' with
| true, Some h => _ <- activate_group h ;; ret tt
| _, _ => ret tt
end
| None => ret tt
end) ;;
am <- getm g ;;
(if sc <? 48 then set_usage_of sc (usage_of s sc - (am_last am + 1)) else ret tt) ;;
mi <- (if negb (am_maplen am =? 0) then
step_seq ;; record_seq sc ;;
ret (Some (prid (am_mem am), am_maplen am * 4096))
else
pf <- find_frame (am_mem am) ;;
amp <- getm (fst pf) ;;
mcheck (slot_is_group (nth_slot amp (snd pf))) 10 ;;
forget_frame (fst pf) (snd pf) ;;
nontrivial_free fuel' (fst pf) (snd pf)) ;;
free_meta g ;;
ret mi
else
(if mask =? 0 then
massert (sc <? 48) 6 ;;
hd <- get_head (HActive sc) ;;
if osptr_eqb hd (Some g) then ret tt else queue (HActive sc) g
else ret tt) ;;
am <- getm g ;;
setm g (am_set_freed (Z.lor (am_freed am) self) am) ;;
ret None
end.
Definition release_slot (g : sptr) (i : Z) : M unit :=
am <- getm g ;;
let sl := nth_slot am i in
let sl' := match ss_fr sl with
| Some fr => if fr_off fr =? 0 then mkSlot (Some (255, 0)) None
else mkSlot (ss_hdr sl) None
| None => sl
end in
setm g (upd_slot am i sl').
Definition free (p : option sptr) : M unit :=
match p with
| None => ret tt
| Some p =>
gi <- find_frame p ;;
let g := fst gi in let i := snd gi in
am <- getm g ;;
let self := bit i in
let all := ones (am_last am) in
release_slot g i ;;
let freed := am_freed am in
let mask := Z.lor freed (am_avail am) in
massert (Z.land mask self =? 0) 7 ;;
if negb (freed =? 0) && negb (mask + self =? all) then
am <- getm g ;; setm g (am_set_freed (freed + self) am)
else
mi <- nontrivial_free NEST_FUEL g i ;;
match mi with
| Some (r, len) =>
_ <- ask (KMunmap r len) ;;
upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false)
| None => ret tt
end
end.
Definition resize_slot (stride i : Z) (sl : slotst) (off n : Z) : slotst :=
let reserved := stride - IB - UNIT * off - n in
let rsv := if 5 <=? reserved then 5 else reserved in
mkSlot (if off =? 0 then Some (i + rsv * 32, (stride * i) / UNIT) else ss_hdr sl)
(Some (mkFrame off n FUser)).
Definition remap_am (am : ameta) (r' : nat) (maplen' : Z) (i off n : Z) : ameta :=
let stride' := maplen' * 4096 - UNIT in
mkAMeta (am_prev am) (am_next am) (SP r' 0) (am_avail am) (am_freed am) (am_last am) (am_sc am)
maplen' (am_aidx am)
(lupd (am_slots am) (Z.to_nat i) (resize_slot stride' i (nth_slot am i) off n)).
Definition realloc_move (p : sptr) (n : Z) : M (option sptr) :=
q <- malloc n ;;
match q with
| None => ret None
| Some q => free (Some p) ;; ret (Some q)
end.
Definition realloc (op : option sptr) (n : Z) : M (option sptr) :=
match op with
| None => malloc n
| Some p =>
if size_overflows n then ret None
else
gi <- find_frame p ;;
let g := fst gi in let i := snd gi in
am <- getm g ;;
match ss_fr (nth_slot am i) with
| None => fail (FModel 13)
| Some fr =>
let stride := stride_of am in
let off := fr_off fr in
let avail := stride - IB - UNIT * off in
if (n <=? avail) && (n <? MMAP_THRESHOLD) && (am_sc am <=? size_to_class n + 1) then
setm g (upd_slot am i (resize_slot stride i (nth_slot am i) off n)) ;;
ret (Some p)
else if (48 <=? am_sc am) && (MMAP_THRESHOLD <=? n) then
massert (am_sc am =? 63) 8 ;;
let needed := page_round (n + UNIT * off + UNIT + IB) in
let r := prid (am_mem am) in
let old_len := am_maplen am * 4096 in
if old_len =? needed then
setm g (upd_slot am i (resize_slot stride i (nth_slot am i) off n)) ;;
ret (Some p)
else
ok <- ask (KMremap r old_len needed) ;;
if ok then
r' <- new_region RkMap needed ;;
setm g (remap_am am r' (needed / 4096) i off n) ;;
upd_region r (fun rg => mkRegion RkMap (rg_len rg) [] false) ;;
ret (Some (padd (slot_start (remap_am am r' (needed / 4096) i off n) i) (UNIT * off)))
else realloc_move p n
else realloc_move p n
end
end.
Inductive outcome (A : Type) := ODone (a : A) | OFailed (f : failure) | OStarved.
Arguments ODone {A}. Arguments OFailed {A}. Arguments OStarved {A}.
Definition default_answer (q : kreq) : Z :=
match q with KJunk pristine => pristine | _ => 1 end.
Fixpoint irun {S A} (fuel : nat) (t : itree S A) (ans : list (option Z)) (tr : list (kreq * Z))
: outcome A * list (kreq * Z) * list (option Z) :=
match fuel with
| O => (OStarved, rev tr, ans)
| S f =>
match t with
| IRet a => (ODone a, rev tr, ans)
| IFail e => (OFailed e, rev tr, ans)
| IAsk q _ k => let z := match hd None ans with Some z => z | None => default_answer q end in
irun f (k z) (tl ans) ((q, z) :: tr)
end
end.
Inductive op := Malloc (n : Z) | Free (k : nat)
| Realloc (k : nat) (n : Z)  .
Record srun := mkRun {
sr_state : astate;
sr_ptrs : list (option sptr);
sr_trace : list (kreq * Z);
sr_ans : list (option Z);
sr_err : option failure
}.
Definition run_op (r : srun) (o : op) : srun :=
match sr_err r with
| Some _ => r
| None =>
match o with
| Malloc n =>
match irun 1000%nat (malloc n (sr_state r)) (sr_ans r) [] with
| (ODone (p, s'), tr, ans) => mkRun s' (sr_ptrs r ++ [p]) (sr_trace r ++ tr) ans None
| (OFailed e, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some e)
| (OStarved, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some FFuel)
end
| Free k =>
match irun 1000%nat (free (nth k (sr_ptrs r) None) (sr_state r)) (sr_ans r) [] with
| (ODone (_, s'), tr, ans) => mkRun s' (sr_ptrs r) (sr_trace r ++ tr) ans None
| (OFailed e, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some e)
| (OStarved, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some FFuel)
end
| Realloc k n =>
match irun 1000%nat (realloc (nth k (sr_ptrs r) None) n (sr_state r)) (sr_ans r) [] with
| (ODone (p, s'), tr, ans) => mkRun s' (sr_ptrs r ++ [p]) (sr_trace r ++ tr) ans None
| (OFailed e, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some e)
| (OStarved, tr, ans) => mkRun (sr_state r) (sr_ptrs r) (sr_trace r ++ tr) ans (Some FFuel)
end
end
end.
Definition run_script (ans : list (option Z)) (ops : list op) : srun :=
fold_left run_op ops (mkRun init_state [] [] ans None).
Definition trace_of (ans : list (option Z)) (ops : list op) : list (kreq * Z) :=
sr_trace (run_script ans ops).
Definition refuse : option Z := Some 0.
Definition grant : option Z := None.
Example size_to_class_examples :
map size_to_class [4096; 6048; 65632; 32864; 2262; 1120; 131051; 100; 24]
= [28; 30; 44; 40; 24; 20; 47; 6; 1].
Proof. vm_compute. reflexivity. Qed.
Definition vec1_prefix : list op :=
[Malloc 4096; Malloc 6048; Malloc 65632; Malloc 65632; Malloc 65632; Malloc 65632;
Free 5; Free 4; Free 3; Free 2; Free 1;
Malloc 6048; Malloc 32864; Malloc 32864; Malloc 131168; Malloc 131168; Malloc 2262;
Free 10; Free 9; Free 8; Free 7; Free 6].
Example vec1_trace :
trace_of [] vec1_prefix =
[(KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1);
(KMmapRW 16384, 1); (KMmapRW 8192, 1);
(KMmapRW 69632, 1); (KMmapRW 69632, 1); (KMmapRW 69632, 1); (KMmapRW 69632, 1);
(KMunmap 6 69632, 1); (KMunmap 5 69632, 1); (KMunmap 4 69632, 1); (KMunmap 3 69632, 1);
(KMunmap 2 8192, 1);
(KMmapRW 8192, 1); (KMmapRW 36864, 1); (KMmapRW 36864, 1);
(KMmapRW 131188, 1); (KMmapRW 131188, 1); (KMmapRW 8192, 1);
(KMunmap 11 135168, 1); (KMunmap 10 135168, 1); (KMunmap 9 36864, 1);
(KMunmap 8 36864, 1); (KMunmap 7 8192, 1)].
Proof. vm_compute. reflexivity. Qed.
Definition describe (s : astate) (p : option sptr) : option (Z * Z * Z * Z) :=
match p with
| None => None
| Some p =>
match find_frame_in (st_metas s) p with
| None => None
| Some (m, i) =>
match mlookup (st_metas s) m with
| Some (MUsed am) =>
match ss_fr (nth_slot am i) with
| Some fr =>
let stride := stride_of am in
let reserved := stride - IB - UNIT * fr_off fr - fr_n fr in
Some (i, stride * i / UNIT + fr_off fr, (poff p) mod 4096,
(if 5 <=? reserved then 5 else reserved))
| None => None
end
| _ => None
end
end
end.
Fixpoint run_descr (r : srun) (ops : list op) (acc : list (option (Z*Z*Z*Z)))
: list (option (Z*Z*Z*Z)) :=
match ops with
| [] => rev acc
| o :: t => let r' := run_op r o in
match o with
| Malloc _ | Realloc _ _ => run_descr r' t (describe (sr_state r') (last (sr_ptrs r') None) :: acc)
| Free _ => run_descr r' t acc
end
end.
Definition hdr_script : list op :=
[Malloc 4096; Malloc 6048; Malloc 65632; Malloc 65632; Malloc 65632; Malloc 65632;
Free 5; Free 4; Free 3; Free 2; Free 1;
Malloc 6048; Malloc 32864; Malloc 32864; Malloc 131168; Malloc 131168; Malloc 2262;
Free 10; Free 9; Free 8; Free 7; Free 6;
Malloc 7256; Malloc 8700; Malloc 16480; Free 14; Free 12; Free 13; Free 11;
Malloc 100; Malloc 100; Malloc 100; Free 19; Free 20; Malloc 100; Malloc 100;
Malloc 24; Malloc 24; Free 24; Malloc 24; Malloc 5000; Free 27; Malloc 5000;
Malloc 200000; Free 29; Malloc 200000].
Example hdr_script_matches_musl :
run_descr (mkRun init_state [] [] [] None) hdr_script [] =
map Some
[(0,1,32,5); (0,2,48,5); (0,3,64,5); (0,4,80,5); (0,5,96,5); (0,6,112,5);
(0,7,128,5); (0,8,144,5); (0,9,160,5); (0,10,176,5); (0,11,192,5); (0,12,208,5);
(0,13,224,5); (0,14,240,5); (0,15,256,5);
(0,0,64,5); (1,7,176,5); (2,14,288,5); (3,21,400,5); (0,0,560,5);
(0,0,1072,4); (1,2,1104,4); (2,4,1136,4); (1,356,1616,5); (2,696,2960,5);
(0,17,288,5); (0,18,304,5)].
Proof. vm_compute. reflexivity. Qed.
Example brk_refused_trace :
trace_of [grant; refuse] [Malloc 4096; Malloc 100; Free 0; Free 1] =
[(KBrkQuery, 1); (KBrkGrow 2, 0); (KMmapNone 8192, 1);
(KMprotect (SP 0 4096), 1); (KMmapRW 16384, 1); (KMmapRW 4096, 1);
(KMunmap 1 16384, 1); (KMunmap 2 4096, 1)].
Proof. vm_compute. reflexivity. Qed.
Example group_mmap_refused :
sr_ptrs (run_script [grant; grant; grant; refuse] [Malloc 4096; Malloc 4096]) = [None; Some (SP 1 32)]
/\ trace_of [grant; grant; grant; refuse] [Malloc 4096; Malloc 4096] =
[(KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1); (KMmapRW 16384, 0); (KMmapRW 16384, 1)].
Proof. vm_compute. split; reflexivity. Qed.
Example direct_map_meta_refused :
trace_of [grant; grant; refuse; refuse] [Malloc 200000] =
[(KMmapRW 200020, 1); (KBrkQuery, 1); (KBrkGrow 2, 0); (KMmapNone 8192, 0);
(KMunmap 0 200020, 1)]
/\ sr_ptrs (run_script [grant; grant; refuse; refuse] [Malloc 200000]) = [None].
Proof. vm_compute. split; reflexivity. Qed.
Example realloc_mremap_granted :
trace_of [] [Malloc 200000; Realloc 0 400000] =
[(KMmapRW 200020, 1); (KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1); (KMremap 0 200704 401408, 1)]
/\ sr_ptrs (run_script [] [Malloc 200000; Realloc 0 400000]) = [Some (SP 0 32); Some (SP 2 32)]
/\ map rg_live (st_regions (sr_state (run_script [] [Malloc 200000; Realloc 0 400000]))) = [false; true; true].
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.
Example realloc_mremap_refused :
trace_of [grant; grant; grant; grant; refuse] [Malloc 200000; Realloc 0 400000; Free 1] =
[(KMmapRW 200020, 1); (KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1); (KMremap 0 200704 401408, 0);
(KMmapRW 400020, 1); (KMunmap 0 200704, 1); (KMunmap 2 401408, 1)]
/\ sr_ptrs (run_script [grant; grant; grant; grant; refuse] [Malloc 200000; Realloc 0 400000]) = [Some (SP 0 32); Some (SP 2 48)].
Proof. vm_compute. split; reflexivity. Qed.
Example realloc_same_pages_no_request :
trace_of [] [Malloc 200000; Realloc 0 200100] =
[(KMmapRW 200020, 1); (KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1)]
/\ sr_ptrs (run_script [] [Malloc 200000; Realloc 0 200100]) = [Some (SP 0 32); Some (SP 0 32)]
/\ describe (sr_state (run_script [] [Malloc 200000; Realloc 0 200100])) (Some (SP 0 32)) = Some (0, 1, 32, 5).
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.
Example realloc_small_to_big :
trace_of [] [Malloc 100; Realloc 0 200000] =
[(KBrkQuery, 1); (KBrkGrow 2, 1); (KGuard, 1); (KMmapRW 4096, 1); (KMmapRW 200020, 1); (KMunmap 1 4096, 1)].
Proof. vm_compute. reflexivity. Qed.
