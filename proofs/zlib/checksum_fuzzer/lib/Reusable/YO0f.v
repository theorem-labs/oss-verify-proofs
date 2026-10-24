(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition zseq (lo : Z) (n : Z) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat n)).
Fixpoint nodupb {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
match l with
| [] => true
| x :: t => negb (existsb (eqb x) t) && nodupb eqb t
end.
Definition memb (p : sptr) (l : list sptr) : bool := existsb (sptr_eqb p) l.
Definition countb {A : Type} (f : A -> bool) (l : list A) : Z := Z.of_nat (length (filter f l)).
Definition implb (a b : bool) : bool := negb a || b.
Local Infix "==>" := implb (at level 55, right associativity).
Definition olinks_noneb (l : option sptr * option sptr) : bool :=
osptr_eqb (fst l) None && osptr_eqb (snd l) None.
Definition used_metas (s : astate) : list (sptr * ameta) :=
flat_map (fun e : sptr * mslot => match e with (p, MUsed am) => [(p, am)] | _ => [] end) (st_metas s).
Definition free_meta_keys (s : astate) : list sptr :=
flat_map (fun e : sptr * mslot => match e with (p, MFree _ _) => [p] | _ => [] end) (st_metas s).
Definition raw_meta_keys (s : astate) : list sptr :=
flat_map (fun e : sptr * mslot => match e with (p, MRaw) => [p] | _ => [] end) (st_metas s).
Definition lookup_used (s : astate) (p : sptr) : option ameta :=
match mlookup (st_metas s) p with Some (MUsed am) => Some am | _ => None end.
Definition region_of (s : astate) (r : nat) : option region := nth_error (st_regions s) r.
Definition allocated (am : ameta) (i : Z) : bool :=
negb (Z.testbit (Z.lor (am_avail am) (am_freed am)) i).
Definition rsv_code (am : ameta) (fr : frame) : Z :=
let reserved := stride_of am - IB - UNIT * fr_off fr - fr_n fr in
if 5 <=? reserved then 5 else reserved.
Definition hdr_byte3 (am : ameta) (i : Z) (fr : frame) : Z :=
match fr_kind fr with
| FUser => i + 32 * rsv_code am fr
| FGroup => i + 192
end.
Definition hdr_off16 (am : ameta) (i : Z) (fr : frame) : Z :=
(stride_of am * i) / UNIT + fr_off fr.
Fixpoint chain (lk : sptr -> option (option sptr * option sptr)) (prev : sptr)
(l : list sptr) (first : sptr) : Prop :=
match l with
| [] => True
| x :: rest => lk x = Some (Some prev, Some (hd first rest)) /\ chain lk x rest first
end.
Definition cycle_ok (lk : sptr -> option (option sptr * option sptr)) (ms : list sptr) : Prop :=
NoDup ms /\ match ms with [] => True | m0 :: _ => chain lk (last ms m0) ms m0 end.
Definition ring_ok (lk : sptr -> option (option sptr * option sptr)) (hd : option sptr)
(ms : list sptr) : Prop :=
cycle_ok lk ms /\ hd = hd_error ms.
Definition olinks_eqb (a b : option (option sptr * option sptr)) : bool :=
match a, b with
| Some (p1, n1), Some (p2, n2) => osptr_eqb p1 p2 && osptr_eqb n1 n2
| None, None => true
| _, _ => false
end.
Fixpoint chainb (lk : sptr -> option (option sptr * option sptr)) (prev : sptr)
(l : list sptr) (first : sptr) : bool :=
match l with
| [] => true
| x :: rest => olinks_eqb (lk x) (Some (Some prev, Some (hd first rest))) && chainb lk x rest first
end.
Definition ring_okb (lk : sptr -> option (option sptr * option sptr)) (hd : option sptr)
(ms : list sptr) : bool :=
nodupb sptr_eqb ms &&
match ms with
| [] => osptr_eqb hd None
| m0 :: _ => osptr_eqb hd (Some m0) && chainb lk (last ms m0) ms m0
end.
Fixpoint collect (lk : sptr -> option (option sptr * option sptr)) (fuel : nat)
(start cur : sptr) (acc : list sptr) : list sptr :=
match fuel with
| O => rev (cur :: acc)
| S f =>
match lk cur with
| Some (_, Some nx) => if sptr_eqb nx start then rev (cur :: acc) else collect lk f start nx (cur :: acc)
| _ => rev (cur :: acc)
end
end.
Definition ring_list (lk : sptr -> option (option sptr * option sptr)) (fuel : nat)
(hd : option sptr) : list sptr :=
match hd with
| None => []
| Some h => collect lk fuel h h []
end.
Definition ring_fuel (s : astate) : nat := S (length (st_metas s)).
Definition active_links (s : astate) (sc : Z) (p : sptr) : option (option sptr * option sptr) :=
match lookup_used s p with
| Some am => if am_sc am =? sc then Some (am_prev am, am_next am) else None
| None => None
end.
Definition freering_links (s : astate) (p : sptr) : option (option sptr * option sptr) :=
match mlookup (st_metas s) p with
| Some (MFree pr nx) => Some (pr, nx)
| _ => None
end.
Definition active_members (s : astate) (sc : Z) : list sptr :=
ring_list (active_links s sc) (ring_fuel s) (nth (Z.to_nat sc) (st_active s) None).
Definition free_members (s : astate) : list sptr :=
ring_list (freering_links s) (ring_fuel s) (st_free_meta_head s).
Definition wf_ctx (s : astate) : bool :=
(Z.of_nat (length (st_active s)) =? 48) &&
(Z.of_nat (length (st_usage s)) =? 48) &&
(Z.of_nat (length (st_unmap_seq s)) =? 32) &&
(Z.of_nat (length (st_bounces s)) =? 32) &&
forallb (fun u => 0 <=? u) (st_usage s) &&
forallb (fun u => (0 <=? u) && (u <=? 255)) (st_unmap_seq s) &&
forallb (fun u => (0 <=? u) && (u <=? 255)) (st_bounces s) &&
(0 <=? st_seq s) && (st_seq s <=? 255) &&
(0 <=? st_mmap_counter s) && (st_mmap_counter s <? 2 ^ 32) &&
(0 <=? st_meta_alloc_shift s) &&
(0 <=? st_avail_meta_count s) && (st_avail_meta_count s <=? METAS_PER_AREA) &&
(0 <=? st_avail_meta_area_count s) &&
(negb (st_init_done s) ==>
(match st_metas s with [] => true | _ => false end &&
match st_areas s with [] => true | _ => false end &&
match st_brk s with BrkNever => true | _ => false end &&
(st_avail_meta_area_count s =? 0))).
Definition area_index (s : astate) (a : sptr) : option nat :=
(fix go (l : list sptr) (k : nat) :=
match l with
| [] => None
| x :: t => if sptr_eqb x a then Some k else go t (S k)
end) (st_areas s) O.
Definition handed_out (s : astate) (j : nat) : Z :=
if (S j =? length (st_areas s))%nat then METAS_PER_AREA - st_avail_meta_count s else METAS_PER_AREA.
Definition meta_key_ok (s : astate) (p : sptr) : bool :=
match p with SP r o =>
existsb (fun a : sptr =>
match a with SP r' ao =>
Nat.eqb r r' &&
let d := o - ao - AREA_HDR in
(0 <=? d) && (d mod META_SIZE =? 0) &&
match area_index s a with
| Some j => d / META_SIZE <? handed_out s j
| None => false
end
end) (st_areas s)
end.
Definition wf_metas (s : astate) : bool :=
nodupb sptr_eqb (map fst (st_metas s)) &&
forallb (meta_key_ok s) (map fst (st_metas s)) &&
match raw_meta_keys s with [] => true | _ => false end &&
(let ms := free_members s in
ring_okb (freering_links s) (st_free_meta_head s) ms &&
(Z.of_nat (length ms) =? Z.of_nat (length (free_meta_keys s))) &&
forallb (fun p => memb p ms) (free_meta_keys s)) &&
match st_areas s with
| [] => st_avail_meta_count s =? 0
| _ => sptr_eqb (st_avail_meta s)
(padd (last (st_areas s) (SP 0 0))
(AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count s)))
end.
Definition parent_slots (s : astate) (mem : sptr) : list (sptr * ameta * Z) :=
flat_map (fun gm : sptr * ameta =>
let '(g, am) := gm in
flat_map (fun i =>
match ss_fr (nth_slot am i) with
| Some fr => match fr_kind fr with
| FGroup => if sptr_eqb (padd (slot_start am i) (UNIT * fr_off fr)) mem
then [(g, am, i)] else []
| FUser => []
end
| None => []
end) (zseq 0 (am_last am + 1))) (used_metas s).
Definition nested_at (s : astate) (p : sptr) : list (sptr * ameta) :=
filter (fun gm : sptr * ameta => (am_maplen (snd gm) =? 0) && sptr_eqb (am_mem (snd gm)) p) (used_metas s).
Definition wf_masks (am : ameta) : bool :=
let last := am_last am in let aidx := am_aidx am in
let av := am_avail am in let fr := am_freed am in
(0 <=? last) && (last <=? 31) &&
(0 <=? aidx) && (aidx <=? last) &&
(Z.of_nat (length (am_slots am)) =? last + 1) &&
(0 <=? av) && (0 <=? fr) &&
(Z.land av fr =? 0) &&
(Z.ldiff (Z.lor av fr) (ones last) =? 0) &&
(Z.ldiff av (ones aidx) =? 0) &&
forallb (fun i => Z.testbit fr i) (zseq (aidx + 1) (last - aidx)).
Definition wf_slot (s : astate) (g : sptr) (am : ameta) (i : Z) : bool :=
let sl := nth_slot am i in
let stride := stride_of am in
match ss_hdr sl with
| Some (h3, h16) => (0 <=? h3) && (h3 <=? 255) && (0 <=? h16) && (h16 <=? 65535)
| None => am_maplen am =? 0
end &&
match ss_fr sl with
| None => negb (allocated am i)
| Some fr =>
allocated am i &&
(0 <=? fr_n fr) && (0 <=? fr_off fr) && (fr_off fr <=? 255) &&
(UNIT * fr_off fr + fr_n fr <=? stride - IB) &&
(hdr_off16 am i fr <=? 65535) &&
match fr_kind fr with
| FGroup => (fr_off fr =? 0) && (fr_n fr =? stride - IB) &&
(Z.of_nat (length (nested_at s (slot_start am i))) =? 1)
| FUser => (Z.of_nat (length (nested_at s (padd (slot_start am i) (UNIT * fr_off fr)))) =? 0)
end &&
((fr_off fr =? 0) ==>
match ss_hdr sl with
| Some (h3, h16) => (h3 =? hdr_byte3 am i fr) && (h16 =? hdr_off16 am i fr)
| None => false
end)
end.
Definition wf_group (s : astate) (g : sptr) (am : ameta) : bool :=
wf_masks am &&
(0 <=? am_maplen am) &&
forallb (wf_slot s g am) (zseq 0 (am_last am + 1)) &&
(if am_sc am =? 63 then
(am_last am =? 0) && (1 <=? am_maplen am) &&
olinks_noneb (am_prev am, am_next am) &&
(am_avail am =? 0) && (am_freed am =? 0) &&
match ss_fr (nth_slot am 0) with
| Some fr => match fr_kind fr with FUser => MMAP_THRESHOLD <=? fr_n fr | FGroup => false end
| None => false
end
else
(0 <=? am_sc am) && (am_sc am <? 48) &&
((stride_of am <? class_size (am_sc am)) ==> ((am_last am =? 0) && allocated am 0)) &&
((am_sc am <=? 26) ==> ((am_maplen am =? 0) || negb (am_last am =? 0))) &&
(stride_of am * (am_last am + 1) <? 2 ^ 20)) &&
(if 0 <? am_maplen am then
match am_mem am with SP r o =>
(o =? 0) &&
match region_of s r with
| Some rg => match rg_kind rg with RkMap => true | _ => false end &&
rg_live rg && (rg_len rg =? am_maplen am * PGSZ)
| None => false
end
end &&
(UNIT + stride_of am * (am_last am + 1) <=? am_maplen am * PGSZ) &&
(((am_last am =? 0) && (am_sc am <? 48)) ==> (am_maplen am * PGSZ <=? page_round (class_size (am_sc am) + UNIT)))
else
negb (am_sc am =? 63) &&
match parent_slots s (am_mem am) with
| [(g', am', i')] =>
(am_sc am <? am_sc am') && negb (am_sc am' =? 63) &&
match ss_fr (nth_slot am' i') with
| Some fr => UNIT + class_size (am_sc am) * (am_last am + 1) - IB <=? fr_n fr
| None => false
end
| _ => false
end).
Definition group_extent (am : ameta) : Z := UNIT + stride_of am * (am_last am + 1) - IB.
Definition insideb (us : list (sptr * ameta)) (a b : ameta) : bool :=
existsb (fun j =>
match ss_fr (nth_slot b j) with
| Some fr => match fr_kind fr with
| FGroup =>
existsb (fun cm : sptr * ameta => let c := snd cm in
(am_maplen c =? 0) && sptr_eqb (am_mem c) (slot_start b j) &&
(poff (am_mem c) <=? poff (am_mem a)) &&
(poff (am_mem a) + group_extent a <=? poff (am_mem c) + group_extent c) &&
(group_extent c <=? fr_n fr)) us
| FUser => false
end
| None => false
end) (zseq 0 (am_last b + 1)).
Definition laminarb (s : astate) : bool :=
let us := used_metas s in
forallb (fun gm1 : sptr * ameta => forallb (fun gm2 : sptr * ameta =>
let '(g1, a1) := gm1 in let '(g2, a2) := gm2 in
sptr_eqb g1 g2 || negb (Nat.eqb (prid (am_mem a1)) (prid (am_mem a2))) ||
(poff (am_mem a1) + group_extent a1 <=? poff (am_mem a2)) ||
(poff (am_mem a2) + group_extent a2 <=? poff (am_mem a1)) ||
insideb us a1 a2 || insideb us a2 a1) us) us.
Definition wf_map_regions (s : astate) : bool :=
let owners := flat_map (fun gm : sptr * ameta =>
if 0 <? am_maplen (snd gm) then [prid (am_mem (snd gm))] else []) (used_metas s) in
nodupb Nat.eqb owners &&
forallb (fun k =>
match region_of s k with
| Some rg => match rg_kind rg with
| RkMap => Bool.eqb (rg_live rg) (existsb (Nat.eqb k) owners)
| _ => true
end
| None => true
end) (seq 0 (length (st_regions s))).
Definition wf_groups (s : astate) : bool :=
forallb (fun gm : sptr * ameta => wf_group s (fst gm) (snd gm)) (used_metas s) &&
wf_map_regions s && laminarb s.
Definition wf_ring (s : astate) (sc : Z) : bool :=
let hd := nth (Z.to_nat sc) (st_active s) None in
let ms := active_members s sc in
ring_okb (active_links s sc) hd ms &&
forallb (fun gm : sptr * ameta =>
let '(g, am) := gm in
(am_sc am =? sc) ==>
(if olinks_noneb (am_prev am, am_next am)
then
negb (memb g ms) && (am_avail am =? 0) && (am_freed am =? 0)
else memb g ms) &&
(negb (am_avail am =? 0) ==> osptr_eqb hd (Some g)) &&
((memb g ms && negb (osptr_eqb hd (Some g))) ==> negb (am_freed am =? 0)))
(used_metas s) &&
(countb (fun gm : sptr * ameta => (am_sc (snd gm) =? sc) && (am_aidx (snd gm) <? am_last (snd gm)))
(used_metas s) <=? 1).
Definition wf_rings (s : astate) : bool := forallb (wf_ring s) (zseq 0 48).
Definition wf_area (s : astate) (a : sptr) : bool :=
match a with SP r o =>
(o mod PGSZ =? 0) &&
match region_of s r with
| Some rg =>
rg_live rg && (o + PGSZ <=? rg_len rg) &&
match rg_kind rg with
| RkBrk => PGSZ <=? o
| RkMetaRes => (PGSZ <=? o) && existsb (Z.eqb o) (rg_rw rg)
| RkMap => false
end
| None => false
end
end.
Definition brk_regions (s : astate) : list nat :=
flat_map (fun k => match region_of s k with
| Some rg => match rg_kind rg with RkBrk => [k] | _ => [] end
| None => []
end) (seq 0 (length (st_regions s))).
Definition wf_areas (s : astate) : bool :=
forallb (fun rg => 0 <=? rg_len rg) (st_regions s) &&
nodupb sptr_eqb (st_areas s) &&
forallb (wf_area s) (st_areas s) &&
osptr_eqb (st_area_head s) (hd_error (st_areas s)) &&
osptr_eqb (st_area_tail s) (match st_areas s with [] => None | l => Some (last l (SP 0 0)) end) &&
forallb (fun k =>
match region_of s k with
| Some rg => match rg_kind rg with
| RkMetaRes => rg_live rg && (rg_len rg mod PGSZ =? 0) &&
forallb (fun o => memb (SP k o) (st_areas s)) (rg_rw rg)
| _ => true
end
| None => true
end) (seq 0 (length (st_regions s))) &&
(fold_right (fun k acc => match region_of s k with
| Some rg => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end
| None => acc
end) 0 (seq 0 (length (st_regions s)))
=? 2 * PGSZ * (2 ^ st_meta_alloc_shift s - 1)) &&
match brk_regions s with
| [] => match st_brk s with BrkCur _ _ => false | _ => true end
| [r] =>
match region_of s r with
| Some rg =>
rg_live rg && (rg_len rg mod PGSZ =? 0) && (2 * PGSZ <=? rg_len rg) &&
forallb (fun k => memb (SP r (PGSZ * k)) (st_areas s)) (zseq 1 (rg_len rg / PGSZ - 1)) &&
match st_brk s with
| BrkCur r' p => Nat.eqb r r' && (rg_len rg =? PGSZ * p)
| BrkDead => true
| BrkNever => false
end
| None => false
end
| _ => false
end &&
(if 0 <? st_avail_meta_area_count s then
match st_avail_meta_areas s with SP r o =>
match region_of s r with
| Some rg => match rg_kind rg with RkMetaRes => true | _ => false end &&
rg_live rg && (o mod PGSZ =? 0) && (PGSZ <=? o) &&
(o + PGSZ * st_avail_meta_area_count s =? rg_len rg) &&
forallb (fun x => x <? o) (rg_rw rg)
| None => false
end
end
else true).
Definition slots_in_class (s : astate) (sc : Z) : Z :=
fold_right (fun gm acc => if am_sc (snd gm) =? sc then am_last (snd gm) + 1 + acc else acc)
0 (used_metas s).
Definition wf_usage (s : astate) : bool :=
forallb (fun sc => usage_of s sc =? slots_in_class s sc) (zseq 0 48).
Definition wfb (s : astate) : bool :=
wf_ctx s && wf_metas s && wf_groups s && wf_rings s && wf_areas s && wf_usage s.
Inductive loc := LCtx (off : Z) | LMem (p : sptr).
Inductive sval :=
| VZ (z : Z)
| VP (p : sptr)
| VLo5 (z : Z)
| VSec.
Record mcell := MCell { mc_loc : loc; mc_w : nat; mc_val : sval }.
Definition optr (o : option sptr) : sval := match o with Some p => VP p | None => VZ 0 end.
Definition lpadd (l : loc) (d : Z) : loc :=
match l with LCtx o => LCtx (o + d) | LMem p => LMem (padd p d) end.
Definition CTX_secret : Z := 0.
Definition CTX_init_done : Z := 8.
Definition CTX_mmap_counter : Z := 12.
Definition CTX_free_meta_head : Z := 16.
Definition CTX_avail_meta : Z := 24.
Definition CTX_avail_meta_count : Z := 32.
Definition CTX_avail_meta_area_count : Z := 40.
Definition CTX_meta_alloc_shift : Z := 48.
Definition CTX_meta_area_head : Z := 56.
Definition CTX_meta_area_tail : Z := 64.
Definition CTX_avail_meta_areas : Z := 72.
Definition CTX_active : Z := 80.
Definition CTX_usage : Z := 464.
Definition CTX_unmap_seq : Z := 848.
Definition CTX_bounces : Z := 880.
Definition CTX_seq : Z := 912.
Definition CTX_brk : Z := 920.
Definition CTX_SIZE : Z := 928.
Definition META_prev : Z := 0.
Definition META_next : Z := 8.
Definition META_mem : Z := 16.
Definition META_avail : Z := 24.
Definition META_freed : Z := 28.
Definition META_bits : Z := 32.
Definition meta_bits (am : ameta) : Z :=
am_last am + 32 + 64 * am_sc am + 4096 * am_maplen am.
Definition ctx_cells (s : astate) : list mcell :=
[MCell (LCtx CTX_secret) 8 (if st_init_done s then VSec else VZ 0);
MCell (LCtx CTX_init_done) 4 (VZ (if st_init_done s then 1 else 0));
MCell (LCtx CTX_mmap_counter) 4 (VZ (st_mmap_counter s));
MCell (LCtx CTX_free_meta_head) 8 (optr (st_free_meta_head s));
MCell (LCtx CTX_avail_meta) 8
(match st_areas s with [] => VZ 0 | _ => VP (st_avail_meta s) end);
MCell (LCtx CTX_avail_meta_count) 8 (VZ (st_avail_meta_count s));
MCell (LCtx CTX_avail_meta_area_count) 8 (VZ (st_avail_meta_area_count s));
MCell (LCtx CTX_meta_alloc_shift) 8 (VZ (st_meta_alloc_shift s));
MCell (LCtx CTX_meta_area_head) 8 (optr (st_area_head s));
MCell (LCtx CTX_meta_area_tail) 8 (optr (st_area_tail s));
MCell (LCtx CTX_avail_meta_areas) 8
(if (match st_areas s with [] => true | _ => false end) && (st_avail_meta_area_count s =? 0)
then VZ 0 else VP (st_avail_meta_areas s));
MCell (LCtx CTX_seq) 1 (VZ (st_seq s));
MCell (LCtx CTX_brk) 8 (match st_brk s with
| BrkNever => VZ 0
| BrkDead => VZ (-1)
| BrkCur r p => VP (SP r (PGSZ * p))
end)]
++ map (fun k => MCell (LCtx (CTX_active + 8 * Z.of_nat k)) 8 (optr (nth k (st_active s) None))) (seq 0 48)
++ map (fun k => MCell (LCtx (CTX_usage + 8 * Z.of_nat k)) 8 (VZ (nth k (st_usage s) 0))) (seq 0 48)
++ map (fun k => MCell (LCtx (CTX_unmap_seq + Z.of_nat k)) 1 (VZ (nth k (st_unmap_seq s) 0))) (seq 0 32)
++ map (fun k => MCell (LCtx (CTX_bounces + Z.of_nat k)) 1 (VZ (nth k (st_bounces s) 0))) (seq 0 32).
Definition meta_slot_cells (q : sptr) (x : option mslot) : list mcell :=
match x with
| Some (MUsed am) =>
[MCell (LMem (padd q META_prev)) 8 (optr (am_prev am));
MCell (LMem (padd q META_next)) 8 (optr (am_next am));
MCell (LMem (padd q META_mem)) 8 (VP (am_mem am));
MCell (LMem (padd q META_avail)) 4 (VZ (am_avail am));
MCell (LMem (padd q META_freed)) 4 (VZ (am_freed am));
MCell (LMem (padd q META_bits)) 8 (VZ (meta_bits am))]
| Some (MFree pr nx) =>
[MCell (LMem (padd q META_prev)) 8 (optr pr);
MCell (LMem (padd q META_next)) 8 (optr nx);
MCell (LMem (padd q META_mem)) 8 (VZ 0);
MCell (LMem (padd q META_avail)) 4 (VZ 0);
MCell (LMem (padd q META_freed)) 4 (VZ 0);
MCell (LMem (padd q META_bits)) 8 (VZ 0)]
| _   =>
[MCell (LMem (padd q META_prev)) 8 (VZ 0);
MCell (LMem (padd q META_next)) 8 (VZ 0);
MCell (LMem (padd q META_mem)) 8 (VZ 0);
MCell (LMem (padd q META_avail)) 4 (VZ 0);
MCell (LMem (padd q META_freed)) 4 (VZ 0);
MCell (LMem (padd q META_bits)) 8 (VZ 0)]
end.
Definition area_cells (s : astate) (a : sptr) (next : option sptr) : list mcell :=
[MCell (LMem a) 8 VSec;
MCell (LMem (padd a 8)) 8 (optr next);
MCell (LMem (padd a 16)) 4 (VZ METAS_PER_AREA)]
++ flat_map (fun k => let q := padd a (AREA_HDR + META_SIZE * Z.of_nat k) in
meta_slot_cells q (mlookup (st_metas s) q))
(seq 0 (Z.to_nat METAS_PER_AREA)).
Fixpoint areas_cells (s : astate) (l : list sptr) : list mcell :=
match l with
| [] => []
| a :: t => area_cells s a (hd_error t) ++ areas_cells s t
end.
Definition slot_cells (am : ameta) (i : Z) : list mcell :=
let st := slot_start am i in
let sl := nth_slot am i in
[MCell (LMem (padd st (-4))) 1 (VZ 0)]
++ match ss_hdr sl with
| Some (h3, h16) => [MCell (LMem (padd st (-3))) 1 (VZ h3); MCell (LMem (padd st (-2))) 2 (VZ h16)]
| None => []
end
++ match ss_fr sl with
| Some fr =>
if fr_off fr =? 0 then []
else let p := padd st (UNIT * fr_off fr) in
[MCell (LMem (padd p (-4))) 1 (VZ 0);
MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr));
MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))]
| None => []
end.
Definition group_cells (g : sptr) (am : ameta) : list mcell :=
[MCell (LMem (am_mem am)) 8 (VP g);
(if am_maplen am =? 0 then MCell (LMem (padd (am_mem am) 8)) 1 (VLo5 (am_aidx am))
else MCell (LMem (padd (am_mem am) 8)) 4 (VZ (am_aidx am)))]
++ flat_map (slot_cells am) (zseq 0 (am_last am + 1)).
Definition image (s : astate) : list mcell :=
ctx_cells s ++ areas_cells s (st_areas s)
++ flat_map (fun gm : sptr * ameta => group_cells (fst gm) (snd gm)) (used_metas s).
Definition footprint (s : astate) : list (loc * Z) :=
(LCtx 0, CTX_SIZE)
:: map (fun a => (LMem a, PGSZ)) (st_areas s)
++ flat_map (fun k => match region_of s k with
| Some rg => match rg_kind rg with
| RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else []
| _ => []
end
| None => []
end) (seq 0 (length (st_regions s))).
Definition user_blocks (s : astate) : list (sptr * Z) :=
flat_map (fun gm : sptr * ameta =>
let am := snd gm in
flat_map (fun i => match ss_fr (nth_slot am i) with
| Some fr => match fr_kind fr with
| FUser => [(padd (slot_start am i) (UNIT * fr_off fr), fr_n fr)]
| FGroup => []
end
| None => []
end) (zseq 0 (am_last am + 1))) (used_metas s).
Definition live_bytes (s : astate) : Z :=
fold_right (fun rg acc => if rg_live rg then rg_len rg + acc else acc) 0 (st_regions s).
Record layout := Layout {
ly_ctx : Z;
ly_reg : nat -> Z;
ly_brk0 : Z;
ly_sec : Z
}.
Definition loc_addr (L : layout) (l : loc) : Z :=
match l with
| LCtx o => ly_ctx L + o
| LMem (SP r o) => ly_reg L r + o
end.
Definition sval_num (L : layout) (v : sval) : Z :=
match v with
| VZ z => z
| VP p => loc_addr L (LMem p)
| VLo5 z => z
| VSec => ly_sec L
end.
Definition le_byte (z : Z) (w k : nat) : Z :=
(Z.shiftr (z mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)) mod 256.
Definition byteview := Z -> option Z.
Definition cell_holds (L : layout) (m : byteview) (c : mcell) : Prop :=
let a := loc_addr L (mc_loc c) in
match mc_val c with
| VLo5 z => exists b, m a = Some b /\ b mod 32 = z
| v => forall k, (k < mc_w c)%nat -> m (a + Z.of_nat k) = Some (le_byte (sval_num L v) (mc_w c) k)
end.
Definition range_mapped (L : layout) (m : byteview) (rg : loc * Z) : Prop :=
forall x, loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg -> m x <> None.
Definition crange (L : layout) (rg : loc * Z) : Z * Z := (loc_addr L (fst rg), snd rg).
Definition ranges_disjoint (a b : Z * Z) : Prop :=
fst a + snd a <= fst b \/ fst b + snd b <= fst a.
Fixpoint pairwise {A : Type} (R : A -> A -> Prop) (l : list A) : Prop :=
match l with
| [] => True
| x :: t => (forall y, In y t -> R x y) /\ pairwise R t
end.
Definition layout_ok (L : layout) (s : astate) : Prop :=
ly_ctx L mod 8 = 0 /\
(forall k rg, region_of s k = Some rg -> rg_live rg = true -> ly_reg L k mod PGSZ = 0) /\
pairwise ranges_disjoint (map (crange L) (footprint s)) /\
(forall rg, In rg (footprint s) -> 0 < fst (crange L rg) /\ fst (crange L rg) + snd (crange L rg) < 2 ^ 63).
Definition repr (L : layout) (s : astate) (m : byteview) : Prop :=
layout_ok L s /\
Forall (cell_holds L m) (image s) /\
Forall (range_mapped L m) (footprint s).
Definition in_footprint (L : layout) (s : astate) (x : Z) : Prop :=
exists rg, In rg (footprint s) /\ loc_addr L (fst rg) <= x < loc_addr L (fst rg) + snd rg.
Definition in_user_block (L : layout) (s : astate) (x : Z) : Prop :=
exists b, In b (user_blocks s) /\ loc_addr L (LMem (fst b)) <= x < loc_addr L (LMem (fst b)) + snd b.
Definition alloc_owned (L : layout) (s : astate) (x : Z) : Prop :=
in_footprint L s x /\ ~ in_user_block L s x.
Record aux_layout := AuxLayout {
ax_libc : Z;
ax_malloc_lock : Z;
ax_errno : Z;
ax_size_classes : Z; ax_small_cnt_tab : Z; ax_med_cnt_tab : Z; ax_debruijn32 : Z
}.
Definition erase_slot (sl : slotst) : slotst :=
mkSlot (match ss_hdr sl with Some _ => Some (0, 0) | None => None end)
(match ss_fr sl with
| Some fr => Some (mkFrame (match fr_kind fr with FUser => 0 | FGroup => fr_off fr end)
(fr_n fr) (fr_kind fr))
| None => None
end).
Definition erase_meta (x : mslot) : mslot :=
match x with
| MUsed am => MUsed (am_set_slots (map erase_slot (am_slots am)) am)
| y => y
end.
Definition erase (s : astate) : astate :=
set_metas (map (fun e : sptr * mslot => (fst e, erase_meta (snd e))) (st_metas s)) s.
Definition shape_eq (s t : astate) : Prop := erase s = erase t.
Record get_meta_view := GMV {
gm_p4 : Z; gm_p3 : Z; gm_off16 : Z;
gm_meta : sptr;
gm_mem : sptr; gm_avail : Z; gm_freed : Z;
gm_last : Z; gm_sc : Z; gm_maplen : Z;
gm_area_check : Z
}.
Definition get_meta_asserts (p base : sptr) (v : get_meta_view) : bool :=
(poff p mod 16 =? 0) &&
(gm_p4 v =? 0) &&
sptr_eqb (gm_mem v) base &&
(Z.land (gm_p3 v) 31 <=? gm_last v) &&
negb (Z.testbit (gm_avail v) (Z.land (gm_p3 v) 31)) &&
negb (Z.testbit (gm_freed v) (Z.land (gm_p3 v) 31)) &&
(gm_area_check v =? 0) &&
(if gm_sc v <? 48 then
(znth (gm_sc v) size_classes * Z.land (gm_p3 v) 31 <=? gm_off16 v) &&
(gm_off16 v <? znth (gm_sc v) size_classes * (Z.land (gm_p3 v) 31 + 1))
else gm_sc v =? 63) &&
((0 <? gm_maplen v) ==> (gm_off16 v <=? gm_maplen v * 4096 / 16 - 1)).
Definition view_of (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : get_meta_view :=
GMV 0 (hdr_byte3 am i fr) (hdr_off16 am i fr) g (am_mem am) (am_avail am) (am_freed am)
(am_last am) (am_sc am) (am_maplen am) 0.
Definition answer_ok (q : kreq) (z : Z) : Prop :=
match q with KJunk _ => 0 <= z < 256 | _ => True end.
Fixpoint safe {A : Type} (t : itree astate A) : Prop :=
match t with
| IRet _ => True
| IFail _ => False
| IAsk q _ k => forall z, answer_ok q z -> safe (k z)
end.
Fixpoint yields {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
match t, tr with
| IRet a', [] => a' = a
| IAsk q _ k, (q', z) :: tr' => q' = q /\ answer_ok q z /\ yields (k z) tr' a
| _, _ => False
end.
Definition resv_total (s : astate) : Z :=
fold_right (fun rg acc => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end)
0 (st_regions s).
Definition req_ok (s : astate) (q : kreq) : Prop :=
match q with
| KBrkQuery => st_brk s = BrkNever /\ brk_regions s = []
| KBrkGrow n =>
(n = 2 /\ st_brk s = BrkNever /\ brk_regions s = [])
\/ (n = 1 /\ exists r p rg, st_brk s = BrkCur r p /\ region_of s r = Some rg /\
rg_kind rg = RkBrk /\ rg_live rg = true /\ rg_len rg = PGSZ * p)
| KGuard =>
exists r rg, st_brk s = BrkCur r 2 /\ S r = length (st_regions s) /\
region_of s r = Some rg /\ rg_kind rg = RkBrk /\ rg_len rg = 2 * PGSZ /\
Forall (fun a : sptr => prid a <> r) (st_areas s)
| KMmapRW len => 1 <= len < 2 ^ 63
| KMmapNone len => len = Z.shiftl 2 (st_meta_alloc_shift s) * PGSZ /\ st_avail_meta_area_count s = 0 /\
0 <= st_meta_alloc_shift s /\ resv_total s = 2 * PGSZ * (2 ^ st_meta_alloc_shift s - 1)
| KMprotect p =>
0 < st_avail_meta_area_count s /\ p = st_avail_meta_areas s /\
exists rg, region_of s (prid p) = Some rg /\ rg_kind rg = RkMetaRes /\ rg_live rg = true /\
poff p mod PGSZ = 0 /\ PGSZ <= poff p /\ poff p + PGSZ <= rg_len rg /\ ~ In (poff p) (rg_rw rg)
| KMunmap r len =>
exists rg, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
rg_len rg = page_round len /\ 0 <= len /\
Forall (fun gm : sptr * ameta => 0 < am_maplen (snd gm) -> prid (am_mem (snd gm)) <> r) (used_metas s)
| KMremap r old_len new_len =>
(exists rg, region_of s r = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ rg_len rg = old_len) /\
0 < old_len /\ old_len mod PGSZ = 0 /\ 0 < new_len < 2 ^ 63 /\ new_len mod PGSZ = 0 /\ new_len <> old_len
| KJunk _ => True
end.
Fixpoint reqs_ok {A : Type} (t : itree astate A) : Prop :=
match t with
| IAsk q snap k => req_ok snap q /\ forall z, answer_ok q z -> reqs_ok (k z)
| _ => True
end.
Fixpoint tsim {A B : Type} (R : A -> B -> Prop) (t : itree astate A) (u : itree astate B) : Prop :=
match t, u with
| IRet a, IRet b => R a b
| IAsk (KJunk _) _ k, IAsk (KJunk _) _ k' =>
forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z')
| IAsk q _ k, IAsk q' _ k' => q = q' /\ forall z, tsim R (k z) (k' z)
| IFail _, IFail _ => True
| _, _ => False
end.
Definition frames (s : astate) : list (sptr * ameta * Z * frame) :=
flat_map (fun gm : sptr * ameta =>
let '(g, am) := gm in
flat_map (fun i => match ss_fr (nth_slot am i) with
| Some fr => [(g, am, i, fr)]
| None => []
end) (zseq 0 (am_last am + 1))) (used_metas s).
Definition frame_ptr (am : ameta) (i : Z) (fr : frame) : sptr :=
padd (slot_start am i) (UNIT * fr_off fr).
Definition cell_range (L : layout) (c : mcell) : Z * Z := (loc_addr L (mc_loc c), Z.of_nat (mc_w c)).
Definition block_range (L : layout) (b : sptr * Z) : Z * Z := (loc_addr L (LMem (fst b)), snd b).
Definition range_incl (a b : Z * Z) : Prop := fst b <= fst a /\ fst a + snd a <= fst b + snd b.
Definition bounded (s : astate) : Prop :=
(forall sc, 0 <= usage_of s sc < 2 ^ 48) /\
0 <= st_meta_alloc_shift s <= 40 /\
Z.of_nat (length (st_areas s)) < 2 ^ 36.
Definition MT (s : astate) : sptr -> option mslot := mlookup (st_metas s).
Definition keys (s : astate) : list sptr := map fst (st_metas s).
Section a0.
Variable X : list sptr.
Variable s : astate.
Definition MTX (g : sptr) : option mslot := if memb g X then None else MT s g.
Definition usedX (g : sptr) (am : ameta) : Prop := MTX g = Some (MUsed am).
Definition alinks (sc : Z) (g : sptr) : option (option sptr * option sptr) :=
match MTX g with
| Some (MUsed am) => if am_sc am =? sc then Some (am_prev am, am_next am) else None
| _ => None
end.
Definition flinks (g : sptr) : option (option sptr * option sptr) :=
match MTX g with
| Some (MFree pr nx) => Some (pr, nx)
| _ => None
end.
End a0.
Definition active_hd (s : astate) (sc : Z) : option sptr := nth (Z.to_nat sc) (st_active s) None.
Definition masks_ok (am : ameta) : Prop :=
0 <= am_last am <= 31 /\
0 <= am_aidx am <= am_last am /\
length (am_slots am) = Z.to_nat (am_last am + 1) /\
0 <= am_avail am /\ 0 <= am_freed am /\
(forall i, 0 <= i -> Z.testbit (am_avail am) i = true -> Z.testbit (am_freed am) i = false) /\
(forall i, am_last am < i -> Z.testbit (am_avail am) i = false /\ Z.testbit (am_freed am) i = false) /\
(forall i, am_aidx am < i -> Z.testbit (am_avail am) i = false) /\
(forall i, am_aidx am < i <= am_last am -> Z.testbit (am_freed am) i = true).
Definition frame_ok (am : ameta) (i : Z) (fr : frame) : Prop :=
0 <= fr_n fr /\ 0 <= fr_off fr <= 255 /\
UNIT * fr_off fr + fr_n fr <= stride_of am - IB /\
hdr_off16 am i fr <= 65535 /\
(fr_kind fr = FGroup -> fr_off fr = 0 /\ fr_n fr = stride_of am - IB).
Definition slot_ok (R : option (sptr * Z)) (g : sptr) (am : ameta) (i : Z) : Prop :=
let sl := nth_slot am i in
(ss_hdr sl = None -> am_maplen am = 0) /\
(forall h3 h16, ss_hdr sl = Some (h3, h16) -> 0 <= h3 <= 255 /\ 0 <= h16 <= 65535) /\
match ss_fr sl with
| None => allocated am i = false \/ R = Some (g, i)
| Some fr => allocated am i = true /\ R <> Some (g, i) /\ frame_ok am i fr /\
(fr_off fr = 0 -> ss_hdr sl = Some (hdr_byte3 am i fr, hdr_off16 am i fr))
end.
Definition class_ok (R : option (sptr * Z)) (g : sptr) (am : ameta) : Prop :=
(am_sc am = 63 /\ am_last am = 0 /\ 1 <= am_maplen am /\ am_avail am = 0 /\ am_freed am = 0 /\
(R = Some (g, 0) \/ exists fr, ss_fr (nth_slot am 0) = Some fr /\ fr_kind fr = FUser /\ MMAP_THRESHOLD <= fr_n fr))
\/
(0 <= am_sc am < 48 /\
(stride_of am < class_size (am_sc am) -> am_last am = 0 /\ allocated am 0 = true) /\
(am_sc am <= 26 -> am_maplen am = 0 \/ am_last am <> 0) /\
stride_of am * (am_last am + 1) < 2 ^ 20).
Definition mapped_ok (s : astate) (am : ameta) : Prop :=
0 < am_maplen am ->
exists r rg, am_mem am = SP r 0 /\ region_of s r = Some rg /\ rg_kind rg = RkMap /\
rg_live rg = true /\ rg_len rg = am_maplen am * PGSZ /\
UNIT + stride_of am * (am_last am + 1) <= am_maplen am * PGSZ /\
(am_last am = 0 -> am_sc am < 48 -> am_maplen am * PGSZ <= page_round (class_size (am_sc am) + UNIT)).
Definition nested_ok (X : list sptr) (s : astate) (am : ameta) : Prop :=
am_maplen am = 0 ->
am_sc am <> 63 /\
exists g' am' i' fr',
usedX X s g' am' /\ 0 <= i' <= am_last am' /\
ss_fr (nth_slot am' i') = Some fr' /\ fr_kind fr' = FGroup /\
am_mem am = slot_start am' i' /\
am_sc am < am_sc am' /\ am_sc am' <> 63 /\
UNIT + class_size (am_sc am) * (am_last am + 1) - IB <= fr_n fr'.
Definition group_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) (g : sptr) (am : ameta) : Prop :=
masks_ok am /\ 0 <= am_maplen am /\
(forall i, 0 <= i <= am_last am -> slot_ok R g am i) /\
class_ok R g am /\ mapped_ok s am /\ nested_ok X s am.
Definition inside (X : list sptr) (s : astate) (a b : ameta) : Prop :=
exists j fr c ac, 0 <= j <= am_last b /\ ss_fr (nth_slot b j) = Some fr /\ fr_kind fr = FGroup /\
usedX X s c ac /\ am_maplen ac = 0 /\ am_mem ac = slot_start b j /\
poff (am_mem ac) <= poff (am_mem a) /\
poff (am_mem a) + group_extent a <= poff (am_mem ac) + group_extent ac /\
group_extent ac <= fr_n fr.
Definition spans_disjoint (a b : ameta) : Prop :=
poff (am_mem a) + group_extent a <= poff (am_mem b) \/
poff (am_mem b) + group_extent b <= poff (am_mem a).
Definition laminar (X : list sptr) (s : astate) : Prop :=
forall g1 a1 g2 a2, usedX X s g1 a1 -> usedX X s g2 a2 -> g1 <> g2 ->
prid (am_mem a1) = prid (am_mem a2) ->
spans_disjoint a1 a2 \/ inside X s a1 a2 \/ inside X s a2 a1.
Definition maps_unique (X : list sptr) (s : astate) : Prop :=
forall g1 a1 g2 a2, usedX X s g1 a1 -> usedX X s g2 a2 ->
0 < am_maplen a1 -> 0 < am_maplen a2 -> prid (am_mem a1) = prid (am_mem a2) -> g1 = g2.
Definition free_ring_ok (X : list sptr) (s : astate) : Prop :=
exists ms, ring_ok (flinks X s) (st_free_meta_head s) ms /\
forall g pr nx, MTX X s g = Some (MFree pr nx) -> In g ms.
Definition active_ring_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) (sc : Z) : Prop :=
exists ms, ring_ok (alinks X s sc) (active_hd s sc) ms /\
(forall g am, usedX X s g am -> am_sc am = sc ->
(In g ms <-> (am_prev am, am_next am) <> (None, None))) /\
(forall g am, usedX X s g am -> am_sc am = sc -> ~ In g ms ->
am_avail am = 0 /\ am_freed am = 0) /\
(forall g am, usedX X s g am -> am_sc am = sc -> am_avail am <> 0 -> active_hd s sc = Some g) /\
(forall g am, usedX X s g am -> am_sc am = sc -> In g ms -> active_hd s sc <> Some g ->
(forall i, R <> Some (g, i)) -> am_freed am <> 0).
Definition partial_unique (X : list sptr) (s : astate) : Prop :=
forall g1 a1 g2 a2, usedX X s g1 a1 -> usedX X s g2 a2 -> am_sc a1 = am_sc a2 ->
am_aidx a1 < am_last a1 -> am_aidx a2 < am_last a2 -> g1 = g2.
Definition direct_unlinked (X : list sptr) (s : astate) : Prop :=
forall g am, usedX X s g am -> am_sc am = 63 -> am_prev am = None /\ am_next am = None.
Definition rings_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop :=
free_ring_ok X s /\ (forall sc, 0 <= sc < 48 -> active_ring_ok X R s sc) /\ direct_unlinked X s.
Definition handed (s : astate) (a : sptr) : Z :=
if sptr_eqb a (last (st_areas s) (SP 0%nat 0)) then METAS_PER_AREA - st_avail_meta_count s else METAS_PER_AREA.
Definition key_placed (s : astate) (p : sptr) : Prop :=
exists a k, In a (st_areas s) /\ 0 <= k < handed s a /\ p = padd a (AREA_HDR + META_SIZE * k).
Definition keys_ok (s : astate) : Prop :=
NoDup (keys s) /\
(forall p, In p (keys s) -> key_placed s p) /\
(st_areas s = [] -> st_avail_meta_count s = 0) /\
(st_areas s <> [] ->
st_avail_meta s = padd (last (st_areas s) (SP 0%nat 0))
(AREA_HDR + META_SIZE * (METAS_PER_AREA - st_avail_meta_count s))) /\
0 <= st_avail_meta_count s <= METAS_PER_AREA.
Definition Xok (X : list sptr) (s : astate) : Prop :=
forall x, In x X ->
In x (keys s) /\
match MT s x with
| Some (MUsed am) =>
am_prev am = None /\ am_next am = None /\
(forall i, ss_fr (nth_slot am i) = None)
| Some MRaw => True
| Some (MFree None None) => True
| _ => False
end.
Definition area_ok (s : astate) (a : sptr) : Prop :=
exists r o rg, a = SP r o /\ o mod PGSZ = 0 /\ PGSZ <= o /\
region_of s r = Some rg /\ rg_live rg = true /\ o + PGSZ <= rg_len rg /\
match rg_kind rg with
| RkBrk => True
| RkMetaRes => In o (rg_rw rg)
| RkMap => False
end.
Definition areas_ok (s : astate) : Prop :=
NoDup (st_areas s) /\
(forall a, In a (st_areas s) -> area_ok s a) /\
st_area_head s = hd_error (st_areas s) /\
st_area_tail s = (match st_areas s with [] => None | l => Some (last l (SP 0%nat 0)) end) /\
(forall k rg, region_of s k = Some rg -> rg_kind rg = RkMetaRes -> rg_live rg = true /\ rg_len rg mod PGSZ = 0 /\ 0 <= rg_len rg) /\
resv_total s = 2 * PGSZ * (2 ^ st_meta_alloc_shift s - 1) /\
match st_brk s with
| BrkNever => brk_regions s = []
| BrkDead => forall r, In r (brk_regions s) -> brk_regions s = [r] /\
exists rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_len rg mod PGSZ = 0 /\ 2 * PGSZ <= rg_len rg
| BrkCur r p => brk_regions s = [r] /\
exists rg, region_of s r = Some rg /\ rg_live rg = true /\ rg_len rg = PGSZ * p /\ 2 <= p
end /\
(0 < st_avail_meta_area_count s ->
exists r o rg, st_avail_meta_areas s = SP r o /\ region_of s r = Some rg /\
rg_kind rg = RkMetaRes /\ rg_live rg = true /\ o mod PGSZ = 0 /\ PGSZ <= o /\
o + PGSZ * st_avail_meta_area_count s = rg_len rg /\
(forall x, In x (rg_rw rg) -> x < o)) /\
(forall k rg, region_of s k = Some rg -> 0 <= rg_len rg).
Definition ctx_ok (s : astate) : Prop :=
length (st_active s) = 48%nat /\ length (st_usage s) = 48%nat /\
length (st_unmap_seq s) = 32%nat /\ length (st_bounces s) = 32%nat /\
(forall u, In u (st_usage s) -> 0 <= u) /\
(forall u, In u (st_unmap_seq s) -> 0 <= u <= 255) /\
(forall u, In u (st_bounces s) -> 0 <= u <= 255) /\
0 <= st_seq s <= 255 /\
0 <= st_mmap_counter s < 2 ^ 32 /\
0 <= st_meta_alloc_shift s /\
0 <= st_avail_meta_area_count s /\
(st_init_done s = false ->
st_metas s = [] /\ st_areas s = [] /\ st_brk s = BrkNever /\ st_avail_meta_area_count s = 0).
Definition contrib (X : list sptr) (s : astate) (sc : Z) (g : sptr) : Z :=
match MTX X s g with
| Some (MUsed am) => if am_sc am =? sc then am_last am + 1 else 0
| _ => 0
end.
Definition class_sum (X : list sptr) (s : astate) (sc : Z) : Z :=
fold_right (fun g acc => contrib X s sc g + acc) 0 (keys s).
Definition usage_ok (X : list sptr) (U : Z -> Z) (s : astate) : Prop :=
forall sc, 0 <= sc < 48 -> usage_of s sc = class_sum X s sc + U sc.
Definition U0 : Z -> Z := fun _ => 0.
Definition reserved_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop :=
forall g i, R = Some (g, i) ->
exists am, usedX X s g am /\ 0 <= i <= am_last am /\
ss_fr (nth_slot am i) = None /\ allocated am i = true.
Definition InvMeta (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) : Prop :=
Xok X s /\
(forall g am, usedX X s g am -> group_ok X R s g am) /\
laminar X s /\ maps_unique X s /\ rings_ok X R s /\ usage_ok X U s /\ reserved_ok X R s /\
partial_unique X s.
Definition Inv (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) : Prop :=
ctx_ok s /\ keys_ok s /\ areas_ok s /\ InvMeta X R U s.
Definition WFI (s : astate) : Prop := Inv [] None U0 s.
Section b0.
Context {X : list sptr} {R : option (sptr * Z)} {U : Z -> Z} {s : astate} (H : Inv X R U s).
Lemma inv_ctx : ctx_ok s. Proof. exact (proj1 H). Qed.
Lemma inv_keys : keys_ok s. Proof. exact (proj1 (proj2 H)). Qed.
Lemma inv_areas : areas_ok s. Proof. exact (proj1 (proj2 (proj2 H))). Qed.
Lemma inv_meta : InvMeta X R U s. Proof. exact (proj2 (proj2 (proj2 H))). Qed.
Lemma inv_X : Xok X s. Proof. exact (proj1 inv_meta). Qed.
Lemma inv_groups : forall g am, usedX X s g am -> group_ok X R s g am.
Proof. exact (proj1 (proj2 inv_meta)). Qed.
Lemma inv_laminar : laminar X s. Proof. exact (proj1 (proj2 (proj2 inv_meta))). Qed.
Lemma inv_maps : maps_unique X s. Proof. exact (proj1 (proj2 (proj2 (proj2 inv_meta)))). Qed.
Lemma inv_rings : rings_ok X R s. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 inv_meta))))). Qed.
Lemma inv_usage : usage_ok X U s. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta)))))). Qed.
Lemma inv_reserved : reserved_ok X R s. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta))))))). Qed.
Lemma inv_partial : partial_unique X s. Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta))))))). Qed.
End b0.
Definition WF (s : astate) : Prop := Inv [] None U0 s.
Lemma wf_init : WF init_state.
Proof.
unfold WF.
assert (NU : forall g am, ~ usedX [] init_state g am) by (intros g am H; unfold usedX, MTX, MT in H; cbn in H; discriminate).
split.
{ unfold ctx_ok. cbn -[Z.le Z.lt Z.pow]. repeat split; try lia; try reflexivity;
intros u Hu; apply repeat_spec in Hu; subst u; lia. }
split.
{ unfold keys_ok, keys. cbn. split; [constructor|]. split; [intros p []|]. split; [reflexivity|]. split; [intros H; exfalso; exact (H eq_refl)|]. unfold METAS_PER_AREA. lia. }
split.
{ unfold areas_ok. cbn -[Z.mul Z.pow Z.sub Z.le Z.lt]. split; [constructor|]. split; [intros a []|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros k rg Hk; unfold region_of in Hk; cbn in Hk; destruct k; discriminate|].
split; [reflexivity|]. split; [reflexivity|]. split; [intros H; lia|].
intros k rg Hk. unfold region_of in Hk. cbn in Hk. destruct k; discriminate. }
split; [intros x []|].
split; [intros g am H; exfalso; exact (NU g am H)|].
split; [intros g1 a1 g2 a2 H; exfalso; exact (NU _ _ H)|].
split; [intros g1 a1 g2 a2 H; exfalso; exact (NU _ _ H)|].
split.
{ split; [|split].
- exists []. split; [split; [split; [constructor | exact I] | reflexivity]|]. intros g pr nx H. unfold MTX, MT in H. cbn in H. discriminate.
- intros sc Hsc. exists []. split.
+ unfold active_hd. cbn [st_active init_state]. rewrite nth_repeat. split; [split; [constructor | exact I] | reflexivity].
+ split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
intros q a Hq; exfalso; exact (NU q a Hq).
- intros g am H. exfalso. exact (NU g am H). }
split.
{ intros sc Hsc. unfold usage_of, class_sum, keys, U0. cbn [st_usage st_metas init_state map fold_right]. unfold znth. rewrite nth_repeat. reflexivity. }
split; [intros g i H; discriminate|].
intros g1 a1 g2 a2 H. exfalso. exact (NU _ _ H).
Qed.
Lemma image_init : image init_state = ctx_cells init_state.
Proof. vm_compute. reflexivity. Qed.
Lemma footprint_init : footprint init_state = [(LCtx 0, CTX_SIZE)].
Proof. reflexivity. Qed.
Lemma user_blocks_init : user_blocks init_state = [].
Proof. reflexivity. Qed.
Definition fold_off (slack off0 : Z) : Z :=
if slack <? off0 then
let m1 := Z.lor slack (Z.shiftr slack 1) in
let m2 := Z.lor m1 (Z.shiftr m1 2) in
let m3 := Z.lor m2 (Z.shiftr m2 4) in
let off1 := Z.land off0 m3 in
if slack <? off1 then off1 - (slack + 1) else off1
else off0.
Lemma fold_off_small_ok :
forallb (fun slack => forallb (fun off0 => let off := fold_off slack off0 in (0 <=? off) && (off <=? slack))
(zseq 0 256))
(zseq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fold_off_ok : forall slack off0,
0 <= slack -> 0 <= off0 < 256 -> 0 <= fold_off slack off0 <= slack.
Proof.
intros slack off0 Hs Ho.
destruct (Z_lt_dec slack 256) as [Hlt|Hge].
- assert (Hin : forall l k, 0 <= k < 256 ->
forallb (fun x => let off := fold_off l x in (0 <=? off) && (off <=? l)) (zseq 0 256) = true ->
0 <= fold_off l k <= l).
{ intros l k Hk Hf. rewrite forallb_forall in Hf.
specialize (Hf k).
assert (HIn : In k (zseq 0 256)).
{ unfold zseq. apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia. }
specialize (Hf HIn). cbn beta in Hf. apply andb_prop in Hf as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
apply Hin; [lia|].
pose proof fold_off_small_ok as HT. rewrite forallb_forall in HT. apply HT.
unfold zseq. apply in_map_iff. exists (Z.to_nat slack). split; [lia|]. apply in_seq. lia.
- unfold fold_off. destruct (slack <? off0) eqn:E; [apply Z.ltb_lt in E; lia|lia].
Qed.
Lemma class_of_units_ok :
forallb (fun k => let c := class_of_units k in
(0 <=? c) && (c <? 48) && (k <? znth c size_classes) &&
((0 <? c) ==> (znth (c - 1) size_classes <=? k)))
(zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_to_class_range : forall n,
0 <= n < MMAP_THRESHOLD ->
0 <= size_to_class n < 48 /\ n + IB <= class_size (size_to_class n).
Proof.
intros n Hn. unfold size_to_class, class_size.
set (k := Z.shiftr (n + IB - 1) 4).
assert (Hk : 0 <= k < 8191).
{ subst k. rewrite Z.shiftr_div_pow2 by lia. unfold MMAP_THRESHOLD, IB in *.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
pose proof class_of_units_ok as HT. rewrite forallb_forall in HT.
specialize (HT k).
assert (HIn : In k (zseq 0 8191)).
{ unfold zseq. apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia. }
specialize (HT HIn). cbn beta in HT.
apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
split; [lia|].
assert (Hkn : n + IB <= UNIT * k + UNIT).
{ subst k. rewrite Z.shiftr_div_pow2 by lia. unfold UNIT, IB in *.
pose proof (Z.mul_succ_div_gt (n + 4 - 1) (2 ^ 4) ltac:(lia)) as Hd. lia. }
unfold UNIT in *. nia.
Qed.
Fixpoint regions_after (rs : list region) (tr : list (kreq * Z)) : list region :=
match tr with
| [] => rs
| (KMmapRW len, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkMap (page_round len) [] true]) t
| (KMmapNone len, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkMetaRes len [] true]) t
| (KBrkGrow 2, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkBrk (2 * PGSZ) [] true]) t
| (KBrkGrow _, z) :: t =>
regions_after rs t
| (KMunmap r len, _) :: t => regions_after (lupd rs r (mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)) t
| (KMremap r ol nl, z) :: t =>
regions_after (if z =? 0 then rs
else lupd (rs ++ [mkRegion RkMap nl [] true]) r
(mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)) t
| _ :: t => regions_after rs t
end.
Definition same_shape_regions (a b : list region) : Prop :=
map rg_kind a = map rg_kind b /\ map rg_live a = map rg_live b.
Module Conjectures.
Lemma free_null : forall s, free None s = IRet (tt, s).
Proof. reflexivity. Qed.
End Conjectures.
Module Probes.
Fixpoint run_states (r : srun) (ops : list op) (acc : list astate) : list astate * option failure :=
match ops with
| [] => (rev acc, None)
| o :: t => let r' := run_op r o in
match sr_err r' with
| Some e => (rev acc, Some e)
| None => run_states r' t (sr_state r' :: acc)
end
end.
Definition states (ans : list (option Z)) (ops : list op) : list astate * option failure :=
run_states (mkRun init_state [] [] ans None) ops [init_state].
Definition check (ans : list (option Z)) (ops : list op) : Z * bool * option failure :=
let '(l, e) := states ans ops in (Z.of_nat (length l), forallb wfb l, e).
Definition lcg (x : Z) : Z := (x * 6364136223846793005 + 1442695040888963407) mod 2 ^ 64.
Definition probe_sizes : list Z :=
[1;8;16;24;40;100;112;160;200;492;500;1000;1120;2000;2262;2720;4000;4096;5000;6048;
7256;8700;16480;32864;65632;100000;131051;131052;131168;200000;300000].
Fixpoint remove_nth (l : list nat) (k : nat) : list nat :=
match l, k with
| [], _ => []
| _ :: t, O => t
| h :: t, S k' => h :: remove_nth t k'
end.
Fixpoint gen (fuel : nat) (seed : Z) (nm : nat) (live : list nat) (pfree : Z) (acc : list op) : list op :=
match fuel with
| O => rev acc
| S f =>
let r := lcg seed in
let choice := (Z.shiftr r 33) mod 100 in
if (choice <? pfree) && negb (Nat.eqb (length live) 0) then
let k := Z.to_nat ((Z.shiftr r 17) mod Z.of_nat (length live)) in
gen f r nm (remove_nth live k) pfree (Free (nth k live O) :: acc)
else
let sz := nth (Z.to_nat ((Z.shiftr r 41) mod Z.of_nat (length probe_sizes))) probe_sizes 16 in
gen f r (S nm) (live ++ [nm]) pfree (Malloc sz :: acc)
end.
Fixpoint gen_ans (fuel : nat) (seed : Z) (pr : Z) (acc : list (option Z)) : list (option Z) :=
match fuel with
| O => rev acc
| S f =>
let r := lcg seed in
let c := (Z.shiftr r 29) mod 100 in
gen_ans f r pr ((if c <? pr then Some 0 else if c <? pr + 20 then Some ((Z.shiftr r 13) mod 256) else None) :: acc)
end.
Definition campaign (seeds : list Z) (nops : nat) (pfree pr : Z) : list (Z * bool * option failure) :=
map (fun sd => check (gen_ans 2000 (sd + 7) pr []) (gen nops sd O [] pfree [])) seeds.
Fixpoint pingpong (n : nat) (k : nat) (sz : Z) : list op :=
match n with O => [] | S n' => Malloc sz :: Free k :: pingpong n' (S k) sz end.
Definition bounce_script : list op :=
pingpong 120 0 20000 ++
[Malloc 20000; Malloc 20000; Malloc 20000; Malloc 20000; Free 123; Free 120;
Malloc 20000; Malloc 20000; Malloc 20000; Free 121; Free 122; Free 124; Free 125; Free 126;
Malloc 20000; Malloc 18000; Malloc 20000; Free 128; Free 127; Free 129; Malloc 20000; Malloc 20000; Free 130]
++ pingpong 40 132 5000 ++ [Malloc 5000; Malloc 5000; Free 172; Malloc 5000; Free 173; Free 174].
Example wf_vec1 : check [] vec1_prefix = (23, true, None).
Proof. vm_compute. reflexivity. Qed.
Example wf_hdr_script : check [] hdr_script = (47, true, None).
Proof. vm_compute. reflexivity. Qed.
Example wf_bounce : check [] bounce_script = (350, true, None).
Proof. vm_compute. reflexivity. Qed.
Example wf_refusals :
map (fun ao => check (fst ao) (snd ao))
[([grant; refuse], [Malloc 4096; Malloc 100; Free 0; Free 1]);
([grant; grant; grant; refuse], [Malloc 4096; Malloc 4096; Free 1]);
([grant; grant; refuse; refuse], [Malloc 200000; Malloc 10; Malloc 200000; Free 2; Free 1]);
([grant; refuse; grant; refuse; refuse; grant], [Malloc 10; Malloc 10; Malloc 5000; Free 2; Free 1])]
= [(5, true, None); (4, true, None); (6, true, None); (6, true, None)].
Proof. vm_compute. reflexivity. Qed.
Example wf_random : campaign [23] 300 50 10 ++ campaign [31] 300 70 30
= [(301, true, None); (301, true, None)].
Proof. vm_compute. reflexivity. Qed.
Definition st1 : astate := sr_state (run_script [] [Malloc 100; Malloc 100; Malloc 5000; Malloc 200000; Free 0]).
Definition first_used (s : astate) : option (sptr * ameta) := hd_error (used_metas s).
Example wf_mutations :
(wfb st1,
wfb (set_usage (zset 6 (usage_of st1 6 + 1) (st_usage st1)) st1),
match first_used st1 with
| Some (g, am) => wfb (set_metas (mupdate (st_metas st1) g (MUsed (am_set_freed (Z.lor (am_freed am) 2) am))) st1)
| None => true
end,
wfb (set_active (lupd (st_active st1) 6%nat (Some (SP 0 0))) st1),
wfb (set_brk BrkNever st1))
= (true, false, false, false, false).
Proof. vm_compute. reflexivity. Qed.
Example st1_blocks :
user_blocks st1 = [(SP 1 176, 100); (SP 2 48, 5000); (SP 3 64, 200000)]
/\ footprint st1 = [(LCtx 0, 928); (LMem (SP 0 4096), 4096); (LMem (SP 1 0), 4096);
(LMem (SP 2 0), 16384); (LMem (SP 3 0), 200704)].
Proof. vm_compute. split; reflexivity. Qed.
Definition frames_ok (s : astate) : bool :=
forallb (fun f : sptr * ameta * Z * frame =>
let '(g, am, i, fr) := f in
get_meta_asserts (frame_ptr am i fr) (am_mem am) (view_of s g am i fr) &&
match find_frame_in (st_metas s) (frame_ptr am i fr) with
| Some (g', i') => sptr_eqb g g' && (i =? i')
| None => false
end)
(frames s).
Example get_meta_probe :
(frames_ok st1, let '(l, _) := states [] bounce_script in forallb frames_ok l,
let '(l, _) := states (gen_ans 2000 30 10 []) (gen 300 23 O [] 50 []) in forallb frames_ok l)
= (true, true, true).
Proof. vm_compute. reflexivity. Qed.
Fixpoint irun2 {A} (fuel : nat) (t : itree astate A) (kans jans : list (option Z)) (tr : list (kreq * Z))
: outcome A * list (kreq * Z) * list (option Z) * list (option Z) :=
match fuel with
| O => (OStarved, rev tr, kans, jans)
| S f =>
match t with
| IRet a => (ODone a, rev tr, kans, jans)
| IFail e => (OFailed e, rev tr, kans, jans)
| IAsk q _ k =>
match q with
| KJunk pristine =>
let z := match hd None jans with Some z => z | None => pristine end in
irun2 f (k z) kans (tl jans) ((q, z) :: tr)
| _ =>
let z := match hd None kans with Some z => z | None => 1 end in
irun2 f (k z) (tl kans) jans ((q, z) :: tr)
end
end
end.
Record srun2 := mkRun2 { s2_state : astate; s2_ptrs : list (option sptr); s2_trace : list (kreq * Z);
s2_kans : list (option Z); s2_jans : list (option Z); s2_err : option failure;
s2_hist : list astate }.
Definition run_op2 (r : srun2) (o : op) : srun2 :=
match s2_err r with
| Some _ => r
| None =>
let step := match o with
| Malloc n => match irun2 1000%nat (malloc n (s2_state r)) (s2_kans r) (s2_jans r) [] with
| (ODone (p, s'), tr, ka, ja) => (ODone (Some p, s'), tr, ka, ja)
| (OFailed e, tr, ka, ja) => (OFailed e, tr, ka, ja)
| (OStarved, tr, ka, ja) => (OStarved, tr, ka, ja)
end
| Free k => match irun2 1000%nat (free (nth k (s2_ptrs r) None) (s2_state r)) (s2_kans r) (s2_jans r) [] with
| (ODone (_, s'), tr, ka, ja) => (ODone (None, s'), tr, ka, ja)
| (OFailed e, tr, ka, ja) => (OFailed e, tr, ka, ja)
| (OStarved, tr, ka, ja) => (OStarved, tr, ka, ja)
end
| Realloc k n => match irun2 1000%nat (realloc (nth k (s2_ptrs r) None) n (s2_state r)) (s2_kans r) (s2_jans r) [] with
| (ODone (p, s'), tr, ka, ja) => (ODone (Some p, s'), tr, ka, ja)
| (OFailed e, tr, ka, ja) => (OFailed e, tr, ka, ja)
| (OStarved, tr, ka, ja) => (OStarved, tr, ka, ja)
end
end in
match step with
| (ODone (np, s'), tr, ka, ja) =>
mkRun2 s' (match np with Some p => s2_ptrs r ++ [p] | None => s2_ptrs r end)
(s2_trace r ++ tr) ka ja None (s2_hist r ++ [s'])
| (OFailed e, tr, ka, ja) => mkRun2 (s2_state r) (s2_ptrs r) (s2_trace r ++ tr) ka ja (Some e) (s2_hist r)
| (OStarved, tr, ka, ja) => mkRun2 (s2_state r) (s2_ptrs r) (s2_trace r ++ tr) ka ja (Some FFuel) (s2_hist r)
end
end.
Definition run_script2 (kans jans : list (option Z)) (ops : list op) : srun2 :=
fold_left run_op2 ops (mkRun2 init_state [] [] kans jans None [init_state]).
Definition kernel_only (tr : list (kreq * Z)) : list (kreq * Z) :=
filter (fun qz : kreq * Z => match fst qz with KJunk _ => false | _ => true end) tr.
Definition listZ_eqb (a b : list Z) : bool :=
Nat.eqb (length a) (length b) && forallb (fun p : Z * Z => fst p =? snd p) (combine a b).
Definition slot_eqb (a b : slotst) : bool :=
match ss_hdr a, ss_hdr b with
| Some (x1, y1), Some (x2, y2) => (x1 =? x2) && (y1 =? y2)
| None, None => true
| _, _ => false
end &&
match ss_fr a, ss_fr b with
| Some f1, Some f2 => (fr_off f1 =? fr_off f2) && (fr_n f1 =? fr_n f2) &&
match fr_kind f1, fr_kind f2 with FUser, FUser | FGroup, FGroup => true | _, _ => false end
| None, None => true
| _, _ => false
end.
Definition ameta_eqb (a b : ameta) : bool :=
osptr_eqb (am_prev a) (am_prev b) && osptr_eqb (am_next a) (am_next b) && sptr_eqb (am_mem a) (am_mem b) &&
(am_avail a =? am_avail b) && (am_freed a =? am_freed b) && (am_last a =? am_last b) && (am_sc a =? am_sc b) &&
(am_maplen a =? am_maplen b) && (am_aidx a =? am_aidx b) &&
Nat.eqb (length (am_slots a)) (length (am_slots b)) &&
forallb (fun p : slotst * slotst => slot_eqb (fst p) (snd p)) (combine (am_slots a) (am_slots b)).
Definition mslot_eqb (a b : mslot) : bool :=
match a, b with
| MFree p1 n1, MFree p2 n2 => osptr_eqb p1 p2 && osptr_eqb n1 n2
| MRaw, MRaw => true
| MUsed x, MUsed y => ameta_eqb x y
| _, _ => false
end.
Definition region_eqb (a b : region) : bool :=
match rg_kind a, rg_kind b with RkBrk, RkBrk | RkMetaRes, RkMetaRes | RkMap, RkMap => true | _, _ => false end &&
(rg_len a =? rg_len b) && Bool.eqb (rg_live a) (rg_live b) && listZ_eqb (rg_rw a) (rg_rw b).
Definition brk_eqb (a b : brkst) : bool :=
match a, b with
| BrkNever, BrkNever | BrkDead, BrkDead => true
| BrkCur r p, BrkCur r' p' => Nat.eqb r r' && (p =? p')
| _, _ => false
end.
Definition astate_eqb (a b : astate) : bool :=
Bool.eqb (st_init_done a) (st_init_done b) && (st_mmap_counter a =? st_mmap_counter b) &&
osptr_eqb (st_free_meta_head a) (st_free_meta_head b) && sptr_eqb (st_avail_meta a) (st_avail_meta b) &&
(st_avail_meta_count a =? st_avail_meta_count b) && (st_avail_meta_area_count a =? st_avail_meta_area_count b) &&
(st_meta_alloc_shift a =? st_meta_alloc_shift b) && osptr_eqb (st_area_head a) (st_area_head b) &&
osptr_eqb (st_area_tail a) (st_area_tail b) && sptr_eqb (st_avail_meta_areas a) (st_avail_meta_areas b) &&
Nat.eqb (length (st_active a)) (length (st_active b)) &&
forallb (fun p : option sptr * option sptr => osptr_eqb (fst p) (snd p)) (combine (st_active a) (st_active b)) &&
listZ_eqb (st_usage a) (st_usage b) && listZ_eqb (st_unmap_seq a) (st_unmap_seq b) &&
listZ_eqb (st_bounces a) (st_bounces b) && (st_seq a =? st_seq b) && brk_eqb (st_brk a) (st_brk b) &&
Nat.eqb (length (st_metas a)) (length (st_metas b)) &&
forallb (fun p : (sptr * mslot) * (sptr * mslot) =>
sptr_eqb (fst (fst p)) (fst (snd p)) && mslot_eqb (snd (fst p)) (snd (snd p)))
(combine (st_metas a) (st_metas b)) &&
Nat.eqb (length (st_regions a)) (length (st_regions b)) &&
forallb (fun p : region * region => region_eqb (fst p) (snd p)) (combine (st_regions a) (st_regions b)) &&
Nat.eqb (length (st_areas a)) (length (st_areas b)) &&
forallb (fun p : sptr * sptr => sptr_eqb (fst p) (snd p)) (combine (st_areas a) (st_areas b)).
Fixpoint states_eqb (l1 l2 : list astate) : bool :=
match l1, l2 with
| [], [] => true
| a :: t1, b :: t2 => astate_eqb a b && states_eqb t1 t2
| _, _ => false
end.
Definition kreq_eqb (q1 q2 : kreq) : bool :=
match q1, q2 with
| KBrkQuery, KBrkQuery | KGuard, KGuard => true
| KBrkGrow x, KBrkGrow y | KMmapRW x, KMmapRW y | KMmapNone x, KMmapNone y => x =? y
| KMprotect p, KMprotect p' => sptr_eqb p p'
| KMunmap r l, KMunmap r' l' => Nat.eqb r r' && (l =? l')
| KJunk x, KJunk y => x =? y
| _, _ => false
end.
Fixpoint trace_eqb (a b : list (kreq * Z)) : bool :=
match a, b with
| [], [] => true
| (q1, z1) :: t1, (q2, z2) :: t2 => kreq_eqb q1 q2 && (z1 =? z2) && trace_eqb t1 t2
| _, _ => false
end.
Fixpoint gen_junk (fuel : nat) (seed : Z) (acc : list (option Z)) : list (option Z) :=
match fuel with
| O => rev acc
| S f => let r := lcg seed in gen_junk f r (Some ((Z.shiftr r 21) mod 256) :: acc)
end.
Fixpoint gen_kans (fuel : nat) (seed : Z) (pr : Z) (acc : list (option Z)) : list (option Z) :=
match fuel with
| O => rev acc
| S f => let r := lcg seed in gen_kans f r pr ((if (Z.shiftr r 29) mod 100 <? pr then Some 0 else None) :: acc)
end.
Definition shape_probe (kans jans1 jans2 : list (option Z)) (ops : list op) :=
let r1 := run_script2 kans jans1 ops in
let r2 := run_script2 kans jans2 ops in
(match s2_err r1, s2_err r2 with None, None => true | _, _ => false end,
Z.of_nat (length (s2_hist r1)),
trace_eqb (kernel_only (s2_trace r1)) (kernel_only (s2_trace r2)),
states_eqb (map erase (s2_hist r1)) (map erase (s2_hist r2)),
negb (states_eqb (s2_hist r1) (s2_hist r2)),
forallb (fun p : option sptr * option sptr =>
match fst p, snd p with None, None | Some _, Some _ => true | _, _ => false end)
(combine (s2_ptrs r1) (s2_ptrs r2)),
Z.of_nat (length (s2_trace r1) - length (kernel_only (s2_trace r1)))).
Example shape_eq_probe :
map (fun sd => shape_probe (gen_kans 3000 (sd + 3) 10 []) (gen_junk 500 (sd + 100) []) (gen_junk 500 (sd + 200) [])
(gen 300 sd O [] 50 []))
[21; 44]
= [(true, 301, true, true, true, true, 19); (true, 301, true, true, true, true, 19)].
Proof. vm_compute. reflexivity. Qed.
Definition no_single_slot_map (sc : Z) : bool :=
let st_b (b : Z) := set_bounces (repeat b 32) init_state in
let size := class_size sc in
let lo := if sc =? 0 then 0 else class_size (sc - 1) - IB + 1 in
let hi := size - IB in
let cands := filter (fun r => (lo <=? r) && (r <=? hi))
(lo :: hi :: flat_map (fun k => [PGSZ * k - 21; PGSZ * k - 20; PGSZ * k - 19]) (zseq 1 3)) in
forallb (fun usage =>
let s := set_usage (zset sc usage (repeat 0 48)) (st_b 0) in
let s' := set_usage (zset sc usage (repeat 0 48)) (st_b 150) in
let cnt0 := initial_cnt sc usage in
if PGSZ / 2 <? size * cnt0 + UNIT then
forallb (fun req => (2 <=? fst (mmap_plan s sc req cnt0 usage)) && (2 <=? fst (mmap_plan s' sc req cnt0 usage)))
cands
else true) (zseq 0 141).
Example no_single_slot_map_le_26 : forallb no_single_slot_map (zseq 0 27) = true.
Proof. vm_compute. reflexivity. Qed.
End Probes.
