(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0n.v, with its module paths changed. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/YG0n.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YP09 YK04 YA0i YA0n YK08.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YK0g.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section u. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aview (segs : list Segment) (H : word -> bool) (mem : word -> option byte) : reader :=
fun a => option_map (fun b => bv_unsigned b) (mbyte segs (mrestrict H mem) a).
Lemma aview_ext : forall segs H H' mem,
H_off_segments segs H -> hsub H' H -> rd_ext (aview segs H mem) (aview segs H' mem).
Proof.
intros segs H H' mem Hoff Hs a v. unfold aview, mbyte, mrestrict.
destruct (H (Z_to_bv 64 a)) eqn:E.
- unfold seg_rom. rewrite (memory_read1_hidden segs H Hoff _ E). cbn. discriminate.
- destruct (H' (Z_to_bv 64 a)) eqn:E'; [rewrite (Hs _ E') in E; discriminate|]. intros Hv; exact Hv.
Qed.
Definition apresent (H : word -> bool) (mem : word -> option byte) (a : Z) : Prop :=
H (Z_to_bv 64 a) = false /\ exists b, mem (Z_to_bv 64 a) = Some b.
Section y.
Variable B : asyms.
Variable ly : alayout.
Local Notation "e +! d" := (aoff e d) (at level 50, left associativity).
Definition region_cells (S : astate) (c : Z) : list acell :=
let r := reg S c in let R := ASp (kRegionInfoOff + 128 * c) in
[ z8 R 0; z8 (R +! 8) 0; z8 (R +! 16) (fa_len (rg_free r)); z8 (R +! 24) (rg_mapped_fa r);
z8 (R +! 32) (rg_alloc_user r); z8 (R +! 40) 0; z8 (R +! 48) (rg_mapped_user r); z8 (R +! 56) 0;
z1 (R +! 68) 0 ].
Definition region_junk (c : Z) : list (aexp * Z) :=
let R := ASp (kRegionInfoOff + 128 * c) in [(R +! 64, 4); (R +! 69, 3); (R +! 72, 56)].
Definition cache_cells (S : astate) (c : Z) : list acell :=
let p := cache S c in let P := AT (t_cache + 80 * c) in
if st_cache_inited S then
z4 P (Z.of_nat (length (pc_chunks p))) :: z4 (P +! 4) (max_cached c) :: z8 (P +! 8) (class_size c)
:: map (fun iv => z4 (P +! (16 + 4 * Z.of_nat (fst iv))) (snd iv / 16)) (combine (seq 0 (length (pc_chunks p))) (pc_chunks p))
else [z4 P 0; z4 (P +! 4) 0; z8 (P +! 8) 0].
Definition cache_junk (S : astate) (c : Z) : list (aexp * Z) :=
let n := (if st_cache_inited S then Z.of_nat (length (pc_chunks (cache S c))) else 0) in
[(AT (t_cache + 80 * c + 16 + 4 * n), 64 - 4 * n)].
Definition hdr_state (k : chunk) : Z := match ck_state k with CAllocated => 2 | CQuarantined => 3 end.
Definition chunk_cells (k : chunk) : list acell :=
let a := sptr_exp (ck_beg k) in let h := a +! (ck_rz k - kChunkHeaderSize) in
[ z1 h (hdr_state k); ACell (h +! 1) 1 (AVmask 127 17)  ; z2 (h +! 2) 0; z4 (h +! 4) (ck_n k) ]
++ (if ck_rz k =? kChunkHeaderSize then [] else [ z8 a 0xCC6E96B9CC6E96B9; c8 (a +! 8) h ]).
Definition chunk_junk (k : chunk) : list (aexp * Z) :=
let a := sptr_exp (ck_beg k) in let rz := ck_rz k in let n := ck_n k in
(if rz =? kChunkHeaderSize then [] else [(a +! 16, rz - 16 - kChunkHeaderSize)])
++ [(a +! (rz - 8), 8)]
++ (match ck_state k with CAllocated => [] | CQuarantined => [(a +! rz, n)] end)
++ [(a +! (rz + n), ck_extent k - rz - n)].
Definition chunk_user (k : chunk) : list (aexp * Z) :=
match ck_state k with CAllocated => [(sptr_exp (ck_user k), ck_n k)] | CQuarantined => [] end.
Definition index_ofZ (l : list nat) (r : nat) : Z :=
match index_of l r 0%nat with Some i => Z.of_nat i | None => 0 end.
Definition sec_cells (S : astate) : list acell :=
c8 (AInst o_sec_reserved) (ANum (st_sec_reserved S)) :: z8 (AInst o_sec_n) (Z.of_nat (length (st_sec_arr S)))
:: z1 (AInst o_sec_mutex) 0
:: map (fun ir => c8 (AQ (8 * Z.of_nat (fst ir))) (ASec (snd ir) 0)) (combine (seq 0 (length (st_sec_arr S))) (st_sec_arr S))
++ flat_map (fun k => match ck_beg k with
| PSec r _ => [ c8 (ASec r 0) (ASec r 0); z8 (ASec r 8) (sec_map_size (ck_req k));
z8 (ASec r 16) (needed_size (ck_req k)); z8 (ASec r 24) (index_ofZ (st_sec_arr S) r) ]
| _ => [] end) (st_chunks S).
Definition sec_junk (S : astate) : list (aexp * Z) :=
(AInst o_sec_sorted, 1) :: (AInst o_sec_stats, o_sec_mutex - o_sec_stats)
:: (AQ (8 * Z.of_nat (length (st_sec_arr S))), 8 * (st_sec_reserved S - Z.of_nat (length (st_sec_arr S))))
:: flat_map (fun k => match ck_beg k with PSec r _ => [(ASec r 32, kPage - 32)] | _ => [] end) (st_chunks S).
Definition batch_exp (b : batch) : aexp := ASp (b_self b).
Fixpoint batch_cells (l : list batch) : list acell :=
match l with
| [] => []
| b :: t =>
c8 (batch_exp b) (match t with [] => ANum 0 | b' :: _ => batch_exp b' end)
:: z8 (batch_exp b +! 8) (b_bytes b) :: z8 (batch_exp b +! 16) (Z.of_nat (length (b_items b)))
:: map (fun iv => c8 (batch_exp b +! (24 + 8 * Z.of_nat (fst iv))) (sptr_exp (ck_hdr (snd iv))))
(combine (seq 0 (length (b_items b))) (b_items b))
++ batch_cells t
end.
Definition batch_junk (b : batch) : list (aexp * Z) :=
[(batch_exp b +! (24 + 8 * Z.of_nat (length (b_items b))), kBatchBytes - 24 - 8 * Z.of_nat (length (b_items b)))].
Definition qc_cells (root : aexp) (q : qcache) : list acell :=
z8 root (Z.of_nat (length (qc_list q)))
:: c8 (root +! 8) (match qc_list q with [] => ANum 0 | b :: _ => batch_exp b end)
:: c8 (root +! 16) (match rev (qc_list q) with [] => ANum 0 | b :: _ => batch_exp b end)
:: z8 (root +! 24) (qc_bytes q)
:: batch_cells (qc_list q).
Definition quar_cells (S : astate) : list acell :=
z1 (AInst o_q_cmutex) 0 :: z1 (AInst o_q_rmutex) 0
:: qc_cells (AT t_qc) (st_qthread S) ++ qc_cells (AInst o_q_size) (st_qglobal S).
Definition quar_junk (S : astate) : list (aexp * Z) := flat_map batch_junk (all_batches S).
Definition fs_cells (S : astate) : list acell :=
z8 (AF 88) kStackSizeLog :: z1 (AF 96) 0
:: map (fun iv => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) (combine (seq 0 11) (fs_hint (st_fs S))).
Definition depot_cells (S : astate) : list acell :=
[ z4 (ADepot d_nuniq) (depot_ids S); c8 (ADepot d_map1) (ANB 0);
z8 (AStore s_total) (Z.of_nat (length (ly_tr0 ly)) + 1 + depot_frames S); c8 (AStore s_block0) (ASB 0) ].
Definition ialloc_cells (S : astate) : list acell :=
let w := as_ialloc_w B - as_ialloc_lo B in
[ z1 (ANum (as_ialloc_flag B)) (if st_internal_inited S then 1 else 0); z1 (ANum (as_ialloc_flag B + 1)) 0;
z8 (AIal w) (if st_internal_inited S then 4096 else 0);
c8 (AIal (w + 8)) (if st_internal_inited S then AIal (w + 16) else ANum 0) ].
Definition ialloc_zero : list (aexp * Z) :=
let w := as_ialloc_w B - as_ialloc_lo B in
[ (AIal 0, w); (AIal (w + 16), as_ialloc_hi B - as_ialloc_lo B - w - 16) ].
Definition thread_cells : list acell := [ z1 (AT t_unwinding) 0 ].
Definition thread_junk : list (aexp * Z) :=
[ (AT t_cache, 80)  ; (AT t_cache_stats, t_stats - t_cache_stats); (AT t_stats, t_unwinding - t_stats);
(AT (t_unwinding + 1), kThreadObjSize - t_unwinding - 1) ].
Definition zseq (lo n : Z) : list Z := map (fun k => lo + Z.of_nat k) (seq 0 (Z.to_nat n)).
Definition acells (S : astate) : list acell :=
flat_map (region_cells S) (zseq 1 31) ++ flat_map (cache_cells S) (zseq 1 31)
++ flat_map chunk_cells (st_chunks S) ++ sec_cells S ++ quar_cells S ++ fs_cells S ++ depot_cells S
++ ialloc_cells S ++ thread_cells.
Definition ajunk (S : astate) : list (aexp * Z) :=
(ASp kRegionInfoOff, 128)   :: (ASp (kRegionInfoOff + 128 * 32), 0) ::
flat_map region_junk (zseq 1 31) ++ flat_map (cache_junk S) (zseq 1 31)
++ flat_map chunk_junk (st_chunks S) ++ sec_junk S ++ quar_junk S ++ thread_junk
++ [(ANum (as_oom_byte B), 1); (ADepot (d_nuniq + 4), 12); (AStore 8, 8); (AStore 24, 8)]
++ as_junk B ly.
Definition aclient (S : astate) : list (aexp * Z) :=
flat_map chunk_user (st_chunks S)
++ map (fun cp => (AF (fs_frame_off (fst cp) (snd cp)), fs_frame_bytes (fst cp))) (frames S)
++ map (fun cp => (ASh (AF (fs_frame_off (fst cp) (snd cp))), fs_frame_bytes (fst cp) / 8)) (frames S).
Definition aareas (S : astate) : list (aexp * Z) :=
flat_map (fun c => [(ASp (region_off c), rg_mapped_user (reg S c)); (ASp (region_off c + kFreeArrayOffset), rg_mapped_fa (reg S c))]) (zseq 1 31)
++ [(AQ 0, 8 * st_sec_reserved S)]
++ flat_map (fun k => match ck_beg k with PSec r _ => [(ASec r 0, sec_map_size (ck_req k))] | _ => [] end) (st_chunks S)
++ [(AF 0, kFakeStackSize); (ANB 0, kNodesBlockSize); (ASB 0, kStoreBlockSize); (AT 0, kThreadObjSize);
(ASp kRegionInfoOff, 4096);
(ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8)].
Fixpoint fa_nth (sz : Z) (l : list fseg) (j : Z) : option Z :=
match l with
| [] => None
| FOne o :: t => if j =? 0 then Some o else fa_nth sz t (j - 1)
| FRun lo k :: t => if j <? k then Some (lo + j * sz) else fa_nth sz t (j - k)
end.
Definition rd32 (rd : reader) (a v : Z) : Prop := forall k, (k < 4)%nat -> rd (a + Z.of_nat k) = Some (le_byte v 4 k).
Definition rd64 (rd : reader) (a v : Z) : Prop := forall k, (k < 8)%nat -> rd (a + Z.of_nat k) = Some (le_byte v 8 k).
Definition fa_entries_ok (rd : reader) (S : astate) : Prop :=
forall c i v, 1 <= c <= 31 -> 0 <= i < fa_len (rg_free (reg S c)) ->
fa_nth (class_size c) (rg_free (reg S c)) (fa_len (rg_free (reg S c)) - 1 - i) = Some v ->
rd32 rd (fa_base ly c + 4 * i) (v / 16).
Definition fs_flags_ok (rd : reader) (S : astate) : Prop :=
forall cid pos, 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
rd (flag_addr ly cid pos) = Some (if mem_pos (frames S) cid pos then 1 else 0).
Definition depot_traces (S : astate) : list (list Z) := ly_tr0 ly :: st_depot S.
Fixpoint chain_has (links : Z -> Z) (hashes : Z -> Z) (fuel : nat) (id h : Z) : Prop :=
match fuel with
| O => False
| S f => id <> 0 /\ (hashes id = h \/ chain_has links hashes f (links id) h)
end.
Definition depot_ok (rd : reader) (S : astate) : Prop :=
exists (heads : Z -> Z) (links : Z -> Z),
let n := depot_ids S in
let hashes := fun id => as_dhash B (nth (Z.to_nat (id - 1)) (depot_traces S) []) in
(forall b, 0 <= b < d_tab_words -> 0 <= heads b <= n /\ rd32 rd (as_depot B + 4 * b) (heads b)) /\
(forall id, 1 <= id <= n -> 0 <= links id < id /\
rd64 rd (ly_NB ly + 16 * id) (hashes id mod 2 ^ 64) /\ rd32 rd (ly_NB ly + 16 * id + 8) (links id)) /\
(forall id, 1 <= id <= n ->
chain_has links hashes (Z.to_nat n) (heads ((hashes id mod 2 ^ 64) mod d_tab_words)) (hashes id)).
Definition ck_base (k : chunk) : Z := sptr_addr B ly (ck_beg k).
Fixpoint find_chunk_at (l : list chunk) (a : Z) : option chunk :=
match l with
| [] => None
| k :: t => if (ck_base k <=? a) && (a <? ck_base k + ck_extent k) then Some k else find_chunk_at t a
end.
Fixpoint in_rangesb (a : Z) (l : list (Z * Z)) : bool :=
match l with [] => false | (lo, len) :: t => ((lo <=? a) && (a <? lo + len)) || in_rangesb a t end.
Definition fa_poison_ranges (S : astate) : list (Z * Z) :=
flat_map (fun c => [(region_base ly c, rg_mapped_user (reg S c)); (fa_base ly c, rg_mapped_fa (reg S c))]) (zseq 1 31)
++ flat_map (fun k => match ck_beg k with PSec r _ => [(ly_sec ly r, sec_map_size (ck_req k))] | _ => [] end) (st_chunks S).
Definition ashadow (S : astate) (g : Z) : option Z :=
match find_chunk_at (st_chunks S) g with
| Some k => Some (chunk_granule k ((g - ck_base k) / 8))
| None => if in_rangesb g (fa_poison_ranges S) then Some shHeapLeftRz else None
end.
Definition shadow_ok (rd : reader) (S : astate) : Prop :=
forall g v, g mod 8 = 0 -> ashadow S g = Some v -> rd (shadow_addr g) = Some v.
Definition zero_shadow_ranges : list (Z * Z) :=
(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) :: as_zero_shadow B.
Definition zshadow_ok (rd : reader) : Prop :=
Forall (fun r => zero_shadow rd SHADOW_OFF (fst r) (snd r)) zero_shadow_ranges.
Definition sec_extents (S : astate) : list (Z * Z) :=
flat_map (fun k => match ck_beg k with PSec r _ => [(ly_sec ly r, sec_map_size (ck_req k))] | _ => [] end) (st_chunks S).
Definition sec_placed (S : astate) : Prop :=
Forall (fun e => page_aligned (fst e) /\ in_app (fst e) (snd e) /\ fst e + snd e <= alloc_ceiling) (sec_extents S) /\
pairwise zdisjoint (sec_extents S ++ static_extents ly).
Definition in_zr (a : Z) (r : Z * Z) : Prop := fst r <= a < fst r + snd r.
Definition core_extents : list (Z * Z) :=
[(ly_Q ly, kPtrArrayResv); (ly_T ly, kThreadObjSize); (ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize); (ly_C ly, 256);
(ly_D ly, 4096)  ].
Definition owned_core (a : Z) : Prop := Exists (in_zr a) (as_owned_static B) \/ Exists (in_zr a) core_extents
\/ Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (as_owned_static B).
Definition cell_owned (c : acell) : Prop :=
forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> owned_core (aeval B ly (c_at c) + k).
Record ARm (S : astate) (rd : reader) : Prop := {
am_wf : Wf (as_universe B) S;
am_universe : universe_ok (as_universe B);
am_syms : asyms_ok B;
am_layout : layout_ok ly;
am_placed : sec_placed S;
am_const : Forall (cell_holds B ly rd) (as_const B ly);
am_const_owned : Forall cell_owned (as_const B ly);
am_cells : Forall (cell_holds B ly rd) (acells S);
am_fa : fa_entries_ok rd S;
am_flags : fs_flags_ok rd S;
am_depot : depot_ok rd S;
am_shadow : shadow_ok rd S;
am_zshadow : zshadow_ok rd;
am_junk : Forall (range_vis B ly rd) (ajunk S);
am_areas : Forall (range_vis B ly rd) (aareas S);
am_client : Forall (range_vis B ly rd) (aclient S);
am_zero : Forall (range_zero B ly rd) ialloc_zero;
am_tsd : ly_tsd ly = as_tsd B;
am_static_img : Forall (fun r => zr_sub r (ly_img ly)) (as_owned_static B ++ as_zero_shadow B)
}.
Definition hm_zone : Z * Z := (kHighMemBeg, kHighMemEnd - kHighMemBeg).
Definition lm_zone : Z * Z := (0, kLowMemEnd).
Lemma hm_zone_shadow : shadow_addr (fst hm_zone) = kHighShadowBeg /\ shadow_addr (fst hm_zone) + (snd hm_zone + 7) / 8 = kHighShadowEnd.
Proof. split; reflexivity. Qed.
Definition aclient_byte (S : astate) (a : Z) : Prop :=
(exists k, In k (st_chunks S) /\ ck_state k = CAllocated /\
sptr_addr B ly (ck_user k) <= a < sptr_addr B ly (ck_user k) + ck_n k) \/
(exists cp, In cp (frames S) /\
(in_zr a (frame_addr ly (fst cp) (snd cp), fs_frame_bytes (fst cp)) \/
in_zr a (shadow_addr (frame_addr ly (fst cp) (snd cp)), fs_frame_bytes (fst cp) / 8))).
Definition aowned (S : astate) (a : Z) : Prop :=
( Exists (in_zr a) (as_owned_static B)
\/ Exists (in_zr a) (owned_extents ly)
\/ in_zr a (ly_C ly, 256)
\/ Exists (in_zr a) (sec_extents S)
\/ Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents S ++ zero_shadow_ranges ++ as_owned_static B ++ [hm_zone; lm_zone]) )
/\ ~ aclient_byte S a.
End y.
Lemma kHighMemBeg_plc : YK08.kHighMemBeg = kHighMemBeg.
Proof. reflexivity. Qed.
Definition band_maps : list (Z * Z) :=
[(kLowShadowBeg, kLowShadowEnd - kLowShadowBeg); (kLowShadowEnd, kHighShadowBeg - kLowShadowEnd); (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)].
Definition seg_resv_z (sg : Segment) : Z * Z :=
let lo := page_round_down_Z (Z.of_N (seg_base sg)) in
let hi := page_round_up_Z (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) in (lo, hi - lo).
Fixpoint tiles_b (l : list (Z * Z)) (lo hi : Z) : bool :=
match l with
| [] => Z.leb hi lo
| e :: t => Z.eqb (fst e) lo && Z.leb 0 (snd e) && Z.ltb (lo + snd e) (2 ^ 64) && tiles_b t (lo + snd e) hi
end.
Definition img_covered_b (segs : list Segment) (img : Z * Z) : bool :=
Z.leb 0 (fst img) && tiles_b (map seg_resv_z segs) (fst img) (fst img + snd img).
Lemma tiles_b_cover : forall l lo hi a, 0 <= lo -> tiles_b l lo hi = true -> lo <= a < hi ->
exists e, In e l /\ fst e <= a < fst e + snd e /\ 0 <= fst e /\ fst e + snd e < 2 ^ 64.
Proof.
induction l as [|e t IH]; intros lo hi a Hlo Ht Ha; cbn [tiles_b] in Ht.
- apply Z.leb_le in Ht. lia.
- apply andb_prop in Ht as [Ht H4]. apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
destruct (Z_lt_le_dec a (lo + snd e)) as [X|X].
+ exists e. split; [left; reflexivity|]. lia.
+ destruct (IH (lo + snd e) hi a ltac:(lia) H4 ltac:(lia)) as (e' & He' & R). exists e'. split; [right; exact He' | exact R].
Qed.
Lemma img_covered_b_ok : forall segs img, img_covered_b segs img = true ->
forall a, in_zr a img -> exists e, In e (segments_reserved segs) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros segs img Hc a Ha. unfold img_covered_b in Hc. apply andb_prop in Hc as [H0 Ht]. apply Z.leb_le in H0. unfold in_zr in Ha.
destruct (tiles_b_cover _ _ _ a H0 Ht Ha) as (e & He & R1 & R2 & R3). apply in_map_iff in He as (sg & <- & Hsg).
exists (segment_reservation sg). split; [unfold segments_reserved; apply in_map; exact Hsg|].
unfold segment_reservation, seg_resv_z in *. cbn [fst snd] in *. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Section a0.
Variable segs : list Segment.
Variable B : asyms.
Variable ly : alayout.
Definition w64 (z : Z) : word := Z_to_bv 64 z.
Definition wiv (r : Z * Z) : word * word := (w64 (fst r), w64 (snd r)).
Definition ASAN_VM_LIMIT : Z := 2 ^ 39.
Definition ASAN_VM_LMIN : Z := 2 ^ 39.
Definition E_BASE : Z := 2 ^ 30.
Definition prim_committed_at (S : astate) (a : Z) : Prop :=
in_zr a (ly_rinfo ly, 4096) \/
exists c, 1 <= c <= 31 /\ (in_zr a (region_base ly c, rg_mapped_user (reg S c)) \/ in_zr a (fa_base ly c, rg_mapped_fa (reg S c))).
Definition prim_hole_at (S : astate) (a : Z) : Prop :=
exists c h, 1 <= c <= 31 /\ In h (rg_holes (reg S c)) /\ in_zr a (region_base ly c + fst h, snd h).
Definition cut_ok (S : astate) (x : Z) : Prop :=
x = ly_prim ly \/ x = ly_prim ly + kPrimResvSize \/
exists c, 1 <= c <= 31 /\
((exists k, x = region_base ly c + kUserMapSize * k /\ 0 <= kUserMapSize * k <= rg_mapped_user (reg S c) + kUserMapSize) \/
(exists k, x = fa_base ly c + kFreeArrayMapSize * k /\ 0 <= kFreeArrayMapSize * k <= rg_mapped_fa (reg S c) + kFreeArrayMapSize)).
Definition prim_pieces_ok (S : astate) (pieces : list (Z * Z)) : Prop :=
Forall (fun p => 0 < snd p /\ cut_ok S (fst p) /\ cut_ok S (fst p + snd p)) pieces /\
pairwise zdisjoint pieces /\
(forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> (Exists (in_zr a) pieces <-> ~ prim_hole_at S a)).
Definition lazy_zones : list (Z * Z) :=
[(kLowShadowBeg, kLowShadowEnd - kLowShadowBeg); (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg);
(kLowShadowEnd, kHighShadowBeg - kLowShadowEnd); (ly_SB ly, kStoreBlockSize); (ly_prim ly, kPrimResvSize);
(ly_Q ly, kPtrArrayResv);
(ly_C ly, kCtxMapSize)  ]
++ ly_extra ly ++ static_extents ly.
Definition perm_maps : list (Z * Z) :=
[(ly_T ly, kThreadObjSize); (ly_F ly, kFakeStackSize); (ly_NB ly, kNodesBlockSize); (ly_SB ly, kStoreBlockSize);
(ly_C ly, kCtxMapSize); (ly_D ly, 4096)] ++ ly_extra ly.
Definition esec (na lz : list (word * word)) (E : list (Z * Z)) : Z :=
YK0g.sum_count (fun x => negb (YK0g.covered (na ++ lz) x)) (map wiv E).
Record ALedger (S : astate) (md : Model) : Prop := {
al_img : forall sg, In sg segs -> fst (ly_img ly) <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= fst (ly_img ly) + snd (ly_img ly);
al_limit : ASAN_VM_LMIN <= vm_limit (m_vmmaps md);
al_reserved : vm_reserved (m_vmmaps md) = segments_reserved segs;
al_prim : exists pieces, prim_pieces_ok S pieces /\
(forall p, In p pieces <-> (In (wiv p) (vm_maps (m_vmmaps md)) /\ 0 < snd p /\ ly_prim ly <= fst p /\ fst p + snd p <= ly_prim ly + kPrimResvSize));
al_Q : In (wiv (ly_Q ly, kPtrArrayResv)) (vm_maps (m_vmmaps md));
al_hs : In (wiv (kHighShadowBeg, kHighShadowEnd - kHighShadowBeg)) (vm_maps (m_vmmaps md));
al_sec : forall e, In e (sec_extents ly S) -> In (wiv e) (vm_maps (m_vmmaps md));
al_cover : forall e, In e (vm_maps (m_vmmaps md)) ->
Exists (fun z => fst z <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= fst z + snd z)
(lazy_zones ++ sec_extents ly S);
al_eager_x : eager_used md <= E_BASE + prim_committed S + 8 * st_sec_reserved S
+ esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S);
al_perm : forall z, In z perm_maps -> In (wiv z) (vm_maps (m_vmmaps md));
al_band : forall z, In z band_maps -> In (wiv z) (vm_maps (m_vmmaps md));
al_secx : forall e z, In e (sec_extents ly S) -> In z perm_maps -> zdisjoint e z;
al_top : YM05.ceil_of_top (alloc_top (m_vmmaps md));
al_imgcov : forall a, in_zr a (ly_img ly) ->
exists e, In e (segments_reserved segs) /\ bv_unsigned (fst e) <= a < bv_unsigned (fst e) + bv_unsigned (snd e);
al_shna : region_free (vm_noaccess (m_vmmaps md)) (w64 kLowShadowBeg) (w64 (kLowShadowEnd - kLowShadowBeg)) = true /\
region_free (vm_noaccess (m_vmmaps md)) (w64 kHighShadowBeg) (w64 (kHighShadowEnd - kHighShadowBeg)) = true
}.
Lemma ceil_top_init_sp_ok : forall md, YM05.ceil_of_top (alloc_top (m_vmmaps md)) -> YK06.init_sp_ok (m_vmmaps md).
Proof.
intros md CT. pose proof (YM05.ceil_le_top _ CT) as LE. pose proof (proj1 alloc_ceiling_val) as [CV _].
unfold YK06.init_sp_ok, alloc_top, stack_max_size, sp_window_lo in *. lia.
Qed.
Lemma al_init_sp_ok : forall S md, ALedger S md -> YK06.init_sp_ok (m_vmmaps md).
Proof. intros S md L. exact (ceil_top_init_sp_ok md (al_top _ _ L)). Qed.
Lemma esec_nil : forall na lz, esec na lz [] = 0.
Proof. reflexivity. Qed.
Lemma esec_cons : forall na lz e E, esec na lz (e :: E) = YK0g.iv_count (fun x => negb (YK0g.covered (na ++ lz) x)) (wiv e) + esec na lz E.
Proof. reflexivity. Qed.
Lemma esec_app : forall na lz E1 E2, esec na lz (E1 ++ E2) = esec na lz E1 + esec na lz E2.
Proof. intros na lz E1 E2. unfold esec. rewrite map_app. apply YK0g.sum_count_app. Qed.
Lemma esec_nonneg : forall na lz E, 0 <= esec na lz E.
Proof. intros na lz E. unfold esec. apply YK0g.sum_count_nonneg. Qed.
Lemma esec_one_le : forall na lz e, 0 <= snd e < 2 ^ 64 -> esec na lz [e] <= snd e.
Proof.
intros na lz e He. unfold esec. cbn [map YK0g.sum_count]. rewrite Z.add_0_r.
unfold YK0g.iv_count. pose proof (YK0g.zcount_le_len (fun x => negb (YK0g.covered (na ++ lz) x)) (YK0g.B (wiv e)) (Z.to_nat (YK0g.S (wiv e)))) as X.
unfold YK0g.S, wiv in X |- *. cbn [snd] in X |- *. unfold w64 in X |- *. rewrite Z_to_bv_unsigned, bv_wrap_small in X |- * by (unfold bv_modulus; lia).
rewrite Z2Nat.id in X by lia. exact X.
Qed.
Lemma esec_ext : forall na lz na' lz' E,
Forall (fun e => 0 <= fst e /\ 0 <= snd e /\ fst e + snd e < 2 ^ 64) E ->
(forall e x, In e E -> fst e <= x < fst e + snd e ->
YK0g.covered (na' ++ lz') x = YK0g.covered (na ++ lz) x) ->
esec na' lz' E = esec na lz E.
Proof.
intros na lz na' lz' E HB HC. induction E as [|e E IH]; [reflexivity|].
apply Forall_cons_iff in HB as [(B1 & B2 & B3) HB]. rewrite !esec_cons. rewrite IH; [| exact HB | intros e' x He' Hx; apply (HC e' x (or_intror He') Hx)].
f_equal. unfold YK0g.iv_count. apply YK0g.zcount_ext. intros x Hx. f_equal. symmetry.
unfold YK0g.B, YK0g.S, wiv, w64 in Hx. cbn [fst snd] in Hx.
rewrite !Z_to_bv_unsigned, !bv_wrap_small in Hx by (unfold bv_modulus; lia). rewrite Z2Nat.id in Hx by lia.
symmetry. apply (HC e x (or_introl eq_refl)). lia.
Qed.
Lemma sec_extents_sizes_sum : forall S,
Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents ly S) -> forall na lz, esec na lz (sec_extents ly S) <= sec_live_bytes S.
Proof.
intros S HF na lz. unfold sec_live_bytes, sec_extents in *. induction (st_chunks S) as [|k t IH]; [cbn; lia|].
cbn [flat_map fold_right] in *. destruct (ck_beg k) as [| |r o|]; cbn [app] in *; try (apply IH; exact HF).
apply Forall_cons_iff in HF as [H1 HF]. change ((ly_sec ly r, sec_map_size (ck_req k)) :: ?t) with ([(ly_sec ly r, sec_map_size (ck_req k))] ++ t).
rewrite esec_app. pose proof (esec_one_le na lz (ly_sec ly r, sec_map_size (ck_req k)) H1) as X. cbn [snd] in X. specialize (IH HF). lia.
Qed.
End a0.
Definition A_BASE : Z := 2 ^ 32.
Definition EV_A : Z := 2 ^ 20.
Section b0.
Variable segs : list Segment.
Variable B : asyms.
Definition abudget (S : astate) : Z := A_BASE + EV_A * st_nev S + sec_hulls S + sec_live_bytes S.
Definition shull (e : Z * Z) : Z * Z :=
(shadow_addr (fst e) / 4096 * 4096, (shadow_addr (fst e) + snd e / 8 + 4095) / 4096 * 4096).
Definition asecA (ly : alayout) (S : astate) (A : list (Z * Z)) : Prop :=
forall e, In e (sec_extents ly S) -> In (fst e, fst e + snd e) A /\ In (shull e) A.
Definition abudget_ok (ly : alayout) (S : astate) (W : world segs) : Prop :=
A_bytes (w_A W) <= abudget S /\ asecA ly S (w_A W).
Lemma abudget_ok_le : forall ly S W, abudget_ok ly S W -> A_bytes (w_A W) <= abudget S.
Proof. intros ly S W [H _]. exact H. Qed.
Lemma abudget_ok_intro : forall ly S W, A_bytes (w_A W) <= abudget S -> asecA ly S (w_A W) -> abudget_ok ly S W.
Proof. intros ly S W H1 H2. exact (conj H1 H2). Qed.
Lemma asecA_nil : forall ly S A, sec_extents ly S = [] -> asecA ly S A.
Proof. intros ly S A E e He. rewrite E in He. destruct He. Qed.
Lemma asecA_transfer : forall ly ly' S S' A A',
asecA ly S A -> (forall e, In e (sec_extents ly' S') -> In e (sec_extents ly S)) -> (forall i, In i A -> In i A') -> asecA ly' S' A'.
Proof. intros ly ly' S S' A A' H HE HI e He. destruct (H e (HE e He)) as [H1 H2]. split; apply HI; assumption. Qed.
Lemma shull_bounds : forall lo len, 0 <= len ->
fst (shull (lo, len)) <= shadow_addr lo /\ shadow_addr lo + len / 8 <= snd (shull (lo, len)) /\
fst (shull (lo, len)) mod 4096 = 0 /\ snd (shull (lo, len)) mod 4096 = 0.
Proof.
intros lo len Hlen. unfold shull. cbn [fst snd].
pose proof (Z.div_mod (shadow_addr lo) 4096 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (shadow_addr lo) 4096 ltac:(lia)) as B1.
pose proof (Z.div_mod (shadow_addr lo + len / 8 + 4095) 4096 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (shadow_addr lo + len / 8 + 4095) 4096 ltac:(lia)) as B2.
pose proof (Z.div_pos len 8 Hlen ltac:(lia)) as L8.
repeat split; [lia | lia | apply Z_mod_mult | apply Z_mod_mult].
Qed.
Lemma asecA_hull_allowed : forall ly S A e (w : word), asecA ly S A -> In e (sec_extents ly S) -> 0 <= snd e ->
shadow_addr (fst e) <= bv_unsigned w < shadow_addr (fst e) + snd e / 8 -> page_allowedb A (page_base w) = true.
Proof.
intros ly S A [lo len] w H He Hlen Hw. destruct (H _ He) as [_ HIN]. cbn [fst snd] in Hw, Hlen.
pose proof (shull_bounds lo len Hlen) as (S1 & S2 & S3 & S4). set (h := shull (lo, len)) in *. destruct h as [hl hh] eqn:Eh. cbn [fst snd] in S1, S2, S3, S4.
assert (PB : bv_unsigned (page_base w) = bv_unsigned w / 4096 * 4096).
{ unfold page_base, page_base_of, page_size. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)). lia. }
unfold page_allowedb. apply existsb_exists. exists (hl, hh). split; [exact HIN|]. cbn [fst snd]. unfold page_size. rewrite PB.
clear - Hw S1 S2 S3 S4.
pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)) as B3.
apply Z.mod_divide in S3 as [a Ha]; [|lia]. apply Z.mod_divide in S4 as [b Hb]; [|lia].
rewrite Ha, Hb in *. apply andb_true_intro. split; apply Z.leb_le; nia.
Qed.
Lemma abudget_ok_transfer : forall ly ly' S S' W W',
abudget_ok ly S W -> sec_extents ly' S' = sec_extents ly S -> (forall i, In i (w_A W) -> In i (w_A W')) ->
A_bytes (w_A W') <= abudget S' -> abudget_ok ly' S' W'.
Proof.
intros ly ly' S S' W W' [_ P] E HI HB. split; [exact HB|]. eapply asecA_transfer; [exact P | intros e He; rewrite <- E; exact He | exact HI].
Qed.
Definition amwf_ivs (md : Model) : Prop :=
(forall q, In q (vm_maps (m_vmmaps md)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) /\
(forall q, In q (vm_noaccess (m_vmmaps md)) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) /\
(forall q, In q (m_vm_lazy md) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) /\
pairwise (fun p q => bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/
bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p)) (vm_maps (m_vmmaps md)) /\
YK06.init_sp_ok (m_vmmaps md).
Definition amwf (md : Model) : Prop :=
amwf_ivs md /\ (forall q, In q (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd q)).
Lemma amwf_same : forall md md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> amwf md -> amwf md'.
Proof. intros md md' E1 E2 H. unfold amwf, amwf_ivs. rewrite E1, E2. exact H. Qed.
Definition in_vis0 (ly : alayout) (a : Z) : Prop := Exists (in_zr a) (ly_vis0 ly).
Definition ahs_pres (ly : alayout) (S : astate) (H : word -> bool) (mem : word -> option byte) : Prop :=
forall a, in_band_rw a -> ~ aclient_byte B ly S a ->
(H (w64 a) = true \/ ~ in_vis0 ly a) -> mem (w64 a) <> None.
Definition hfree (ly : alayout) (S : astate) (g : Z) : Prop :=
Forall (fun e : Z * Z => g + 8 <= fst e \/ fst e + snd e <= g) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Definition ahz (ly : alayout) (S : astate) (mem : word -> option byte) : Prop :=
forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S g -> mem (w64 (shadow_addr g)) = Some (Z_to_bv 8 0).
Definition ahs (ly : alayout) (S : astate) (H : word -> bool) (mem : word -> option byte) : Prop :=
ahs_pres ly S H mem /\ ahz ly S mem.
Lemma ahs_pres_hsub : forall ly S H H' mem, hsub H' H -> ahs_pres ly S H mem -> ahs_pres ly S H' mem.
Proof. intros ly S H H' mem Hs HA a Ha NC [Hh|Hv]; [exact (HA a Ha NC (or_introl (Hs _ Hh))) | exact (HA a Ha NC (or_intror Hv))]. Qed.
Lemma ahs_hsub : forall ly S H H' mem, hsub H' H -> ahs ly S H mem -> ahs ly S H' mem.
Proof. intros ly S H H' mem Hs [HA HZ]. split; [exact (ahs_pres_hsub ly S H H' mem Hs HA) | exact HZ]. Qed.
Lemma ahz_keep : forall ly S S' mem mem',
(forall g, g mod 8 = 0 -> in_app g 8 -> hfree ly S' g ->
hfree ly S g /\ mem' (w64 (shadow_addr g)) = mem (w64 (shadow_addr g))) ->
ahz ly S mem -> ahz ly S' mem'.
Proof. intros ly S S' mem mem' HK HZ g Hg Ha HF. destruct (HK g Hg Ha HF) as [HF0 E]. rewrite E. exact (HZ g Hg Ha HF0). Qed.
Lemma shadow_addr_band : forall g, kHighMemBeg <= g -> g + 8 <= ASAN_CEIL -> kHighShadowBeg <= shadow_addr g < kHighShadowEnd.
Proof. intros g H1 H2. pose proof ASAN_CEIL_range as [CR _]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg, kHighShadowBeg, kHighShadowEnd in *. split; [|]; lia. Qed.
Lemma shadow_addr_band_rw : forall g, in_app g 8 -> in_band_rw (shadow_addr g).
Proof. intros g Hg. rewrite <- (Z.add_0_r g). apply (shadow_addr_in_band g 8 0 Hg). lia. Qed.
Lemma ahz_keep_same : forall ly S S' mem mem',
sec_extents ly S' = sec_extents ly S -> (forall a, in_band_rw a -> mem' (w64 a) = mem (w64 a)) ->
ahz ly S mem -> ahz ly S' mem'.
Proof.
intros ly S S' mem mem' HE HM. apply ahz_keep. intros g Hg Ha HF. split.
- unfold hfree in *. rewrite HE in HF. exact HF.
- apply HM. apply shadow_addr_band_rw; assumption.
Qed.
Lemma ahz_keep_out : forall ly S S' mem mem',
sec_extents ly S' = sec_extents ly S ->
(forall a, in_band_rw a ->
Forall (fun e : Z * Z => a < shadow_addr (fst e) \/ shadow_addr (fst e) + (snd e + 7) / 8 <= a) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) ->
mem' (w64 a) = mem (w64 a)) ->
ahz ly S mem -> ahz ly S' mem'.
Proof.
intros ly S S' mem mem' HE HM. apply ahz_keep. intros g Hg Ha HF. unfold hfree in *. rewrite HE in HF. split; [exact HF|].
apply HM; [apply shadow_addr_band_rw; assumption|]. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) HF e He) as X. cbn beta in X. unfold shadow_addr, SHADOW_OFF in *.
apply Z.mod_divide in Hg as [q Hq]; [|lia]. subst g.
pose proof (Z.mul_div_le (fst e) 8 ltac:(lia)) as M1. pose proof (Z.mul_div_le (snd e + 7) 8 ltac:(lia)) as M2.
pose proof (Z.div_mod (fst e) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (fst e) 8 ltac:(lia)) as B1.
replace (q * 8 / 8) with q by (symmetry; apply Z.div_mul; lia).
destruct X as [X|X].
- left. assert (q + 1 <= fst e / 8) by (apply Z.div_le_lower_bound; lia). lia.
- right. lia.
Qed.
Definition AR (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model) : Prop :=
ARm B ly S (aview segs (w_H W) mem) /\ ALedger segs ly S md /\ abudget_ok ly S W /\ amwf md /\ ahs ly S (w_H W) mem.
Lemma Forall_cell_holds_ext : forall ly rd rd' l,
rd_ext rd rd' -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros ly rd rd' l Hx H. apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) H c Hc) as Hh.
unfold cell_holds in *. destruct (c_val c) as [e | m v].
- intros k Hk. apply Hx, Hh, Hk.
- destruct Hh as (b & Hb & Hm). exists b. split; [apply Hx, Hb | exact Hm].
Qed.
Lemma Forall_range_vis_ext : forall ly rd rd' l,
rd_ext rd rd' -> Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l.
Proof.
intros ly rd rd' l Hx H. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) H r Hr i Hi) as Hh.
destruct (rd (aeval B ly (fst r) + i)) as [v|] eqn:E; [|exfalso; apply Hh; reflexivity].
rewrite (Hx _ _ E). discriminate.
Qed.
Lemma ARm_ext : forall ly S rd rd', rd_ext rd rd' -> ARm B ly S rd -> ARm B ly S rd'.
Proof.
intros ly S rd rd' Hx M. destruct M. constructor; try assumption.
- eapply Forall_cell_holds_ext; eassumption.
- eapply Forall_cell_holds_ext; eassumption.
- intros c i v Hc Hi Hv k Hk. apply Hx. exact (am_fa0 c i v Hc Hi Hv k Hk).
- intros cid pos Hc Hp. apply Hx. exact (am_flags0 cid pos Hc Hp).
- destruct am_depot0 as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
+ intros b Hb. destruct (D1 b Hb) as [H1 H2]. split; [exact H1|]. intros k Hk. apply Hx, H2, Hk.
+ intros id Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|]. split; intros k Hk; apply Hx; auto.
- intros g v Hg Hv. apply Hx. exact (am_shadow0 g v Hg Hv).
- unfold zshadow_ok in *. apply Forall_forall. intros r Hr.
eapply zero_shadow_ext; [exact Hx|]. exact (proj1 (Forall_forall _ _) am_zshadow0 r Hr).
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- eapply Forall_range_vis_ext; eassumption.
- apply Forall_forall. intros r Hr i Hi. apply Hx. exact (proj1 (Forall_forall _ _) am_zero0 r Hr i Hi).
Qed.
Lemma AR_wle : forall ly S W W' mem md,
AR ly S W mem md -> wle W W' -> (forall i, In i (w_A W) -> In i (w_A W')) -> A_bytes (w_A W') <= abudget S -> AR ly S W' mem md.
Proof.
intros ly S W W' mem md (M & L & B0 & MW & HS) Hs HI Hb.
split; [|split; [exact L | split; [exact (abudget_ok_transfer ly ly S S W W' B0 eq_refl HI Hb) | split; [exact MW | exact (ahs_hsub ly S _ _ mem Hs HS)]]]].
eapply ARm_ext; [|exact M]. apply aview_ext; [apply w_Hoff | exact Hs].
Qed.
Definition rd_agree_on (P : Z -> Prop) (rd rd' : reader) : Prop := forall a, P a -> rd' a = rd a.
Definition rd_keeps_vis (rd rd' : reader) : Prop := forall a, rd a <> None -> rd' a <> None.
Lemma ALedger_same : forall ly S md md',
ALedger segs ly S md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
eager_used md' = eager_used md -> ALedger segs ly S md'.
Proof.
intros ly S md md' L Hv Hl He. destruct L. constructor; rewrite ?Hv, ?Hl, ?He; assumption.
Qed.
End b0.
Definition ameter (s : astate) : Z := E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s + abudget s.
Definition VM_HEAD : Z := 2 ^ 30.
Definition RF_HEAD : Z := 2 ^ 23.
Definition mroom (s : astate) : Prop := ameter s + VM_HEAD <= ASAN_VM_LMIN.
Definition rroom (s : astate) : Prop := ameter s + RF_HEAD <= ASAN_VM_LMIN.
Definition qmeter (s : astate) : Prop := qtight s /\ mroom s.
Definition qloosem (s : astate) : Prop := qloose s /\ rroom s.
Definition mtr_ok (s : astate) (m : Z) : Prop := ameter s + m + VM_HEAD <= ASAN_VM_LMIN.
Definition mtr_le (s s' : astate) (m : Z) : Prop := ameter s' <= ameter s + m.
Lemma qmeter_tight : forall s, qmeter s -> qtight s.            Proof. intros s [H _]; exact H. Qed.
Lemma qmeter_room : forall s, qmeter s -> mroom s.              Proof. intros s [_ H]; exact H. Qed.
Lemma qloosem_loose : forall s, qloosem s -> qloose s.          Proof. intros s [H _]; exact H. Qed.
Lemma qloosem_room : forall s, qloosem s -> rroom s.            Proof. intros s [_ H]; exact H. Qed.
Lemma mroom_rroom : forall s s', ameter s' <= ameter s + (VM_HEAD - RF_HEAD) -> mroom s -> rroom s'.
Proof. intros s s' H R. unfold mroom, rroom in *. lia. Qed.
Lemma qmeter_loosem : forall s, qmeter s -> qloosem s.
Proof. intros s [T R]. split; [exact (qtight_qloose s T) | apply (mroom_rroom s s); [unfold VM_HEAD, RF_HEAD; lia | exact R]]. Qed.
Lemma mroom_of_mtr_ok : forall s m, 0 <= m -> mtr_ok s m -> mroom s.
Proof. intros s m Hm H. unfold mtr_ok, mroom in *. lia. Qed.
Lemma qmeter_intro : forall s m, qtight s -> 0 <= m -> mtr_ok s m -> qmeter s.
Proof. intros s m T Hm H. split; [exact T | exact (mroom_of_mtr_ok s m Hm H)]. Qed.
Lemma mtr_le_refl : forall s, mtr_le s s 0.
Proof. intros s. unfold mtr_le. lia. Qed.
Lemma mtr_le_trans : forall s1 s2 s3 m1 m2, mtr_le s1 s2 m1 -> mtr_le s2 s3 m2 -> mtr_le s1 s3 (m1 + m2).
Proof. intros s1 s2 s3 m1 m2 H1 H2. unfold mtr_le in *. lia. Qed.
Lemma mtr_le_mono : forall s s' m m', mtr_le s s' m -> m <= m' -> mtr_le s s' m'.
Proof. intros s s' m m' H Hm. unfold mtr_le in *. lia. Qed.
Lemma mtr_ok_le : forall s m m', mtr_ok s m' -> m <= m' -> mtr_ok s m.
Proof. intros s m m' H Hm. unfold mtr_ok in *. lia. Qed.
Lemma mtr_ok_step : forall s s' m1 m2, mtr_ok s (m1 + m2) -> mtr_le s s' m1 -> mtr_ok s' m2.
Proof. intros s s' m1 m2 H1 H2. unfold mtr_ok, mtr_le in *. lia. Qed.
Lemma ameter_ext : forall s s', prim_committed s' = prim_committed s -> st_sec_reserved s' = st_sec_reserved s ->
sec_live_bytes s' = sec_live_bytes s -> st_nev s' = st_nev s -> sec_hulls s' = sec_hulls s -> ameter s' = ameter s.
Proof. intros s s' H1 H2 H3 H4 H5. unfold ameter, abudget. rewrite H1, H2, H3, H4, H5. reflexivity. Qed.
Lemma rroom_tick : forall s s', prim_committed s' = prim_committed s -> st_sec_reserved s' = st_sec_reserved s ->
sec_live_bytes s' = sec_live_bytes s -> st_nev s' = st_nev s + 1 -> sec_hulls s' = sec_hulls s -> mroom s -> rroom s'.
Proof. intros s s' H1 H2 H3 H4 H5 R. unfold mroom, rroom, ameter, abudget, VM_HEAD, RF_HEAD, EV_A in *. rewrite H1, H2, H3, H4, H5. lia. Qed.
End u.
