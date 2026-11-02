(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2x.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2t.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u8_of_Z v : 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof. intros Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv. Qed.
Lemma le_byte1_small v : 0 <= v < 256 -> le_byte (v mod 2 ^ (8 * Z.of_N 1)) (N.to_nat 1) 0 = v.
Proof.
intros Hv. unfold le_byte. replace (2 ^ (8 * Z.of_N 1)) with 256 by reflexivity.
replace (2 ^ (8 * Z.of_nat (N.to_nat 1))) with 256 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small v 256) by lia. rewrite (Z.mod_small v 256) by lia. apply Z.mod_small. lia.
Qed.
Lemma le_byte4_0 v : 0 <= v < 256 -> le_byte v 4 0 = v.
Proof.
intros Hv. unfold le_byte. replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 by reflexivity.
replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r. rewrite (Z.mod_small v 4294967296) by lia. apply Z.mod_small. lia.
Qed.
Lemma le_byte4_hi v v' k : 0 <= v < 256 -> 0 <= v' < 256 -> (0 < k)%nat -> le_byte v 4 k = le_byte v' 4 k.
Proof.
intros Hv Hv' Hk. unfold le_byte. replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 by reflexivity.
rewrite (Z.mod_small v), (Z.mod_small v') by lia. rewrite !Z.shiftr_div_pow2 by lia.
assert (256 <= 2 ^ (8 * Z.of_nat k)) by (change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia).
rewrite !Z.div_small by lia. reflexivity.
Qed.
Definition aidx_cell (am : ameta) : mcell :=
if am_maplen am =? 0 then MCell (LMem (padd (am_mem am) 8)) 1 (VLo5 (am_aidx am))
else MCell (LMem (padd (am_mem am) 8)) 4 (VZ (am_aidx am)).
Lemma group_cells_shape g am :
group_cells g am = [MCell (LMem (am_mem am)) 8 (VP g); aidx_cell am] ++ flat_map (slot_cells am) (zseq 0 (am_last am + 1)).
Proof. reflexivity. Qed.
Lemma aidx_cell_range L am : cell_range L (aidx_cell am) = (ptr_addr L (am_mem am) + 8, if am_maplen am =? 0 then 1 else 4).
Proof. unfold aidx_cell, cell_range. destruct (am_maplen am =? 0); cbn [mc_loc mc_w fst snd]; rewrite loc_addr_padd'; reflexivity. Qed.
Lemma group_tail_cells_set_aidx v a : group_tail_cells (am_set_aidx v a) = group_tail_cells a.
Proof. destruct a; reflexivity. Qed.
Lemma meta_slot_cells_set_aidx q v a : meta_slot_cells q (Some (MUsed (am_set_aidx v a))) = meta_slot_cells q (Some (MUsed a)).
Proof. destruct a; reflexivity. Qed.
Lemma slot_cells_set_aidx v a i : slot_cells (am_set_aidx v a) i = slot_cells a i.
Proof. destruct a; reflexivity. Qed.
Lemma group_cells_set_aidx g v a c :
In c (group_cells g (am_set_aidx v a)) -> c = aidx_cell (am_set_aidx v a) \/ In c (group_cells g a).
Proof.
rewrite !group_cells_shape. intros Hc. apply in_app_iff in Hc as [[<-|[<-|[]]]|Hc].
- right. apply in_app_iff. left. left. destruct a; reflexivity.
- left. reflexivity.
- right. apply in_app_iff. right. replace (am_last (am_set_aidx v a)) with (am_last a) in Hc by (destruct a; reflexivity).
apply in_flat_map in Hc as (i & Hi & Hc). apply in_flat_map. exists i. split; [exact Hi|]. rewrite slot_cells_set_aidx in Hc. exact Hc.
Qed.
Lemma area_cells_upd_sameG s g am am' a next :
MT s g = Some (MUsed am) ->
meta_slot_cells g (Some (MUsed am')) = meta_slot_cells g (Some (MUsed am)) ->
area_cells (upd_meta g (MUsed am') s) a next = area_cells s a next.
Proof.
intros Hg Hm. unfold area_cells. f_equal. apply flat_map_ext_In. intros k _.
change (mlookup (st_metas (upd_meta g (MUsed am') s))) with (MT (upd_meta g (MUsed am') s)).
change (mlookup (st_metas s)) with (MT s). rewrite MT_upd.
destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E; [|reflexivity].
apply sptr_eqb_eq in E. rewrite E, Hg. exact Hm.
Qed.
Lemma areas_cells_upd_sameG s g am am' l :
MT s g = Some (MUsed am) ->
meta_slot_cells g (Some (MUsed am')) = meta_slot_cells g (Some (MUsed am)) ->
areas_cells (upd_meta g (MUsed am') s) l = areas_cells s l.
Proof.
intros Hg Hm. induction l as [|a t IH]; cbn [areas_cells]; [reflexivity|].
rewrite IH. f_equal. destruct t; apply (area_cells_upd_sameG s g am am'); assumption.
Qed.
Lemma imageX_set_aidx X s q a v c :
MT s q = Some (MUsed a) ->
In c (imageX X (upd_meta q (MUsed (am_set_aidx v a)) s)) -> c = aidx_cell (am_set_aidx v a) \/ In c (imageX X s).
Proof.
intros Mq Hc. unfold imageX in *. rewrite ctx_cells_upd_meta in Hc.
change (st_areas (upd_meta q _ s)) with (st_areas s) in Hc.
rewrite (areas_cells_upd_sameG s q a (am_set_aidx v a) (st_areas s) Mq (meta_slot_cells_set_aidx q v a)) in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [right; apply in_app_iff; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc]; [right; apply in_app_iff; right; apply in_app_iff; left; exact Hc|].
destruct (used_metasX_upd X s q a (am_set_aidx v a) Mq) as (u1 & u2 & E1 & E2). rewrite E2 in Hc.
rewrite !flat_map_app in Hc. apply in_app_iff in Hc as [H|Hc]; [right; do 2 (apply in_app_iff; right); rewrite E1, !flat_map_app; apply in_app_iff; left; exact H|].
apply in_app_iff in Hc as [H|H].
- destruct (memb q X); [destruct H|]. cbn [flat_map fst snd] in H. rewrite app_nil_r in H.
destruct (group_cells_set_aidx q v a c H) as [E|H']; [left; exact E|].
right. do 2 (apply in_app_iff; right). rewrite E1, !flat_map_app. apply in_app_iff. right. apply in_app_iff. left. cbn [flat_map fst snd]. rewrite app_nil_r. exact H'.
- right. do 2 (apply in_app_iff; right). rewrite E1, !flat_map_app. apply in_app_iff. right. apply in_app_iff. right. exact H.
Qed.
Lemma tail_cellsX_set_aidx X s q a v c :
MT s q = Some (MUsed a) -> In c (tail_cellsX X (upd_meta q (MUsed (am_set_aidx v a)) s)) -> In c (tail_cellsX X s).
Proof.
intros Mq Hc. unfold tail_cellsX in *.
destruct (used_metasX_upd X s q a (am_set_aidx v a) Mq) as (u1 & u2 & E1 & E2). rewrite E2 in Hc. rewrite E1.
rewrite !flat_map_app in *. apply in_app_iff in Hc as [H|Hc]; [apply in_app_iff; left; exact H|].
apply in_app_iff. right. apply in_app_iff in Hc as [H|H]; apply in_app_iff; [left | right; exact H].
destruct (memb q X); [destruct H|]. cbn [flat_map fst snd] in *. rewrite group_tail_cells_set_aidx in H. exact H.
Qed.
Lemma tail_cells_set_aidx s q a v : MT s q = Some (MUsed a) -> tail_cells (upd_meta q (MUsed (am_set_aidx v a)) s) = tail_cells s.
Proof.
intros Mq. unfold tail_cells. destruct (used_metas_upd s q a Mq) as (u1 & u2 & E1 & E2). rewrite E1, (E2 (am_set_aidx v a)).
rewrite !flat_map_app. cbn [flat_map snd]. rewrite group_tail_cells_set_aidx. reflexivity.
Qed.
Lemma aidx_cell_In_imageX X s g am : List.NoDup (keys s) -> usedX X s g am -> In (aidx_cell am) (imageX X s).
Proof.
intros ND Hu. unfold imageX. apply in_app_iff. right. apply in_app_iff. right.
apply in_flat_map. exists (g, am). split; [| rewrite group_cells_shape; apply in_app_iff; left; right; left; reflexivity].
destruct (usedX_MT _ _ _ _ Hu) as [M NX]. unfold used_metasX. apply filter_In. split; [| cbn [fst]; rewrite NX; reflexivity].
apply (proj2 (used_metas_iff s g am ND)). exact M.
Qed.
Section m.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Variables (g : sptr) (am : ameta).
Hypothesis Hu : usedX X s g am.
Let base := ly_reg L (prid (am_mem am)).
Let lo := poff (am_mem am) + 8.
Let hi := poff (am_mem am) + 12.
Lemma loc_addr_mem' p d : loc_addr L (LMem (padd p d)) = ly_reg L (prid p) + poff p + d.
Proof. destruct p; cbn. lia. Qed.
Lemma hdr_span :
exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
range_incl (base + lo, hi - lo) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)) /\
28 <= group_extent am /\ 16 <= stride_of am.
Proof.
destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _).
assert (E28 : 28 <= group_extent am) by (unfold group_extent, UNIT, IB; nia).
exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
unfold range_incl, crange. cbn [fst snd loc_addr]. unfold base, lo, hi. unfold IB in *. repeat split; lia.
Qed.
Lemma other_entry' c e :
In e (footprint s) -> range_incl (cell_range L c) (crange L e) ->
(forall rg, region_of s (prid (am_mem am)) = Some rg -> rg_kind rg = RkMap -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)) ->
ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros He Ic Hne. destruct hdr_span as (rg & Hr & Hk & Hl & InR & IB' & _).
pose proof HL as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR (Hne rg Hr Hk)) as [D|D].
- eapply ranges_disjoint_incl; [exact D | exact Ic | exact IB'].
- apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact IB' | exact Ic].
Qed.
Lemma same_region_cell' c q d :
mc_loc c = LMem (padd q d) -> prid q = prid (am_mem am) ->
(poff q + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff q + d) ->
ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros E Hp D. unfold ranges_disjoint, cell_range. cbn [fst snd]. rewrite E, loc_addr_mem', Hp. unfold base, lo, hi in *. lia.
Qed.
Lemma group_cells_hdr q aq c :
usedX X s q aq -> In c (group_cells q aq) -> c <> aidx_cell am -> ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros Uq Hc Hne. destruct hdr_span as (rg & Hr & Hk & Hl & InR & IB' & E28 & S16).
destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (group_cell_homeX X R U s L HI q aq c Uq Hc) as (rg' & Hr' & Hk' & Hl' & In' & I').
apply (other_entry' c _ In' I'). intros rg0 Hr0 Hk0 E. injection E as Ep _. exact (Hdiff Ep). }
destruct (sptr_eq_dec q g) as [-> | Hqg].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->. rewrite group_cells_shape in Hc.
apply in_app_iff in Hc as [[<-|[<-|[]]]|Hc].
+ apply (same_region_cell' _ (am_mem am) 0); [cbn [mc_loc]; destruct (am_mem am); cbn; rewrite Z.add_0_r; reflexivity | reflexivity | cbn [mc_w]; unfold lo; lia].
+ exfalso. exact (Hne eq_refl).
+ apply in_flat_map in Hc as (i & Hi & Hc). apply In_zseq in Hi.
destruct (In_slot_cells X R U s g am i c HI Hu ltac:(lia) Hc) as (d & E & Lo & _).
apply (same_region_cell' _ _ _ E eq_refl). right. unfold hi. assert (0 <= stride_of am * i) by nia. unfold UNIT, IB in Lo. lia.
- destruct (In_group_cells_span X R U s q aq c HI Uq Hc) as (d & E & Hd & Hw).
destruct (inv_laminar HI q aq g am Uq Hu Hqg Hsame) as [Dj | [I | I]].
+ apply (same_region_cell' c _ _ E Hsame). unfold spans_disjoint in Dj. unfold lo, hi. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
rewrite Mem0, poff_slot_start in Lo0. apply (same_region_cell' c _ _ E Hsame). right. unfold hi. assert (0 <= stride_of am * j0) by nia. unfold UNIT in Lo0. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
rewrite Mem0 in Lo0, Hi0.
destruct (group_cells_vs_body X R U s q aq j0 lo hi c HI Uq Hj0 Hc
ltac:(rewrite Hfr0, Off0; unfold lo, UNIT in *; lia)
ltac:(unfold hi, IB in *; lia)) as (d' & E' & D').
exact (same_region_cell' c _ _ E' Hsame D').
Qed.
Lemma tail_cells_hdr q aq c :
usedX X s q aq -> In c (group_tail_cells aq) -> ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros Uq Hc. destruct hdr_span as (rg & Hr & Hk & Hl & InR & IB' & E28 & S16).
destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (tail_cell_homeX X R U s L HI aq c q Uq Hc) as (rg' & Hr' & Hk' & Hl' & In' & I').
apply (other_entry' c _ In' I'). intros rg0 Hr0 Hk0 E. injection E as Ep _. exact (Hdiff Ep). }
destruct (tail_cell_home X R U s HI q aq c Uq Hc) as (rg' & d & _ & _ & _ & E & Hd & Ho' & Hfit & Hw).
destruct (sptr_eq_dec q g) as [-> | Hqg].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->. apply (same_region_cell' c _ _ E eq_refl). right. unfold hi, UNIT in *. lia.
- pose proof (extent_pos _ _ _ _ _ (inv_groups HI q aq Uq)) as Pq.
destruct (inv_laminar HI q aq g am Uq Hu Hqg Hsame) as [Dj | [I | I]].
+ apply (same_region_cell' c _ _ E Hsame). unfold spans_disjoint in Dj. unfold lo, hi, UNIT in *. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
rewrite Mem0, poff_slot_start in Lo0. apply (same_region_cell' c _ _ E Hsame). right. unfold hi. assert (0 <= stride_of am * j0) by nia. unfold UNIT in *. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
rewrite Mem0 in Lo0, Hi0.
destruct (tail_cells_vs_body X R U s HI q aq j0 lo hi c Uq Hj0 Hc
ltac:(unfold lo, UNIT in *; lia) ltac:(unfold hi, IB in *; lia)
ltac:(intros f Hf Hkf; rewrite Hfr0 in Hf; injection Hf as <-; rewrite Hk0 in Hkf; discriminate)) as (d' & E' & D').
exact (same_region_cell' c _ _ E' Hsame D').
Qed.
Theorem aidx_bytes_free c :
In c (imageX X s ++ tail_cellsX X s) -> c <> aidx_cell am ->
ranges_disjoint (cell_range L c) (ptr_addr L (am_mem am) + 8, 4).
Proof.
intros Hc Hne.
assert (EQ : (ptr_addr L (am_mem am) + 8, 4) = (base + lo, hi - lo)).
{ unfold base, lo, hi, ptr_addr. destruct (am_mem am); cbn. f_equal; lia. }
rewrite EQ. apply in_app_iff in Hc as [Hc|Hc].
- unfold imageX in Hc. apply in_app_iff in Hc as [Hc|Hc].
{ destruct (ctx_cell_home L s c Hc) as [In1 I1]. apply (other_entry' c _ In1 I1). intros; discriminate. }
apply in_app_iff in Hc as [Hc|Hc].
{ destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc'). destruct (area_cell_home L s a next c Ha Hc') as [In1 I1].
apply (other_entry' c _ In1 I1). intros rg Hr Hk. exact (area_entry_not_region X R U s HI a _ rg Ha Hr Hk). }
apply in_flat_map in Hc as ([q aq] & Hq & Hc). cbn [fst snd] in Hc.
exact (group_cells_hdr q aq c (usedX_of_used_metasX X R U s HI q aq Hq) Hc Hne).
- unfold tail_cellsX in Hc. apply in_flat_map in Hc as ([q aq] & Hq & Hc). cbn [snd] in Hc.
exact (tail_cells_hdr q aq c (usedX_of_used_metasX X R U s HI q aq Hq) Hc).
Qed.
Theorem aidx_bytes_no_block b : In b (user_blocks s) -> ranges_disjoint (block_range L b) (ptr_addr L (am_mem am) + 8, 4).
Proof.
intros Hb. pose proof HL as (_ & _ & PW & _).
assert (EQ : (ptr_addr L (am_mem am) + 8, 4) = (base + lo, hi - lo)).
{ unfold base, lo, hi, ptr_addr. destruct (am_mem am); cbn. f_equal; lia. }
rewrite EQ. destruct hdr_span as (rg & Hr & Hk & Hl & InR & IB' & E28 & Sp).
pose proof (inv_groups HI g am Hu) as G. pose proof G as (_ & _ & Gsl & _).
destruct (in_user_blocks_inv s b Hb) as (q & aq & j & fq & Hq & Hj & Hfq & Hkq & ->).
assert (Uq : usedX X s q aq).
{ apply (used_metas_iff s q aq (proj1 (inv_keys HI))) in Hq. apply usedX_intro; [|exact Hq].
destruct (memb q X) eqn:M; [|reflexivity]. exfalso.
destruct (inv_X HI q (proj1 (memb_In q X) M)) as [_ Hx]. rewrite Hq in Hx. destruct Hx as (_ & _ & Hnofr). rewrite (Hnofr j) in Hfq. discriminate. }
pose proof (inv_groups HI q aq Uq) as Gq. pose proof (stride_pos _ _ _ _ _ Gq) as Spq. pose proof Gq as (_ & _ & Gslq & _).
pose proof (Gslq j Hj) as (_ & _ & S3). rewrite Hfq in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
destruct (used_group_region X R U s q aq HI Uq) as (rg' & Hr' & Hk' & Hl' & Ho' & Hext' & _).
pose proof (slot_in_span X R U s HI q aq j Uq Hj) as [T1 T2].
assert (BI : range_incl (block_range L (frame_ptr aq j fq, fr_n fq)) (crange L (LMem (SP (prid (am_mem aq)) 0), rg_len rg'))).
{ unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
unfold frame_ptr, slot_start in *. destruct (am_mem aq) as [r o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia. }
destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (footprint_region_In s _ _ Hr' Hk' Hl') InR
ltac:(intros E2; injection E2; intros _ Ep; exact (Hdiff Ep))) as [D|D].
- eapply ranges_disjoint_incl; [exact D | exact BI | exact IB'].
- apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact IB' | exact BI]. }
assert (GOAL : poff (frame_ptr aq j fq) + fr_n fq <= lo \/ hi <= poff (frame_ptr aq j fq) ->
ranges_disjoint (block_range L (frame_ptr aq j fq, fr_n fq)) (base + lo, hi - lo)).
{ intros D. unfold block_range, ranges_disjoint, loc_addr. cbn [fst snd]. unfold base.
unfold frame_ptr, slot_start in *. destruct (am_mem aq) as [r' o'], (am_mem am) as [r o]. cbn [padd prid poff] in *. subst r'. lia. }
apply GOAL. unfold frame_ptr. rewrite poff_padd. unfold lo, hi in *.
destruct (sptr_eq_dec q g) as [-> | Hne].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->. right. rewrite poff_slot_start. assert (0 <= stride_of am * j) by nia. unfold UNIT in *. lia.
- pose proof (extent_pos _ _ _ _ _ Gq) as Pq.
destruct (inv_laminar HI q aq g am Uq Hu Hne Hsame) as [Dj | [I | I]].
+ unfold spans_disjoint in Dj. rewrite poff_slot_start in *. unfold group_extent, UNIT, IB in *.
assert (stride_of aq * j + stride_of aq <= stride_of aq * (am_last aq + 1)) by nia. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
rewrite Mem0, poff_slot_start in Lo0. right. rewrite poff_slot_start in *. assert (0 <= stride_of am * j0) by nia. assert (0 <= stride_of aq * j) by nia. unfold UNIT in *. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
assert (Hjj : j <> j0) by (intros ->; rewrite Hfr0 in Hfq; injection Hfq as <-; rewrite Hk0 in Hkq; discriminate).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
destruct (same_group_starts aq j j0 Hjj Spq) as [LE|LE]; rewrite ?poff_slot_start in *; unfold UNIT, IB in *; [left|right]; lia.
Qed.
Corollary aidx_bytes_owned k : 0 <= k < 4 -> alloc_owned L s (ptr_addr L (am_mem am) + 8 + k).
Proof.
intros Hk. destruct hdr_span as (rg & Hr & Hkd & Hl & InR & IB' & _). split.
- exists (LMem (SP (prid (am_mem am)) 0), rg_len rg). split; [exact InR|]. revert IB'.
unfold range_incl, crange, base, lo, hi, ptr_addr. destruct (am_mem am) as [r o]. cbn [fst snd loc_addr prid poff]. lia.
- intros (b & Hb & Hx). pose proof (aidx_bytes_no_block b Hb) as D. unfold ranges_disjoint, block_range in *. cbn [fst snd] in *. lia.
Qed.
Corollary aidx_cell_exclusive c :
In c (imageX X s ++ tail_cellsX X s) -> c = aidx_cell am \/ ranges_disjoint (cell_range L c) (cell_range L (aidx_cell am)).
Proof.
intros Hc. destruct (mcell_eq_dec c (aidx_cell am)) as [->|Hne]; [left; reflexivity | right].
pose proof (aidx_bytes_free c Hc Hne) as D. rewrite aidx_cell_range.
unfold ranges_disjoint in *. cbn [fst snd] in *. destruct (am_maplen am =? 0); lia.
Qed.
End m.
Section u.
Variable B : malloc_syms.
Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate) (L : layout).
Variables (mem mem' : word -> option byte).
Variables (NEW : list mcell) (stk : Z * Z).
Hypothesis HI : Inv X R U s.
Hypothesis HI' : Inv X' R' U' s'.
Hypothesis HL : layout_ok L s.
Hypothesis Efp : footprint s' = footprint s.
Hypothesis Erg : st_regions s' = st_regions s.
Hypothesis MR : memrepX B X L s mem.
Hypothesis Hcells : forall c, In c (imageX X' s' ++ tail_cellsX X' s') -> In c NEW \/ In c (imageX X s ++ tail_cellsX X s).
Hypothesis Hnew_home : forall n, In n NEW -> (exists p, mc_loc n = LMem p) \/ In n (ctx_cells s').
Hypothesis Hnew_excl : forall n c, In n NEW -> In c (imageX X' s' ++ tail_cellsX X' s') -> c = n \/ ranges_disjoint (cell_range L c) (cell_range L n).
Hypothesis Hnew_mem : forall n, In n NEW -> cell_mem B L mem' n.
Hypothesis Hnew_present : forall n k, In n NEW -> (k < mc_w n)%nat -> (exists p, mc_loc n = LMem p) -> present mem' (loc_addr L (mc_loc n) + Z.of_nat k).
Hypothesis Hstk : forall e, In e (footprint s) -> loc_addr L (fst e) + snd e <= fst stk.
Hypothesis Hframe : forall a, 0 <= a < 2 ^ 64 ->
(forall n, In n NEW -> ~ in_range a (cell_range L n)) -> ~ in_range a stk ->
mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (present mem a -> present mem' a).
Lemma old_byte_frameX c k :
In c (imageX X' s' ++ tail_cellsX X' s') -> ~ In c NEW -> In c (imageX X s ++ tail_cellsX X s) -> (k < mc_w c)%nat ->
let a := loc_addr L (mc_loc c) + Z.of_nat k in
mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (present mem a -> present mem' a).
Proof.
intros Hc' Hnot Hc Hk.
destruct (cellX_in_footprint X R U s L HI c Hc) as (e & He & Ie). pose proof (proj2 (proj2 (proj2 HL)) e He) as Re.
apply Hframe.
- unfold range_incl, cell_range, crange in Ie, Re. cbn [fst snd] in Ie, Re. lia.
- intros n Hn Hin. destruct (Hnew_excl n c Hn Hc') as [->|Dj]; [exact (Hnot Hn)|].
exact (ranges_disjoint_not_both _ _ _ Dj (cell_range_in L c k Hk) Hin).
- intros Hin. pose proof (Hstk e He). unfold range_incl, cell_range, crange, in_range in *. cbn [fst snd] in *. lia.
Qed.
Lemma cells_holdX c : In c (imageX X' s' ++ tail_cellsX X' s') -> cell_mem B L mem' c.
Proof.
intros Hc'. destruct (In_dec mcell_eq_dec c NEW) as [Hn|Hn]; [apply Hnew_mem; exact Hn|].
destruct (Hcells c Hc') as [Hn'|Hc]; [exfalso; exact (Hn Hn')|].
assert (OLD : cell_mem B L mem c).
{ pose proof MR as (MI & MT' & _). apply in_app_iff in Hc as [H|H];
[exact (proj1 (Forall_forall _ _) MI _ H) | exact (proj1 (Forall_forall _ _) MT' _ H)]. }
unfold cell_mem in *. destruct (mc_val c) eqn:Ev;
try (intros k Hk; rewrite <- (OLD k Hk); apply (old_byte_frameX c k Hc' Hn Hc Hk)).
intros Hw. destruct (OLD Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
pose proof (old_byte_frameX c 0 Hc' Hn Hc Hw) as [E _]. rewrite Z.add_0_r in E. rewrite E. exact Hb.
Qed.
Theorem memrepX_after_cells : memrepX B X' L s' mem'.
Proof.
split; [|split].
- apply Forall_forall. intros c Hc. apply cells_holdX. apply in_app_iff. left. exact Hc.
- apply Forall_forall. intros c Hc. apply cells_holdX. apply in_app_iff. right. exact Hc.
- rewrite Efp. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) e He) as Fe.
unfold foot_ok in *. destruct e as [[o|q] len]; [exact I|]. cbn [fst snd] in *. intros x Hx.
destruct (in_ranges_dec (cell_range L) x NEW) as [(n & Hn & Hin)|Hno].
+ unfold in_range, cell_range in Hin. cbn [fst snd] in Hin.
replace x with (loc_addr L (mc_loc n) + Z.of_nat (Z.to_nat (x - loc_addr L (mc_loc n)))) by lia.
destruct (Hnew_home n Hn) as [Hl|Hc].
* apply (Hnew_present n _ Hn); [lia | exact Hl].
* exfalso. destruct (In_ctx_cells s' n Hc) as (off & E & Ho & Hw).
pose proof HL as (_ & _ & PW & _).
assert (Hne : (LCtx 0, CTX_SIZE) <> (LMem q, len)) by discriminate.
assert (R1 : ly_ctx L + off <= x < ly_ctx L + off + Z.of_nat (mc_w n)).
{ rewrite E in Hin. cbn [fst snd loc_addr] in Hin. exact Hin. }
cbn [loc_addr] in Hx.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (or_introl eq_refl) He Hne) as [Dj|Dj];
unfold ranges_disjoint, crange in Dj; cbn [fst snd loc_addr] in Dj; lia.
+ pose proof (proj2 (proj2 (proj2 HL)) _ He) as Re. cbn [fst snd crange] in Re.
apply (proj2 (Hframe x ltac:(lia) Hno ltac:(pose proof (Hstk _ He) as S; cbn [fst snd] in S; unfold in_range; lia))). exact (Fe x Hx).
Qed.
End u.
End h.
