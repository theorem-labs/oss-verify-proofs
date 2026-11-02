(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2o.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Lemma usedX_of_used_metasX g am : In (g, am) (used_metasX X s) -> usedX X s g am.
Proof.
intros Hin. unfold used_metasX in Hin. apply List.filter_In in Hin as [Hin Hx]. cbn [fst] in Hx.
apply usedX_intro; [destruct (memb g X); [discriminate | reflexivity] |].
apply (used_metas_iff s g am (proj1 (inv_keys HI))). exact Hin.
Qed.
Lemma areas_cells_pairwise' l :
List.NoDup l -> (forall a, In a l -> In a (st_areas s)) ->
pairwise ranges_disjoint (map (cell_range L) (areas_cells s l)).
Proof.
induction l as [|a t IH]; intros ND Hsub; cbn [areas_cells]; [exact I|].
inversion ND as [|a' t' Ha Ht]; subst. rewrite map_app.
apply pairwise_app.
- apply area_cells_disjoint.
- apply IH; [exact Ht | intros b Hb; apply Hsub; right; exact Hb].
- intros x y Hx Hy. apply in_map_iff in Hx as [c [<- Hc]]. apply in_map_iff in Hy as [c' [<- Hc']].
destruct (In_areas_cells s t c' Hc') as (a' & next' & Ha' & Hc'').
destruct (area_cell_home L s a (hd_error t) c (Hsub a (or_introl eq_refl)) Hc) as [In1 I1].
destruct (area_cell_home L s a' next' c' (Hsub a' (or_intror Ha')) Hc'') as [In2 I2].
eapply cells_disjoint_via_footprint; [exact HL | exact In1 | exact In2 | | exact I1 | exact I2].
intros E. injection E as <-. exact (Ha Ha').
Qed.
Lemma group_cell_homeX g am c :
usedX X s g am -> In c (group_cells g am) ->
exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
range_incl (cell_range L c) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
Proof.
intros Hu Hc. destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
destruct (In_group_cells_span X R U s g am c HI Hu Hc) as (d & E & Hd & Hw).
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. unfold IB in Hext. lia.
Qed.
Lemma tail_cell_homeX am c g :
usedX X s g am -> In c (group_tail_cells am) ->
exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
range_incl (cell_range L c) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)).
Proof.
intros Hu Hc. destruct (tail_cell_home X R U s HI g am c Hu Hc) as (rg & d & Hr & Hk & Hl & E & Hd & Ho & Hfit & _).
exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
unfold cell_range, crange, range_incl, loc_addr. rewrite E. destruct (am_mem am) as [r o]. cbn [fst snd padd prid poff] in *. unfold UNIT in Hd. lia.
Qed.
Lemma area_entry_not_region a k rg :
In a (st_areas s) -> region_of s k = Some rg -> rg_kind rg = RkMap -> (LMem a, PGSZ) <> (LMem (SP k 0), rg_len rg).
Proof.
intros Ha Hk Hkd E. injection E as -> _.
destruct (proj1 (proj2 (inv_areas HI)) _ Ha) as (r & o & rga & Ea & _ & _ & Hra & _ & _ & Hrak).
injection Ea as <- _. rewrite Hk in Hra. injection Hra as <-. rewrite Hkd in Hrak. exact Hrak.
Qed.
Lemma cellX_home c :
In c (imageX X s ++ tail_cellsX X s) ->
(In c (ctx_cells s) /\ range_incl (cell_range L c) (crange L (LCtx 0, CTX_SIZE))) \/
(In c (areas_cells s (st_areas s)) /\ exists a next, In a (st_areas s) /\ In c (area_cells s a next) /\
range_incl (cell_range L c) (crange L (LMem a, PGSZ))) \/
(exists k rg, region_of s k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
range_incl (cell_range L c) (crange L (LMem (SP k 0), rg_len rg))).
Proof.
intros Hc. apply in_app_iff in Hc as [Hc|Hc].
- unfold imageX in Hc. apply in_app_iff in Hc as [Hc|Hc]; [left; exact (conj Hc (proj2 (ctx_cell_home L s c Hc)))|].
apply in_app_iff in Hc as [Hc|Hc].
+ right; left. split; [exact Hc|]. destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc').
exists a, next. split; [exact Ha|]. split; [exact Hc'|]. exact (proj2 (area_cell_home L s a next c Ha Hc')).
+ right; right. apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [fst snd] in Hc.
destruct (group_cell_homeX g am c (usedX_of_used_metasX g am Hg) Hc) as (rg & Hr & Hk & Hl & _ & I). eauto 8.
- right; right. unfold tail_cellsX in Hc. apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [snd] in Hc.
destruct (tail_cell_homeX am c g (usedX_of_used_metasX g am Hg) Hc) as (rg & Hr & Hk & Hl & _ & I). eauto 8.
Qed.
Theorem meta_cell_exclusive m c :
In m (areas_cells s (st_areas s)) -> In c (imageX X s ++ tail_cellsX X s) ->
c = m \/ ranges_disjoint (cell_range L c) (cell_range L m).
Proof.
intros Hm Hc. pose proof (inv_areas HI) as (ND & _).
destruct (In_areas_cells s _ m Hm) as (am0 & nextm & Ham & Hm'). destruct (area_cell_home L s am0 nextm m Ham Hm') as [Inm Im].
destruct (mcell_eq_dec c m) as [->|Hne]; [left; reflexivity | right].
destruct (cellX_home c Hc) as [[Hcc Ic] | [[Hca _] | (k & rg & Hk & Hkd & Hl & Ic)]].
- eapply cells_disjoint_via_footprint; [exact HL | left; reflexivity | exact Inm | discriminate | exact Ic | exact Im].
- destruct (pairwise_map_In ranges_disjoint (cell_range L) _ _ _ (areas_cells_pairwise' (st_areas s) ND (fun a H => H)) Hca Hm Hne) as [D|D];
[exact D | apply ranges_disjoint_sym; exact D].
- eapply cells_disjoint_via_footprint; [exact HL | apply footprint_region_In; eassumption | exact Inm | | exact Ic | exact Im].
intros E. exact (area_entry_not_region am0 k rg Ham Hk Hkd (eq_sym E)).
Qed.
Theorem ctx_cell_exclusive m c :
In m (ctx_cells s) -> In c (imageX X s ++ tail_cellsX X s) ->
c = m \/ ranges_disjoint (cell_range L c) (cell_range L m).
Proof.
intros Hm Hc. destruct (ctx_cell_home L s m Hm) as [Inm Im].
destruct (mcell_eq_dec c m) as [->|Hne]; [left; reflexivity | right].
destruct (cellX_home c Hc) as [[Hcc Ic] | [[Hca (a & next & Ha & Hc' & Ic)] | (k & rg & Hk & Hkd & Hl & Ic)]].
- destruct (pairwise_map_In ranges_disjoint (cell_range L) _ _ _ (ctx_cells_disjoint L s) Hcc Hm Hne) as [D|D];
[exact D | apply ranges_disjoint_sym; exact D].
- eapply cells_disjoint_via_footprint; [exact HL | exact (proj1 (area_cell_home L s a next c Ha Hc')) | exact Inm | discriminate | exact Ic | exact Im].
- eapply cells_disjoint_via_footprint; [exact HL | apply footprint_region_In; eassumption | exact Inm | discriminate | exact Ic | exact Im].
Qed.
Lemma meta_cells_in_areas g am c :
MT s g = Some (MUsed am) -> In c (meta_slot_cells g (Some (MUsed am))) -> In c (areas_cells s (st_areas s)).
Proof.
intros Mg Hc. pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP g ltac:(unfold keys; apply in_map_iff; exists (g, MUsed am); split; [reflexivity | apply In_of_mlookup; exact Mg])) as (a & k & Ha & Hk & E).
apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next.
unfold area_cells. apply in_app_iff. right. apply in_flat_map. exists (Z.to_nat k).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. rewrite <- E. unfold MT in Mg. rewrite Mg. exact Hc.
Qed.
End f.
End e.
