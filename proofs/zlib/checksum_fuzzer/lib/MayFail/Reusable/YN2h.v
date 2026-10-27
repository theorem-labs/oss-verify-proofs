(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2h.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2g.
From Stdlib Require Import List.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition Xclean (X : list sptr) (s : astate) : Prop :=
forall x am, In x X -> MT s x <> Some (MUsed am).
Lemma Xclean_nil : forall s, Xclean [] s.
Proof. intros s x am []. Qed.
Section e.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.
Hypothesis XC : Xclean X s.
Lemma used_metas_usedX' : forall g am, In (g, am) (used_metas s) <-> usedX X s g am.
Proof.
intros g am. rewrite (used_metas_iff s g am (proj1 (inv_keys HI))). unfold usedX, MTX. split.
- intros HM. destruct (memb g X) eqn:Em; [|exact HM].
exfalso. apply (XC g am); [apply memb_In; exact Em | exact HM].
- intros H. destruct (memb g X); [discriminate | exact H].
Qed.
Lemma area_prid : forall a, In a (st_areas s) -> (prid a < length (st_regions s))%nat.
Proof.
intros a Ha. destruct (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & -> & _ & _ & Hr & _). cbn. exact (region_of_lt _ _ _ Hr).
Qed.
Lemma key_prid : forall p, In p (keys s) -> (prid p < length (st_regions s))%nat.
Proof.
intros p Hp. destruct (inv_keys HI) as (_ & KP & _). destruct (KP p Hp) as (a & k & Ha & _ & E). rewrite E.
pose proof (area_prid _ Ha) as H. destruct a as [r o]. cbn in *. exact H.
Qed.
Lemma used_prid : forall g am, usedX X s g am -> (prid (am_mem am) < length (st_regions s))%nat.
Proof. intros g am Hu. exact (used_group_prid_lt _ _ _ _ g am HI Hu). Qed.
Lemma used_links_keys : forall g am, usedX X s g am ->
(forall p, am_prev am = Some p -> In p (keys s)) /\ (forall q, am_next am = Some q -> In q (keys s)).
Proof.
intros g am Hu. pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _).
destruct (inv_rings HI) as (F & AR & D).
destruct Gcl as [(C63 & _) | (Csc & _)].
- destruct (D g am Hu C63) as [E1 E2]. rewrite E1, E2. split; intros; discriminate.
- destruct (AR (am_sc am) Csc) as (ms & Rg & Mem & _).
destruct (am_prev am) as [pr|] eqn:Ep; destruct (am_next am) as [nx|] eqn:En;
try (split; intros; try discriminate).
all: assert (Hin : In g ms) by (apply (Mem g am Hu eq_refl); rewrite Ep, En; intros E; discriminate).
all: assert (AL : alinks X s (am_sc am) g = Some (am_prev am, am_next am))
by (unfold alinks; unfold usedX in Hu; rewrite Hu, Z.eqb_refl; reflexivity).
all: rewrite Ep, En in AL.
all: destruct (cycle_link_in _ ms g _ _ (proj1 Rg) Hin AL) as [P Q].
all: try (injection H as <-).
+ destruct (ring_members_used _ _ _ _ _ _ Rg (P pr eq_refl)) as (am' & Hu' & _). exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu'))).
+ destruct (ring_members_used _ _ _ _ _ _ Rg (Q nx eq_refl)) as (am' & Hu' & _). exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu'))).
+ destruct (ring_members_used _ _ _ _ _ _ Rg (P pr eq_refl)) as (am' & Hu' & _). exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu'))).
+ destruct (ring_members_used _ _ _ _ _ _ Rg (Q nx eq_refl)) as (am' & Hu' & _). exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu'))).
Qed.
Lemma free_ring_keys : forall ms, ring_ok (flinks X s) (st_free_meta_head s) ms -> forall p, In p ms -> In p (keys s).
Proof.
intros ms Rg p Hp. destruct (ring_links _ _ _ _ Rg Hp) as (pr' & nx' & L).
destruct (flinks_free _ _ _ _ L) as (pr & nx & _ & HM & _). exact (MT_Some_In_keys _ _ _ HM).
Qed.
Lemma free_links_keys : forall g pr nx, MT s g = Some (MFree pr nx) ->
(forall p, pr = Some p -> In p (keys s)) /\ (forall q, nx = Some q -> In q (keys s)).
Proof.
intros g pr nx Hg. destruct (inv_rings HI) as ((ms & Rg & Mem) & _).
destruct (memb g X) eqn:Em.
-
pose proof (proj1 (inv_meta HI) g (proj1 (memb_In _ _) Em)) as [_ Hx]. rewrite Hg in Hx.
destruct pr, nx; try contradiction. split; intros; discriminate.
- assert (Hin : In g ms) by (apply (Mem g pr nx); unfold MTX; rewrite Em; exact Hg).
assert (FL : flinks X s g = Some (pr, nx)) by (unfold flinks, MTX; rewrite Em, Hg; reflexivity).
destruct (cycle_link_in _ ms g _ _ (proj1 Rg) Hin FL) as [P Q].
split; [intros p Hp; apply (free_ring_keys ms Rg), P, Hp | intros q Hq; apply (free_ring_keys ms Rg), Q, Hq].
Qed.
Lemma free_head_key : forall p, st_free_meta_head s = Some p -> In p (keys s).
Proof.
intros p Hp. destruct (inv_rings HI) as ((ms & Rg & Mem) & _). rewrite Hp in Rg.
destruct (ring_head_In _ _ _ Rg) as [Hin _]. rewrite <- Hp in Rg. exact (free_ring_keys ms Rg p Hin).
Qed.
Lemma active_head_key : forall k p, (k < 48)%nat -> nth k (st_active s) None = Some p -> In p (keys s).
Proof.
intros k p Hk Hp. destruct (inv_rings HI) as (_ & AR & _).
destruct (AR (Z.of_nat k) ltac:(lia)) as (ms & Rg & _).
unfold active_hd in Rg. rewrite Nat2Z.id, Hp in Rg.
destruct (ring_head_In _ _ _ Rg) as [Hin _].
destruct (ring_members_used _ _ _ _ _ _ Rg Hin) as (am & Hu & _). exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu))).
Qed.
Let N := length (st_regions s).
Hypothesis AMA : ama_ok s.
Lemma ctx_cells_below : forall c, In c (ctx_cells s) -> refs_below N c.
Proof.
intros c Hc. pose proof (inv_areas HI) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
destruct (inv_keys HI) as (_ & KP & K3 & K4 & K5).
unfold ctx_cells in Hc. rewrite !in_app_iff in Hc. cbn [In] in Hc.
destruct Hc as [[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]] | [Hc|[Hc|[Hc|Hc]]]];
try (apply (refs_below_intro s); [exact I|]).
- destruct (st_init_done s); exact I.
- exact I.
- exact I.
- apply (optr_below s). intros p Hp. apply key_prid. apply free_head_key. exact Hp.
- destruct (st_areas s) as [|a0 l] eqn:Ea; [exact I|]. cbn.
rewrite (K4 ltac:(congruence)). rewrite prid_padd. apply area_prid. rewrite ?Ea. apply In_last. discriminate.
- exact I.
- exact I.
- exact I.
- apply (optr_below s). intros p Hp. rewrite A3 in Hp. destruct (st_areas s) as [|a0 l] eqn:Ea; [discriminate|]. cbn in Hp. injection Hp as <-.
apply area_prid. rewrite Ea. left. reflexivity.
- apply (optr_below s). intros p Hp. rewrite A4 in Hp. destruct (st_areas s) as [|a0 l] eqn:Ea; [discriminate|]. injection Hp as <-.
pose proof (area_prid (last (a0 :: l) (SP 0%nat 0))) as H. rewrite Ea in H. apply H. apply In_last. discriminate.
- destruct (Z.eq_dec (st_avail_meta_area_count s) 0) as [E0|E0].
+ rewrite E0. cbn [Z.eqb andb]. destruct (st_areas s) as [|a0 l] eqn:Ea; cbn; [exact I|].
unfold ama_ok in AMA. apply AMA. rewrite Ea. discriminate.
+ pose proof (inv_ctx HI) as CT.
destruct (A8 ltac:(destruct CT as (_&_&_&_&_&_&_&_&_&_&C11&_); lia)) as (r & o & rg & Er & Hr & _).
replace ((match st_areas s with [] => true | _ :: _ => false end) && (st_avail_meta_area_count s =? 0)) with false.
* rewrite Er. cbn. exact (region_of_lt _ _ _ Hr).
* symmetry. apply andb_false_iff. right. apply Z.eqb_neq. exact E0.
- exact I.
- destruct (st_brk s) as [| |r pg] eqn:Eb; try exact I. cbn. rewrite ?Eb in A7. destruct A7 as (_ & rg & Hr & _). exact (region_of_lt _ _ _ Hr).
- apply in_map_iff in Hc as (k & <- & Hk). apply in_seq in Hk. apply (refs_below_intro s); [exact I|].
apply (optr_below s). intros p Hp. apply key_prid. apply (active_head_key k); [lia | exact Hp].
- apply in_map_iff in Hc as (k & <- & Hk). apply (refs_below_intro s); exact I.
- apply in_map_iff in Hc as (k & <- & Hk). apply (refs_below_intro s); exact I.
- apply in_map_iff in Hc as (k & <- & Hk). apply (refs_below_intro s); exact I.
Qed.
Lemma meta_slot_cells_below : forall q x c, (prid q < N)%nat ->
(forall am, x = Some (MUsed am) -> usedX X s q am) ->
(forall pr nx, x = Some (MFree pr nx) -> MT s q = Some (MFree pr nx)) ->
In c (meta_slot_cells q x) -> refs_below N c.
Proof.
intros q x c Hq Hu Hf Hc.
assert (LOC : match mc_loc c with LMem p => (prid p < N)%nat | LCtx _ => True end).
{ destruct (In_meta_slot_cells q x c Hc) as (d & -> & _). rewrite prid_padd. exact Hq. }
split; [exact LOC|].
destruct x as [[pr nx| |am]|]; cbn [meta_slot_cells] in Hc.
- destruct (free_links_keys q pr nx (Hf pr nx eq_refl)) as [P Q].
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_val]; try exact I; apply (optr_below s); intros p Hp; apply key_prid; auto.
- destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; exact I.
- pose proof (Hu am eq_refl) as Us. destruct (used_links_keys q am Us) as [P Q].
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [mc_val]; try exact I.
+ apply (optr_below s); intros p Hp; apply key_prid; auto.
+ apply (optr_below s); intros p Hp; apply key_prid; auto.
+ exact (used_prid q am Us).
- destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; exact I.
Qed.
Lemma area_cells_below : forall a next c, In a (st_areas s) ->
(forall p, next = Some p -> In p (st_areas s)) ->
In c (area_cells s a next) -> refs_below N c.
Proof.
intros a next c Ha Hnext Hc. pose proof (area_prid a Ha) as Pa.
unfold area_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
- destruct Hc as [<-|[<-|[<-|[]]]]; (split; [cbn; rewrite ?prid_padd; exact Pa|]); cbn [mc_val]; try exact I.
apply (optr_below s). intros p Hp. apply area_prid. apply Hnext. exact Hp.
- apply in_flat_map in Hc as (k & Hk & Hc). cbv zeta in Hc.
eapply meta_slot_cells_below; [| | |exact Hc].
+ rewrite prid_padd. exact Pa.
+ intros am E. apply used_metas_usedX'. apply (used_metas_iff s _ _ (proj1 (inv_keys HI))). exact E.
+ intros pr nx E. exact E.
Qed.
Lemma areas_cells_below : forall l c, (forall a, In a l -> In a (st_areas s)) -> In c (areas_cells s l) -> refs_below N c.
Proof.
induction l as [|a l IH]; intros c Hl Hc; [destruct Hc|].
cbn [areas_cells] in Hc. apply in_app_iff in Hc as [Hc|Hc].
- eapply area_cells_below; [apply Hl; left; reflexivity | | exact Hc].
intros p Hp. destruct l; [discriminate|]. injection Hp as <-. apply Hl. right. left. reflexivity.
- apply IH; [intros a' Ha'; apply Hl; right; exact Ha' | exact Hc].
Qed.
Lemma group_cells_below : forall g am c, usedX X s g am -> In c (group_cells g am) -> refs_below N c.
Proof.
intros g am c Hu Hc. pose proof (used_prid g am Hu) as Pg.
assert (LOC : match mc_loc c with LMem p => (prid p < N)%nat | LCtx _ => True end).
{ destruct (In_group_cells X R U s g am c HI Hu Hc) as (d & -> & _). rewrite prid_padd. exact Pg. }
split; [exact LOC|].
unfold group_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
- destruct Hc as [<-|[<-|[]]]; cbn [mc_val].
+ apply key_prid. exact (MT_Some_In_keys _ _ _ (proj1 (usedX_MT _ _ _ _ Hu))).
+ destruct (am_maplen am =? 0); exact I.
- apply in_flat_map in Hc as (i & Hi & Hc). unfold slot_cells in Hc. cbv zeta in Hc.
rewrite !in_app_iff in Hc. destruct Hc as [[<-|[]] | [Hc | Hc]]; [exact I| |].
+ destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hc]. destruct Hc as [<-|[<-|[]]]; exact I.
+ destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hc]. destruct (fr_off fr =? 0); [destruct Hc|].
destruct Hc as [<-|[<-|[<-|[]]]]; exact I.
Qed.
Lemma tail_cells_below : forall c, In c (tail_cells s) -> refs_below N c.
Proof.
intros c Hc. unfold tail_cells in Hc. apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [snd] in Hc.
apply used_metas_usedX' in Hg. pose proof (used_prid g am Hg) as Pg.
unfold group_tail_cells in Hc. destruct Hc as [<- | Hc]; [split; [cbn; rewrite prid_padd; exact Pg | exact I]|].
apply in_flat_map in Hc as (i & Hi & Hc). unfold frame_tail_cells in Hc.
destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hc]. destruct (fr_kind fr); [|destruct Hc].
apply in_app_iff in Hc as [Hc|Hc].
- destruct (0 <? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]].
split; [cbn; unfold frame_ptr, slot_start; rewrite !prid_padd; exact Pg | exact I].
- destruct (5 <=? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[<-|[]]];
(split; [cbn; unfold slot_end, slot_start; rewrite !prid_padd; exact Pg | exact I]).
Qed.
Theorem Inv_ptrs_below : ptrs_below s.
Proof.
intros c [Hc|Hc]; [| exact (tail_cells_below c Hc)].
unfold image in Hc. apply in_app_iff in Hc as [Hc'|Hc']; [exact (ctx_cells_below c Hc')|].
apply in_app_iff in Hc' as [Hc'|Hc'].
- apply (areas_cells_below (st_areas s)); [intros x Hx; exact Hx | exact Hc'].
- apply in_flat_map in Hc' as ([g am] & Hg & Hc'). apply (group_cells_below g am); [apply used_metas_usedX'; exact Hg | exact Hc'].
Qed.
Lemma tail_cell_region : forall c, In c (tail_cells s) ->
exists p rg, mc_loc c = LMem p /\ region_of s (prid p) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff p /\ poff p + Z.of_nat (mc_w c) <= rg_len rg.
Proof.
intros c Hc. unfold tail_cells in Hc. apply in_flat_map in Hc as ([g am] & Hg & Hc). cbn [snd] in Hc.
apply used_metas_usedX' in Hg.
destruct (used_group_region X R U s g am HI Hg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (inv_groups HI g am Hg) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _) & _ & Gsl & _).
assert (Hsi : forall i, 0 <= i <= am_last am -> 0 <= stride_of am * i /\ stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)).
{ intros i Hi. split; [nia|]. nia. }
unfold group_tail_cells in Hc. destruct Hc as [<- | Hc].
- exists (padd (am_mem am) (group_extent am)), rg. destruct (am_mem am) as [k o]. cbn [mc_loc mc_w padd prid poff] in *.
unfold group_extent, UNIT, IB in *. repeat split; try assumption; nia.
- apply in_flat_map in Hc as (i & Hi & Hc). apply In_zseq in Hi. unfold frame_tail_cells in Hc.
destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hc]. destruct (fr_kind fr); [|destruct Hc].
pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (Fn & Foff & Ffit & _) & _).
destruct (Hsi i ltac:(lia)) as [Si1 Si2].
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (0 <? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]].
exists (padd (frame_ptr am i fr) (fr_n fr)), rg. unfold frame_ptr, slot_start. destruct (am_mem am) as [k o].
cbn [mc_loc mc_w padd prid poff] in *. unfold group_extent, UNIT, IB in *. repeat split; try assumption; nia.
+ destruct (5 <=? reserved_of am fr); [|destruct Hc].
destruct Hc as [<-|[<-|[]]]; unfold slot_end, slot_start; destruct (am_mem am) as [k o];
cbn [mc_loc mc_w padd prid poff] in *.
* exists (SP k (o + (UNIT + stride_of am * i) + (stride_of am - IB) + -4)), rg. cbn [prid poff].
unfold group_extent, UNIT, IB in *. repeat split; try assumption; nia.
* exists (SP k (o + (UNIT + stride_of am * i) + (stride_of am - IB) + -5)), rg. cbn [prid poff].
unfold group_extent, UNIT, IB in *. repeat split; try assumption; nia.
Qed.
Lemma group_cell_region : forall g am c, In (g, am) (used_metas s) -> In c (group_cells g am) ->
exists p rg, mc_loc c = LMem p /\ region_of s (prid p) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff p /\ poff p + Z.of_nat (mc_w c) <= rg_len rg.
Proof.
intros g am c Hg Hc. apply used_metas_usedX' in Hg.
destruct (used_group_region X R U s g am HI Hg) as (rg & Hr & Hk & Hl & Ho & Hext & _).
destruct (In_group_cells X R U s g am c HI Hg Hc) as (d & E & Hd1 & Hd2).
exists (padd (am_mem am) d), rg. rewrite E. destruct (am_mem am) as [k o]. cbn [padd prid poff] in *.
repeat split; try assumption; lia.
Qed.
Lemma area_cell_page : forall a next c, In a (st_areas s) -> In c (area_cells s a next) ->
exists d rg, mc_loc c = LMem (padd a d) /\ 0 <= d /\ d + Z.of_nat (mc_w c) <= PGSZ /\
region_of s (prid a) = Some rg /\ rg_kind rg <> RkMap /\ rg_live rg = true /\
PGSZ <= poff a /\ poff a + PGSZ <= rg_len rg /\ poff a mod PGSZ = 0.
Proof.
intros a next c Ha Hc. destruct (In_area_cells s a next c Hc) as (d & E & Hd1 & Hd2).
destruct (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rg & Ea & Ho & Hlo & Hr & Hl & Hlen & Hk).
exists d, rg. rewrite Ea in *. cbn [prid poff]. repeat split; try assumption; try lia.
intros K. rewrite K in Hk. exact Hk.
Qed.
End e.
End b.
