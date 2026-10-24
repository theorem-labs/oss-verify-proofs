(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09 YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (mem1 : word -> option byte) (sp : Z).
Hypothesis MR : MRc B L A mem md.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis Hfr : ss_fr (nth_slot am idx) = Some fr.
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis HI2 : Inv [] (Some (g, idx)) U0 (upd_meta g (MUsed (am_rel idx am)) A).
Hypothesis Hsp : alloc_ceiling + 8192 <= sp.
Hypothesis F1 : forall a, 0 <= a < 2 ^ 64 ->
~ (ptr_addr L (frame_ptr am idx fr) - 3 <= a < ptr_addr L (frame_ptr am idx fr)) -> ~ (sp - 8192 <= a < sp) ->
mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Hypothesis F2 : mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 3) = Some (Z_to_bv 8 255) /\
mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 2) = Some (Z_to_bv 8 0) /\
mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 1) = Some (Z_to_bv 8 0).
Hypothesis F4 : forall a, (ptr_addr L (frame_ptr am idx fr) - 3 <= a < ptr_addr L (frame_ptr am idx fr)) -> present mem1 a.
Theorem memrep_rel :
memrep B L (upd_meta g (MUsed (am_rel idx am)) A) mem1 /\ tail_geom L (upd_meta g (MUsed (am_rel idx am)) A).
Proof.
set (am2 := am_rel idx am) in *. set (A2 := upd_meta g (MUsed am2) A) in *.
pose proof (mc_wf _ _ _ _ _ MR) as HW. pose proof (mc_layout _ _ _ _ _ MR) as HL.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & _) & Hhdr0).
assert (SE : shape_eq am am2 idx) by (apply shape_eq_rel; [exact Hidx | exact Glen]).
assert (Hnone : ss_fr (nth_slot am2 idx) = None).
{ subst am2. rewrite nth_slot_rel by (exact Hidx || exact Glen). apply released_slot_fr. rewrite Hfr. discriminate. }
assert (HL2 : layout_ok L A2) by (subst A2; apply layout_ok_upd_meta; exact HL).
assert (Hu2 : usedX [] A2 g am2) by (subst A2; apply usedX_upd; left; auto).
destruct (used_group_region [] None U0 A g am HW Hu) as (rg & Hrg1 & Hrgk & Hrgl & Ho & Hext & _).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hrg1 Hrgl) as (Ral & R4096 & Rceil & Rimg).
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
remember (ly_reg L kr) as GLO eqn:EGLO. remember (stride_of am) as ST eqn:EST.
assert (P1 : 0 <= ST * idx) by nia. assert (P2 : ST * idx + ST <= ST * (am_last am + 1)) by nia.
remember (ptr_addr L (frame_ptr am idx fr)) as P eqn:EP.
assert (Est : loc_addr L (LMem (slot_start am idx)) = GLO + ko + 16 + ST * idx).
{ unfold loc_addr, slot_start. rewrite Emem. cbn [padd]. subst ST GLO. unfold UNIT. lia. }
assert (Efp : P = GLO + ko + 16 + ST * idx + 16 * fr_off fr).
{ rewrite EP. unfold ptr_addr, loc_addr, frame_ptr, slot_start. rewrite Emem. cbn [padd]. subst ST GLO. unfold UNIT. lia. }
unfold group_extent, UNIT, IB in Hext. rewrite <- EST in Hext. unfold UNIT, IB in Bf.
pose proof alloc_ceiling_lt as HCE.
destruct (meta_in_area A g (MUsed am) HW (In_of_mlookup _ _ _ Mg)) as (a & ka & Hain & Hka & Eg).
destruct (proj1 (proj2 (inv_areas HW)) a Hain) as (ra & oa & rga & Ea & Hoa & Hoa2 & Hra & Hral & Hoalen & Hrak).
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hra Hral) as (Aal & A4096 & Aceil & Aimg).
remember (ly_reg L ra) as ALO eqn:EALO.
assert (Eg' : ptr_addr L g = ALO + oa + AREA_HDR + META_SIZE * ka).
{ unfold ptr_addr, loc_addr. rewrite Eg, Ea. cbn [padd]. subst ALO. lia. }
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *.
assert (InG : In (LMem (SP kr 0), rg_len rg) (footprint A)) by (apply footprint_region_In; assumption).
assert (InA : In (LMem a, 4096) (footprint A)) by (right; apply in_app_iff; left; apply in_map_iff; exists a; auto).
pose proof HL as (_ & _ & PW & FB).
assert (FLOW : forall e x, In e (footprint A) -> loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> 4096 <= x < alloc_ceiling).
{ intros e x He Hx. exact (footprint_low B L A mem md e x MR He Hx). }
destruct (image_upd_slot A g am idx Mg Hidx) as (l1 & l2 & Eim & Hchk & Hctx & Hareas & Hnew).
pose proof (image_cells_disjoint A L HW HL) as DISJ. rewrite Eim in DISJ.
assert (D23 : exists d2 d3, In d2 (slot_rest am idx) /\ In d3 (slot_rest am idx) /\
cell_range L d2 = (P - 3, 1) /\ cell_range L d3 = (P - 2, 2)).
{ unfold slot_rest. destruct (Z.eq_dec (fr_off fr) 0) as [O0|O0].
- rewrite (Hhdr0 O0). eexists; eexists. split; [apply in_app_iff; left; left; reflexivity|].
split; [apply in_app_iff; left; right; left; reflexivity|].
unfold cell_range. cbn [mc_loc mc_w]. unfold loc_addr, slot_start. rewrite Emem. cbn [padd]. rewrite <- EGLO, <- EST. unfold UNIT. split; f_equal; lia.
- rewrite Hfr. replace (fr_off fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact O0).
eexists; eexists. split; [apply in_app_iff; right; right; left; reflexivity|].
split; [apply in_app_iff; right; right; right; left; reflexivity|].
unfold cell_range. cbn [mc_loc mc_w]. unfold loc_addr, slot_start. rewrite Emem. cbn [padd]. rewrite <- EGLO, <- EST. unfold UNIT. split; f_equal; lia. }
destruct D23 as (d2 & d3 & Hd2 & Hd3 & Rd2 & Rd3).
assert (AVOIDP : forall c k, In c (l1 ++ l2) -> (k < mc_w c)%nat ->
~ (P - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < P)).
{ intros c k Hc Hkw Hin.
destruct (pairwise_app_mid ranges_disjoint (cell_range L) l1 (slot_rest am idx) l2 d2 c DISJ Hd2 Hc) as [D|D];
destruct (pairwise_app_mid ranges_disjoint (cell_range L) l1 (slot_rest am idx) l2 d3 c DISJ Hd3 Hc) as [D'|D'];
rewrite Rd2 in D; rewrite Rd3 in D'; unfold ranges_disjoint, cell_range in D, D'; cbn [fst snd] in D, D'; lia. }
assert (LOWA : forall c k, In c (image A) -> (k < mc_w c)%nat -> 4096 <= loc_addr L (mc_loc c) + Z.of_nat k < alloc_ceiling).
{ intros c k Hc Hkw. destruct (image_in_footprint A L c HW HL Hc) as (e & He & Hincl).
unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. apply (FLOW e _ He). lia. }
pose proof (fun c (H : In c (image A)) => memrep_cell B L A mem c (MRc_memrep B L A mem md MR) H) as CELL.
assert (KEEP : forall c, In c (image A) ->
(forall k, (k < mc_w c)%nat -> ~ (P - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < P)) ->
cell_mem B L mem1 c).
{ intros c HcA Hav. apply (cell_keep B L mem mem1 c (CELL c HcA)). intros k Hkw.
pose proof (LOWA c k HcA Hkw). apply F1; [lia | apply Hav; exact Hkw | lia]. }
assert (Vmeta : am_prev am2 = am_prev am /\ am_next am2 = am_next am /\ am_mem am2 = am_mem am /\ am_avail am2 = am_avail am /\ meta_bits am2 = meta_bits am /\ am_freed am2 = am_freed am).
{ subst am2. unfold am_rel, upd_slot, meta_bits. cbn. repeat split; reflexivity. }
assert (IMG : Forall (cell_mem B L mem1) (image A2)).
{ apply Forall_forall. intros c Hc2.
destruct (Hnew am2 c SE Hc2) as [Hl12 | [Hmeta | Hslot]].
-
assert (HcA : In c (image A)) by (rewrite Eim; apply in_app_iff in Hl12 as [H|H]; apply in_app_iff; [left; exact H | right; apply in_app_iff; right; exact H]).
apply KEEP; [exact HcA | intros k Hkw; apply (AVOIDP c k Hl12 Hkw)].
-
destruct Vmeta as (V1 & V2 & V3 & V4 & V5 & V6).
assert (HcA : In c (areas_cells A (st_areas A))).
{ assert (Hm : In c (meta_slot_cells g (Some (MUsed am)))).
{ cbn [meta_slot_cells] in Hmeta |- *. rewrite V1, V2, V3, V4, V5, V6 in Hmeta.
destruct Hmeta as [H|[H|[H|[H|[H|[H|[]]]]]]]; try (rewrite <- H; cbn; tauto). }
pose proof (meta_cells_in_image A g am c HW Hu Hm) as HI.
unfold image in HI. apply in_app_iff in HI as [HI|HI].
{ exfalso. destruct (In_ctx_cells A c HI) as (off & E & _). cbn [meta_slot_cells] in Hm.
destruct Hm as [H|[H|[H|[H|[H|[H|[]]]]]]]; rewrite <- H in E; discriminate. }
apply in_app_iff in HI as [HI|HI]; [exact HI|]. exfalso.
apply in_flat_map in HI as ([g' am'] & Hg' & Hc'). cbn [fst snd] in Hc'.
apply (used_metas_usedX A g' am' HW) in Hg'.
destruct (group_cell_home L A g' am' c HW Hg' Hc') as (rg' & Hr' & Hk' & _ & In' & Incl').
destruct (area_cell_home L A a (hd_error []) c Hain) as [InA' InclA].
{ unfold area_cells. apply in_app_iff. right. apply in_flat_map. exists (Z.to_nat ka). split; [apply (proj2 (in_seq _ _ _)); unfold METAS_PER_AREA; lia|].
rewrite Z2Nat.id by lia. unfold AREA_HDR, META_SIZE. rewrite <- Eg. change (mlookup (st_metas A) g) with (MT A g). rewrite Mg. exact Hm. }
assert (Hne' : (LMem (SP (prid (am_mem am')) 0), rg_len rg') <> (LMem a, 4096)).
{ intros E. injection E as E1 E2. rewrite Ea in E1. injection E1 as E3 E4. rewrite <- E3, Hr' in Hra. injection Hra as <-. rewrite Hk' in Hrak. exact Hrak. }
pose proof (cells_disjoint_via_footprint L A c c _ _ HL In' InA Hne' Incl' InclA) as D.
unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D.
cbn [meta_slot_cells] in Hm. destruct Hm as [H|[H|[H|[H|[H|[H|[]]]]]]]; rewrite <- H in D; cbn [mc_w] in D; lia. }
assert (Hl1 : In c l1) by (apply Hareas; exact HcA).
apply KEEP; [| intros k Hkw; apply (AVOIDP c k); [apply in_app_iff; left; exact Hl1 | exact Hkw]].
unfold image. apply in_app_iff. right. apply in_app_iff. left. exact HcA.
-
unfold slot_rest in Hslot. rewrite Hnone in Hslot. rewrite app_nil_r in Hslot.
subst am2. rewrite nth_slot_rel in Hslot by (exact Hidx || exact Glen).
rewrite (shape_eq_slot_start am _ idx idx SE) in Hslot.
unfold released_slot in Hslot. rewrite Hfr in Hslot. destruct F2 as (F2a & F2b & F2c).
destruct (fr_off fr =? 0) eqn:O0.
+ apply Z.eqb_eq in O0. cbn [ss_hdr] in Hslot.
destruct Hslot as [<-|[<-|[]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros k Hkw.
* destruct k; [|lia]. replace (Z.of_nat 0) with 0 by reflexivity. rewrite Z.add_0_r.
replace (loc_addr L (LMem (padd (slot_start am idx) (-3)))) with (P - 3); [rewrite F2a; reflexivity|].
unfold loc_addr, slot_start. rewrite Emem. cbn [padd]. unfold UNIT. lia.
* replace (loc_addr L (LMem (padd (slot_start am idx) (-2)))) with (P - 2) by (unfold loc_addr, slot_start; rewrite Emem; cbn [padd]; unfold UNIT; lia).
destruct k as [|[|]]; [| | lia].
-- replace (Z.of_nat 0) with 0 by reflexivity. rewrite Z.add_0_r, F2b. f_equal.
-- replace (P - 2 + Z.of_nat 1) with (P - 1) by lia. rewrite F2c. f_equal.
+ apply Z.eqb_neq in O0. cbn [ss_hdr] in Hslot.
destruct (ss_hdr (nth_slot am idx)) as [[h3 h16]|] eqn:Ehdr; [|destruct Hslot].
destruct (slot_start_cells A g am idx HW ltac:(apply (used_metas_usedX A g am HW); exact Hu) Hidx) as [_ SC]. rewrite Ehdr in SC. destruct SC as [SC3 SC16].
assert (HcA : In c (image A)) by (destruct Hslot as [<-|[<-|[]]]; assumption).
apply KEEP; [exact HcA |].
intros k Hkw. destruct Hslot as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hkw |- *; unfold loc_addr, slot_start; rewrite Emem; cbn [padd]; unfold UNIT; lia. }
assert (TL : forall c, In c (tail_cells A2) -> In c (tail_cells A) /\ forall k, (k < mc_w c)%nat ->
4096 <= loc_addr L (mc_loc c) + Z.of_nat k < alloc_ceiling /\
~ (P - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < P)).
{ intros c Hc2. assert (HcA : In c (tail_cells A)) by (subst A2; eapply tail_cells_upd; eauto). split; [exact HcA|].
intros k Hkw.
unfold tail_cells in Hc2. apply in_flat_map in Hc2 as ([g'' am''] & Hg'' & Hc''). cbn [snd] in Hc''.
assert (Hu'' : usedX [] A2 g'' am'') by (apply usedX_intro; [reflexivity|]; apply (used_metas_iff A2 g'' am'' (proj1 (inv_keys HI2))); exact Hg'').
destruct (tail_cell_span [] (Some (g, idx)) U0 A2 HI2 g'' am'' c Hu'' Hc'') as (d & Hloc & Hd16 & Hdw).
destruct (used_group_region [] (Some (g, idx)) U0 A2 g'' am'' HI2 Hu'') as (rg'' & Hrg'' & Hk'' & Hl'' & Ho'' & Hext'' & _).
assert (Hrg''A : region_of A (prid (am_mem am'')) = Some rg'') by (subst A2; exact Hrg'').
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hrg''A Hl'') as (Ral'' & R4096'' & Rceil'' & _).
pose proof (footprint_region_In A _ _ Hrg''A Hk'' Hl'') as In''.
rewrite Hloc. destruct (am_mem am'') as [kr'' ko''] eqn:Emem''. cbn [prid poff loc_addr padd] in *.
unfold IB in Hext''. unfold UNIT in Hd16.
split; [clear - R4096'' Rceil'' Ho'' Hd16 Hdw Hext'' Hkw; lia|].
destruct (Nat.eq_dec kr'' kr) as [->|Hkr].
+ pose proof (tail_cells_avoid_slot [] (Some (g, idx)) U0 A2 HI2 g am2 idx g'' am'' c d k Hu2 ltac:(destruct SE as (_&_&_&Hl&_); rewrite Hl; exact Hidx) Hnone Hu'' Hc'') as AV.
rewrite Emem'' in AV. cbn [prid poff] in AV. destruct SE as (SEm & _).
specialize (AV Hloc Hkw ltac:(rewrite SEm, Emem; reflexivity)).
rewrite (shape_eq_slot_start am am2 idx idx) in AV by (apply shape_eq_rel; [exact Hidx | exact Glen]).
rewrite (shape_eq_stride am am2 idx) in AV by (apply shape_eq_rel; [exact Hidx | exact Glen]).
rewrite poff_slot_start, Emem in AV. cbn [poff] in AV. rewrite <- EST in AV. unfold UNIT, IB in AV. lia.
+ assert (Hne' : (LMem (SP kr'' 0), rg_len rg'') <> (LMem (SP kr 0), rg_len rg)) by (intros E; injection E; intros; exact (Hkr ltac:(assumption))).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In'' InG Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; rewrite <- ?EGLO in D; lia. }
split; [split; [exact IMG | split]|].
-   apply Forall_forall. intros c Hc2. destruct (TL c Hc2) as [HcA Hbytes].
apply (cell_keep B L mem mem1 c (memrep_tail B L A mem c (MRc_memrep B L A mem md MR) HcA)).
intros k Hkw. destruct (Hbytes k Hkw) as (B1 & B2). apply F1; lia.
-   subst A2. rewrite footprint_upd_meta. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ MR) e He) as Fe.
unfold foot_ok in *. destruct e as [[o|q] len]; cbn [fst snd] in *; [exact I|]. intros x Hx.
pose proof (FLOW _ x He Hx) as Lx. cbn [fst snd] in Lx.
destruct (Z_lt_dec x (P - 3)) as [L1|L1]; [| destruct (Z_lt_dec x P) as [L2|L2]; [apply F4; lia|]];
(destruct (Fe x Hx) as [b Hb]; exists b; rewrite <- Hb; apply F1; lia).
-   unfold tail_geom. apply Forall_forall. intros c Hc2 k Hkw. destruct (TL c Hc2) as [HcA _].
pose proof (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ MR) c HcA k Hkw) as [Hin Hnb].
split; [exact Hin|].
intros (b & Hb & Hx). apply Hnb. exists b. split; [| exact Hx]. subst A2. eapply user_blocks_upd; eauto.
Qed.
End h.
End f.
