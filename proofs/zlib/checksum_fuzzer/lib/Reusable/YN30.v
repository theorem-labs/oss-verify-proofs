(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0b YO0g YO0w YO0s YO0u YO15 YO10 YO12 YO0v YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2b YN31 YN25 YN26 YN2a
YN2o YN2u YN2p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma loc_addr_padd_ L p d : loc_addr L (LMem (padd p d)) = ptr_addr L p + d.
Proof. destruct p; cbn. unfold ptr_addr. cbn. lia. Qed.
Lemma ptr_addr_padd_ L p d : ptr_addr L (padd p d) = ptr_addr L p + d.
Proof. destruct p; unfold ptr_addr; cbn. lia. Qed.
Lemma le_byte_1_0 z : 0 <= z < 256 -> le_byte z 1 0 = z.
Proof. intros Hz. unfold le_byte. change (2 ^ (8 * Z.of_nat 1))%Z with 256%Z. change (8 * Z.of_nat 0)%Z with 0%Z. rewrite Z.shiftr_0_r.
rewrite (Z.mod_small z 256) by lia. apply Z.mod_small. lia. Qed.
Lemma meta_slot_cells_upd_slot g am i x :
meta_slot_cells g (Some (MUsed (upd_slot am i x))) = meta_slot_cells g (Some (MUsed am)).
Proof. destruct am; reflexivity. Qed.
Lemma shape_eq_upd_slot am idx x :
0 <= idx -> (Z.to_nat idx < length (am_slots am))%nat -> shape_eq am (upd_slot am idx x) idx.
Proof.
intros Hidx Hlen. unfold shape_eq.
split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|].
split; [destruct am; reflexivity|]. split; [destruct am; reflexivity|].
intros j Hj Hne. rewrite nth_slot_upd_slot by assumption. replace (j =? idx) with false by (symmetry; apply Z.eqb_neq; exact Hne). reflexivity.
Qed.
Section h.
Lemma area_cells_upd_same s g am am' a next :
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
Lemma areas_cells_upd_same s g am am' l :
MT s g = Some (MUsed am) ->
meta_slot_cells g (Some (MUsed am')) = meta_slot_cells g (Some (MUsed am)) ->
areas_cells (upd_meta g (MUsed am') s) l = areas_cells s l.
Proof.
intros Hg Hm. induction l as [|a t IH]; cbn [areas_cells]; [reflexivity|].
rewrite IH. f_equal. destruct t; apply (area_cells_upd_same s g am am'); assumption.
Qed.
End h.
Theorem image_upd_slot_eq s g am am' idx :
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am -> shape_eq am am' idx ->
meta_slot_cells g (Some (MUsed am')) = meta_slot_cells g (Some (MUsed am)) ->
exists l1 l2, image s = l1 ++ slot_rest am idx ++ l2 /\
image (upd_meta g (MUsed am') s) = l1 ++ slot_rest am' idx ++ l2 /\
In (slot_chk am idx) l1.
Proof.
intros Hg Hidx SE Hm.
destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
destruct (zseq_split (am_last am + 1) idx ltac:(lia)) as (z1 & z2 & Ez & Hnz).
set (GC := fun gm : sptr * ameta => group_cells (fst gm) (snd gm)).
exists (ctx_cells s ++ areas_cells s (st_areas s) ++ flat_map GC u1 ++ group_hdr g am ++ flat_map (slot_cells am) z1 ++ [slot_chk am idx]),
(flat_map (slot_cells am) z2 ++ flat_map GC u2).
assert (EZ : forall z, (forall j, In j z -> In j (zseq 0 (am_last am + 1)) /\ j <> idx) ->
flat_map (slot_cells am') z = flat_map (slot_cells am) z).
{ intros z Hz. apply flat_map_ext_In. intros j Hj. destruct (Hz j Hj) as [Hin Hne]. apply In_zseq in Hin.
apply (shape_eq_slot_cells am am' idx j SE); lia. }
split; [|split].
- unfold image. fold GC. rewrite Eu, flat_map_app. cbn [flat_map]. unfold GC at 2. cbn [fst snd].
rewrite group_cells_eq, Ez, flat_map_app. cbn [flat_map]. rewrite slot_cells_eq. cbn [app].
rewrite !app_comm_cons. rewrite ?app_nil_r. repeat rewrite <- app_assoc. reflexivity.
- unfold image. rewrite ctx_cells_upd_meta. change (st_areas (upd_meta g (MUsed am') s)) with (st_areas s).
rewrite (areas_cells_upd_same s g am am' (st_areas s) Hg Hm).
fold GC. rewrite Eu', flat_map_app. cbn [flat_map]. unfold GC at 2. cbn [fst snd].
rewrite group_cells_eq, (shape_eq_hdr g am am' idx SE).
replace (am_last am') with (am_last am) by (destruct SE as (_ & _ & _ & H & _); symmetry; exact H).
rewrite Ez, flat_map_app. cbn [flat_map]. rewrite slot_cells_eq, (shape_eq_chk am am' idx SE). cbn [app].
rewrite (EZ z1) by (intros j Hj; split; [rewrite Ez; apply in_app_iff; left; exact Hj | intros ->; apply Hnz; apply in_app_iff; left; exact Hj]).
rewrite (EZ z2) by (intros j Hj; split; [rewrite Ez; apply in_app_iff; right; right; exact Hj | intros ->; apply Hnz; apply in_app_iff; right; exact Hj]).
rewrite !app_comm_cons. rewrite ?app_nil_r. repeat rewrite <- app_assoc. reflexivity.
- rewrite !in_app_iff. right; right; right; right; right. left. reflexivity.
Qed.
Lemma tail_cells_upd' s g am am' idx c :
MT s g = Some (MUsed am) -> shape_eq am am' idx -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = None ->
In c (tail_cells (upd_meta g (MUsed am') s)) -> In c (tail_cells s) \/ In c (frame_tail_cells am' idx).
Proof.
intros Hg SE Hidx Hnone Hc. destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
unfold tail_cells in *. rewrite Eu' in Hc. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
apply in_app_iff in Hc as [Hc|Hc]; [left; apply in_app_iff; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc]; [| left; apply in_app_iff; right; apply in_app_iff; right; exact Hc].
cbn [snd] in *. pose proof (shape_eq_stride _ _ _ SE) as Hst. destruct SE as (Hm & Hml & Hai & Hl & Hsc & Hs).
unfold group_tail_cells in *. destruct Hc as [<-|Hc].
- left. apply in_app_iff. right. apply in_app_iff. left. left. unfold group_extent. rewrite Hm, Hst, Hl. reflexivity.
- apply in_flat_map in Hc as (j & Hj & Hc). rewrite Hl in Hj. pose proof Hj as Hj'. apply In_zseq in Hj'.
destruct (Z.eq_dec j idx) as [->|Hne]; [right; exact Hc|].
left. apply in_app_iff. right. apply in_app_iff. left. right. apply in_flat_map. exists j. split; [exact Hj|].
unfold frame_tail_cells, reserved_of, slot_end, frame_ptr, slot_start in *. rewrite (Hs j ltac:(lia) Hne), Hst, Hm in Hc. exact Hc.
Qed.
Lemma cell_keep_mbyte B L mem mem' c :
cell_mem B L mem c ->
(forall k, (k < mc_w c)%nat -> mbyte (ms_segs B) mem' (loc_addr L (mc_loc c) + Z.of_nat k) = mbyte (ms_segs B) mem (loc_addr L (mc_loc c) + Z.of_nat k)) ->
cell_mem B L mem' c.
Proof.
intros Hc Heq. unfold cell_mem in *. destruct c as [loc w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v; try (intros k Hk; rewrite (Heq k Hk); exact (Hc k Hk)).
intros Hw. destruct (Hc Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
specialize (Heq 0%nat Hw). rewrite Z.add_0_r in Heq. rewrite Heq. exact Hb.
Qed.
Lemma no_child_at_frameless X R U s g am idx :
Inv X R U s -> usedX X s g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = None ->
forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am idx.
Proof.
intros HI Hu Hidx Hnone c ac Uc Hml Emc.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof (inv_groups HI c ac Uc) as (_ & _ & _ & _ & _ & Gns).
destruct (Gns Hml) as (_ & g' & am' & i' & fr' & U' & Hi' & Hfr' & Hk' & Em & _).
pose proof (inv_groups HI g' am' U') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'.
rewrite Emc in Em.
pose proof (f_equal poff Em) as Eo. pose proof (f_equal prid Em) as Er. rewrite !prid_slot_start in Er.
destruct (sptr_eq_dec g' g) as [->|Hne].
- pose proof (usedX_fun _ _ _ _ _ U' Hu) as ->.
rewrite !poff_slot_start in Eo. assert (i' = idx) as -> by nia. rewrite Hnone in Hfr'. discriminate.
- pose proof (slot_in_span X R U s HI g am idx Hu Hidx) as [S1 S2].
pose proof (slot_in_span X R U s HI g' am' i' U' Hi') as [S1' S2'].
pose proof (extent_pos _ _ _ _ _ G) as EP. pose proof (extent_pos _ _ _ _ _ G') as EP'.
destruct (inv_laminar HI g' am' g am U' Hu Hne (eq_sym Er)) as [D | [I | I]].
+ unfold spans_disjoint in D. unfold UNIT, IB in *. lia.
+ destruct (inside_slot_start X R U s HI g' am' i' g am U' Hu Hi' I) as (j & fr & Hj & Hfr & Hk & Lo & Hi2).
rewrite <- Eo in Lo, Hi2. rewrite !poff_slot_start in Lo, Hi2.
assert (idx <> j) by (intros ->; rewrite Hnone in Hfr; discriminate).
assert (idx < j \/ j < idx) as [C|C] by lia; unfold UNIT in *; nia.
+ destruct (inside_slot_start X R U s HI g am idx g' am' Hu U' Hidx I) as (j & fr & Hj & Hfr & Hk & Lo & Hi2).
rewrite Eo in Lo, Hi2. rewrite !poff_slot_start in Lo, Hi2.
assert (i' < j \/ j < i' \/ i' = j) as [C|[C|C]] by lia; [unfold UNIT in *; nia | unfold UNIT in *; nia |].
subst j. unfold UNIT in *. lia.
Qed.
Section m.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (U : Z -> Z).
Variables (g : sptr) (am : ameta) (idx off n : Z) (hdr : Z * Z) (memF : word -> option byte).
Definition fr1 : frame := mkFrame off n FUser.
Definition am1 : ameta := upd_slot am idx (mkSlot (Some hdr) (Some fr1)).
Definition A1 : astate := upd_meta g (MUsed am1) A.
Hypothesis MID : midrep B L A mem md.
Hypothesis HI : Inv [] (Some (g, idx)) U A.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis HW1 : WF A1.
Hypothesis Hoff : 0 <= off /\ 0 <= n /\ UNIT * off + n <= stride_of am - IB.
Hypothesis Hhdr : hdr = (if off =? 0 then (hdr_byte3 am1 idx fr1, hdr_off16 am1 idx fr1) else (224, off)).
Definition P0 : Z := ptr_addr L (slot_start am idx).
Definition Q : Z := P0 + UNIT * off.
Definition E : Z := P0 + stride_of am - IB.
Definition rsv : Z := reserved_of am1 fr1.
Hypothesis F_frame : forall x, 0 <= x < 2 ^ 64 ->
~ ((P0 - 4 <= x < P0) \/ (Q - 4 <= x < Q) \/ (Q + n <= x < E)) -> memF (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Hypothesis F_present : forall a, mem a <> None -> memF a <> None.
Hypothesis F_hdr :
mbyte (ms_segs B) memF (P0 - 4) = Some (Z_to_bv 8 0) /\
mbyte (ms_segs B) memF (P0 - 3) = Some (Z_to_bv 8 (fst hdr)) /\
(forall k, (k < 2)%nat -> mbyte (ms_segs B) memF (P0 - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (snd hdr) 2 k))) /\
mbyte (ms_segs B) memF (Q - 4) = Some (Z_to_bv 8 0) /\
mbyte (ms_segs B) memF (Q - 3) = Some (Z_to_bv 8 (hdr_byte3 am1 idx fr1)) /\
(forall k, (k < 2)%nat -> mbyte (ms_segs B) memF (Q - 2 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (hdr_off16 am1 idx fr1) 2 k))).
Hypothesis F_tail :
(0 < rsv -> mbyte (ms_segs B) memF (Q + n) = Some (Z_to_bv 8 0)) /\
(5 <= rsv -> mbyte (ms_segs B) memF (E - 5) = Some (Z_to_bv 8 0)) /\
(5 <= rsv -> forall k, (k < 4)%nat -> mbyte (ms_segs B) memF (E - 4 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte rsv 4 k))).
Let MR : memrep B L A mem := mid_mem _ _ _ _ _ MID.
Let HL : layout_ok L A := mid_layout _ _ _ _ _ MID.
Let Mg : MT A g = Some (MUsed am) := proj1 (usedX_MT _ _ _ _ Hu).
Lemma G_facts :
length (am_slots am) = Z.to_nat (am_last am + 1) /\ 16 <= stride_of am /\
ss_fr (nth_slot am idx) = None /\ (0 <= am_sc am /\ 0 <= am_last am <= 31) /\
(exists rg, region_of A (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
0 <= poff (am_mem am) /\ poff (am_mem am) + group_extent am + IB <= rg_len rg).
Proof.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _ & Glen & _) & _ & _ & Gcl & _).
destruct (inv_reserved HI g idx eq_refl) as (am_ & Hu_ & _ & Hfr_ & _). pose proof (usedX_fun _ _ _ _ _ Hu_ Hu) as ->.
split; [exact Glen|]. split; [exact Sp|]. split; [exact Hfr_|]. split; [destruct Gcl as [(C & _)|(C & _)]; lia|].
destruct (used_group_region [] (Some (g, idx)) U A g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _). exists rg. auto 10.
Qed.
Lemma SE : shape_eq am am1 idx.
Proof. pose proof G_facts as (Glen & _). apply shape_eq_upd_slot; [lia | rewrite Glen; lia]. Qed.
Lemma slot1 : nth_slot am1 idx = mkSlot (Some hdr) (Some fr1).
Proof. pose proof G_facts as (Glen & _). unfold am1. rewrite nth_slot_upd_slot by (try lia; rewrite Glen; lia). rewrite Z.eqb_refl. reflexivity. Qed.
Lemma HL1 : layout_ok L A1.
Proof. unfold A1. apply layout_ok_upd_meta. exact HL. Qed.
Lemma Hu1 : usedX [] A1 g am1.
Proof. unfold A1. apply usedX_upd. left. pose proof (usedX_MT _ _ _ _ Hu) as [_ NX]. auto. Qed.
Lemma lin :
exists kr ko GLO ST rg,
am_mem am = SP kr ko /\ ly_reg L kr = GLO /\ stride_of am = ST /\ 16 <= ST /\
P0 = GLO + ko + 16 + ST * idx /\ 0 <= ST * idx /\ ST * idx + ST <= ST * (am_last am + 1) /\
region_of A kr = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\ 0 <= ko /\
ko + 16 + ST * (am_last am + 1) <= rg_len rg /\
GLO mod PGSZ = 0 /\ 4096 <= GLO /\ GLO + rg_len rg <= alloc_ceiling /\
(forall a, GLO <= a < GLO + rg_len rg -> ~ in_img B a) /\
In (LMem (SP kr 0), rg_len rg) (footprint A).
Proof.
pose proof G_facts as (Glen & Sp & Hnone & Hsc0 & (rg & Hr & Hk & Hl & Ho & Hext)).
destruct (am_mem am) as [kr ko] eqn:Emem. cbn [prid poff] in *.
destruct (lg_placed _ _ _ _ (mid_ledger _ _ _ _ _ MID) _ _ Hr Hl) as (Ral & R4096 & Rceil & Rimg).
exists kr, ko, (ly_reg L kr), (stride_of am), rg.
assert (P1 : 0 <= stride_of am * idx) by nia. assert (P2 : stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
unfold group_extent, UNIT, IB in Hext.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
split; [unfold P0, ptr_addr, loc_addr, slot_start; rewrite Emem; cbn [padd]; unfold UNIT; lia|].
split; [lia|]. split; [lia|]. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [lia|]. split; [lia|].
split; [exact Ral|]. split; [lia|]. split; [lia|]. split; [exact Rimg|]. apply footprint_region_In; assumption.
Qed.
Lemma old_chk : mbyte (ms_segs B) mem (P0 - 4) = Some (Z_to_bv 8 0).
Proof.
destruct (image_upd_slot A g am idx Mg Hidx) as (l1 & l2 & Eim & Hchk & _).
assert (Hc : In (slot_chk am idx) (image A)) by (rewrite Eim; apply in_app_iff; left; exact Hchk).
pose proof (memrep_cell B L A mem _ MR Hc) as C. unfold cell_mem, slot_chk in C. cbn [mc_loc mc_w mc_val sval_num] in C.
specialize (C 0%nat ltac:(lia)). rewrite loc_addr_padd_, Z.add_0_r in C. unfold P0. exact C.
Qed.
Lemma unchanged x : 0 <= x < 2 ^ 64 -> ~ (P0 - 3 <= x < E) ->
mbyte (ms_segs B) memF x = mbyte (ms_segs B) mem x /\ (present mem x -> present memF x).
Proof.
intros Hx Hn. pose proof Hoff as (Ho1 & Ho2 & Ho3). pose proof G_facts as (_ & Sp & _).
destruct (Z.eq_dec x (P0 - 4)) as [->|Hne].
- rewrite (proj1 F_hdr), old_chk. split; [reflexivity|]. intros [b Hb].
destruct (memF (Z_to_bv 64 (P0 - 4))) as [b'|] eqn:Eb; [exists b'; exact Eb|]. exfalso. apply (F_present (Z_to_bv 64 (P0 - 4))); [rewrite Hb; discriminate | exact Eb].
- assert (EQ : memF (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
{ apply F_frame; [exact Hx|]. unfold Q, E in *. unfold UNIT, IB in *. lia. }
split; [unfold mbyte; rewrite EQ; reflexivity|]. intros [b Hb]. exists b. rewrite EQ. exact Hb.
Qed.
Lemma old_image_body c k :
In c (image A) -> (k < mc_w c)%nat -> ~ (P0 <= loc_addr L (mc_loc c) + Z.of_nat k < E).
Proof.
intros Hc Hk Hin. pose proof G_facts as (Glen & Sp & Hnone & _).
destruct lin as (kr & ko & GLO & ST & rg & Emem & EGLO & EST & _ & EP0 & P1 & P2 & _).
assert (B1 : poff (slot_start am idx) <= poff (slot_start am idx)) by lia.
assert (B2 : poff (slot_start am idx) + stride_of am - IB <= poff (slot_start am idx) + stride_of am - IB) by lia.
assert (B3 : poff (slot_start am idx) < poff (slot_start am idx) + stride_of am - IB) by (unfold IB; clear - Sp; lia).
pose proof (slot_body_free [] (Some (g, idx)) U A L HI HL g am idx (poff (slot_start am idx)) (poff (slot_start am idx) + stride_of am - IB)
Hu Hidx Hnone B1 B2 c) as D.
specialize (D ltac:(unfold imageX, image in *; rewrite used_metasX_nil; apply in_app_iff; left; exact Hc)).
unfold ranges_disjoint, cell_range in D. cbn [fst snd] in D.
unfold E, P0, ptr_addr in Hin. rewrite Emem in D. cbn [prid] in D. unfold slot_start in D, Hin. rewrite Emem in D, Hin. cbn [padd poff loc_addr] in D, Hin.
clear - D Hin Sp P1 Hk. lia.
Qed.
Lemma old_tail_body c k :
In c (tail_cells A) -> (k < mc_w c)%nat -> ~ (P0 - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < E).
Proof.
intros Hc Hk Hin. pose proof G_facts as (Glen & Sp & Hnone & _).
destruct lin as (kr & ko & GLO & ST & rg & Emem & EGLO & EST & ST16 & EP0 & P1 & P2 & Hr & Hrk & Hrl & Hko & Hfit & _ & _ & _ & _ & InR).
unfold tail_cells in Hc. apply in_flat_map in Hc as ([g' am'] & Hg' & Hc'). cbn [snd] in Hc'.
assert (Hu' : usedX [] A g' am').
{ apply usedX_intro; [reflexivity|]. apply (used_metas_iff A g' am' (proj1 (inv_keys HI))). exact Hg'. }
destruct (tail_cell_home [] (Some (g, idx)) U A HI g' am' c Hu' Hc') as (rg' & d & Hr' & Hk' & Hl' & Eloc & Hd & Ho' & Hfit' & _).
rewrite Eloc in Hin. destruct (am_mem am') as [kr' ko'] eqn:Emem'. cbn [prid poff loc_addr padd] in *.
destruct (Nat.eq_dec kr' kr) as [->|Hne].
- pose proof (tail_cells_avoid_slot [] (Some (g, idx)) U A HI g am idx g' am' c d k Hu Hidx Hnone Hu' Hc') as AV.
rewrite Emem' in AV. cbn [prid poff] in AV. specialize (AV Eloc Hk ltac:(rewrite Emem; reflexivity)).
rewrite poff_slot_start, Emem in AV. cbn [poff] in AV. unfold E, P0, ptr_addr, slot_start in Hin. rewrite Emem in Hin. cbn [loc_addr padd] in Hin.
unfold UNIT, IB in *. lia.
- pose proof HL as (_ & _ & PW & _).
pose proof (footprint_region_In A _ _ Hr' Hk' Hl') as In'.
assert (Hne' : (LMem (SP kr' 0), rg_len rg') <> (LMem (SP kr 0), rg_len rg)) by (intros X; injection X; intros; exact (Hne ltac:(assumption))).
unfold E, P0, ptr_addr, slot_start in Hin. rewrite Emem in Hin. cbn [loc_addr padd] in Hin.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In' InR Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; unfold UNIT, IB in *;
clear - D Hin Hfit' Ho' Hd Hk Hko Hfit P1 P2 EGLO EST ST16; lia.
Qed.
Lemma HB3R : 0 <= hdr_byte3 am1 idx fr1 < 256.
Proof.
pose proof Hoff as (Ho1 & Ho2 & Ho3). pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some fr1))) as (_ & _ & _ & _ & Fst & _).
pose proof G_facts as (_ & _ & _ & [_ Glast] & _).
unfold hdr_byte3. cbn [fr_kind fr1].
assert (R0 : 0 <= stride_of am1 - IB - UNIT * fr_off fr1 - fr_n fr1).
{ unfold am1. rewrite Fst. cbn [fr_off fr_n fr1]. unfold UNIT, IB in *. clear - Ho1 Ho2 Ho3. lia. }
pose proof (rsv_code_range am1 fr1 R0). clear - H Hidx Glast. lia.
Qed.
Lemma H3R : 0 <= fst hdr < 256.
Proof. rewrite Hhdr. pose proof HB3R. destruct (off =? 0); cbn [fst]; lia. Qed.
Theorem memrep_enframe : memrep B L A1 memF.
Proof.
pose proof G_facts as (Glen & Sp & Hnone & Hsc0 & _). pose proof Hoff as (Ho1 & Ho2 & Ho3). pose proof HB3R as HB3R. pose proof H3R as H3R.
destruct lin as (kr & ko & GLO & ST & rg & Emem & EGLO & EST & ST16 & EP0 & P1 & P2 & Hr & Hrk & Hrl & Hko & Hfit & Ral & R4096 & Rceil & Rimg & InR).
pose proof alloc_ceiling_lt as HCE.
destruct (image_upd_slot_eq A g am am1 idx Mg Hidx SE (meta_slot_cells_upd_slot g am idx _)) as (l1 & l2 & Eim & Eim1 & Hchk).
fold A1 in Eim1.
pose proof (image_cells_disjoint A1 L HW1 HL1) as DISJ1. rewrite Eim1 in DISJ1.
assert (NEWh : In (MCell (LMem (padd (slot_start am idx) (-3))) 1 (VZ (fst hdr))) (slot_rest am1 idx) /\
In (MCell (LMem (padd (slot_start am idx) (-2))) 2 (VZ (snd hdr))) (slot_rest am1 idx)).
{ unfold slot_rest. rewrite slot1. cbn [ss_hdr ss_fr]. rewrite (shape_eq_slot_start _ _ _ idx SE). destruct hdr as [h3 h16]. cbn [fst snd].
split; apply in_app_iff; left; cbn; auto. }
destruct NEWh as [N3 N16].
assert (KEEP : forall c, In c (l1 ++ l2) -> c <> slot_chk am idx -> forall k, (k < mc_w c)%nat ->
~ (P0 - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < E)).
{ intros c Hc Hne k Hk Hin.
assert (HcA : In c (image A)) by (rewrite Eim; apply in_app_iff in Hc as [Hc|Hc]; apply in_app_iff; [left; exact Hc | right; apply in_app_iff; right; exact Hc]).
destruct (Z_lt_dec (loc_addr L (mc_loc c) + Z.of_nat k) P0) as [Hlt|Hge]; [| apply (old_image_body c k HcA Hk); lia].
destruct (pairwise_app_mid ranges_disjoint (cell_range L) l1 (slot_rest am1 idx) l2 _ c DISJ1 N3 Hc) as [D|D];
destruct (pairwise_app_mid ranges_disjoint (cell_range L) l1 (slot_rest am1 idx) l2 _ c DISJ1 N16 Hc) as [D'|D'];
unfold ranges_disjoint, cell_range in D, D'; cbn [fst snd mc_loc mc_w] in D, D'; rewrite loc_addr_padd_ in D, D'; fold P0 in D, D'; lia. }
assert (ADDR : forall c k, In c (image A) \/ In c (tail_cells A) -> (k < mc_w c)%nat -> 0 <= loc_addr L (mc_loc c) + Z.of_nat k < 2 ^ 64).
{ intros c k Hc Hk.
destruct (cellX_in_footprint [] (Some (g, idx)) U A L HI c) as (e & He & Ie).
{ unfold imageX, tail_cellsX, image, tail_cells in *. rewrite used_metasX_nil. apply in_app_iff. exact Hc. }
pose proof (proj2 (proj2 (proj2 HL)) _ He) as Re. unfold range_incl, cell_range, crange in Ie, Re. cbn [fst snd] in Ie, Re.
clear - Ie Re Hk. lia. }
split; [|split].
-
apply Forall_forall. intros c Hc1. rewrite Eim1 in Hc1.
assert (CASES : In c (l1 ++ l2) \/ In c (slot_rest am1 idx)).
{ apply in_app_iff in Hc1 as [H|H]; [left; apply in_app_iff; left; exact H|].
apply in_app_iff in H as [H|H]; [right; exact H | left; apply in_app_iff; right; exact H]. }
destruct CASES as [Hold | Hnew].
+ destruct (mcell_eq_dec c (slot_chk am idx)) as [-> | Hne].
* unfold cell_mem, slot_chk. cbn [mc_loc mc_w mc_val sval_num]. intros k Hk. destruct k; [|lia].
rewrite loc_addr_padd_, Z.add_0_r. fold P0. replace (P0 + -4) with (P0 - 4) by lia. rewrite (proj1 F_hdr). reflexivity.
* assert (HcA : In c (image A)) by (rewrite Eim; apply in_app_iff in Hold as [H|H]; apply in_app_iff; [left; exact H | right; apply in_app_iff; right; exact H]).
apply (cell_keep_mbyte B L mem memF c (memrep_cell B L A mem c MR HcA)).
intros k Hk. apply (proj1 (unchanged _ (ADDR c k (or_introl HcA) Hk) (KEEP c Hold Hne k Hk))).
+
destruct F_hdr as (Fc4 & F3 & F16 & Fq4 & Fq3 & Fq16).
unfold slot_rest in Hnew. rewrite slot1 in Hnew. cbn [ss_hdr ss_fr] in Hnew. rewrite (shape_eq_slot_start _ _ _ idx SE) in Hnew.
change (fr_off fr1) with off in Hnew.
apply in_app_iff in Hnew as [Hnew|Hnew].
* destruct hdr as [h3 h16]. cbn [fst snd] in F3, F16.
destruct Hnew as [<-|[<-|[]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros k Hk; rewrite loc_addr_padd_; fold P0.
-- destruct k; [|lia]. rewrite Z.add_0_r. replace (P0 + -3) with (P0 - 3) by lia. rewrite F3. f_equal. rewrite le_byte_1_0 by exact H3R. reflexivity.
-- replace (P0 + -2) with (P0 - 2) by lia. apply F16. exact Hk.
* destruct (off =? 0) eqn:Eo; [destruct Hnew|].
destruct Hnew as [<-|[<-|[<-|[]]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros k Hk; rewrite !loc_addr_padd_, !ptr_addr_padd_; fold P0.
-- destruct k; [|lia]. rewrite Z.add_0_r. replace (P0 + UNIT * off + -4) with (Q - 4) by (unfold Q; lia). rewrite Fq4. f_equal.
-- destruct k; [|lia]. rewrite Z.add_0_r. replace (P0 + UNIT * off + -3) with (Q - 3) by (unfold Q; lia). rewrite Fq3. f_equal. rewrite le_byte_1_0 by exact HB3R. reflexivity.
-- replace (P0 + UNIT * off + -2) with (Q - 2) by (unfold Q; lia). apply Fq16. exact Hk.
-
apply Forall_forall. intros c Hc1.
destruct (tail_cells_upd' A g am am1 idx c Mg SE Hidx Hnone Hc1) as [Hold | Hnew].
+ apply (cell_keep_mbyte B L mem memF c (memrep_tail B L A mem c MR Hold)).
intros k Hk. apply (proj1 (unchanged _ (ADDR c k (or_intror Hold) Hk) (old_tail_body c k Hold Hk))).
+ destruct F_tail as (T1 & T2 & T3).
unfold frame_tail_cells in Hnew. rewrite slot1 in Hnew. cbn [ss_fr fr_kind fr1] in Hnew. fold fr1 in Hnew. fold rsv in Hnew.
pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some fr1))) as (_ & _ & _ & _ & Fst & _ & Fss). fold am1 in Fst, Fss.
assert (EQn : loc_addr L (LMem (padd (frame_ptr am1 idx fr1) (fr_n fr1))) = Q + n).
{ unfold frame_ptr. rewrite Fss. rewrite !loc_addr_padd_, ptr_addr_padd_. cbn [fr_off fr_n fr1]. unfold Q, P0. lia. }
assert (EQe : forall d, loc_addr L (LMem (padd (slot_end am1 idx) d)) = E + d).
{ intros d. unfold slot_end. rewrite Fss, Fst. rewrite !loc_addr_padd_, ptr_addr_padd_. unfold E, P0. lia. }
apply in_app_iff in Hnew as [Hnew|Hnew].
* destruct (0 <? rsv) eqn:Er; [|destruct Hnew]. apply Z.ltb_lt in Er. destruct Hnew as [<-|[]].
unfold cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros k Hk. destruct k; [|lia]. rewrite EQn, Z.add_0_r, (T1 Er). reflexivity.
* destruct (5 <=? rsv) eqn:Er; [|destruct Hnew]. apply Z.leb_le in Er. destruct Hnew as [<-|[<-|[]]]; unfold cell_mem; cbn [mc_loc mc_w mc_val sval_num]; intros k Hk.
-- rewrite EQe. replace (E + -4) with (E - 4) by lia. apply (T3 Er). exact Hk.
-- destruct k; [|lia]. rewrite EQe, Z.add_0_r. replace (E + -5) with (E - 5) by lia. rewrite (T2 Er). reflexivity.
-
unfold A1. rewrite footprint_upd_meta. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) e He) as Fe.
unfold foot_ok in *. destruct e as [[o|q] len]; cbn [fst snd] in *; [exact I|]. intros x Hx.
destruct (Fe x Hx) as [b Hb]. destruct (memF (Z_to_bv 64 x)) as [b'|] eqn:Eb; [exists b'; exact Eb|].
exfalso. apply (F_present (Z_to_bv 64 x)); [rewrite Hb; discriminate | exact Eb].
Qed.
Hypothesis HB : bounded A.
Hypothesis HR : rsv_ok A.
Hypothesis HAma : ama_ok A.
Hypothesis HSp : span_ok A.
Hypothesis Hsc48 : am_sc am < 48.
Lemma frames_upd' g0 am0 i fr :
In (g0, am0, i, fr) (frames A1) ->
(g0 = g /\ am0 = am1 /\ i = idx /\ fr = fr1) \/ exists am0', In (g0, am0', i, fr) (frames A) /\ stride_of am0' = stride_of am0.
Proof.
pose proof G_facts as (Glen & Sp & Hnone & _).
intros Hf. destruct (used_metas_upd A g am Mg) as (u1 & u2 & Eu & Eu').
unfold frames in *. unfold A1 in Hf. rewrite Eu' in Hf. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
apply in_app_iff in Hf as [Hf|Hf].
{ right. exists am0. split; [apply in_app_iff; left; exact Hf | reflexivity]. }
apply in_app_iff in Hf as [Hf|Hf].
2:{ right. exists am0. split; [apply in_app_iff; right; apply in_app_iff; right; exact Hf | reflexivity]. }
pose proof SE as SE'. pose proof (shape_eq_stride _ _ _ SE') as Hst. destruct SE' as (Hm & Hml & Hai & Hl & Hsc & Hs).
apply in_flat_map in Hf as (j & Hj & Hf). rewrite Hl in Hj. pose proof Hj as Hj'. apply In_zseq in Hj'.
destruct (Z.eq_dec j idx) as [->|Hne].
- rewrite slot1 in Hf. cbn [ss_fr] in Hf. destruct Hf as [E0|[]]. injection E0 as <- <- <- <-. left. auto.
- rewrite (Hs j ltac:(lia) Hne) in Hf. destruct (ss_fr (nth_slot am j)) as [fr0|] eqn:Efr; [|destruct Hf]. destruct Hf as [E0|[]].
injection E0 as <- <- <- <-. right. exists am. split; [|symmetry; exact Hst].
apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists j. split; [exact Hj|]. rewrite Efr. left. reflexivity.
Qed.
Lemma rsv_ok_A1 : rsv_ok A1.
Proof.
pose proof Hoff as (Ho1 & Ho2 & Ho3). pose proof G_facts as (Glen & Sp & Hnone & [Hsc0 Glast] & _).
pose proof (inv_groups HI g am Hu) as (_ & _ & _ & Gcl & _).
intros g0 am0 i fr Hf Hk. destruct (frames_upd' g0 am0 i fr Hf) as [(-> & -> & -> & ->) | (am0' & Hf' & Hst)].
- unfold reserved_of. pose proof (upd_slot_fields am idx (mkSlot (Some hdr) (Some fr1))) as (_ & _ & _ & _ & Fst & _). fold am1 in Fst. rewrite Fst.
cbn [fr_off fr_n fr1]. destruct Gcl as [(C & _) | (_ & _ & _ & Cext)]; [lia|].
assert (stride_of am <= stride_of am * (am_last am + 1)) by nia. unfold UNIT, IB in *. clear - Ho1 Ho2 Ho3 Cext H. lia.
- pose proof (HR g0 am0' i fr Hf' Hk) as R. unfold reserved_of in *. rewrite Hst in R. exact R.
Qed.
Lemma span_ok_A1 : span_ok A1.
Proof.
unfold A1. apply (span_ok_upd_same3 A g am); [exact HSp | exact (proj1 (usedX_MT _ _ _ _ Hu)) | reflexivity | reflexivity | reflexivity].
Qed.
Lemma statics_A1 : statics_ok B memF.
Proof.
pose proof G_facts as (Glen & Sp & Hnone & _). pose proof Hoff as (Ho1 & Ho2 & Ho3).
destruct lin as (kr & ko & GLO & ST & rg & Emem & EGLO & EST & ST16 & EP0 & P1 & P2 & Hr & Hrk & Hrl & Hko & Hfit & Ral & R4096 & Rceil & Rimg & InR).
apply (statics_ok_ext B mem memF (mid_statics _ _ _ _ _ MID)).
intros a Ha. pose proof (so_statics_img _ (mid_syms _ _ _ _ _ MID) a Ha) as Hi. pose proof (so_img_hi _ (mid_syms _ _ _ _ _ MID) a Hi) as Hlo.
assert (NIN : ~ (P0 - 3 <= a < E)).
{ intros Hin. apply (Rimg a); [| exact Hi]. unfold E, IB in Hin. clear - Hin EP0 EST ST16 P1 P2 Hko Hfit. lia. }
exact (proj1 (unchanged a ltac:(pose proof alloc_ceiling_lt; lia) NIN)).
Qed.
Theorem MRx_enframe : MRx B L A1 memF md.
Proof.
pose proof (mid_md _ _ _ _ _ MID) as (Hh & Hlz & Hmat).
apply midrep_MRx; [| exact HW1 | unfold A1; apply (proj2 (bounded_upd_meta _ _ _)); exact HB | apply rsv_ok_A1 | unfold A1, ama_ok in *; cbn; exact HAma | apply span_ok_A1].
split.
- exact (mid_syms _ _ _ _ _ MID).
- apply memrep_enframe.
- apply tail_geom_of_WF; [exact HW1 | apply HL1].
- apply statics_A1.
- unfold A1. apply ledger_ok_upd_meta. exact (mid_ledger _ _ _ _ _ MID).
- eapply ledger_x_same_regions; [exact (mid_ledgerx _ _ _ _ _ MID) | reflexivity | reflexivity | reflexivity].
- apply HL1.
- exact (mid_ctx _ _ _ _ _ MID).
- exact (mid_sec _ _ _ _ _ MID).
- exact (mid_md _ _ _ _ _ MID).
Qed.
End m.
End f.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
