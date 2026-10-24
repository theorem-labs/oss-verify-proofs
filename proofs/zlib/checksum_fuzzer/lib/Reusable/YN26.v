(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0s YK0i YK15 YM06 YM02 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b0.
Variables (A : astate) (p g : sptr) (idx : Z) (am : ameta).
Hypothesis Hff : find_frame_in (st_metas A) p = Some (g, idx).
Hypothesis Hg : mlookup (st_metas A) g = Some (MUsed am).
Definition released_slot : slotst :=
match ss_fr (nth_slot am idx) with
| Some fr => if fr_off fr =? 0 then mkSlot (Some (255, 0)) None else mkSlot (ss_hdr (nth_slot am idx)) None
| None => nth_slot am idx
end.
Definition am_rel : ameta := upd_slot am idx released_slot.
Definition A_rel : astate := upd_meta g (MUsed am_rel) A.
Definition freed' : Z := am_freed am + bit idx.
Definition am_fast : ameta := am_set_freed freed' am_rel.
Definition A_fast : astate := upd_meta g (MUsed am_fast) A_rel.
Definition mask0 : Z := Z.lor (am_freed am) (am_avail am).
Definition fast_cond : bool := negb (am_freed am =? 0) && negb (mask0 + bit idx =? ones (am_last am)).
Definition free_K (r : option (nat * Z) * astate) : itree astate (unit * astate) :=
match fst r with
| Some (k, len) =>
IAsk (KMunmap k len) (snd r)
(fun _ => IRet (tt, set_regions (lupd (st_regions (snd r)) k
(mkRegion RkMap (rg_len (nth k (st_regions (snd r)) (mkRegion RkMap 0 [] false))) [] false)) (snd r)))
| None => IRet (tt, snd r)
end.
Lemma free_tree :
Z.land mask0 (bit idx) = 0 ->
free (Some p) A =
if fast_cond then IRet (tt, A_fast)
else ibind (nontrivial_free NEST_FUEL g idx A_rel) free_K.
Proof.
intros Hmask.
unfold free. unfold bind at 1. unfold find_frame. unfold bind at 1. unfold get. cbn [ibind]. rewrite Hff.
unfold ret at 1. cbn [ibind fst snd].
unfold bind at 1. unfold getm at 1. unfold bind at 1. unfold get. cbn [ibind]. rewrite Hg. unfold ret at 1. cbn [ibind].
unfold bind at 1. unfold release_slot. unfold bind at 1. unfold getm at 1, bind at 1. unfold get. cbn [ibind]. rewrite Hg.
unfold ret at 1. cbn [ibind]. unfold setm at 1, modify. cbn [ibind].
unfold bind at 1. unfold massert. fold mask0. rewrite Hmask. cbn [Z.eqb]. unfold ret at 1; cbn [ibind].
fold released_slot. fold fast_cond. change (upd_slot am idx released_slot) with am_rel.
change (set_metas (mupdate (st_metas A) g (MUsed am_rel)) A) with A_rel.
destruct fast_cond.
- unfold bind, getm, bind, get. cbn [ibind].
change (mlookup (st_metas A_rel) g) with (MT A_rel g). unfold A_rel. rewrite MT_upd_same. fold A_rel.
unfold ret. cbn [ibind]. unfold setm, modify. reflexivity.
- unfold bind at 1. f_equal. apply FunctionalExtensionality.functional_extensionality.
intros [mi s2]. unfold free_K. cbn [fst snd]. destruct mi as [[k len]|]; [|reflexivity].
unfold bind, ask. cbn [ibind]. unfold upd_region, modify. reflexivity.
Qed.
End b0.
Section c0.
Variable segs : list Segment.
Lemma mreal_conj {R} : forall (t : itree astate R) c (Q : R -> config -> Prop) (P : R -> Prop),
mreal segs c t Q -> itok t P -> mreal segs c t (fun r c' => Q r c' /\ P r).
Proof.
induction t as [r | q s k IH | f]; intros c Q P HM HT; cbn in *.
- eapply SR_mono; [exact HM|]. intros c' H'. split; [exact H' | exact HT].
- destruct HT as [_ HT]. eapply SR_mono; [exact HM|]. intros c1 Hk.
destruct q;
try (destruct Hk as (J & nx & bit & i0 & Hn & Hc & Hcl); exists J, nx, bit, i0;
split; [exact Hn|]; split; [| exact Hcl]; intros i; apply IH; [apply Hc|]; apply HT; exact I).
destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply IH; [exact Hc|]. apply HT. exact Hz.
- exact I.
Qed.
End c0.
Lemma footprint_upd_meta g x s : footprint (upd_meta g x s) = footprint s.
Proof. reflexivity. Qed.
Lemma ctx_cells_upd_meta g x s : ctx_cells (upd_meta g x s) = ctx_cells s.
Proof. reflexivity. Qed.
Lemma user_blocks_set_regions f s : user_blocks (set_regions f s) = user_blocks s.
Proof. reflexivity. Qed.
Lemma layout_ok_upd_meta L g x s : layout_ok L (upd_meta g x s) <-> layout_ok L s.
Proof. unfold layout_ok. rewrite footprint_upd_meta. unfold region_of, upd_meta. cbn. tauto. Qed.
Lemma bounded_upd_meta g x s : bounded (upd_meta g x s) <-> bounded s.
Proof. unfold bounded, usage_of, upd_meta. cbn. tauto. Qed.
Lemma live_bytes_upd_meta g x s : live_bytes (upd_meta g x s) = live_bytes s.
Proof. reflexivity. Qed.
Lemma nslots_upd_meta g x s : nslots (upd_meta g x s) = nslots s.
Proof. reflexivity. Qed.
Section e0.
Variable B : malloc_syms.
Lemma ledger_ok_upd_meta L g x s md : ledger_ok B L s md -> ledger_ok B L (upd_meta g x s) md.
Proof.
intros G. split; apply G.
Qed.
Lemma statics_ok_ext mem mem' :
statics_ok B mem ->
(forall a, static_owned B a -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a) ->
statics_ok B mem'.
Proof.
intros S HS. split.
- rewrite HS; [apply (st_needlocks _ _ S) | unfold static_owned; lia].
- intros k Hk. rewrite HS; [apply (st_pagesize _ _ S); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite HS; [apply (st_lock _ _ S); exact Hk | unfold static_owned; lia].
- intros k Hk. rewrite HS; [apply (st_got _ _ S); exact Hk | unfold static_owned; lia].
- destruct (st_guard _ _ S) as (gd & Hg). exists gd. intros k Hk. rewrite HS; [apply Hg; exact Hk | unfold static_owned; lia].
- intros a Ha. rewrite HS; [apply (st_tables _ _ S); exact Ha | unfold static_owned; unfold table_addr in Ha; lia].
Qed.
End e0.
Definition slot_rest (am : ameta) (i : Z) : list mcell :=
match ss_hdr (nth_slot am i) with
| Some (h3, h16) => [MCell (LMem (padd (slot_start am i) (-3))) 1 (VZ h3); MCell (LMem (padd (slot_start am i) (-2))) 2 (VZ h16)]
| None => []
end
++ match ss_fr (nth_slot am i) with
| Some fr =>
if fr_off fr =? 0 then []
else let p := padd (slot_start am i) (UNIT * fr_off fr) in
[MCell (LMem (padd p (-4))) 1 (VZ 0);
MCell (LMem (padd p (-3))) 1 (VZ (hdr_byte3 am i fr));
MCell (LMem (padd p (-2))) 2 (VZ (hdr_off16 am i fr))]
| None => []
end.
Definition slot_chk (am : ameta) (i : Z) : mcell := MCell (LMem (padd (slot_start am i) (-4))) 1 (VZ 0).
Lemma slot_cells_eq am i : slot_cells am i = slot_chk am i :: slot_rest am i.
Proof. reflexivity. Qed.
Definition group_hdr (g : sptr) (am : ameta) : list mcell :=
[MCell (LMem (am_mem am)) 8 (VP g);
(if am_maplen am =? 0 then MCell (LMem (padd (am_mem am) 8)) 1 (VLo5 (am_aidx am))
else MCell (LMem (padd (am_mem am) 8)) 4 (VZ (am_aidx am)))].
Lemma group_cells_eq g am : group_cells g am = group_hdr g am ++ flat_map (slot_cells am) (zseq 0 (am_last am + 1)).
Proof. reflexivity. Qed.
Definition shape_eq (am am' : ameta) (idx : Z) : Prop :=
am_mem am' = am_mem am /\ am_maplen am' = am_maplen am /\ am_aidx am' = am_aidx am /\
am_last am' = am_last am /\ am_sc am' = am_sc am /\
(forall j, 0 <= j -> j <> idx -> nth_slot am' j = nth_slot am j).
Lemma shape_eq_stride am am' idx : shape_eq am am' idx -> stride_of am' = stride_of am.
Proof. intros (_ & Hml & _ & Hl & Hsc & _). unfold stride_of, class_size. rewrite Hml, Hl, Hsc. reflexivity. Qed.
Lemma shape_eq_slot_start am am' idx j : shape_eq am am' idx -> slot_start am' j = slot_start am j.
Proof. intros H. unfold slot_start. rewrite (shape_eq_stride _ _ _ H). destruct H as (-> & _). reflexivity. Qed.
Lemma shape_eq_slot_cells am am' idx j : shape_eq am am' idx -> 0 <= j -> j <> idx -> slot_cells am' j = slot_cells am j.
Proof.
intros H Hj0 Hj. unfold slot_cells. rewrite (shape_eq_slot_start _ _ _ j H).
destruct H as (Hm & Hml & Hai & Hl & Hsc & Hs). rewrite (Hs j Hj0 Hj).
unfold hdr_byte3, hdr_off16, rsv_code.
replace (stride_of am') with (stride_of am) by (symmetry; apply (shape_eq_stride am am' idx); repeat split; auto).
reflexivity.
Qed.
Lemma shape_eq_chk am am' idx : shape_eq am am' idx -> slot_chk am' idx = slot_chk am idx.
Proof. intros H. unfold slot_chk. rewrite (shape_eq_slot_start _ _ _ idx H). reflexivity. Qed.
Lemma shape_eq_hdr g am am' idx : shape_eq am am' idx -> group_hdr g am' = group_hdr g am.
Proof. intros (Hm & Hml & Hai & _). unfold group_hdr. rewrite Hm, Hml, Hai. reflexivity. Qed.
Lemma used_metas_upd s g am :
MT s g = Some (MUsed am) ->
exists u1 u2, used_metas s = u1 ++ (g, am) :: u2 /\
forall am', used_metas (upd_meta g (MUsed am') s) = u1 ++ (g, am') :: u2.
Proof.
unfold MT, used_metas, upd_meta. cbn. induction (st_metas s) as [|[q y] t IH]; cbn; intros H; [discriminate|].
destruct (sptr_eqb g q) eqn:E.
- apply sptr_eqb_eq in E. subst q. injection H as ->. exists [], (flat_map (fun e : sptr * mslot => let (p0, m) := e in match m with MUsed am0 => [(p0, am0)] | _ => [] end) t).
split; [reflexivity|]. intros am'. cbn. reflexivity.
- destruct (IH H) as (u1 & u2 & E1 & E2).
exists (match y with MUsed a0 => [(q, a0)] | _ => [] end ++ u1), u2. split.
+ rewrite E1. destruct y; reflexivity.
+ intros am'. cbn. rewrite E2. destruct y; reflexivity.
Qed.
Lemma area_cells_upd s g x a next c :
In c (area_cells (upd_meta g x s) a next) -> In c (area_cells s a next) \/ In c (meta_slot_cells g (Some x)).
Proof.
unfold area_cells. intros H. apply in_app_iff in H as [H|H]; [left; apply in_app_iff; left; exact H|].
apply in_flat_map in H as (k & Hk & Hc).
change (mlookup (st_metas (upd_meta g x s))) with (MT (upd_meta g x s)) in Hc. rewrite MT_upd in Hc.
destruct (sptr_eqb (padd a (AREA_HDR + META_SIZE * Z.of_nat k)) g) eqn:E.
- apply sptr_eqb_eq in E. rewrite E in Hc. right. exact Hc.
- left. apply in_app_iff. right. apply in_flat_map. exists k. split; [exact Hk|]. exact Hc.
Qed.
Lemma areas_cells_upd s g x l c :
In c (areas_cells (upd_meta g x s) l) -> In c (areas_cells s l) \/ In c (meta_slot_cells g (Some x)).
Proof.
induction l as [|a t IH]; cbn [areas_cells]; intros H; [destruct H|].
apply in_app_iff in H as [H|H].
- destruct (area_cells_upd s g x a (hd_error t) c H) as [H'|H']; [left; apply in_app_iff; left; exact H' | right; exact H'].
- destruct (IH H) as [H'|H']; [left; apply in_app_iff; right; exact H' | right; exact H'].
Qed.
Lemma zseq_split n i : 0 <= i < n -> exists z1 z2, zseq 0 n = z1 ++ i :: z2 /\ ~ In i (z1 ++ z2).
Proof.
intros Hi. destruct (in_split i (zseq 0 n) (proj2 (In_zseq 0 n i) ltac:(lia))) as (z1 & z2 & E).
exists z1, z2. split; [exact E|]. apply NoDup_remove_2. rewrite <- E. apply zseq_NoDup.
Qed.
Theorem image_upd_slot s g am idx :
MT s g = Some (MUsed am) -> 0 <= idx <= am_last am ->
exists l1 l2, image s = l1 ++ slot_rest am idx ++ l2 /\
In (slot_chk am idx) l1 /\
(forall c, In c (ctx_cells s) -> In c l1) /\
(forall c, In c (areas_cells s (st_areas s)) -> In c l1) /\
forall am' c, shape_eq am am' idx ->
In c (image (upd_meta g (MUsed am') s)) ->
In c (l1 ++ l2) \/ In c (meta_slot_cells g (Some (MUsed am'))) \/ In c (slot_rest am' idx).
Proof.
intros Hg Hidx.
destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
destruct (zseq_split (am_last am + 1) idx ltac:(lia)) as (z1 & z2 & Ez & Hnz).
set (GC := fun gm : sptr * ameta => group_cells (fst gm) (snd gm)).
exists (ctx_cells s ++ areas_cells s (st_areas s) ++ flat_map GC u1 ++ group_hdr g am ++ flat_map (slot_cells am) z1 ++ [slot_chk am idx]),
(flat_map (slot_cells am) z2 ++ flat_map GC u2).
split; [|split; [|split; [|split]]].
- unfold image. fold GC. rewrite Eu, flat_map_app. cbn [flat_map]. unfold GC at 2. cbn [fst snd].
rewrite group_cells_eq, Ez, flat_map_app. cbn [flat_map]. rewrite slot_cells_eq. cbn [app].
rewrite !app_comm_cons. rewrite ?app_nil_r. repeat rewrite <- app_assoc. reflexivity.
- rewrite !in_app_iff. right; right; right; right; right. left. reflexivity.
- intros c Hc. rewrite !in_app_iff. left. exact Hc.
- intros c Hc. rewrite !in_app_iff. right; left. exact Hc.
- intros am' c SE Hc. unfold image in Hc. rewrite ctx_cells_upd_meta in Hc.
change (st_areas (upd_meta g (MUsed am') s)) with (st_areas s) in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [left; rewrite !in_app_iff; left; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc].
+ destruct (areas_cells_upd s g (MUsed am') (st_areas s) c Hc) as [H|H]; [left; rewrite !in_app_iff; left; right; left; exact H | right; left; exact H].
+ fold GC in Hc. rewrite Eu', flat_map_app in Hc. cbn [flat_map] in Hc. apply in_app_iff in Hc as [Hc|Hc]; [left; rewrite !in_app_iff; left; right; right; left; exact Hc|].
apply in_app_iff in Hc as [Hc|Hc]; [| left; rewrite !in_app_iff; right; right; exact Hc].
unfold GC in Hc. cbn [fst snd] in Hc. rewrite group_cells_eq in Hc. rewrite (shape_eq_hdr g am am' idx SE) in Hc.
replace (am_last am') with (am_last am) in Hc by (destruct SE as (_ & _ & _ & H & _); symmetry; exact H).
rewrite Ez, flat_map_app in Hc. cbn [flat_map] in Hc.
apply in_app_iff in Hc as [Hc|Hc]; [left; rewrite !in_app_iff; left; right; right; right; left; exact Hc|].
assert (EZ : forall z, (forall j, In j z -> In j (zseq 0 (am_last am + 1)) /\ j <> idx) ->
flat_map (slot_cells am') z = flat_map (slot_cells am) z).
{ intros z Hz. apply flat_map_ext_In. intros j Hj. destruct (Hz j Hj) as [Hin Hne]. apply In_zseq in Hin.
apply (shape_eq_slot_cells am am' idx j SE); lia. }
rewrite (EZ z1) in Hc by (intros j Hj; split; [rewrite Ez; apply in_app_iff; left; exact Hj | intros ->; apply Hnz; apply in_app_iff; left; exact Hj]).
rewrite (EZ z2) in Hc by (intros j Hj; split; [rewrite Ez; apply in_app_iff; right; right; exact Hj | intros ->; apply Hnz; apply in_app_iff; right; exact Hj]).
apply in_app_iff in Hc as [Hc|Hc]; [left; rewrite !in_app_iff; left; right; right; right; right; left; exact Hc|].
rewrite slot_cells_eq in Hc. rewrite (shape_eq_chk am am' idx SE) in Hc. destruct Hc as [<-|Hc]; [left; rewrite !in_app_iff; left; right; right; right; right; right; left; reflexivity|].
apply in_app_iff in Hc as [Hc|Hc]; [right; right; exact Hc|].
left. rewrite !in_app_iff. right; left; exact Hc.
Qed.
Lemma pairwise_app_mid {A B} (R : B -> B -> Prop) (f : A -> B) l1 m l2 x y :
pairwise R (map f (l1 ++ m ++ l2)) -> In x m -> In y (l1 ++ l2) -> R (f x) (f y) \/ R (f y) (f x).
Proof.
revert m l2 x y. induction l1 as [|a t IH]; intros m l2 x y HP Hx Hy.
- cbn in HP, Hy. revert l2 y HP Hx Hy. induction m as [|b u IHm]; intros l2 y HP Hx Hy; [destruct Hx|].
cbn in HP. destruct HP as [H1 H2]. destruct Hx as [->|Hx].
+ left. apply H1. rewrite map_app. apply in_app_iff. right. apply in_map. exact Hy.
+ apply (IHm l2 y H2 Hx Hy).
- cbn in HP. destruct HP as [H1 H2]. destruct Hy as [->|Hy].
+ right. apply H1. rewrite !map_app. apply in_app_iff. right. apply in_app_iff. left. apply in_map. exact Hx.
+ apply (IH m l2 x y H2 Hx Hy).
Qed.
Lemma padd_padd p a b : padd (padd p a) b = padd p (a + b).
Proof. destruct p; cbn. f_equal. lia. Qed.
Lemma In_group_tail_cells am' c :
In c (group_tail_cells am') ->
(c = MCell (LMem (padd (am_mem am') (group_extent am'))) 1 (VZ 0)) \/
(exists j fr d, 0 <= j <= am_last am' /\ ss_fr (nth_slot am' j) = Some fr /\ fr_kind fr = FUser /\
mc_loc c = LMem (padd (slot_start am' j) d) /\
UNIT * fr_off fr + fr_n fr <= d /\ d + Z.of_nat (mc_w c) <= stride_of am' - IB).
Proof.
intros H. unfold group_tail_cells in H. destruct H as [<-|H]; [left; reflexivity|right].
apply in_flat_map in H as (j & Hj & Hc). apply In_zseq in Hj.
unfold frame_tail_cells in Hc. destruct (ss_fr (nth_slot am' j)) as [fr|] eqn:Efr; [|destruct Hc].
destruct (fr_kind fr) eqn:Ek; [|destruct Hc].
unfold reserved_of, slot_end, frame_ptr in Hc.
assert (GOAL : forall d c', mc_loc c' = LMem (padd (slot_start am' j) d) ->
UNIT * fr_off fr + fr_n fr <= d -> d + Z.of_nat (mc_w c') <= stride_of am' - IB ->
exists j0 fr0 d0, 0 <= j0 <= am_last am' /\ ss_fr (nth_slot am' j0) = Some fr0 /\ fr_kind fr0 = FUser /\
mc_loc c' = LMem (padd (slot_start am' j0) d0) /\ UNIT * fr_off fr0 + fr_n fr0 <= d0 /\ d0 + Z.of_nat (mc_w c') <= stride_of am' - IB).
{ intros d c' E1 E2 E3. exists j, fr, d. split; [lia|]. split; [exact Efr|]. split; [exact Ek|]. split; [exact E1|]. split; [exact E2 | exact E3]. }
apply in_app_iff in Hc as [Hc|Hc].
- destruct (0 <? stride_of am' - IB - UNIT * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.ltb_lt in E.
destruct Hc as [<-|[]]. apply (GOAL (UNIT * fr_off fr + fr_n fr)); cbn [mc_loc mc_w]; [rewrite padd_padd; reflexivity | lia | lia].
- destruct (5 <=? stride_of am' - IB - UNIT * fr_off fr - fr_n fr) eqn:E; [|destruct Hc]. apply Z.leb_le in E.
destruct Hc as [<-|[<-|[]]].
+ apply (GOAL (stride_of am' - IB - 4)); cbn [mc_loc mc_w]; [rewrite padd_padd; f_equal; f_equal; lia | lia | lia].
+ apply (GOAL (stride_of am' - IB - 5)); cbn [mc_loc mc_w]; [rewrite padd_padd; f_equal; f_equal; lia | lia | lia].
Qed.
Section f0.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate).
Hypothesis HI : Inv X R U s.
Lemma tail_cell_span g' am' c :
usedX X s g' am' -> In c (group_tail_cells am') ->
exists d, mc_loc c = LMem (padd (am_mem am') d) /\ UNIT <= d /\ d + Z.of_nat (mc_w c) <= group_extent am' + 1.
Proof.
intros Hu Hc. pose proof (stride_pos _ _ _ _ _ (inv_groups HI g' am' Hu)) as Sp.
pose proof (inv_groups HI g' am' Hu) as ((Glast & _) & _).
destruct (In_group_tail_cells am' c Hc) as [-> | (j & fr & d & Hj & Hfr & Hk & E & Lo & Hi)].
- exists (group_extent am'). cbn [mc_loc mc_w]. split; [reflexivity|]. unfold group_extent, UNIT, IB in *. split; nia.
- exists (UNIT + stride_of am' * j + d). rewrite E. unfold slot_start. rewrite padd_padd. split; [f_equal; f_equal; lia|].
pose proof (inv_groups HI g' am' Hu) as (_ & _ & Gsl & _). pose proof (Gsl j Hj) as (_ & _ & S3). rewrite Hfr in S3.
destruct S3 as (_ & _ & (N0 & O0 & _) & _).
unfold group_extent, UNIT, IB in *. split; [nia|].
assert (stride_of am' * j + stride_of am' <= stride_of am' * (am_last am' + 1)) by nia. lia.
Qed.
Lemma tail_cells_avoid_slot g am idx g' am' c d k :
usedX X s g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = None ->
usedX X s g' am' -> In c (group_tail_cells am') ->
mc_loc c = LMem (padd (am_mem am') d) -> (k < mc_w c)%nat ->
prid (am_mem am') = prid (am_mem am) ->
~ (poff (slot_start am idx) - 3 <= poff (am_mem am') + d + Z.of_nat k < poff (slot_start am idx) + stride_of am - IB).
Proof.
intros Hu Hidx Hnone Hu' Hc Hloc Hk Hpr.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & _) & _ & Gsl & _).
pose proof (inv_groups HI g' am' Hu') as G'. pose proof (stride_pos _ _ _ _ _ G') as Sp'.
pose proof G' as ((Glast' & _) & _ & Gsl' & _).
assert (P1 : 0 <= stride_of am * idx) by nia.
assert (P2 : stride_of am * idx + stride_of am <= stride_of am * (am_last am + 1)) by nia.
assert (P3 : 0 <= stride_of am' * (am_last am' + 1)) by nia.
assert (LOC : (d = group_extent am' /\ mc_w c = 1%nat) \/
(exists j fr, 0 <= j <= am_last am' /\ ss_fr (nth_slot am' j) = Some fr /\ fr_kind fr = FUser /\
poff (slot_start am' j) <= poff (am_mem am') + d /\
poff (am_mem am') + d + Z.of_nat (mc_w c) <= poff (slot_start am' j) + stride_of am' - IB)).
{ destruct (In_group_tail_cells am' c Hc) as [Ec | (j & fr & d' & Hj & Hfr & Hfk & E & Lo & Hi)].
- left. rewrite Ec in Hloc. cbn in Hloc. injection Hloc as Hloc. pose proof (f_equal poff Hloc) as Ho. rewrite !poff_padd in Ho.
split; [lia|]. rewrite Ec. reflexivity.
- right. exists j, fr. rewrite E in Hloc. injection Hloc as Hloc. pose proof (f_equal poff Hloc) as Ho. rewrite !poff_padd in Ho.
pose proof (Gsl' j Hj) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N0 & O0 & _) & _).
repeat split; auto; unfold UNIT in *; lia. }
assert (Hk' : Z.of_nat k < Z.of_nat (mc_w c)) by lia.
destruct (sptr_eq_dec g' g) as [->|Hne].
-
pose proof (usedX_fun _ _ _ _ _ Hu' Hu) as ->.
destruct LOC as [[-> Hw] | (j & fr & Hj & Hfr & Hfk & Lo & Hi)].
+ rewrite Hw in Hk'. rewrite poff_slot_start. unfold group_extent, UNIT, IB in *. cbn in Hk'. lia.
+ assert (Hji : j <> idx) by (intros ->; rewrite Hnone in Hfr; discriminate).
destruct (same_group_starts am j idx Hji Sp); unfold IB in *; lia.
- destruct (inv_laminar HI g' am' g am Hu' Hu Hne Hpr) as [D | [I | I]].
+
pose proof (slot_in_span X R U s HI g am idx Hu Hidx) as [L1 H1].
unfold spans_disjoint in D. destruct LOC as [[-> Hw] | (j & fr & Hj & Hfr & Hfk & Lo & Hi)].
* rewrite Hw in Hk'. cbn in Hk'. unfold group_extent, UNIT, IB in *. lia.
* pose proof (slot_in_span X R U s HI g' am' j Hu' Hj) as [L2 H2]. unfold UNIT, IB in *. lia.
+
destruct I as (j0 & fr0 & cc & ac & Hj0 & Hfr0 & Hk0 & Uc & Mc & Memc & Lo0 & Hi0 & Fit0).
assert (Hj0i : j0 <> idx) by (intros ->; rewrite Hnone in Hfr0; discriminate).
destruct (fgroup_frame X R U s HI g am j0 fr0 Hu Hj0 Hfr0 Hk0) as [Fn _].
pose proof (f_equal poff Memc) as Eoc.
pose proof (stride_pos _ _ _ _ _ (inv_groups HI cc ac Uc)) as Spc.
pose proof (inv_groups HI cc ac Uc) as ((Glc & _) & _).
assert (P4 : 0 <= stride_of ac * (am_last ac + 1)) by nia.
assert (IN : poff (slot_start am j0) <= poff (am_mem am') + d /\
poff (am_mem am') + d + Z.of_nat k < poff (slot_start am j0) + stride_of am - IB + 1).
{ destruct LOC as [[-> Hw] | (j & fr & Hj & Hfr & Hfk & Lo & Hi)].
- rewrite Hw in Hk'. cbn in Hk'. unfold group_extent, UNIT, IB in *. lia.
- pose proof (slot_in_span X R U s HI g' am' j Hu' Hj) as [L2 H2]. unfold group_extent, UNIT, IB in *. lia. }
destruct (same_group_starts am j0 idx Hj0i Sp); unfold UNIT, IB in *; lia.
+
destruct I as (j1 & fr1 & cc & ac & Hj1 & Hfr1 & Hk1 & Uc & Mc & Memc & Lo1 & Hi1 & Fit1).
destruct (fgroup_frame X R U s HI g' am' j1 fr1 Hu' Hj1 Hfr1 Hk1) as [Fn _].
pose proof (f_equal poff Memc) as Eoc.
pose proof (slot_in_span X R U s HI g am idx Hu Hidx) as [L1 H1].
assert (IN : poff (slot_start am' j1) <= poff (slot_start am idx) - 3 - 1 /\
poff (slot_start am idx) + stride_of am - IB <= poff (slot_start am' j1) + stride_of am' - IB).
{ unfold group_extent, UNIT, IB in *. split; lia. }
destruct LOC as [[-> Hw] | (j & fr & Hj & Hfr & Hfk & Lo & Hi)].
* rewrite Hw in Hk'. cbn in Hk'. rewrite poff_slot_start in IN.
assert (P5 : stride_of am' * j1 + stride_of am' <= stride_of am' * (am_last am' + 1)) by nia.
unfold group_extent, UNIT, IB in *. lia.
* destruct (Z.eq_dec j j1) as [->|Hjj]; [rewrite Hfr1 in Hfr; injection Hfr as ->; rewrite Hk1 in Hfk; discriminate|].
destruct (same_group_starts am' j j1 Hjj Sp'); unfold UNIT, IB in *; lia.
Qed.
End f0.
Lemma mupdate_twice l g x y : mupdate (mupdate l g x) g y = mupdate l g y.
Proof.
induction l as [|[q v] t IH]; cbn.
- rewrite sptr_eqb_refl. reflexivity.
- destruct (sptr_eqb g q) eqn:E; cbn; rewrite E; [reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma upd_meta_twice g x y s : upd_meta g y (upd_meta g x s) = upd_meta g y s.
Proof. unfold upd_meta. cbn. rewrite mupdate_twice. reflexivity. Qed.
Lemma A_fast_eq A g idx am : A_fast A g idx am = upd_meta g (MUsed (am_fast idx am)) A.
Proof. unfold A_fast, A_rel. apply upd_meta_twice. Qed.
Lemma shape_eq_rel am idx : 0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) -> shape_eq am (am_rel idx am) idx.
Proof.
intros Hi Hlen. unfold shape_eq, am_rel. repeat split; try reflexivity.
intros j Hj0 Hj. rewrite nth_slot_upd_slot; [|lia|lia|rewrite Hlen; lia].
replace (j =? idx) with false by (symmetry; apply Z.eqb_neq; exact Hj). reflexivity.
Qed.
Lemma shape_eq_fast am idx : 0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) -> shape_eq am (am_fast idx am) idx.
Proof.
intros Hi Hlen. destruct (shape_eq_rel am idx Hi Hlen) as (H1 & H2 & H3 & H4 & H5 & H6).
unfold am_fast, am_set_freed, shape_eq. cbn. repeat split; auto.
Qed.
Lemma nth_slot_rel am idx : 0 <= idx <= am_last am -> length (am_slots am) = Z.to_nat (am_last am + 1) ->
nth_slot (am_rel idx am) idx = released_slot idx am.
Proof.
intros Hi Hlen. unfold am_rel. rewrite nth_slot_upd_slot; [|lia|lia|rewrite Hlen; lia]. rewrite Z.eqb_refl. reflexivity.
Qed.
Lemma nth_slot_fast am idx j : nth_slot (am_fast idx am) j = nth_slot (am_rel idx am) j.
Proof. reflexivity. Qed.
Lemma released_slot_fr idx am : ss_fr (nth_slot am idx) <> None -> ss_fr (released_slot idx am) = None.
Proof. unfold released_slot. destruct (ss_fr (nth_slot am idx)) as [fr|]; [|congruence]. destruct (fr_off fr =? 0); reflexivity. Qed.
Lemma group_tail_cells_shape am am' idx c :
shape_eq am am' idx -> ss_fr (nth_slot am' idx) = None ->
In c (group_tail_cells am') -> In c (group_tail_cells am).
Proof.
intros SE Hnone Hc. pose proof (shape_eq_stride _ _ _ SE) as Hst. destruct SE as (Hm & Hml & Hai & Hl & Hsc & Hs).
unfold group_tail_cells in *. destruct Hc as [<-|Hc].
- left. unfold group_extent. rewrite Hm, Hst, Hl. reflexivity.
- right. apply in_flat_map in Hc as (j & Hj & Hc). rewrite Hl in Hj. apply in_flat_map. exists j. split; [exact Hj|].
apply In_zseq in Hj. destruct (Z.eq_dec j idx) as [->|Hne].
+ unfold frame_tail_cells in Hc. rewrite Hnone in Hc. destruct Hc.
+ unfold frame_tail_cells, reserved_of, slot_end, frame_ptr, slot_start in *. rewrite (Hs j ltac:(lia) Hne), Hst, Hm in Hc. exact Hc.
Qed.
Lemma tail_cells_upd s g am am' idx c :
MT s g = Some (MUsed am) -> shape_eq am am' idx -> ss_fr (nth_slot am' idx) = None ->
In c (tail_cells (upd_meta g (MUsed am') s)) -> In c (tail_cells s).
Proof.
intros Hg SE Hnone Hc. destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
unfold tail_cells in *. rewrite Eu' in Hc. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
apply in_app_iff in Hc as [Hc|Hc]; [apply in_app_iff; left; exact Hc|].
apply in_app_iff. right. apply in_app_iff in Hc as [Hc|Hc]; apply in_app_iff; [left|right; exact Hc].
cbn [snd] in *. eapply group_tail_cells_shape; eauto.
Qed.
Lemma frames_upd s g am am' idx g0 am0 i fr :
MT s g = Some (MUsed am) -> shape_eq am am' idx -> ss_fr (nth_slot am' idx) = None ->
In (g0, am0, i, fr) (frames (upd_meta g (MUsed am') s)) ->
exists am1, In (g0, am1, i, fr) (frames s) /\ stride_of am1 = stride_of am0.
Proof.
intros Hg SE Hnone Hf. destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
unfold frames in *. rewrite Eu' in Hf. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
assert (KEEP : forall l, In (g0, am0, i, fr) (flat_map (fun gm : sptr * ameta => let '(g1, am1) := gm in
flat_map (fun i0 : Z => match ss_fr (nth_slot am1 i0) with Some fr0 => [(g1, am1, i0, fr0)] | None => [] end) (zseq 0 (am_last am1 + 1))) l) ->
exists am1, In (g0, am1, i, fr) (flat_map (fun gm : sptr * ameta => let '(g1, am2) := gm in
flat_map (fun i0 : Z => match ss_fr (nth_slot am2 i0) with Some fr0 => [(g1, am2, i0, fr0)] | None => [] end) (zseq 0 (am_last am2 + 1))) l) /\ stride_of am1 = stride_of am0).
{ intros l H. exists am0. split; [exact H | reflexivity]. }
apply in_app_iff in Hf as [Hf|Hf].
{ destruct (KEEP u1 Hf) as (am1 & H1 & H2). exists am1. split; [apply in_app_iff; left; exact H1 | exact H2]. }
apply in_app_iff in Hf as [Hf|Hf].
2:{ destruct (KEEP u2 Hf) as (am1 & H1 & H2). exists am1. split; [apply in_app_iff; right; apply in_app_iff; right; exact H1 | exact H2]. }
pose proof (shape_eq_stride _ _ _ SE) as Hst. destruct SE as (Hm & Hml & Hai & Hl & Hsc & Hs).
apply in_flat_map in Hf as (j & Hj & Hf). rewrite Hl in Hj. pose proof Hj as Hj'. apply In_zseq in Hj'.
destruct (Z.eq_dec j idx) as [->|Hne]; [rewrite Hnone in Hf; destruct Hf|].
rewrite (Hs j ltac:(lia) Hne) in Hf. destruct (ss_fr (nth_slot am j)) as [fr0|] eqn:Efr; [|destruct Hf]. destruct Hf as [E|[]].
injection E as <- <- <- <-. exists am. split; [|symmetry; exact Hst].
apply in_app_iff. right. apply in_app_iff. left. apply in_flat_map. exists j. split; [exact Hj|]. rewrite Efr. left. reflexivity.
Qed.
Lemma user_blocks_upd s g am am' idx b :
MT s g = Some (MUsed am) -> shape_eq am am' idx -> ss_fr (nth_slot am' idx) = None ->
In b (user_blocks (upd_meta g (MUsed am') s)) -> In b (user_blocks s).
Proof.
intros Hg SE Hnone Hb. destruct (used_metas_upd s g am Hg) as (u1 & u2 & Eu & Eu').
unfold user_blocks in *. rewrite Eu' in Hb. rewrite Eu. rewrite !flat_map_app in *. cbn [flat_map] in *.
apply in_app_iff in Hb as [Hb|Hb]; [apply in_app_iff; left; exact Hb|].
apply in_app_iff. right. apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left|right; exact Hb].
cbn [snd] in *. pose proof (fun j => shape_eq_slot_start am am' idx j SE) as SS. destruct SE as (Hm & Hml & Hai & Hl & Hsc & Hs).
apply in_flat_map in Hb as (j & Hj & Hb). rewrite Hl in Hj. apply in_flat_map. exists j. split; [exact Hj|]. apply In_zseq in Hj.
destruct (Z.eq_dec j idx) as [->|Hne]; [rewrite Hnone in Hb; destruct Hb|].
rewrite (Hs j ltac:(lia) Hne), (SS j) in Hb. exact Hb.
Qed.
Section h0.
Variable B : malloc_syms.
Lemma cell_keep L mem mem1 c :
cell_mem B L mem c ->
(forall k, (k < mc_w c)%nat -> mem1 (Z_to_bv 64 (loc_addr L (mc_loc c) + Z.of_nat k)) = mem (Z_to_bv 64 (loc_addr L (mc_loc c) + Z.of_nat k))) ->
cell_mem B L mem1 c.
Proof.
intros Hc Heq. unfold cell_mem in *. destruct c as [loc w v]; cbn [mc_loc mc_w mc_val] in *.
destruct v.
- intros k Hk. unfold mbyte. rewrite (Heq k Hk). exact (Hc k Hk).
- intros k Hk. unfold mbyte. rewrite (Heq k Hk). exact (Hc k Hk).
- intros Hw. destruct (Hc Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
unfold mbyte in *. specialize (Heq 0%nat Hw). rewrite Z.add_0_r in Heq. rewrite Heq. exact Hb.
- intros k Hk. unfold mbyte. rewrite (Heq k Hk). exact (Hc k Hk).
Qed.
End h0.
Lemma sptr_eq_dec' (p q : sptr) : {p = q} + {p <> q}.
Proof. decide equality; [apply Z.eq_dec | apply Nat.eq_dec]. Defined.
Lemma mcell_eq_dec (c d : mcell) : {c = d} + {c <> d}.
Proof.
destruct c as [l w v], d as [l' w' v'].
destruct (Nat.eq_dec w w') as [<-|]; [|right; congruence].
assert (LD : {l = l'} + {l <> l'}).
{ destruct l as [o|p], l' as [o'|p']; try (right; discriminate).
- destruct (Z.eq_dec o o') as [<-|]; [left; reflexivity | right; congruence].
- destruct (sptr_eq_dec' p p') as [<-|]; [left; reflexivity | right; congruence]. }
assert (VD : {v = v'} + {v <> v'}).
{ destruct v as [z|p|z|], v' as [z'|p'|z'|]; try (right; discriminate); try (left; reflexivity).
- destruct (Z.eq_dec z z') as [<-|]; [left; reflexivity | right; congruence].
- destruct (sptr_eq_dec' p p') as [<-|]; [left; reflexivity | right; congruence].
- destruct (Z.eq_dec z z') as [<-|]; [left; reflexivity | right; congruence]. }
destruct LD as [<-|]; [|right; congruence]. destruct VD as [<-|]; [left; reflexivity | right; congruence].
Defined.
Section k0.
Variable B : malloc_syms.
Variables (L : layout) (A : astate) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (idx : Z) (fr : frame) (mem1 : word -> option byte) (sp : Z).
Hypothesis MR : MRc B L A mem md.
Hypothesis Hu : usedX [] A g am.
Hypothesis Hidx : 0 <= idx <= am_last am.
Hypothesis Hfr : ss_fr (nth_slot am idx) = Some fr.
Hypothesis Hk : fr_kind fr = FUser.
Hypothesis HW2 : WF (upd_meta g (MUsed (am_fast idx am)) A).
Hypothesis Hsp : alloc_ceiling + 8192 <= sp.
Hypothesis F1 : forall a, 0 <= a < 2 ^ 64 ->
~ (ptr_addr L (frame_ptr am idx fr) - 3 <= a < ptr_addr L (frame_ptr am idx fr)) ->
~ (ptr_addr L g + 28 <= a < ptr_addr L g + 32) -> ~ (sp - 8192 <= a < sp) ->
mem1 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Hypothesis F2 : mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 3) = Some (Z_to_bv 8 255) /\
mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 2) = Some (Z_to_bv 8 0) /\
mbyte (ms_segs B) mem1 (ptr_addr L (frame_ptr am idx fr) - 1) = Some (Z_to_bv 8 0).
Hypothesis F3 : forall k, (k < 4)%nat ->
mbyte (ms_segs B) mem1 (ptr_addr L g + 28 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte (am_freed am + bit idx) 4 k)).
Hypothesis F4 : forall a, (ptr_addr L (frame_ptr am idx fr) - 3 <= a < ptr_addr L (frame_ptr am idx fr)) \/
(ptr_addr L g + 28 <= a < ptr_addr L g + 32) -> present mem1 a.
Theorem memrep_fast :
memrep B L (upd_meta g (MUsed (am_fast idx am)) A) mem1 /\ tail_geom L (upd_meta g (MUsed (am_fast idx am)) A).
Proof.
set (am2 := am_fast idx am) in *. set (A2 := upd_meta g (MUsed am2) A) in *.
pose proof (mc_wf _ _ _ _ _ MR) as HW. pose proof (mc_layout _ _ _ _ _ MR) as HL.
pose proof (usedX_MT _ _ _ _ Hu) as [Mg _].
pose proof (inv_groups HW g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp.
pose proof G as ((Glast & Gaidx & Glen & Gav & Gfrn & Gdisj & Gabove & Gavp & Gfra) & Gml & Gsl & Gcl & Gmp & Gns).
pose proof (Gsl idx Hidx) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (Hal & _ & (Nf & Of & Bf & H16 & _) & Hhdr0).
assert (SE : shape_eq am am2 idx) by (apply shape_eq_fast; [exact Hidx | exact Glen]).
assert (Hnone : ss_fr (nth_slot am2 idx) = None).
{ subst am2. rewrite nth_slot_fast, nth_slot_rel by (exact Hidx || exact Glen). apply released_slot_fr. rewrite Hfr. discriminate. }
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
pose proof (image_cells_disjoint A2 L HW2 HL2) as DISJ2.
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
set (cF := MCell (LMem (padd g META_freed)) 4 (VZ (am_freed am2))).
assert (HcF : In cF (image A2)) by (apply (meta_cells_in_image A2 g am2 _ HW2 Hu2); cbn; auto 10).
assert (RcF : cell_range L cF = (ptr_addr L g + 28, 4)).
{ unfold cell_range, cF. cbn [mc_loc mc_w]. unfold ptr_addr, loc_addr, META_freed. rewrite Eg, Ea. cbn [padd]. f_equal. lia. }
assert (AVOIDF : forall c k, In c (image A2) -> c <> cF -> (k < mc_w c)%nat ->
~ (ptr_addr L g + 28 <= loc_addr L (mc_loc c) + Z.of_nat k < ptr_addr L g + 32)).
{ intros c k Hc Hne Hkw Hin.
destruct (pairwise_map_In ranges_disjoint (cell_range L) (image A2) c cF DISJ2 Hc HcF Hne) as [D|D];
rewrite RcF in D; unfold ranges_disjoint, cell_range in D; cbn [fst snd] in D; lia. }
assert (LOWA : forall c k, In c (image A) -> (k < mc_w c)%nat -> 4096 <= loc_addr L (mc_loc c) + Z.of_nat k < alloc_ceiling).
{ intros c k Hc Hkw. destruct (image_in_footprint A L c HW HL Hc) as (e & He & Hincl).
unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. apply (FLOW e _ He). lia. }
assert (LOWA2 : forall c k, In c (image A2) -> (k < mc_w c)%nat -> 4096 <= loc_addr L (mc_loc c) + Z.of_nat k < alloc_ceiling).
{ intros c k Hc Hkw. destruct (image_in_footprint A2 L c HW2 HL2 Hc) as (e & He & Hincl).
unfold range_incl, cell_range, crange in Hincl. cbn [fst snd] in Hincl. subst A2. rewrite footprint_upd_meta in He. apply (FLOW e _ He). lia. }
pose proof (fun c (H : In c (image A)) => memrep_cell B L A mem c (MRc_memrep B L A mem md MR) H) as CELL.
assert (KEEP : forall c, In c (image A) -> In c (image A2) -> c <> cF ->
(forall k, (k < mc_w c)%nat -> ~ (P - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < P)) ->
cell_mem B L mem1 c).
{ intros c HcA HcA2 Hne Hav. apply (cell_keep B L mem mem1 c (CELL c HcA)). intros k Hkw.
pose proof (LOWA c k HcA Hkw). apply F1; [lia | apply Hav; exact Hkw | apply (AVOIDF c k HcA2 Hne Hkw) | lia]. }
assert (Vfr : am_freed am2 = am_freed am + bit idx) by reflexivity.
assert (Vmeta : am_prev am2 = am_prev am /\ am_next am2 = am_next am /\ am_mem am2 = am_mem am /\ am_avail am2 = am_avail am /\ meta_bits am2 = meta_bits am).
{ subst am2. unfold am_fast, am_rel, am_set_freed, upd_slot, meta_bits. cbn. repeat split; reflexivity. }
assert (IMG : Forall (cell_mem B L mem1) (image A2)).
{ apply Forall_forall. intros c Hc2.
destruct (mcell_eq_dec c cF) as [->|Hne].
{   unfold cF, cell_mem. cbn [mc_loc mc_w mc_val sval_num]. intros k Hkw. rewrite Vfr.
rewrite <- (F3 k Hkw). f_equal. unfold ptr_addr, loc_addr, META_freed. rewrite Eg, Ea. cbn [padd]. lia. }
destruct (Hnew am2 c SE Hc2) as [Hl12 | [Hmeta | Hslot]].
-
assert (HcA : In c (image A)) by (rewrite Eim; apply in_app_iff in Hl12 as [H|H]; apply in_app_iff; [left; exact H | right; apply in_app_iff; right; exact H]).
apply KEEP; [exact HcA | exact Hc2 | exact Hne | intros k Hkw; apply (AVOIDP c k Hl12 Hkw)].
-
destruct Vmeta as (V1 & V2 & V3 & V4 & V5).
assert (HcA : In c (areas_cells A (st_areas A))).
{ assert (Hm : In c (meta_slot_cells g (Some (MUsed am)))).
{ cbn [meta_slot_cells] in Hmeta |- *. rewrite V1, V2, V3, V4, V5 in Hmeta.
destruct Hmeta as [H|[H|[H|[H|[H|[H|[]]]]]]]; try (rewrite <- H; cbn; tauto).
exfalso. apply Hne. rewrite <- H. reflexivity. }
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
apply KEEP; [| exact Hc2 | exact Hne | intros k Hkw; apply (AVOIDP c k); [apply in_app_iff; left; exact Hl1 | exact Hkw]].
unfold image. apply in_app_iff. right. apply in_app_iff. left. exact HcA.
-
unfold slot_rest in Hslot. rewrite Hnone in Hslot. rewrite app_nil_r in Hslot.
subst am2. rewrite nth_slot_fast, nth_slot_rel in Hslot by (exact Hidx || exact Glen).
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
apply KEEP; [exact HcA | exact Hc2 | exact Hne |].
intros k Hkw. destruct Hslot as [<-|[<-|[]]]; cbn [mc_loc mc_w] in Hkw |- *; unfold loc_addr, slot_start; rewrite Emem; cbn [padd]; unfold UNIT; lia. }
assert (TL : forall c, In c (tail_cells A2) -> In c (tail_cells A) /\ forall k, (k < mc_w c)%nat ->
4096 <= loc_addr L (mc_loc c) + Z.of_nat k < alloc_ceiling /\
~ (P - 3 <= loc_addr L (mc_loc c) + Z.of_nat k < P) /\
~ (ptr_addr L g + 28 <= loc_addr L (mc_loc c) + Z.of_nat k < ptr_addr L g + 32)).
{ intros c Hc2. assert (HcA : In c (tail_cells A)) by (subst A2; eapply tail_cells_upd; eauto). split; [exact HcA|].
intros k Hkw.
unfold tail_cells in Hc2. apply in_flat_map in Hc2 as ([g'' am''] & Hg'' & Hc''). cbn [snd] in Hc''.
assert (Hu'' : usedX [] A2 g'' am'') by (apply (used_metas_usedX A2 g'' am'' HW2); exact Hg'').
destruct (tail_cell_span [] None U0 A2 HW2 g'' am'' c Hu'' Hc'') as (d & Hloc & Hd16 & Hdw).
destruct (used_group_region [] None U0 A2 g'' am'' HW2 Hu'') as (rg'' & Hrg'' & Hk'' & Hl'' & Ho'' & Hext'' & _).
assert (Hrg''A : region_of A (prid (am_mem am'')) = Some rg'') by (subst A2; exact Hrg'').
destruct (lg_placed _ _ _ _ (mc_ledger _ _ _ _ _ MR) _ _ Hrg''A Hl'') as (Ral'' & R4096'' & Rceil'' & _).
pose proof (footprint_region_In A _ _ Hrg''A Hk'' Hl'') as In''.
rewrite Hloc. destruct (am_mem am'') as [kr'' ko''] eqn:Emem''. cbn [prid poff loc_addr padd] in *.
unfold IB in Hext''. unfold UNIT in Hd16.
split; [clear - R4096'' Rceil'' Ho'' Hd16 Hdw Hext'' Hkw; lia|]. split.
-
destruct (Nat.eq_dec kr'' kr) as [->|Hkr].
+ pose proof (tail_cells_avoid_slot [] None U0 A2 HW2 g am2 idx g'' am'' c d k Hu2 ltac:(destruct SE as (_&_&_&Hl&_); rewrite Hl; exact Hidx) Hnone Hu'' Hc'') as AV.
rewrite Emem'' in AV. cbn [prid poff] in AV. destruct SE as (SEm & _).
specialize (AV Hloc Hkw ltac:(rewrite SEm, Emem; reflexivity)).
rewrite (shape_eq_slot_start am am2 idx idx) in AV by (apply shape_eq_fast; [exact Hidx | exact Glen]).
rewrite (shape_eq_stride am am2 idx) in AV by (apply shape_eq_fast; [exact Hidx | exact Glen]).
rewrite poff_slot_start, Emem in AV. cbn [poff] in AV. rewrite <- EST in AV. unfold UNIT, IB in AV. lia.
+ assert (Hne' : (LMem (SP kr'' 0), rg_len rg'') <> (LMem (SP kr 0), rg_len rg)) by (intros E; injection E; intros; exact (Hkr ltac:(assumption))).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In'' InG Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; rewrite <- ?EGLO in D; lia.
-
assert (Hne' : (LMem (SP kr'' 0), rg_len rg'') <> (LMem a, 4096)).
{ intros E. injection E as E1 E2. rewrite Ea in E1. injection E1 as E3 E4. rewrite <- E3, Hrg''A in Hra. injection Hra as <-. rewrite Hk'' in Hrak. exact Hrak. }
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint A) _ _ PW In'' InA Hne') as [D|D];
unfold ranges_disjoint, crange in D; cbn [fst snd loc_addr] in D; rewrite Ea in D; cbn [loc_addr] in D; rewrite <- ?EALO in D; lia. }
split; [split; [exact IMG | split]|].
-   apply Forall_forall. intros c Hc2. destruct (TL c Hc2) as [HcA Hbytes].
apply (cell_keep B L mem mem1 c (memrep_tail B L A mem c (MRc_memrep B L A mem md MR) HcA)).
intros k Hkw. destruct (Hbytes k Hkw) as (B1 & B2 & B3). apply F1; lia.
-   subst A2. rewrite footprint_upd_meta. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) (mc_foot _ _ _ _ _ MR) e He) as Fe.
unfold foot_ok in *. destruct e as [[o|q] len]; cbn [fst snd] in *; [exact I|]. intros x Hx.
pose proof (FLOW _ x He Hx) as Lx. cbn [fst snd] in Lx.
destruct (Z_lt_dec x (P - 3)) as [L1|L1]; [| destruct (Z_lt_dec x P) as [L2|L2]; [apply F4; left; lia|]];
(destruct (Z_lt_dec x (ptr_addr L g + 28)) as [L3|L3]; [| destruct (Z_lt_dec x (ptr_addr L g + 32)) as [L4|L4]; [apply F4; right; lia|]]);
(destruct (Fe x Hx) as [b Hb]; exists b; rewrite <- Hb; apply F1; lia).
-   unfold tail_geom. apply Forall_forall. intros c Hc2 k Hkw. destruct (TL c Hc2) as [HcA _].
pose proof (proj1 (Forall_forall _ _) (mc_tail_geom _ _ _ _ _ MR) c HcA k Hkw) as [Hin Hnb].
split; [exact Hin|].
intros (b & Hb & Hx). apply Hnb. exists b. split; [| exact Hx]. subst A2. eapply user_blocks_upd; eauto.
Qed.
End k0.
End h.
