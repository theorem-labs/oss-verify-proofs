(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2u.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition in_range (a : Z) (r : Z * Z) : Prop := fst r <= a < fst r + snd r.
Lemma loc_addr_padd' L p d : loc_addr L (LMem (padd p d)) = ptr_addr L p + d.
Proof. destruct p; cbn. unfold ptr_addr. cbn. lia. Qed.
Lemma in_range_dec a r : {in_range a r} + {~ in_range a r}.
Proof. unfold in_range. destruct (Z_le_dec (fst r) a); [destruct (Z_lt_dec a (fst r + snd r)); [left; lia|] |]; right; lia. Qed.
Lemma in_ranges_dec {T} (f : T -> Z * Z) a (l : list T) :
{exists x, In x l /\ in_range a (f x)} + {forall x, In x l -> ~ in_range a (f x)}.
Proof.
induction l as [|y l IH].
- right. intros x [].
- destruct (in_range_dec a (f y)) as [Hy|Hy].
+ left. exists y. split; [left; reflexivity | exact Hy].
+ destruct IH as [IH|IH].
* left. destruct IH as (x & Hx & Hr). exists x. split; [right; exact Hx | exact Hr].
* right. intros x [<-|Hx]; [exact Hy | apply IH; exact Hx].
Qed.
Lemma ranges_disjoint_not_both a r1 r2 : ranges_disjoint r1 r2 -> in_range a r1 -> in_range a r2 -> False.
Proof. unfold ranges_disjoint, in_range. lia. Qed.
Lemma cell_range_in L c k : (k < mc_w c)%nat -> in_range (loc_addr L (mc_loc c) + Z.of_nat k) (cell_range L c).
Proof. intros Hk. unfold in_range, cell_range. cbn [fst snd]. lia. Qed.
Section j.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Lemma cellX_in_footprint c :
In c (imageX X s ++ tail_cellsX X s) ->
exists e, In e (footprint s) /\ range_incl (cell_range L c) (crange L e).
Proof.
intros Hc. destruct (cellX_home X R U s L HI c Hc) as [[Hcc Ic] | [[Hca (a & next & Ha & Hc' & Ic)] | (k & rg & Hk & Hkd & Hl & Ic)]].
- exists (LCtx 0, CTX_SIZE). split; [left; reflexivity | exact Ic].
- exists (LMem a, PGSZ). split; [exact (proj1 (area_cell_home L s a next c Ha Hc')) | exact Ic].
- exists (LMem (SP k 0), rg_len rg). split; [apply footprint_region_In; assumption | exact Ic].
Qed.
Lemma slot_cells_in_areas g x c :
MT s g = Some x -> In c (meta_slot_cells g (Some x)) -> In c (areas_cells s (st_areas s)).
Proof.
intros Mg Hc. pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk & E).
apply (In_areas_cells_intro s (st_areas s) a c Ha). intros next.
unfold area_cells. apply in_app_iff. right. apply in_flat_map. exists (Z.to_nat k).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. rewrite <- E. unfold MT in Mg. rewrite Mg. exact Hc.
Qed.
Lemma new_cell_exclusive n c :
In n (areas_cells s (st_areas s)) \/ In n (ctx_cells s) ->
In c (imageX X s ++ tail_cellsX X s) ->
c = n \/ ranges_disjoint (cell_range L c) (cell_range L n).
Proof.
intros [Hn|Hn] Hc; [eapply (meta_cell_exclusive X R U s L HI HL); eauto | eapply (ctx_cell_exclusive X R U s L HI HL); eauto].
Qed.
End j.
Section m.
Variable B : malloc_syms.
Variables (X X' : list sptr) (R R' : option (sptr * Z)) (U U' : Z -> Z) (s s' : astate) (L : layout).
Variables (mem mem' : word -> option byte).
Variables (NEW : list mcell) (D : list (Z * Z)) (stk : Z * Z).
Hypothesis HI : Inv X R U s.
Hypothesis HI' : Inv X' R' U' s'.
Hypothesis HL : layout_ok L s.
Hypothesis Efp : footprint s' = footprint s.
Hypothesis Erg : st_regions s' = st_regions s.
Hypothesis MR : memrepX B X L s mem.
Hypothesis Hcells : forall c, In c (imageX X' s' ++ tail_cellsX X' s') -> In c NEW \/ In c (imageX X s ++ tail_cellsX X s).
Hypothesis Hnew_home : forall n, In n NEW -> In n (areas_cells s' (st_areas s')) \/ In n (ctx_cells s').
Hypothesis Hnew_mem : forall n, In n NEW -> cell_mem B L mem' n.
Hypothesis Hnew_present : forall n k, In n NEW -> (k < mc_w n)%nat ->
(exists p, mc_loc n = LMem p) -> present mem' (loc_addr L (mc_loc n) + Z.of_nat k).
Hypothesis HD : forall d c, In d D -> In c (imageX X' s' ++ tail_cellsX X' s') -> ranges_disjoint (cell_range L c) d.
Hypothesis HDp : forall d a, In d D -> in_range a d -> present mem a -> present mem' a.
Hypothesis Hstk : forall e, In e (footprint s) -> loc_addr L (fst e) + snd e <= fst stk.
Hypothesis Hframe : forall a, 0 <= a < 2 ^ 64 ->
(forall n, In n NEW -> ~ in_range a (cell_range L n)) ->
(forall d, In d D -> ~ in_range a d) -> ~ in_range a stk ->
mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (present mem a -> present mem' a).
Lemma layout_ok_s' : layout_ok L s'.
Proof.
pose proof HL as (A1 & A2 & A3 & A4). unfold layout_ok. rewrite Efp. unfold region_of. rewrite Erg.
split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.
Lemma old_byte_frame c k :
In c (imageX X' s' ++ tail_cellsX X' s') -> ~ In c NEW -> In c (imageX X s ++ tail_cellsX X s) -> (k < mc_w c)%nat ->
let a := loc_addr L (mc_loc c) + Z.of_nat k in
mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\ (present mem a -> present mem' a).
Proof.
intros Hc' Hnot Hc Hk.
destruct (cellX_in_footprint X R U s L HI c Hc) as (e & He & Ie). pose proof (proj2 (proj2 (proj2 HL)) e He) as Re.
apply Hframe.
- unfold range_incl, cell_range, crange in Ie, Re. cbn [fst snd] in Ie, Re. lia.
- intros n Hn Hin. destruct (new_cell_exclusive X' R' U' s' L HI' layout_ok_s' n c (Hnew_home n Hn) Hc') as [->|Dj]; [exact (Hnot Hn)|].
exact (ranges_disjoint_not_both _ _ _ Dj (cell_range_in L c k Hk) Hin).
- intros d Hd Hin. exact (ranges_disjoint_not_both _ _ _ (HD d c Hd Hc') (cell_range_in L c k Hk) Hin).
- intros Hin. pose proof (Hstk e He). unfold range_incl, cell_range, crange, in_range in *. cbn [fst snd] in *. lia.
Qed.
Lemma In_dec_cell (c : mcell) (l : list mcell) : {In c l} + {~ In c l}.
Proof. apply In_dec. apply mcell_eq_dec. Qed.
Lemma cells_hold c : In c (imageX X' s' ++ tail_cellsX X' s') -> cell_mem B L mem' c.
Proof.
intros Hc'. destruct (In_dec_cell c NEW) as [Hn|Hn]; [apply Hnew_mem; exact Hn|].
destruct (Hcells c Hc') as [Hn'|Hc]; [exfalso; exact (Hn Hn')|].
assert (OLD : cell_mem B L mem c).
{ pose proof MR as (MI & MT' & _). apply in_app_iff in Hc as [H|H];
[exact (proj1 (Forall_forall _ _) MI _ H) | exact (proj1 (Forall_forall _ _) MT' _ H)]. }
unfold cell_mem in *. destruct (mc_val c) eqn:Ev;
try (intros k Hk; rewrite <- (OLD k Hk); apply (old_byte_frame c k Hc' Hn Hc Hk)).
intros Hw. destruct (OLD Hw) as (b & Hb & Hz). exists b. split; [|exact Hz].
pose proof (old_byte_frame c 0 Hc' Hn Hc Hw) as [E _]. rewrite Z.add_0_r in E. rewrite E. exact Hb.
Qed.
Theorem memrepX_after : memrepX B X' L s' mem'.
Proof.
split; [|split].
- apply Forall_forall. intros c Hc. apply cells_hold. apply in_app_iff. left. exact Hc.
- apply Forall_forall. intros c Hc. apply cells_hold. apply in_app_iff. right. exact Hc.
- rewrite Efp. apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) (proj2 (proj2 MR)) e He) as Fe.
unfold foot_ok in *. destruct e as [[o|q] len]; [exact I|]. cbn [fst snd] in *. intros x Hx.
destruct (in_ranges_dec (cell_range L) x NEW) as [(n & Hn & Hin)|Hno].
+ unfold in_range, cell_range in Hin. cbn [fst snd] in Hin.
replace x with (loc_addr L (mc_loc n) + Z.of_nat (Z.to_nat (x - loc_addr L (mc_loc n)))) by lia.
apply (Hnew_present n _ Hn); [lia|].
destruct (Hnew_home n Hn) as [Ha|Hc].
* destruct (In_areas_cells s' _ n Ha) as (a & next & _ & Hn'). destruct (In_area_cells s' a next n Hn') as (d & E & _). rewrite E. eexists; reflexivity.
* exfalso. destruct (In_ctx_cells s' n Hc) as (off & E & Ho & Hw).
pose proof HL as (_ & _ & PW & _).
assert (Hne : (LCtx 0, CTX_SIZE) <> (LMem q, len)) by discriminate.
assert (R1 : ly_ctx L + off <= x < ly_ctx L + off + Z.of_nat (mc_w n)).
{ unfold in_range, cell_range in Hin. rewrite E in Hin. cbn [fst snd loc_addr] in Hin. exact Hin. }
cbn [loc_addr] in Hx.
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW (or_introl eq_refl) He Hne) as [Dj|Dj];
unfold ranges_disjoint, crange in Dj; cbn [fst snd loc_addr] in Dj; lia.
+ destruct (in_ranges_dec (fun d => d) x D) as [(d & Hd & Hin)|HnoD]; [exact (HDp d x Hd Hin (Fe x Hx))|].
pose proof (proj2 (proj2 (proj2 HL)) _ He) as Re. cbn [fst snd crange] in Re.
apply (proj2 (Hframe x ltac:(lia) Hno HnoD ltac:(pose proof (Hstk _ He) as S; cbn [fst snd] in S; unfold in_range; lia))). exact (Fe x Hx).
Qed.
End m.
Section t.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Lemma block_homeX b :
In b (user_blocks s) ->
exists k rg, region_of s k = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP k 0), rg_len rg) (footprint s) /\ range_incl (block_range L b) (crange L (LMem (SP k 0), rg_len rg)).
Proof.
intros Hin. destruct (in_user_blocks_inv s b Hin) as (g & am & i & fr & Hg & Hi & Hfr & Hk & ->).
assert (Hu : usedX X s g am).
{ apply (used_metas_iff s g am (proj1 (inv_keys HI))) in Hg. apply usedX_intro; [|exact Hg].
destruct (memb g X) eqn:M; [|reflexivity]. exfalso.
destruct (inv_X HI g (proj1 (memb_In g X) M)) as [_ Hx]. rewrite Hg in Hx.
destruct Hx as (_ & _ & Hnofr). rewrite (Hnofr i) in Hfr. discriminate. }
destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hkd & Hl & Ho & Hext & _).
exists (prid (am_mem am)), rg. split; [exact Hr|]. split; [exact Hkd|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
pose proof (inv_groups HI g am Hu) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3. destruct S3 as (_ & _ & (N & O & Bf & _) & _).
pose proof (slot_in_span X R U s HI g am i Hu Hi) as [S1 S2].
unfold block_range, crange, range_incl, loc_addr. cbn [fst snd].
unfold frame_ptr, slot_start in *. destruct (am_mem am) as [k o]. cbn [padd prid poff] in *. unfold IB, UNIT in *. lia.
Qed.
Lemma owned_of_entry e x :
In e (footprint s) -> (forall k rg, region_of s k = Some rg -> rg_kind rg = RkMap -> e <> (LMem (SP k 0), rg_len rg)) ->
loc_addr L (fst e) <= x < loc_addr L (fst e) + snd e -> alloc_owned L s x.
Proof.
intros He Hnot Hx. split; [exists e; auto|].
intros (b & Hb & Hbx). destruct (block_homeX b Hb) as (k & rg & Hk & Hkd & Hl & Hin & Incl).
pose proof HL as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He Hin (Hnot k rg Hk Hkd)) as [Dj|Dj];
unfold ranges_disjoint, crange, range_incl, block_range in *; cbn [fst snd] in *; lia.
Qed.
Theorem ctx_bytes_owned x : ly_ctx L <= x < ly_ctx L + CTX_SIZE -> alloc_owned L s x.
Proof.
intros Hx. apply (owned_of_entry (LCtx 0, CTX_SIZE)); [left; reflexivity | intros; discriminate | cbn; lia].
Qed.
Theorem area_bytes_owned a x : In a (st_areas s) -> ptr_addr L a <= x < ptr_addr L a + PGSZ -> alloc_owned L s x.
Proof.
intros Ha Hx. apply (owned_of_entry (LMem a, PGSZ)).
- right. apply in_app_iff. left. apply in_map_iff. exists a. auto.
- intros k rg Hk Hkd. apply (area_entry_not_region X R U s HI a k rg Ha Hk Hkd).
- cbn [fst snd]. unfold ptr_addr in Hx. exact Hx.
Qed.
Theorem meta_bytes_owned g x (mx : mslot) :
MT s g = Some mx -> ptr_addr L g <= x < ptr_addr L g + META_SIZE -> alloc_owned L s x.
Proof.
intros Mg Hx. pose proof (inv_keys HI) as (NDk & KP & _ & _ & Hcnt).
destruct (KP g (MT_Some_In_keys _ _ _ Mg)) as (a & k & Ha & Hk & E).
assert (Hk' : 0 <= k < METAS_PER_AREA) by (unfold handed in Hk; destruct (sptr_eqb a _); lia).
apply (area_bytes_owned a x Ha). rewrite E in Hx. unfold ptr_addr in Hx. rewrite loc_addr_padd' in Hx.
unfold AREA_HDR, META_SIZE, METAS_PER_AREA, PGSZ in *. lia.
Qed.
End t.
End h.
