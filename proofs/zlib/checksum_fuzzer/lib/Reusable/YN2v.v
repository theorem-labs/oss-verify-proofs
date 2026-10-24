(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YN2h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis XC : Xclean X s.
Hypothesis HL : layout_ok L s.
Variables (k : nat) (rg : YO0i.region) (x : Z).
Hypothesis Hk : region_of s k = Some rg.
Hypothesis Hlive : rg_live rg = true.
Hypothesis Hkind : rg_kind rg = RkMap.
Hypothesis Hx : ly_reg L k <= x < ly_reg L k + rg_len rg.
Hypothesis H12 : (x - ly_reg L k) mod 16 = 12.
Let eK : loc * Z := (LMem (SP k 0), rg_len rg).
Let eK_in : In eK (footprint s) := footprint_region_In s k rg Hk Hkind Hlive.
Lemma other_home : forall c e, In e (footprint s) -> e <> eK -> range_incl (cell_range L c) (crange L e) ->
~ (loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c)).
Proof.
intros c e He Hne HIc Hcov. pose proof HL as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He eK_in Hne) as [D|D];
unfold ranges_disjoint, range_incl, crange, cell_range in *; subst eK; cbn [fst snd loc_addr] in *; lia.
Qed.
Lemma mod16_of : forall a b, a mod 16 = 0 -> (a + b) mod 16 = b mod 16.
Proof. intros a b Ha. rewrite Z.add_mod, Ha, Z.add_0_l, Z.mod_mod by lia. reflexivity. Qed.
Lemma group_cell_12 : forall g am c, usedX X s g am -> In c (group_cells g am) ->
loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) -> mc_w c = 1%nat /\ mc_val c = VZ 0.
Proof.
intros g am c Hu Hc Hcov.
destruct (used_group_region X R U s g am HI Hu) as (rg2 & Hr2 & Hk2 & Hl2 & Ho2 & Hext2 & _).
destruct (In_group_cells_span X R U s g am c HI Hu Hc) as (d & E & Hd & Hw).
destruct (Nat.eq_dec (prid (am_mem am)) k) as [Ek|Nk].
2:{ exfalso. apply (other_home c (LMem (SP (prid (am_mem am)) 0), rg_len rg2) (footprint_region_In s _ _ Hr2 Hk2 Hl2)); [| | exact Hcov].
- intros Ee. apply Nk. subst eK. injection Ee as E1 _. exact E1.
- unfold cell_range, crange, range_incl. rewrite E. rewrite loc_addr_LMem, poff_padd, prid_padd. cbn [fst snd loc_addr]. unfold IB in Hext2. lia. }
rewrite Ek in *. rewrite Hk in Hr2. injection Hr2 as <-.
pose proof (used_group_aligned X R U s HI _ g am Hu (Nat.le_refl _)) as Hal.
pose proof (stride_mod16 X R U s g am HI Hu) as Hst.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _ & Gsl & _).
rewrite E, loc_addr_LMem, poff_padd, prid_padd, Ek in Hcov.
assert (T : exists t, 0 <= t < Z.of_nat (mc_w c) /\ (poff (am_mem am) + d + t) mod 16 = 12).
{ exists (x - ly_reg L k - poff (am_mem am) - d). split; [lia|]. replace (poff (am_mem am) + d + (x - ly_reg L k - poff (am_mem am) - d)) with (x - ly_reg L k) by lia. exact H12. }
destruct T as (t & Ht & Hm). rewrite <- Z.add_assoc, (mod16_of _ _ Hal) in Hm.
unfold group_cells in Hc. apply in_app_iff in Hc as [Hc|Hc].
- exfalso. destruct Hc as [<-|[<-|[]]]; cbn [mc_loc mc_w] in E, Ht.
+ rewrite <- (padd_0 (am_mem am)) in E at 1. apply (f_equal (fun l => match l with LMem p => poff p | _ => 0 end)) in E. rewrite !poff_padd in E.
assert (d = 0) by lia. subst d. rewrite Z.mod_small in Hm by lia. lia.
+ destruct (am_maplen am =? 0); cbn [mc_loc mc_w] in E, Ht;
apply (f_equal (fun l => match l with LMem p => poff p | _ => 0 end)) in E; rewrite !poff_padd in E;
(assert (d = 8) by lia); subst d; rewrite Z.mod_small in Hm by lia; lia.
- apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi.
assert (Hsi : (stride_of am * i) mod 16 = 0).
{ rewrite Z.mul_mod, Hst, Z.mul_0_l by lia. reflexivity. }
unfold slot_cells in Hc. rewrite !in_app_iff in Hc.
assert (EQD : forall p dd, LMem (padd (am_mem am) d) = LMem (padd p dd) -> d = poff p + dd - poff (am_mem am)).
{ intros p dd Ep. apply (f_equal (fun l => match l with LMem q => poff q | _ => 0 end)) in Ep. rewrite !poff_padd in Ep. lia. }
destruct Hc as [Hc|[Hc|Hc]].
+ destruct Hc as [<-|[]]. split; reflexivity.
+ exfalso. destruct (ss_hdr (nth_slot am i)) as [[h3 h16]|]; [|destruct Hc].
destruct Hc as [<-|[<-|[]]]; cbn [mc_loc mc_w] in E, Ht; symmetry in E; apply EQD in E; rewrite ?poff_padd, ?poff_slot_start in E; subst d.
* replace (poff (am_mem am) + UNIT + stride_of am * i + -3 - poff (am_mem am) + t) with (stride_of am * i + (13 + t)) in Hm by (unfold UNIT; lia).
rewrite (mod16_of _ _ Hsi), Z.mod_small in Hm by lia. lia.
* replace (poff (am_mem am) + UNIT + stride_of am * i + -2 - poff (am_mem am) + t) with (stride_of am * i + (14 + t)) in Hm by (unfold UNIT; lia).
rewrite (mod16_of _ _ Hsi), Z.mod_small in Hm by lia. lia.
+ destruct (ss_fr (nth_slot am i)) as [fr|]; [|destruct Hc]. destruct (fr_off fr =? 0); [destruct Hc|].
destruct Hc as [<-|[<-|[<-|[]]]]; cbn [mc_loc mc_w] in E, Ht; [split; reflexivity | exfalso | exfalso];
symmetry in E; apply EQD in E; rewrite ?poff_padd, ?poff_slot_start in E; subst d.
* replace (poff (am_mem am) + UNIT + stride_of am * i + UNIT * fr_off fr + -3 - poff (am_mem am) + t) with ((stride_of am * i + fr_off fr * 16) + (13 + t)) in Hm by (unfold UNIT; lia).
rewrite mod16_of, Z.mod_small in Hm by (try lia; rewrite Z.add_mod, Hsi, Z_mod_mult by lia; reflexivity). lia.
* replace (poff (am_mem am) + UNIT + stride_of am * i + UNIT * fr_off fr + -2 - poff (am_mem am) + t) with ((stride_of am * i + fr_off fr * 16) + (14 + t)) in Hm by (unfold UNIT; lia).
rewrite mod16_of, Z.mod_small in Hm by (try lia; rewrite Z.add_mod, Hsi, Z_mod_mult by lia; reflexivity). lia.
Qed.
Lemma tail_cell_12 : forall g am c, usedX X s g am -> In c (group_tail_cells am) ->
loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) -> mc_w c = 1%nat /\ mc_val c = VZ 0.
Proof.
intros g am c Hu Hc Hcov.
destruct (used_group_region X R U s g am HI Hu) as (rg2 & Hr2 & Hk2 & Hl2 & Ho2 & Hext2 & _).
pose proof (used_group_aligned X R U s HI _ g am Hu (Nat.le_refl _)) as Hal.
pose proof (stride_mod16 X R U s g am HI Hu) as Hst.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as ((Glast & _) & _ & Gsl & _).
unfold group_tail_cells in Hc. destruct Hc as [<-|Hc]; [split; reflexivity|].
apply in_flat_map in Hc as [i [Hi Hc]]. apply In_zseq in Hi. unfold frame_tail_cells in Hc.
destruct (ss_fr (nth_slot am i)) as [fr|] eqn:Efr; [|destruct Hc]. destruct (fr_kind fr); [|destruct Hc].
apply in_app_iff in Hc as [Hc|Hc].
- destruct (0 <? reserved_of am fr); [|destruct Hc]. destruct Hc as [<-|[]]. split; reflexivity.
- destruct (5 <=? reserved_of am fr) eqn:E5; [|destruct Hc]. apply Z.leb_le in E5.
destruct Hc as [<-|[<-|[]]]; [exfalso | split; reflexivity]. cbn [mc_loc mc_w] in Hcov.
unfold slot_end in Hcov. rewrite loc_addr_LMem, !poff_padd, !prid_padd, poff_slot_start, prid_slot_start in Hcov.
assert (Hsi : (stride_of am * i) mod 16 = 0) by (rewrite Z.mul_mod, Hst, Z.mul_0_l by lia; reflexivity).
pose proof (Gsl i ltac:(lia)) as (_ & _ & S3). rewrite Efr in S3. destruct S3 as (_ & _ & (Nf & Of & Bf & _) & _).
unfold reserved_of in E5.
destruct (Nat.eq_dec (prid (am_mem am)) k) as [Ek|Nk].
+ rewrite Ek in *.
assert (T : exists t, 0 <= t < 4 /\ (poff (am_mem am) + ((stride_of am * i + stride_of am) + (8 + t))) mod 16 = 12).
{ exists (x - ly_reg L k - (poff (am_mem am) + UNIT + stride_of am * i + (stride_of am - IB) + -4)). split; [cbn [Z.of_nat] in Hcov; lia|].
match goal with |- ?a mod 16 = 12 => replace a with (x - ly_reg L k) by (unfold UNIT, IB; lia) end. exact H12. }
destruct T as (t & Ht & Hm). rewrite (mod16_of _ _ Hal) in Hm.
rewrite mod16_of, Z.mod_small in Hm; [lia | lia |]. rewrite Z.add_mod, Hsi, Hst by lia. reflexivity.
+ apply (other_home (MCell (LMem (padd (padd (slot_start am i) (stride_of am - IB)) (-4))) 4 (VZ (stride_of am - IB - UNIT * fr_off fr - fr_n fr)))
(LMem (SP (prid (am_mem am)) 0), rg_len rg2) (footprint_region_In s _ _ Hr2 Hk2 Hl2)).
* intros Ee. apply Nk. subst eK. injection Ee as E1 _. exact E1.
* unfold cell_range, crange, range_incl. cbn [mc_loc mc_w fst snd]. unfold slot_end. rewrite ?loc_addr_LMem, ?poff_padd, ?prid_padd, ?poff_slot_start, ?prid_slot_start. cbn [loc_addr].
assert (stride_of am * i + stride_of am <= stride_of am * (am_last am + 1)) by nia. assert (0 <= stride_of am * i) by nia.
cbn [prid poff Z.of_nat Pos.to_nat]. unfold group_extent, UNIT, IB in *. lia.
* cbn [mc_loc mc_w]. unfold slot_end. rewrite ?loc_addr_LMem, ?poff_padd, ?prid_padd, ?poff_slot_start, ?prid_slot_start. exact Hcov.
Qed.
Theorem cells_at_12 : forall c, In c (image s ++ tail_cells s) ->
loc_addr L (mc_loc c) <= x < loc_addr L (mc_loc c) + Z.of_nat (mc_w c) -> mc_w c = 1%nat /\ mc_val c = VZ 0.
Proof.
intros c Hin Hcov. apply in_app_iff in Hin as [Hin|Hin].
- destruct (In_image_inv s c Hin) as [Hc | [(a & next & Ha & Hc) | (g & am & Hg & Hc)]].
+ exfalso. destruct (ctx_cell_home L s c Hc) as [He HIc]. apply (other_home c _ He); [| exact HIc | exact Hcov]. intros E. discriminate E.
+ exfalso. destruct (area_cell_home L s a next c Ha Hc) as [He HIc]. apply (other_home c _ He); [| exact HIc | exact Hcov].
intros E. subst eK. injection E as Ea _. destruct (inv_areas HI) as (_ & Hareas & _).
destruct (Hareas a Ha) as (r & o & rga & Eao & _ & _ & Hr & _ & _ & Hknd). rewrite Eao in Ea. injection Ea as -> ->.
rewrite Hk in Hr. injection Hr as <-. rewrite Hkind in Hknd. exact Hknd.
+ apply (group_cell_12 g am c); [| exact Hc | exact Hcov]. apply (used_metas_usedX' X R U s HI XC). exact Hg.
- unfold tail_cells in Hin. apply in_flat_map in Hin as [[g am] [Hg Hc]]. cbn [snd] in Hc.
apply (tail_cell_12 g am c); [| exact Hc | exact Hcov]. apply (used_metas_usedX' X R U s HI XC). exact Hg.
Qed.
End h.
End f.
