(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2p.v, with its module paths changed. *)
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
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO10.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO12.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2o.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2u.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section i.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Variables (g : sptr) (am : ameta) (J lo hi : Z).
Hypothesis Hu : usedX X s g am.
Hypothesis HJ : 0 <= J <= am_last am.
Hypothesis Hnofr : ss_fr (nth_slot am J) = None.
Hypothesis Hlo : poff (slot_start am J) <= lo.
Hypothesis Hhi : hi <= poff (slot_start am J) + stride_of am - IB.
Hypothesis Hlh : lo < hi.
Let base := ly_reg L (prid (am_mem am)).
Lemma loc_addr_mem p d : loc_addr L (LMem (padd p d)) = ly_reg L (prid p) + poff p + d.
Proof. destruct p; cbn. lia. Qed.
Lemma body_span :
exists rg, region_of s (prid (am_mem am)) = Some rg /\ rg_kind rg = RkMap /\ rg_live rg = true /\
In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint s) /\
range_incl (base + lo, hi - lo) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg)) /\
poff (am_mem am) + UNIT <= lo /\ hi <= poff (am_mem am) + group_extent am.
Proof.
destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (slot_in_span X R U s HI g am J Hu HJ) as [S1 S2].
exists rg. split; [exact Hr|]. split; [exact Hk|]. split; [exact Hl|]. split; [apply footprint_region_In; assumption|].
unfold range_incl, crange. cbn [fst snd loc_addr]. unfold base. unfold UNIT, IB in *. repeat split; lia.
Qed.
Lemma other_entry c e :
In e (footprint s) -> range_incl (cell_range L c) (crange L e) ->
(forall rg, region_of s (prid (am_mem am)) = Some rg -> rg_kind rg = RkMap -> e <> (LMem (SP (prid (am_mem am)) 0), rg_len rg)) ->
ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros He Ic Hne. destruct body_span as (rg & Hr & Hk & Hl & InR & IB' & _).
pose proof HL as (_ & _ & PW & _).
destruct (pairwise_map_In ranges_disjoint (crange L) (footprint s) _ _ PW He InR (Hne rg Hr Hk)) as [D|D].
- eapply ranges_disjoint_incl; [exact D | exact Ic | exact IB'].
- apply ranges_disjoint_sym. eapply ranges_disjoint_incl; [exact D | exact IB' | exact Ic].
Qed.
Lemma same_region_cell c q d :
mc_loc c = LMem (padd q d) -> prid q = prid (am_mem am) ->
(poff q + d + Z.of_nat (mc_w c) <= lo \/ hi <= poff q + d) ->
ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros E Hp D. unfold ranges_disjoint, cell_range. cbn [fst snd]. rewrite E, loc_addr_mem, Hp. unfold base. lia.
Qed.
Lemma group_cells_free q aq c :
usedX X s q aq -> In c (group_cells q aq) -> ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros Uq Hc. destruct body_span as (rg & Hr & Hk & Hl & InR & IB' & Blo & Bhi).
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (group_cell_homeX X R U s L HI q aq c Uq Hc) as (rg' & Hr' & Hk' & Hl' & In' & I').
apply (other_entry c _ In' I'). intros rg0 Hr0 Hk0 E. injection E as Ep _. exact (Hdiff Ep). }
destruct (In_group_cells_span X R U s q aq c HI Uq Hc) as (d & E & Hd & Hw).
destruct (sptr_eq_dec q g) as [-> | Hne].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->.
destruct (group_cells_vs_body X R U s g am J lo hi c HI Hu HJ Hc ltac:(rewrite Hnofr; lia) Hhi) as (d' & E' & D').
exact (same_region_cell c _ _ E' eq_refl D').
- destruct (inv_laminar HI q aq g am Uq Hu Hne Hsame) as [Dj | [I | I]].
+
apply (same_region_cell c _ _ E Hsame). unfold spans_disjoint in Dj. unfold UNIT, IB in *. lia.
+
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
assert (Hj : j0 <> J) by (intros ->; rewrite Hnofr in Hfr0; discriminate).
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0. rewrite poff_slot_start in Hlo, Hhi.
apply (same_region_cell c _ _ E Hsame).
destruct (same_group_starts am j0 J Hj Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
+
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
rewrite Mem0 in Lo0, Hi0.
destruct (group_cells_vs_body X R U s q aq j0 lo hi c HI Uq Hj0 Hc
ltac:(rewrite Hfr0, Off0; unfold UNIT in *; lia)
ltac:(unfold IB in *; lia)) as (d' & E' & D').
exact (same_region_cell c _ _ E' Hsame ltac:(lia)).
Qed.
Lemma tail_cells_free q aq c :
usedX X s q aq -> In c (group_tail_cells aq) -> ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros Uq Hc. destruct body_span as (rg & Hr & Hk & Hl & InR & IB' & Blo & Bhi).
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
destruct (Nat.eq_dec (prid (am_mem aq)) (prid (am_mem am))) as [Hsame | Hdiff].
2:{ destruct (tail_cell_homeX X R U s L HI aq c q Uq Hc) as (rg' & Hr' & Hk' & Hl' & In' & I').
apply (other_entry c _ In' I'). intros rg0 Hr0 Hk0 E. injection E as Ep _. exact (Hdiff Ep). }
destruct (tail_cell_home X R U s HI q aq c Uq Hc) as (rg' & d & _ & _ & _ & E & Hd & Ho' & Hfit & Hw).
destruct (sptr_eq_dec q g) as [-> | Hne].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->.
destruct (tail_cells_vs_body X R U s HI g am J lo hi c Hu HJ Hc Hlo Hhi ltac:(intros f Hf; rewrite Hnofr in Hf; discriminate)) as (d' & E' & D').
exact (same_region_cell c _ _ E' eq_refl D').
- pose proof (extent_pos _ _ _ _ _ (inv_groups HI q aq Uq)) as Pq.
destruct (inv_laminar HI q aq g am Uq Hu Hne Hsame) as [Dj | [I | I]].
+ apply (same_region_cell c _ _ E Hsame). unfold spans_disjoint in Dj. unfold UNIT, IB in *. lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
assert (Hj : j0 <> J) by (intros ->; rewrite Hnofr in Hfr0; discriminate).
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0. rewrite poff_slot_start in Hlo, Hhi.
apply (same_region_cell c _ _ E Hsame).
destruct (same_group_starts am j0 J Hj Sp) as [LE|LE]; rewrite !poff_slot_start in LE; unfold UNIT, IB in *; [left|right]; lia.
+ destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
rewrite Mem0 in Lo0, Hi0.
destruct (tail_cells_vs_body X R U s HI q aq j0 lo hi c Uq Hj0 Hc
ltac:(unfold UNIT in *; lia) ltac:(unfold IB in *; lia)
ltac:(intros f Hf Hkf; rewrite Hfr0 in Hf; injection Hf as <-; rewrite Hk0 in Hkf; discriminate)) as (d' & E' & D').
exact (same_region_cell c _ _ E' Hsame ltac:(lia)).
Qed.
Theorem slot_body_free c :
In c (imageX X s ++ tail_cellsX X s) -> ranges_disjoint (cell_range L c) (base + lo, hi - lo).
Proof.
intros Hc. apply in_app_iff in Hc as [Hc|Hc].
- unfold imageX in Hc. apply in_app_iff in Hc as [Hc|Hc].
{ destruct (ctx_cell_home L s c Hc) as [In1 I1]. apply (other_entry c _ In1 I1). intros; discriminate. }
apply in_app_iff in Hc as [Hc|Hc].
{ destruct (In_areas_cells s _ c Hc) as (a & next & Ha & Hc'). destruct (area_cell_home L s a next c Ha Hc') as [In1 I1].
apply (other_entry c _ In1 I1). intros rg Hr Hk. exact (area_entry_not_region X R U s HI a _ rg Ha Hr Hk). }
apply in_flat_map in Hc as ([q aq] & Hq & Hc). cbn [fst snd] in Hc.
exact (group_cells_free q aq c (usedX_of_used_metasX X R U s HI q aq Hq) Hc).
- unfold tail_cellsX in Hc. apply in_flat_map in Hc as ([q aq] & Hq & Hc). cbn [snd] in Hc.
exact (tail_cells_free q aq c (usedX_of_used_metasX X R U s HI q aq Hq) Hc).
Qed.
End i.
Section k.
Variables (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) (L : layout).
Hypothesis HI : Inv X R U s.
Hypothesis HL : layout_ok L s.
Variables (g : sptr) (am : ameta) (J lo hi : Z).
Hypothesis Hu : usedX X s g am.
Hypothesis HJ : 0 <= J <= am_last am.
Hypothesis HnoUser : forall f, ss_fr (nth_slot am J) = Some f -> fr_kind f = FGroup.
Hypothesis HnoChild : forall c ac, usedX X s c ac -> am_maplen ac = 0 -> am_mem ac <> slot_start am J.
Hypothesis Hlo : poff (slot_start am J) <= lo.
Hypothesis Hhi : hi <= poff (slot_start am J) + stride_of am - IB.
Hypothesis Hlh : lo < hi.
Let base := ly_reg L (prid (am_mem am)).
Theorem slot_body_no_block b : In b (user_blocks s) -> ranges_disjoint (block_range L b) (base + lo, hi - lo).
Proof.
intros Hb. pose proof HL as (_ & _ & PW & _).
destruct (used_group_region X R U s g am HI Hu) as (rg & Hr & Hk & Hl & Ho & Hext & _).
pose proof (slot_in_span X R U s HI g am J Hu HJ) as [S1 S2].
pose proof (footprint_region_In s _ _ Hr Hk Hl) as InR.
pose proof (inv_groups HI g am Hu) as G. pose proof (stride_pos _ _ _ _ _ G) as Sp. pose proof G as (_ & _ & Gsl & _).
assert (IB' : range_incl (base + lo, hi - lo) (crange L (LMem (SP (prid (am_mem am)) 0), rg_len rg))).
{ unfold range_incl, crange. cbn [fst snd loc_addr]. unfold base. unfold UNIT, IB in *. lia. }
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
apply GOAL. unfold frame_ptr. rewrite poff_padd.
destruct (sptr_eq_dec q g) as [-> | Hne].
- pose proof (usedX_fun _ _ _ _ _ Uq Hu) as ->.
assert (Hjj : j <> J) by (intros ->; rewrite Hfq in HnoUser; specialize (HnoUser fq eq_refl); rewrite Hkq in HnoUser; discriminate).
destruct (same_group_starts am j J Hjj Sp) as [LE|LE]; rewrite ?poff_slot_start in *; unfold UNIT, IB in *; [left|right]; lia.
- pose proof (extent_pos _ _ _ _ _ Gq) as Pq.
destruct (inv_laminar HI q aq g am Uq Hu Hne Hsame) as [Dj | [I | I]].
+ unfold spans_disjoint in Dj. unfold UNIT, IB in *. lia.
+
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
assert (Hjj : j0 <> J) by (intros ->; exact (HnoChild c0 ac0 Uc0 Ml0 Mem0)).
pose proof (Gsl j0 Hj0) as (_ & _ & S3). rewrite Hfr0 in S3. destruct S3 as (_ & _ & (N0 & O0 & B0 & _) & _).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
destruct (same_group_starts am j0 J Hjj Sp) as [LE|LE]; rewrite ?poff_slot_start in *; unfold UNIT, IB in *; [left|right]; lia.
+
destruct I as (j0 & fr0 & c0 & ac0 & Hj0 & Hfr0 & Hk0 & Uc0 & Ml0 & Mem0 & Lo0 & Hi0 & Fit0).
destruct (fgroup_frame X R U s HI q aq j0 fr0 Uq Hj0 Hfr0 Hk0) as [Fn0 Off0].
assert (Hjj : j <> j0) by (intros ->; rewrite Hfr0 in Hfq; injection Hfq as <-; rewrite Hk0 in Hkq; discriminate).
rewrite Mem0, poff_slot_start in Lo0, Hi0.
destruct (same_group_starts aq j j0 Hjj Spq) as [LE|LE]; rewrite ?poff_slot_start in *; unfold UNIT, IB in *; [left|right]; lia.
Qed.
End k.
End h.
