(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w YC0j YC0v YC0r YC0t YC0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma af_newcfg_kept : forall (m m' : word -> option byte) nw lpal fattr fgen delay nlp tidx,
af_newcfg m nw lpal fattr fgen delay nlp tidx ->
(forall a, nw <= a < nw + 40 -> ~ (nw + 8 <= a < nw + 16) -> mbyte trasegs m' a = mbyte trasegs m a) ->
af_newcfg m' nw lpal fattr fgen delay nlp tidx.
Proof.
intros m m' nw lpal fattr fgen delay nlp tidx (V0 & V16 & V20 & V24 & V26 & V28) HK.
assert (T : forall a (n : nat) v, val_mem trasegs m a n v -> nw <= a -> a + Z.of_nat n <= nw + 40 ->
(a + Z.of_nat n <= nw + 8 \/ nw + 16 <= a) -> val_mem trasegs m' a n v).
{ intros a n v Hv H1 H2 H3 j Hj. rewrite (HK (a + Z.of_nat j)) by lia. exact (Hv j Hj). }
split; [apply (T _ 8%nat _ V0); cbn; lia|]. split; [apply (T _ 4%nat _ V16); cbn; lia|]. split; [apply (T _ 4%nat _ V20); cbn; lia|].
split; [apply (T _ 2%nat _ V24); cbn; lia|]. split; [apply (T _ 2%nat _ V26); cbn; lia|].
intros H6. apply (T _ 1%nat _ (V28 H6)); cbn; lia.
Qed.

Ltac awr_x_rec Usp E32u Hing HTS Bnw Anw HnwIn :=
lazymatch goal with
| |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
| |- awr_ok _ (YQ0b.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
first
[ apply awr_ok_cons_ro; [cbn; lia|]
| lazymatch goal with
| |- awr_ok _ (YQ0b.mkRegion (Some 2%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -224);
[reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite Usp; lia
| cbn; rewrite HTS; lia | cbn; lia |]
| |- awr_ok _ (YQ0b.mkRegion (Some 32%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
eapply awr_ok_cons_block with (n := 32%nat) (m := CGIF_SIZE);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact E32u | exact Hing | cbn [YQ0b.r_wlo]; lia
| cbn [YQ0b.r_whi]; change (req_size CGIF_SIZE) with 96; lia
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; unfold FPa, ablocks_fp, cgif_blocks; cbn [map fst snd app];
lazymatch type of E32u with _ = ?g => exists (g, g + req_size CGIF_SIZE) end;
split; [left; reflexivity | cbn [fst snd]; change (req_size CGIF_SIZE) with 96; lia]
| ]
| |- awr_ok _ (YQ0b.mkRegion (Some 23%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bnw with _ = ?nw =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 23%nat nw);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Bnw
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; replace a with (nw + (a - nw)) by lia; apply Anw; [exact HnwIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_x: no rule for the head region" ];
awr_x_rec Usp E32u Hing HTS Bnw Anw HnwIn
end.
Ltac awr_x Usp E32u Hing HTS Bnw Anw HnwIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_x_rec Usp E32u Hing HTS Bnw Anw HnwIn.
Ltac locvD2 HR0 sp0 E32 E32u E38 E46 E67 E23 E23u Usp Hcfp HZg Hgceil Hn4096 Hnceil C1 :=
lazymatch goal with |- val_mem _ _ (?spx - 224 + ?off) 8 ?v =>
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk off (CVal 8 ?e)] =>
apply (field_of_region Ex _ 2 (spx - 224) cs lo hi wlo whi off 8 e v HR0 Usp); [cbn; tauto | | | cbn; lia];
[ lazymatch e with
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 32 38 _ _ SB E32 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 46 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 46 38 _ _ SB E46 E38); clear - HZg Hcfp Hgceil C1; unfold SB; lia
| SAlu ALU_ADD (SAlu ALU_SRL (SOff 23 _) (SLit 3)) (SOff 38 0) => apply (denot_shx Ex 23 38 _ _ SB E23 E38); clear - Hn4096 Hnceil C1; unfold SB; lia
| _ => cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub];
rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E46 | exact E67 | exact E23 | rewrite E32u; reflexivity | rewrite E23u; reflexivity | rewrite E46, unsigned_lit_small by lia; reflexivity
| idtac "LOCVD2-DENOT-FAIL" off ]
end
| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
first [ lazymatch goal with |- 0 <= _ + ?x / 8 < _ =>
let Hd := fresh "Hd" in
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (clear - Hcfp HZg Hn4096 Hnceil C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]);
clear - Hd C1; unfold SB; lia end
| clear - Hcfp HZg Hn4096 Hnceil C1; lia
| destruct (Z.land _ 4 =? 0); clear; lia
| idtac "LOCVD2-RANGE-FAIL" off ] ]
| _ => idtac "LOCVD2-NO-CHUNK" off
end end end.
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsD2 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88))
21 (SOff 46 8)) 25 (shq 46 8)) 26 (SOff 32 48)) 19 (shq 32 48)) 27 (SOff 32 50)) 20 (shq 32 50).
Definition af_lcxD2 : list YQ0b.chunk :=
[YQ0b.mkChunk 8 (CVal 8 (shq 46 0)); YQ0b.mkChunk 16 (CVal 8 (shq 23 0)); YQ0b.mkChunk 24 (CVal 8 (shq 46 26));
YQ0b.mkChunk 72 (CVal 8 (SOff 46 26)); YQ0b.mkChunk 96 (CVal 8 (SOff 23 8)); YQ0b.mkChunk 112 (CVal 8 (shq 23 8))].
Definition af_SH23 : list shent := af_SH ++ [mkSHE 23 0 FRAME_SIZE].
Definition af_nwr : YQ0b.region := YQ0b.mkRegion (Some 23%nat) 0 40 8 16 [].
Section l.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis AMEMCPY : aintrin_realizes trasegs B OCpy A_asan_memcpy.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsD2_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp lpal img fattr fgen delay nlp tidx more,
af_regs_at B regs regs1 g -> af_s1_at regs1 g ->
getr regs1 21 = w64 (cfp + 8) -> getr regs1 25 = w64 (SB + (cfp + 8) / 8) ->
getr regs1 26 = w64 (g + 48) -> getr regs1 19 = w64 (SB + (g + 48) / 8) ->
getr regs1 27 = w64 (g + 50) -> getr regs1 20 = w64 (SB + (g + 50) / 8) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)) regsD2 regs1.
Proof.
intros regs regs1 g s1 cfp lpal img fattr fgen delay nlp tidx more (R2 & R3 & R4 & R18 & R8 & R22) R9 R21 R25 R26 R19 R27 R20 Hg0 Hgc Hc0 Hcc. unfold af_s1_at in R9.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9
| rewrite (denot_shx E 32 38 48 g SB E32 E38) by (unfold SB; lia); exact R19
| rewrite (denot_shx E 32 38 50 g SB E32 E38) by (unfold SB; lia); exact R20
| rewrite (denot_shx E 46 38 8 cfp SB E46 E38) by (unfold SB; lia); exact R25
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; first [exact R8 | exact R26 | exact R27]]
| rewrite E38; exact R22
| rewrite E46; rewrite unsigned_lit_small by lia; exact R21 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_D2 : AF_RETC_stmt B -> AF_E_stmt B -> AF_D3_stmt B -> AF_D2_stmt B.
Proof.
intros PRC PE PD3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw
CX MID Hk HBB HR HR9 R24 R23 R10 R21 R25 R26 R19 R27 R20 HL HnoTab Hi Hnone Hs1 HnwIn HNC.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R22).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
assert (HEVF : EV_FLUSH = 35) by reflexivity. assert (HEVA : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
assert (HFS : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds trasegs _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
pose proof (in_app_sub _ _ cfp 32 Hfhigh ltac:(clear - Hflo; lia) ltac:(clear; lia) ltac:(clear - Hfhi; lia)) as Hcfp_ia.
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof HWF1 as (_ & HWge & HHge & HNWH & HNmax & _).
assert (HN1 : 1 <= N <= 100000000) by (clear - HWge HHge HNWH HNmax; nia).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0) as [He | Hne]; [exfalso; clear - HN1 He; lia | reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (HPn : Permutation (ablocks B lyc Sc) ((nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ eapply Permutation_trans; [exact HPerm1|]. apply Permutation_sym. apply (Permutation_middle (cgif_blocks g s1 N) (af_cblocks img N fattr lpa nlp rest) (nw, FRAME_SIZE)). }
assert (SEPw : forall b m, In (b, m) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> nw + 40 <= b \/ b + req_size m <= nw).
{ intros b m Hb. pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (nw, FRAME_SIZE) (b, m) _ HAR HPn Hb) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof (SEPw g CGIF_SIZE ltac:(left; reflexivity)) as D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trasegs _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal.
set (E := Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0])).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 36%nat ltac:(lia)) as E36. pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38.
pose proof (ES 42%nat ltac:(lia)) as E42. pose proof (ES 43%nat ltac:(lia)) as E43. pose proof (ES 46%nat ltac:(lia)) as E46.
pose proof (ES 47%nat ltac:(lia)) as E47. pose proof (ES 48%nat ltac:(lia)) as E48. pose proof (ES 49%nat ltac:(lia)) as E49. pose proof (ES 50%nat ltac:(lia)) as E50.
pose proof (ES 51%nat ltac:(lia)) as E51. pose proof (ES 52%nat ltac:(lia)) as E52. pose proof (ES 53%nat ltac:(lia)) as E53. pose proof (ES 67%nat ltac:(lia)) as E67.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E36, E37, E38, E42, E43, E46, E47, E48, E49, E50, E51, E52, E53, E67.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
pose proof HL as ((HLE & L8 & L16 & L24 & L112) & L72 & L96).
assert (HLX : Forall (YQ0b.chunk_ok trasegs E (mrestrict (w_H Wc) memc) (sp0 - 224 - 0)) af_lcxD2).
{ assert (Dsh : forall n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c <= 40 -> v + c <= alloc_ceiling ->
sv_denot E (shq n c) = Z_to_bv 64 (SB + (v + c) / 8) /\ 0 <= SB + (v + c) / 8 < 2 ^ (8 * Z.of_N 8)).
{ intros n c v Hn Hv Hc Hvc. split; [apply (denot_shx E n 38 c v SB Hn E38); unfold SB; clear - Hv Hc Hvc C1; lia|].
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by (clear - Hv Hc Hvc C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hd. unfold SB. lia. }
unfold af_lcxD2. repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YQ0b.chunk_ok _ _ _ _ (YQ0b.mkChunk ?off (CVal 8 ?e)) =>
lazymatch e with
| shq 46 ?c => destruct (Dsh 46%nat c cfp E46 ltac:(clear - Hcfp; lia) ltac:(clear; lia) ltac:(clear - Hcfp; lia)) as [Dd Dr];
apply (chunk_ok_val trasegs E _ (sp0 - 224 - 0) off 8 e _ Dd Dr); [cbn; clear; lia | replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption]
| shq 23 ?c => destruct (Dsh 23%nat c nw E23 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil; lia)) as [Dd Dr];
apply (chunk_ok_val trasegs E _ (sp0 - 224 - 0) off 8 e _ Dd Dr); [cbn; clear; lia | replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption]
| SOff 46 ?c => apply (chunk_ok_val trasegs E _ (sp0 - 224 - 0) off 8 e (cfp + c));
[ cbn [sv_denot]; rewrite E46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcfp C1; lia | cbn; clear; lia
| replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption ]
| SOff 23 ?c => apply (chunk_ok_val trasegs E _ (sp0 - 224 - 0) off 8 e (nw + c));
[ cbn [sv_denot]; rewrite Bnw; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia | cbn; clear; lia
| replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption ]
end end. }
destruct (af_reseedxE B TL LAWS AF_D2 regsD2 0 0 af_lcxD2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 [(nw, FRAME_SIZE)] []
CX MID Rsp HLE HLX ltac:(clear; lia) ltac:(clear; lia)
(regsD2_ok regs regs1 g s1 cfp lpal img fattr fgen delay nlp tidx _ HR HR9 R21 R25 R26 R19 R27 R20 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp))
ltac:(vm_compute; reflexivity)) as [HS SHOK].
change (Ereg regs1 _) with E in HS, SHOK.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA.
{ awr_a Usp E32u Hing HTS. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340228) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre lyc (aview trasegs (w_H Wc) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre lyc _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp, Usp; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot]; rewrite E32u; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
assert (HliveC : blocks_bytes Sc + N <= LIVE_MAX) by (clear - HBB Hlive HN1 HFS; unfold LIVE_ADDFRAME in Hlive; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_malloc_at trasegs B LAWS Hsegs errno_low ML AMALLOC Wc (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
lyc Sc _ k N (-224) (Z_to_bv 64 0x863a8) [] HJ);
[ rewrite Ra0; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl); exact R10
| unfold MALLOC_MAX; clear - HN1; lia
| exact HliveC
| unfold spZ; rewrite Qsp, Usp; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp, (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite Qtp, (EEo 4%nat 4%bv eq_refl); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| clear - Hnev Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode; apply (tl_universe B TL);
apply TRACES_cgif_addframe_U; apply memZL_In; vm_compute; reflexivity ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hres).
pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & HLY2 & _ & _ & _ & _ & Hnev2 & _).
destruct (mres_kept B lyc Sc Wc _ W2 mem2 ly2 S2 _ _ res N Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 lyc Sc res N _ _ HAR2 Hres) as Hrng. rewrite HrqN in Hrng, HK.
pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY2 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
assert (SEPn : forall b m ii, In (b, m) (ablocks B lyc Sc) -> 0 <= ii < req_size m -> ~ (res <> 0 /\ res <= b + ii < res + N)).
{ intros b m ii Hb Hii [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res N b m HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hb) as D.
rewrite HrqN in D. clear - D Hii Hin. lia. }
assert (HnewG : forall a, g + 0 <= a < g + 96 -> ~ (res <> 0 /\ res <= a < res + N)).
{ intros a Ha. replace a with (g + (a - g)) by (clear; lia). apply (SEPn g CGIF_SIZE (a - g) Hing). change (req_size CGIF_SIZE) with 96. clear - Ha. lia. }
assert (HnewN : forall a, nw + 0 <= a < nw + 40 -> ~ (res <> 0 /\ res <= a < res + N)).
{ intros a Ha. replace a with (nw + (a - nw)) by (clear; lia). apply (SEPn nw FRAME_SIZE (a - nw) HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha. lia. }
assert (HnewF : forall a, cfp + 0 <= a < cfp + 32 -> ~ (res <> 0 /\ res <= a < res + N)).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ res N cid pos HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2; exact Hfin)) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. rewrite HrqN in D. clear - D Ha Hin Hflo Hfhi. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep HS 68%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trasegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | clear; lia].
- apply (region_kept_val trasegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | clear; lia].
- eapply (region_kept_block_aj trasegs B); [exact HK | exact E32u | exact Hing | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | exact HnewG].
- eapply (region_kept_frame_aj trasegs B); [exact HK | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia | clear; lia | exact HnewF]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 68 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 68)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 72 = Z_to_bv 64 res) by (rewrite HE2; change 72%nat with (68 + 4)%nat; rewrite (YO3v.ew_havoc_new E 68 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Ha0).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 224) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E23_2 : ew E2 23 = Z_to_bv 64 nw) by (rewrite OLD2 by lia; exact E23).
assert (Bnw2 : bv_unsigned (ew E2 23) = nw) by (rewrite OLD2 by lia; exact Bnw).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (E46_2 : ew E2 46 = Z_to_bv 64 cfp) by (rewrite OLD2 by lia; exact E46).
assert (E47_2 : ew E2 47 = Z_to_bv 64 lpal) by (rewrite OLD2 by lia; exact E47).
assert (E48_2 : ew E2 48 = Z_to_bv 64 img) by (rewrite OLD2 by lia; exact E48).
assert (E49_2 : ew E2 49 = Z_to_bv 64 fattr) by (rewrite OLD2 by lia; exact E49).
assert (E52_2 : ew E2 52 = Z_to_bv 64 nlp) by (rewrite OLD2 by lia; exact E52).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
assert (Kblk : forall b m, In (b, m) (ablocks B lyc Sc) -> blk_kept (w_H Wc) (w_H W2) memc mem2 b (req_size m)).
{ intros b m Hb ii Hii. pose proof HK as (_ & K2 & _). etransitivity; [exact (K2 b m ii Hb Hii (SEPn b m ii Hb Hii))|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _). apply UN1; clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia. }
assert (HT2 : tcgif_at (mrestrict (w_H W2) mem2) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- exact (obj_at_blk_kept _ _ _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF (Kblk g CGIF_SIZE Hing)).
- apply (obj_at_blk_kept _ _ _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). apply (Kblk (cg_raw s1) RAW_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. left. reflexivity.
- intros f Hfi. apply (obj_at_blk_kept _ _ _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). apply (Kblk (fr_ptr f) FRAME_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
assert (HFR2 : af_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR). intros a Ha. pose proof HK as (K1 & _). apply (mbyte_of_aview trasegs).
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN1; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
assert (HNC2 : af_newcfg (mrestrict (w_H W2) mem2) nw lpal fattr fgen delay nlp tidx).
{ apply (af_newcfg_kept _ _ nw lpal fattr fgen delay nlp tidx HNC). intros a Ha Hn. apply (mbyte_of_aview trasegs).
replace a with (nw + (a - nw)) by (clear; lia). apply (Kblk nw FRAME_SIZE HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha; lia. }
pose proof (obj_at_nth trasegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
pose proof (HBin _ HnwIn) as HnwIn2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR2 HnwIn2) as (_ & _ & _ & _ & HnP2 & _). rewrite HFS in HnP2. change (req_size 40) with 40 in HnP2.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw2; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ af_nwr HS eq_refl
ltac:(unfold region_ok, af_nwr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw2; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HnP2 (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_nwr; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bnw2, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok trasegs Bxa af_SH23 E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR2 (HBin _ HnwIn)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw2.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{
destruct Hres as [(_ & Ebl & _) | (Habs & _)]; [| exfalso; clear - Habs Hres0; lia].
pose proof (st_ok_pin_reg' trasegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS.
aj_run_tok tratbl_lib_ok HS HJ2 SHOK RBspanA.
{ awr_x Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bnw2 Anw HnwIn2. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2b & _ & Kgot2b & _). rewrite HBgot, HBcell in Kgot2b. rewrite HBcell in Kcell2b.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp. rreg HS (8%bv : bv 5) Qs0.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340224) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; vm_compute; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre ly2 (aview trasegs (w_H W2) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre ly2 _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E32u2; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_free_at trasegs B LAWS Hsegs errno_low ML AFREE W2 (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly2 S2 _ (k + 1) nw FRAME_SIZE (-224) (Z_to_bv 64 0x86670) [] HJ2 HnwIn2);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E23_2
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| clear - Hnev2 Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode; apply (tl_universe B TL);
apply TRACES_cgif_addframe_U; apply memZL_In; vm_compute; reflexivity
| intros HnwOld ii Hii; exact (proj1 (HnewX _ (or_introl eq_refl)) HnwOld ii Hii) ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & El1 & Eab3) & Hfrs3 & HK3).
pose proof (proj1 HJ3) as HAR3. pose proof HJ3 as (_ & HLY3 & _).
rewrite HFS in HK3. change (req_size 40) with 40 in HK3.
replace (sp0 + -224 - ASTACK) with (sp0 - 224 - ASTACK) in HK3 by (clear; lia). replace (sp0 + -224) with (sp0 - 224) in HK3 by (clear; lia).
assert (HPerm3 : Permutation (ablocks B ly3 S3) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ rewrite Eab3. apply (Permutation_app_inv l1 l2 (cgif_blocks g s1 N) (af_cblocks img N fattr lpa nlp rest) (nw, FRAME_SIZE)).
rewrite <- El1, Ebl. exact HPerm1. }
assert (HBl3 : forall b m, In (b, m) (ablocks B lyc Sc) -> (b, m) <> (nw, FRAME_SIZE) -> In (b, m) (ablocks B ly3 S3)).
{ intros b m Hb Hne. rewrite Eab3. rewrite <- Ebl, El1 in Hb. apply in_app_iff in Hb. apply in_app_iff.
destruct Hb as [Hb | [Hb | Hb]]; [left; exact Hb | exfalso; exact (Hne (eq_sym Hb)) | right; exact Hb]. }
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (apply (HBl3 _ _ Hing); intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold CGIF_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
assert (EFA3 : frame_addr ly3 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY3 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa af_SH23 ss) end in
jafter_call_keep HS K regs3 (mrestrict (w_H W3) mem3) HP3 [1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj trasegs B); [exact HK3 | exact HJ3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp2 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj trasegs B); [exact HK3 | exact HJ3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Usp2 | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2b) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot3) | clear; lia].
- apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2b) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell3) | clear; lia].
- eapply (region_kept_block_aj trasegs B); [exact HK3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32u2 | exact (HBin _ Hing) | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia
| intros a Ha Hc; clear - Ha Hc Dgn; lia].
- eapply (region_kept_frame_aj trasegs B); [exact HK3 | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia
| rewrite Hfrs2; exact Hfin | rewrite EFA2; clear - Hflo; lia | rewrite EFA2; clear - Hfhi; lia | clear; lia | intros a Ha Hc; clear - Ha Hc Dcn; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in HS end.
assert (OLD3 : forall n, (n < 84)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 224) by (rewrite OLD3 by lia; exact Usp2).
assert (E32u3 : bv_unsigned (ew E3 32) = g) by (rewrite OLD3 by lia; exact E32u2).
assert (E32_3 : ew E3 32 = Z_to_bv 64 g) by (rewrite OLD3 by lia; exact E32_2).
assert (E38_3 : ew E3 38 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E38_2).
assert (E46_3 : ew E3 46 = Z_to_bv 64 cfp) by (rewrite OLD3 by lia; exact E46_2).
assert (EEo3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E3 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD3 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok trasegs Bxa af_SH E3 (mrestrict (w_H W3) mem3)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly3 S3 W3 _ _ _ g s N _ cfp 32 HJ3 HAR0 HPerm HFO) as (_ & _ & HRA3).
unfold sh_ok, af_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_block trasegs B LAWS ly3 S3 W3 mem3 md3 E3 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR3 Hing3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u3.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W3) mem3 E3 Bxa 46 cfp 32 cfp 0 32 HRA3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app. }
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RBspanA AF_RETC; [awr_a Usp3 E32u3 Hing3 HTS |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp3, ?E32u3 in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msq) => set (msL := msq) in * end.
assert (K3s : forall a, sp0 - 104 <= a < sp0 -> mbyte trasegs (mrestrict (w_H W3) (ms_mem msL)) a = mbyte trasegs (mrestrict (w_H W2) mem2) a).
{ intros a Ha. pose proof HK3 as (K1 & _). apply (mbyte_of_aview trasegs).
etransitivity; [apply UN3; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia|].
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN2; clear - Ha Hceil Hslo Hshi H47 HTS C1 Hnceil; lia. }
assert (K3b : forall b m ii, In (b, m) (cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> 0 <= ii < req_size m ->
~ (sp0 - 224 <= b + ii < sp0 - 104) ->
mbyte trasegs (mrestrict (w_H W3) (ms_mem msL)) (b + ii) = mbyte trasegs (mrestrict (w_H W2) mem2) (b + ii)).
{ intros b m ii Hb Hii Hns. pose proof HK3 as (_ & K2 & _). pose proof (SEPw b m Hb) as Hnn.
assert (Hbc : In (b, m) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPn|]; right; exact Hb).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbc) as (_ & Hb4096 & Hbceil & _).
apply (mbyte_of_aview trasegs).
etransitivity; [apply UN3; [clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia | exact Hns]|].
etransitivity; [apply (K2 b m ii (HBin _ Hbc) Hii); clear - Hnn Hii; lia|].
apply UN2; [clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia | clear - Hns Hnn Hii; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly3 S3 W3 rg mm mdq (k + 2) s1 2 CX) end.
- split; [replace (k + 2) with (k + 1 + 1) by (clear; lia); exact HJ3|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); exact K3s |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii.
apply (K3b g CGIF_SIZE ii ltac:(left; reflexivity) ltac:(change (req_size CGIF_SIZE) with 96; clear - Hii; lia)). clear - Hii HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. destruct (HZr ii Hii) as [Hb Hn].
apply (K3b (cg_raw s1) RAW_SIZE ii ltac:(right; left; reflexivity) ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia) Hn).
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. destruct (HZf f ii Hfi Hii) as [Hb Hn].
apply (K3b (fr_ptr f) FRAME_SIZE ii ltac:(apply in_app_iff; left; exact (af_frame_in_blocks g s1 N f Hfi)) ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia) Hn). }
split; [exact HOK|]. split; [exact HPerm3 | exact Hnew].
- clear - Hk HEVF HEVA; lia.
- unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E32_3 | exact E38_3 | rewrite E32u3; reflexivity
| rewrite (EEo3 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp | rewrite (EEo3 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (EEo3 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; reflexivity. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
rreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres.
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Rres. rewrite ?ew_ewset_other in Rres by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Rres.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 72%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2 ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E2r, unsigned_lit_small by lia; change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1 HN1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res N HAR2 HrIn) as (_ & _ & _ & _ & HrP & _). rewrite HrqN in HrP.
assert (Bres : bv_unsigned (ew E2 72) = res) by (rewrite E2r; apply unsigned_lit_small; lia).
pose proof (aftok_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N HJ HAR2 Ebl ltac:(clear - HN1; lia)) as Tnew.
assert (Anew : forall blc ii lyq ownq, In (res, N) blc -> 0 <= ii < req_size N -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (res + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (awr_new_block_any trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res N blc ii lyq ownq HJ HAR2 Ebl ltac:(clear - HN1; lia) Hbl Hii). }
assert (HimgC : In (img, N) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. right. apply in_app_iff. right. left. reflexivity. }
pose proof (HBin _ HimgC) as Himg2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N HAR2 Himg2) as (_ & Hi4096 & Hiceil & Hih_ia & HiP & _). pose proof (proj1 Hih_ia) as Hih. rewrite HrqN in Hiceil. rewrite HrqN in HiP.
pose proof (blk_off_img _ _ _ _ _ _ img N HAR2 Himg2) as Hih_img.
assert (Dri : res + N <= img \/ img + N <= res).
{ pose proof (SEPn img N 0 HimgC ltac:(rewrite HrqN; clear - HN1; lia)) as D1. pose proof (SEPn img N (N - 1) HimgC ltac:(rewrite HrqN; clear - HN1; lia)) as D2.
clear - D1 D2 Hr4096 HN1. lia. }
aj_run_tok tratbl_lib_ok HS HJ2 SHOK RBspanA.
{ awr_x Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bnw2 Anw HnwIn2. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2b & _ & Kgot2b & _). rewrite HBgot, HBcell in Kgot2b. rewrite HBcell in Kcell2b.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N (proj1 HJ2) Himg2) as (_ & _ & _ & _ & HiP0 & _). rewrite HrqN in HiP0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Qsp. rreg HS (3%bv : bv 5) Qgp. rreg HS (4%bv : bv 5) Qtp.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 335280) with (Z_to_bv 64 A_asan_memcpy).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at trasegs B LAWS Hsegs OCpy A_asan_memcpy AMEMCPY _ (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPa g s N) ly S W mem md []
ly2 S2 _ (k + 1) res img N (-224) (Z_to_bv 64 0x863f0) HJ2);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E2r
| rewrite Ra1; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E48_2
|
clear Ra2; let R := fresh "R" in rregD HS (12%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal;
lazymatch goal with |- U ?Ex _ = _ =>
let RW := fresh "RW" in let RH := fresh "RH" in let UH := fresh "UH" in let UW := fresh "UW" in
pose proof (obj_at_nth trasegs _ _ _ _ 7 (48, 2%N) (cg_W s1) (proj1 HT1) eq_refl eq_refl) as [_ RW];
pose proof (obj_at_nth trasegs _ _ _ _ 8 (50, 2%N) (cg_H s1) (proj1 HT1) eq_refl eq_refl) as [_ RH]; cbn [snd] in RW, RH;
assert (UH : U Ex (SExt false 16 (SOff 43 0)) = cg_H s1) by (apply (U_zext_small Ex 16 _ _ (U_atom Ex 43 _ ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite OLD2 by lia; exact E43) ltac:(clear - RH; lia))); [clear - RH; cbn in RH |- *; lia | cbn; clear; lia]);
assert (UW : U Ex (SExt false 16 (SOff 42 0)) = cg_W s1) by (apply (U_zext_small Ex 16 _ _ (U_atom Ex 42 _ ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite OLD2 by lia; exact E42) ltac:(clear - RW; lia))); [clear - RW; cbn in RW |- *; lia | cbn; clear; lia]);
rewrite U_mul_smallD by (rewrite UH, UW; clear - RW RH; nia); rewrite UH, UW; clear - HNWH; lia end
| clear - HN1; lia | clear - Hr4096; lia | clear - HrCeil C1; lia
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; lia
| reflexivity
| clear; lia
| rewrite HTS; unfold ESTACK; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| exact Rra
| apply ret_ok_even; vm_compute; reflexivity
| intros a Ha; split; [replace a with (res + (a - res)) by (clear; lia); apply Anew; [exact HrIn | rewrite HrqN; clear - Ha; lia] | unfold ESTACK; intro; clear - Ha H Hr4096 HrCeil Hceil Hslo HTS C1; lia]
| apply (amem_range_of_block trasegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJ2) HrIn); rewrite ?HrqN; clear - HN1; lia
| apply (range_addressable_of_block trasegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJ2) HrIn); rewrite ?HrqN; clear - HN1; lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly2 S2 W2 _ _ res N _ _ (proj1 HJ2) HrIn); rewrite ?HrqN; clear - HN1; lia
| split; [clear - Hi4096; lia|]; split; [clear - Hiceil C1; lia|]; split;
[ intros a Ha; split; [| unfold spZ, ESTACK; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; intro; clear - Ha H Hi4096 Hiceil Hceil Hslo HTS C1; lia];
apply (aview_some_of_apresent trasegs); apply (proj1 (HiP0 a ltac:(clear - Ha; lia)))
| split; [clear - Dri; lia|];
split; [apply (amem_range_of_block trasegs B LAWS ly2 S2 W2 _ _ img N _ _ (proj1 HJ2) Himg2); rewrite ?HrqN; clear - HN1; lia|]; split;
[ apply (range_addressable_of_block trasegs B LAWS ly2 S2 W2 _ _ img N _ _ (proj1 HJ2) Himg2); rewrite ?HrqN; clear - HN1; lia
| intros _; apply (shadow_hull_vis_of_block trasegs B LAWS ly2 S2 W2 _ _ img N _ _ (proj1 HJ2) Himg2); rewrite ?HrqN; clear - HN1; lia ] ] ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3).
replace (sp0 + -224 - ESTACK) with (sp0 - 224 - ESTACK) in Hfr3 by (clear; lia). replace (sp0 + -224) with (sp0 - 224) in Hfr3 by (clear; lia).
assert (HES : ESTACK = 4096) by reflexivity.
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 Bxa af_SH23 ss) end in
jafter_call_keep HS K regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil];
first
[ eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact Bnw2 | exact Usp2 | exact E32u2 | rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia]
| intros a Ha; cbn [YQ0b.r_lo YQ0b.r_hi] in Ha; apply Hfr3;
[ clear - Ha Hn4096 Hnceil HZg Hcfp HrCeil Hceil Hslo Hshi H47 HTS C1; lia
| intros X;
first [ apply (HnewN a); [clear - Ha; lia | split; [clear - Hr4096; lia | exact X]]
| apply (HnewG a); [clear - Ha; lia | split; [clear - Hr4096; lia | exact X]]
| apply (HnewF a); [clear - Ha; lia | split; [clear - Hr4096; lia | exact X]]
| clear - Ha X HrCeil Hceil Hslo HTS C1; lia ]
| rewrite HES; clear - Ha Hn4096 Hnceil HZg Hcfp Hgceil Hceil Hslo Hshi H47 HTS C1; lia ]
| exact Hpres3 ]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2b) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot3) | clear; lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2b) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell3) | clear; lia]
| match goal with |- ?gg => idtac "KEPTFAIL" gg end ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?Ex _ _ => set (E3 := Ex) in HS end.
assert (OLD3 : forall n, (n < 84)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; rewrite YO3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 224) by (rewrite OLD3 by lia; exact Usp2).
assert (E32u3 : bv_unsigned (ew E3 32) = g) by (rewrite OLD3 by lia; exact E32u2).
assert (E32_3 : ew E3 32 = Z_to_bv 64 g) by (rewrite OLD3 by lia; exact E32_2).
assert (E23_3 : ew E3 23 = Z_to_bv 64 nw) by (rewrite OLD3 by lia; exact E23_2).
assert (Bnw3 : bv_unsigned (ew E3 23) = nw) by (rewrite OLD3 by lia; exact Bnw2).
assert (E38_3 : ew E3 38 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E38_2).
assert (E46_3 : ew E3 46 = Z_to_bv 64 cfp) by (rewrite OLD3 by lia; exact E46_2).
assert (E47_3 : ew E3 47 = Z_to_bv 64 lpal) by (rewrite OLD3 by lia; exact E47_2).
assert (E67_3 : ew E3 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD3 by lia; exact E67_2).
assert (E72_3 : ew E3 72 = Z_to_bv 64 res) by (rewrite OLD3 by lia; exact E2r).
assert (Bres3 : bv_unsigned (ew E3 72) = res) by (rewrite OLD3 by lia; exact Bres).
assert (EEo3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 68)%nat -> ew E3 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD3 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok trasegs Bxa af_SH23 E3 (mrestrict (w_H W2) mem3)).
{ assert (HRA3 : range_addressable (aview trasegs (w_H W2) mem3) SHADOW_OFF cfp 32).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ3 HAR0 HPerm HFO) as (_ & _ & HRA3). exact HRA3. }
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ3) (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u3.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H W2) mem3 E3 Bxa 46 cfp 32 cfp 0 32 HRA3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trasegs B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE (proj1 HJ3) HnwIn2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw3.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
aj_run_tok tratbl_lib_ok HS HJ3 SHOK RBspanA.
all: try (awr_x Usp3 E32u3 ltac:(exact (HBin _ Hing)) HTS Bnw3 Anw HnwIn2).
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq1 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq1 by (clear; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq1.
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of Hq1 with context [U ?Ex (SExt false 8 (SOff 49 0))] =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (clear; lia); rewrite OLD3 by (clear; lia); exact E49_2) ltac:(clear - Rfattr; cbn in Rfattr; lia)) in Hq1 end.
change (Z.of_N 8) with 8 in Hq1.
assert (Hft : Z.land fattr 1 = 0).
{ rewrite <- (land_mod2p fattr 1 8); [exact Hq1 | clear - Rfattr; lia | clear; lia | clear; lia]. }
clear Hq1. rename Hft into Hq1.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RBspanA AF_E; [awr_x Usp3 E32u3 ltac:(exact (HBin _ Hing)) HTS Bnw3 Anw HnwIn2 |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN4.
cbv beta in UN4. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (AGx : forall n, (n < 84)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; apply OLD3; exact Hn).
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) -> ~ (res <= a < res + N) -> ~ (sp0 - 224 - ESTACK <= a < sp0 - 224) ->
aview trasegs (w_H W2) (ms_mem msL) a = aview trasegs (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3. etransitivity; [exact (UN4 a Ha Hn1)|]. etransitivity; [exact (UN3 a Ha Hn1)|]. etransitivity; [exact (Hfr3 a Ha Hn2 Hn3)|]. exact (UN2 a Ha Hn1). }
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67_2).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23_2).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw2).
assert (X72 : ew EL 72 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 72) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i nw res 0 CX) end.
+
split; [exact HJ3|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trasegs); apply K23;
[clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia | rewrite HES; clear - Ha; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply K23;
[clear - Hii HZg; lia | clear - Hii HZg Dgn; lia | pose proof (HnewG (g + ii)) as D; clear - Hii D Hr4096; lia | rewrite HES; clear - Hii Hgceil Hceil Hslo HTS C1; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & _ & Hrc & _). change (req_size RAW_SIZE) with 48 in Hrc.
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; left; reflexivity)) as Dw. change (req_size RAW_SIZE) with 48 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096; lia | rewrite HES; clear - Hii Hrc Hceil Hslo HTS C1; lia].
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZf f ii Hfi Hii) as [Hb Hn].
assert (Hfb' : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N f Hfi).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact Hfb').
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & _ & Hfc & _). rewrite HFS in Hfc. change (req_size 40) with 40 in Hfc.
pose proof (SEPn _ _ ii Hfb ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(apply in_app_iff; left; exact Hfb')) as Dw. rewrite HFS in Dw. change (req_size 40) with 40 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096; lia | rewrite HES; clear - Hii Hfc Hceil Hslo HTS C1; lia]. }
split; [exact HOK|]. split.
{ unfold af_newblocks. rewrite Hq1. cbn [Z.eqb app]. rewrite Ebl.
eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. apply Permutation_sym. apply (Permutation_cons_append (af_cblocks img N fattr lpa nlp rest) (res, N)). }
split; [exact Hnew|]. unfold af_newblocks. rewrite Hq1. cbn [Z.eqb app].
intros b [<- | [<- | []]]; [exact (HnewX _ (or_introl eq_refl))|].
split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64;
apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear; lia)); exact R24.
+ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
+
unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locvD2 HR0 sp0 X32 X32u X38 X46 X67 X23 X23u Xsp Hcfp HZg Hgceil Hn4096 Hnceil C1.
+ exact HnoTab.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HnwIn2.
+
rewrite Hq1. cbn [Z.eqb]. apply (af_newcfg_kept _ _ nw lpal fattr fgen delay nlp tidx HNC2). intros a Ha Hn. apply (mbyte_of_aview trasegs). apply K23;
[clear - Ha Hn4096 Hnceil C1; lia | clear - Ha Hn Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN a) as D; clear - Ha D Hr4096; lia | rewrite HES; clear - Ha Hnceil Hceil Hslo HTS C1; lia].
+
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 8 8 (SOff 72 0) res HRn X23u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hr4096 HrCeil C1 HN1; lia) ltac:(cbn; lia)) as V8 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V8. exact V8.
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq1 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq1 by (clear; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq1.
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of Hq1 with context [U ?Ex (SExt false 8 (SOff 49 0))] =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (clear; lia); rewrite OLD3 by (clear; lia); exact E49_2) ltac:(clear - Rfattr; cbn in Rfattr; lia)) in Hq1 end.
change (Z.of_N 8) with 8 in Hq1.
assert (Hft : Z.land fattr 1 <> 0).
{ rewrite <- (land_mod2p fattr 1 8); [exact Hq1 | clear - Rfattr; lia | clear; lia | clear; lia]. }
clear Hq1. rename Hft into Hq1.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RBspanA AF_D3; [awr_x Usp3 E32u3 ltac:(exact (HBin _ Hing)) HTS Bnw3 Anw HnwIn2 |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?ew_havoc_old in Hrr by lia; rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2, ?Usp3, ?E32u3, ?Bnw3 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN4.
cbv beta in UN4. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (AGx : forall n, (n < 84)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; apply OLD3; exact Hn).
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 8 <= a < nw + 16)) -> ~ (res <= a < res + N) -> ~ (sp0 - 224 - ESTACK <= a < sp0 - 224) ->
aview trasegs (w_H W2) (ms_mem msL) a = aview trasegs (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3. etransitivity; [exact (UN4 a Ha Hn1)|]. etransitivity; [exact (UN3 a Ha Hn1)|]. etransitivity; [exact (Hfr3 a Ha Hn2 Hn3)|]. exact (UN2 a Ha Hn1). }
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67_2).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23_2).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw2).
assert (X72 : ew EL 72 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 72) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PD3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i nw res CX) end.
+
split; [exact HJ3|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview trasegs); apply K23;
[clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | clear - Ha HrCeil Hceil Hslo HTS C1; lia | rewrite HES; clear - Ha; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply K23;
[clear - Hii HZg; lia | clear - Hii HZg Dgn; lia | pose proof (HnewG (g + ii)) as D; clear - Hii D Hr4096; lia | rewrite HES; clear - Hii Hgceil Hceil Hslo HTS C1; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & _ & Hrc & _). change (req_size RAW_SIZE) with 48 in Hrc.
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; left; reflexivity)) as Dw. change (req_size RAW_SIZE) with 48 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096; lia | rewrite HES; clear - Hii Hrc Hceil Hslo HTS C1; lia].
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZf f ii Hfi Hii) as [Hb Hn].
assert (Hfb' : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N f Hfi).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact Hfb').
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & _ & Hfc & _). rewrite HFS in Hfc. change (req_size 40) with 40 in Hfc.
pose proof (SEPn _ _ ii Hfb ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(apply in_app_iff; left; exact Hfb')) as Dw. rewrite HFS in Dw. change (req_size 40) with 40 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096; lia | rewrite HES; clear - Hii Hfc Hceil Hslo HTS C1; lia]. }
split; [exact HOK|]. split.
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. apply Permutation_sym. apply (Permutation_cons_append (af_cblocks img N fattr lpa nlp rest) (res, N)). }
split; [exact Hnew|].
intros b [<- | [<- | []]]; [exact (HnewX _ (or_introl eq_refl))|].
split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ rewrite (blocks_bytes_bsum B ly2 S2), Ebl, bsum_app, <- (blocks_bytes_bsum B lyc Sc). cbn [bsum fold_right snd]. clear - HBB HN1. lia.
+ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo2 2%nat 2%bv eq_refl ltac:(clear; lia)); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo2 3%nat 3%bv eq_refl ltac:(clear; lia)); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo2 4%nat 4%bv eq_refl ltac:(clear; lia)); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64;
apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+
let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear; lia)); exact R24.
+ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
+
let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
+
pose proof (obj_at_nth trasegs _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. cbn [snd] in Rnlp.
let R := fresh "R" in rregD HS (10%bv : bv 5) R; rewrite R; rewrite denot_lit_U; unfold w64; f_equal.
apply (U_zext_small EL 16 _ _ (U_atom EL 52 _ ltac:(rewrite AGx by (clear; lia); exact E52_2) ltac:(clear - Rnlp; lia))); [clear - Rnlp; cbn in Rnlp |- *; lia | cbn; clear; lia].
+
unfold af_locsD3, af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locvD2 HR0 sp0 X32 X32u X38 X46 X67 X23 X23u Xsp Hcfp HZg Hgceil Hn4096 Hnceil C1.
+ exact Hq1.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HnwIn2.
+ exact HrIn.
+
apply (af_newcfg_kept _ _ nw lpal fattr fgen delay nlp tidx HNC2). intros a Ha Hn. apply (mbyte_of_aview trasegs). apply K23;
[clear - Ha Hn4096 Hnceil C1; lia | clear - Ha Hn Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN a) as D; clear - Ha D Hr4096; lia | rewrite HES; clear - Ha Hnceil Hceil Hslo HTS C1; lia].
+ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 8 8 (SOff 72 0) res HRn X23u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hr4096 HrCeil C1 HN1; lia) ltac:(cbn; lia)) as V8 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V8. exact V8.
Qed.
End l.
End h.
