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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI1h YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w YC0j YC0v YC0r YC0t YC0k YC0l YC0m YC0q YC0p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac awr_y_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn :=
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
| |- awr_ok _ (YQ0b.mkRegion (Some ?p) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
lazymatch type of Bfp with bv_unsigned _ = ?fpa =>
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ p fpa);
[ reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia;
lazymatch type of Bfp with bv_unsigned ?x = _ => let x' := eval cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in x in
first [exact Bfp | rewrite <- Bfp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; reflexivity] end
| let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YQ0b.r_wlo YQ0b.r_whi] in Ha; replace a with (fpa + (a - fpa)) by lia; apply Afp; [exact HfpIn | change (req_size 40) with 40; lia]
| ] end
end
| fail 1 "awr_y: no rule for the head region" ];
awr_y_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn
end.
Ltac awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
awr_y_rec Usp E32u Hing HTS Bnw Anw HnwIn Bfp Afp HfpIn.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsE2 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88)) 16 (SOff 46 0)) 17 (SOff 46 16))
10 (SOff 23 33)) 13 (shq 23 33).
Section h.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsE2_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more nw,
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 16 = w64 cfp -> getr regs1 17 = w64 (cfp + 16) ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= nw -> nw + 40 <= alloc_ceiling ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp cf more)) regsE2 regs1.
Proof.
intros regs regs1 g s1 cfp cf more nw (R2 & R3 & R4 & R18 & R8 & R22) R9s R16 R17 R23 R10 R13 Hg0 Hgc Hc0 Hcc Hn0 Hnc. unfold af_s1_at in R9s.
assert (E46x : ew (Ereg regs1 (af_extra regs g s1 cfp cf more)) 46 = Z_to_bv 64 cfp) by (change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp cf more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 23 38 33 nw SB E23 E38) by (unfold SB; lia); exact R13
| rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9s
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; exact R8]
| rewrite E38; exact R22
| change (ew E 46) with (ew (Ereg regs1 (af_extra regs g s1 cfp cf more)) 46); rewrite E46x; first [exact R16 | rewrite unsigned_lit_small by lia; exact R17]
| rewrite E23; rewrite unsigned_lit_small by lia; exact R10 ] ]
| ]); try (destruct Hr; fail).
Qed.
Definition e2_prev (fp : frame_st) : frame_st := set_fr_gen_disp fp (Z.land (fr_gen fp) 18446744073709551613) 8.
Lemma af_E2 : AF_E3_stmt B -> AF_E2_stmt B.
Proof.
intros PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw fn
CX MID Hk HR HR9 R25 R23 R16 R17 R10 R13 HL Hi Hfn Hnw Hih.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R22).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
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
assert (Hilt : (Z.to_nat i < length (cg_frames s1))%nat) by (rewrite Hlen1; clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
assert (Hfne : nth_error (cg_frames s1) (Z.to_nat i) = Some (Some fn)) by (rewrite <- Hfn; apply nth_error_nth'; exact Hilt).
assert (Hfin1 : In (Some fn) (cg_frames s1)) by (rewrite <- Hfn; apply nth_In; exact Hilt).
assert (HnwC : In (nw, FRAME_SIZE) (cgif_blocks g s1 N)) by (rewrite <- Hnw; exact (af_frame_in_blocks g s1 N fn Hfin1)).
assert (HnwIn : In (nw, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HnwC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (nw, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; rewrite <- Hnw; apply af_frames_blocks_ptr_in; exact Hfin1)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
assert (Hgd : exists gp dp, gp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_gen fp | None => 0 end /\
dp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_disp fp | None => 0 end /\
0 <= gp < 2 ^ 32 /\ 0 <= dp < 2 ^ 8).
{ destruct (nth (Z.to_nat i - 1) (cg_frames s1) None) as [fp|] eqn:Hop.
- assert (Hfpi : In (Some fp) (cg_frames s1)) by (rewrite <- Hop; apply nth_In; rewrite Hlen1; clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
pose proof (obj_at_nth trasegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rg]. cbn [snd] in Rg.
pose proof (obj_at_nth trasegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rd]. cbn [snd] in Rd.
exists (fr_gen fp), (fr_disp fp). split; [reflexivity|]. split; [reflexivity|]. clear - Rg Rd. cbn in Rg, Rd. lia.
- exists 0, 0. clear. repeat split; lia. }
destruct Hgd as (gp & dp & Egp & Edp & Hgpr & Hdpr).
pose proof (obj_at_nth trasegs _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx]. cbn [snd] in Rtidx.
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr.
pose proof (obj_at_nth trasegs _ _ _ _ 8 (33, 1%N) (fr_tidx fn) (proj2 (proj2 HT1) fn Hfin1) eq_refl eq_refl) as [Vft Rft]. cbn [fst snd] in Vft, Rft. rewrite Hnw in Vft.
destruct (af_reseedxE B TL LAWS AF_E2 regsE2 0 0 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 [] [fr_tidx fn; gp; dp]
CX (af_midx_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID) Rsp HL (Forall_nil _) ltac:(clear; lia) ltac:(clear; lia)
(regsE2_ok regs regs1 g s1 cfp _ _ nw HR HR9 R16 R17 R23 R10 R13 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp) ltac:(lia) Hnceil)
ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := Ereg regs1 _) in HS, SHOK.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0; fr_tidx fn; gp; dp]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34.
pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38.
pose proof (ES 46%nat ltac:(lia)) as E46. pose proof (ES 53%nat ltac:(lia)) as E53. pose proof (ES 67%nat ltac:(lia)) as E67. pose proof (ES 68%nat ltac:(lia)) as E68.
pose proof (ES 69%nat ltac:(lia)) as E69. pose proof (ES 70%nat ltac:(lia)) as E70. pose proof (ES 49%nat ltac:(lia)) as E49.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E37, E38, E46, E49, E53, E67, E68, E69, E70.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 69%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 70%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E70, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 23%nat) 0 40 33 34 [YQ0b.mkChunk 33 (CVal 1 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs _ _ nw 33 1 (SOff 68 0) (fr_tidx fn));
[ cbn [sv_denot]; rewrite E68, unsigned_lit_small, Z.add_0_r by (clear - Rft; cbn in Rft; lia); reflexivity
| clear - Rft; exact Rft | cbn; clear; lia | exact Vft ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok trasegs Bxa af_SH23 E (mrestrict (w_H Wc) memc)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ _ g s N _ cfp 32 HJ HAR0 HPerm HFO) as (_ & _ & HRA1).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trasegs B LAWS lyc Sc Wc memc mdc E Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trasegs (w_H Wc) memc E Bxa 46 cfp 32 cfp 0 32 HRA1).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trasegs B LAWS lyc Sc Wc memc mdc E Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR HnwIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HnwC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPa. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists nw, FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA.
{ awr_x Usp E32u Hing HTS Bnw Anw HnwIn. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq2 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq2 by (clear; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq2.
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr8]. cbn [snd] in Rfattr8.
lazymatch type of Hq2 with context [U ?Ex (SExt false 8 (SOff 49 0))] =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (clear; lia); exact E49) ltac:(clear - Rfattr8; cbn in Rfattr8; lia)) in Hq2 end.
change (Z.of_N 8) with 8 in Hq2.
assert (Hf2 : Z.land fattr 2 = 0).
{ rewrite <- (land_mod2p fattr 2 8); [exact Hq2 | clear - Rfattr8; lia | clear; lia | clear; lia]. }
clear Hq2.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_E3; [awr_x Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) ->
aview trasegs (w_H Wc) (ms_mem msL) a = aview trasegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 71)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_tidx fn)) by (rewrite AGx by lia; exact E68).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s1 i nw fn CX) end.
+
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trasegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- intros f Hfi. destruct (In_nth_error _ _ Hfi) as [j Hj].
destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
+ rewrite Hfne in Hj. injection Hj as <-.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (frame_vals fn) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trasegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rft]. cbn [fst]. rewrite Hnw.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SOff 68 0) (fr_tidx fn) HRn X23u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X68, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rft; exact Rft) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
{ intros j' Hj'. reflexivity. }
+ pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hj Hfne Hne) as Dff. rewrite Hnw in Dff.
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZf f ii Hfi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split; [exact HOK|]. split; [exact HPerm1 | exact Hnew].
+ exact Hk.
+ split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+ let R := fresh "R" in rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
+ let R := fresh "R" in rreg HS (22%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X38.
+   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
+   let R := fresh "R" in rreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
+ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
+ let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
+ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
+ unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1.
+ exact Hi.
+ exact Hfn.
+ exact Hnw.
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq2 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq2 by (clear; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq2.
pose proof (obj_at_nth trasegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr8]. cbn [snd] in Rfattr8.
lazymatch type of Hq2 with context [U ?Ex (SExt false 8 (SOff 49 0))] =>
rewrite (U_zext Ex 8 (SOff 49 0)), (U_atom Ex 49 fattr ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by (clear; lia); exact E49) ltac:(clear - Rfattr8; cbn in Rfattr8; lia)) in Hq2 end.
change (Z.of_N 8) with 8 in Hq2.
assert (Hf2 : Z.land fattr 2 <> 0).
{ rewrite <- (land_mod2p fattr 2 8); [exact Hq2 | clear - Rfattr8; lia | clear; lia | clear; lia]. }
clear Hq2.
destruct Hi as [-> | ->].
+
rreg HS (24%bv : bv 5) Q25.
pose proof (st_ok_pin_reg' trasegs _ _ _ (24%bv : bv 5) 1 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q25; rewrite ?ew_ewset_other by (clear; lia); rewrite (EEo 24%nat 24%bv eq_refl), R25; reflexivity) eq_refl) as HS3.
clear HS Q25. rename HS3 into HS. norm_ss HS.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_x Usp E32u Hing HTS Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
change (Z.to_nat 1) with 1%nat in Hfne, Hfn. change (Z.to_nat 1 - 1)%nat with 0%nat in Egp, Edp.
destruct (nth 0 (cg_frames s1) None) as [fp|] eqn:Hop.
*
cbn [frame_ptr] in E33. cbn in Egp, Edp. subst gp dp.
assert (Hfpe : nth_error (cg_frames s1) 0 = Some (Some fp)) by (rewrite <- Hop; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpi : In (Some fp) (cg_frames s1)) by (eapply nth_error_In; exact Hfpe).
assert (HfpC : In (fr_ptr fp, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N fp Hfpi).
assert (HfpIn : In (fr_ptr fp, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HfpC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE HAR HfpIn) as (Hp16 & Hp4096 & Hpceil & Hph_ia & HpP & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hfpe Hfne ltac:(clear; lia)) as Dpn. rewrite Hnw in Dpn.
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trasegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth trasegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 33) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear; lia); rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E69);
assert (Y70 : ew Ex 70 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E70) end.
assert (Vg2 : val_mem trasegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview trasegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem trasegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview trasegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 33%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 33%nat) 0 32 20 24 [YQ0b.mkChunk 20 (CVal 4 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs _ _ (fr_ptr fp) 20 4 (SOff 69 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 33%nat) 32 40 32 33 [YQ0b.mkChunk 32 (CVal 1 (SOff 70 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs _ _ (fr_ptr fp) 32 1 (SOff 70 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y70, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok trasegs Bxa (af_SH23 ++ [mkSHE 33 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc Wc _ _ _ Bxa 33 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite ?ew_ewset_other by (clear; lia). rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Y33.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (Afp : forall blc ii lyq ownq, In (fr_ptr fp, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (fr_ptr fp + ii)).
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HfpC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPa. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists (fr_ptr fp), FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_E3; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E33 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview trasegs (w_H Wc) (ms_mem msL) a = aview trasegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 71)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X33u : bv_unsigned (ew EL 33) = fr_ptr fp) by (rewrite AGx by lia; rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X69 : ew EL 69 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E69).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
set (gen' := Z.land (fr_gen fp) 18446744073709551613).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 69 0) (SLit (-3))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 69 (fr_gen fp) X69) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-3)) with 18446744073709551613. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vti : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 tidx).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YQ0b.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vgen : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 1 fn')) 0 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear; lia); exact Hfpe).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (upd_frame (upd_frame s1 1 fn') 0 fp') 1 nw fn' CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trasegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- rewrite (tcgif_vals_upd_frame (upd_frame s1 1 fn') 0 fp fp' Hfpe1 eq_refl), (tcgif_vals_upd_frame s1 1 fn fn' Hfne eq_refl).
apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii HZg; lia | clear - Hii HZg Dgn Dgp; lia].
- rewrite !cg_raw_upd_frame, !traw_vals_upd_frame.
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HfpIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D, D2. cbn [fst snd] in D, D2. change (req_size RAW_SIZE) with 48 in D, D2. rewrite HFS in D, D2. change (req_size 40) with 40 in D, D2.
apply UN; [exact Hb | clear - Hn D D2 Hii; lia].
- apply (tframes_at_upd2 _ _ s1 1 0 (Some fn) fn' (Some fp) fp' Hf Hfne Hfpe ltac:(clear; lia)).
+ change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trasegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dpn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw. exact Vti. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii Hp4096 Hpceil C1; lia | clear - Hii Hw1 Hw2 Hpceil Hceil Hslo HTS C1 Dpn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vdisp. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne1) as Dff. rewrite Hnw in Dff.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfpe Hne0) as Dff2.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trasegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Dff2 Hii; lia]. }
split.
{ apply (af_obj_ok_upd_frame s (upd_frame s1 1 fn') N 0 fp fp' ); [| exact Hfpe1 |].
- apply (af_obj_ok_upd_frame s s1 N 1 fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity].
- rewrite cg_attr_upd_frame. split; [| right; reflexivity].
cbn [fr_attr fp' set_fr_gen_disp]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fp Hfpi)). }
rewrite (cgif_blocks_upd_frame g (upd_frame s1 1 fn') N 0 fp fp' Hfpe1 eq_refl), (cgif_blocks_upd_frame g s1 N 1 fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
-- exact Hk.
-- split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-- let R := fresh "R" in rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
-- let R := fresh "R" in rreg HS (22%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X38.
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1.
-- left; reflexivity.
-- cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite (nth_upd_frame_other _ 0 1) by (clear; lia).
rewrite (nth_error_nth _ _ _ (nth_error_upd_frame_same s1 1 (Some fn) fn' Hfne)). reflexivity.
-- exact Hnw.
*
cbn [frame_ptr] in E33.
rreg HS (12%bv : bv 5) Q12.
pose proof (st_ok_pin_reg' trasegs _ _ _ (12%bv : bv 5) 0 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q12; rewrite ?ew_ewset_other by (clear; lia); exact E33) eq_refl) as HS3.
clear HS Q12. rename HS3 into HS. norm_ss HS.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_E3; [awr_x Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) ->
aview trasegs (w_H Wc) (ms_mem msL) a = aview trasegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 71)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
assert (Vti : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 tidx).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YQ0b.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (upd_frame s1 1 fn') 1 nw fn' CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trasegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- rewrite (tcgif_vals_upd_frame s1 1 fn fn' Hfne eq_refl).
apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- rewrite cg_raw_upd_frame, traw_vals_upd_frame.
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- apply (tframes_at_upd _ _ s1 1 (Some fn) fn' Hf Hfne).
+ change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trasegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw. exact Vti. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne) as Dff. rewrite Hnw in Dff.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trasegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s1 N 1 fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s1 N 1 fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
-- exact Hk.
-- split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-- let R := fresh "R" in rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
-- let R := fresh "R" in rreg HS (22%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X38.
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1.
-- left; reflexivity.
-- cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite (nth_error_nth _ _ _ (nth_error_upd_frame_same s1 1 (Some fn) fn' Hfne)). reflexivity.
-- exact Hnw.
+
rreg HS (24%bv : bv 5) Q25.
pose proof (st_ok_pin_reg' trasegs _ _ _ (24%bv : bv 5) 2 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q25; rewrite ?ew_ewset_other by (clear; lia); rewrite (EEo 24%nat 24%bv eq_refl), R25; reflexivity) eq_refl) as HS3.
clear HS Q25. rename HS3 into HS. norm_ss HS.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_x Usp E32u Hing HTS Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
change (Z.to_nat 2) with 2%nat in Hfne, Hfn. change (Z.to_nat 2 - 1)%nat with 1%nat in Egp, Edp.
destruct (nth 1 (cg_frames s1) None) as [fp|] eqn:Hop.
*
cbn [frame_ptr] in E34. cbn in Egp, Edp. subst gp dp.
assert (Hfpe : nth_error (cg_frames s1) 1 = Some (Some fp)) by (rewrite <- Hop; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpi : In (Some fp) (cg_frames s1)) by (eapply nth_error_In; exact Hfpe).
assert (HfpC : In (fr_ptr fp, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N fp Hfpi).
assert (HfpIn : In (fr_ptr fp, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HfpC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE HAR HfpIn) as (Hp16 & Hp4096 & Hpceil & Hph_ia & HpP & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hfpe Hfne ltac:(clear; lia)) as Dpn. rewrite Hnw in Dpn.
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trasegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth trasegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 34) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear; lia); rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E69);
assert (Y70 : ew Ex 70 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E70) end.
assert (Vg2 : val_mem trasegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview trasegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem trasegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview trasegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ 34%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 34%nat) 0 32 20 24 [YQ0b.mkChunk 20 (CVal 4 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs _ _ (fr_ptr fp) 20 4 (SOff 69 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trasegs Ex _ _ (YQ0b.mkRegion (Some 34%nat) 32 40 32 33 [YQ0b.mkChunk 32 (CVal 1 (SOff 70 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trasegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trasegs _ _ (fr_ptr fp) 32 1 (SOff 70 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y70, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok trasegs Bxa (af_SH23 ++ [mkSHE 34 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block trasegs B LAWS lyc Sc Wc _ _ _ Bxa 34 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite ?ew_ewset_other by (clear; lia). rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Y33.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (Afp : forall blc ii lyq ownq, In (fr_ptr fp, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPa g s N) (ablocks B ly S) blc lyq ownq (fr_ptr fp + ii)).
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HfpC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPa. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists (fr_ptr fp), FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_E3; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E34 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview trasegs (w_H Wc) (ms_mem msL) a = aview trasegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 71)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X33u : bv_unsigned (ew EL 34) = fr_ptr fp) by (rewrite AGx by lia; rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X69 : ew EL 69 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E69).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
set (gen' := Z.land (fr_gen fp) 18446744073709551613).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 69 0) (SLit (-3))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 69 (fr_gen fp) X69) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-3)) with 18446744073709551613. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vti : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 tidx).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YQ0b.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vgen : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 2 fn')) 1 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear; lia); exact Hfpe).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (upd_frame (upd_frame s1 2 fn') 1 fp') 2 nw fn' CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trasegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- rewrite (tcgif_vals_upd_frame (upd_frame s1 2 fn') 1 fp fp' Hfpe1 eq_refl), (tcgif_vals_upd_frame s1 2 fn fn' Hfne eq_refl).
apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii HZg; lia | clear - Hii HZg Dgn Dgp; lia].
- rewrite !cg_raw_upd_frame, !traw_vals_upd_frame.
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HfpIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D, D2. cbn [fst snd] in D, D2. change (req_size RAW_SIZE) with 48 in D, D2. rewrite HFS in D, D2. change (req_size 40) with 40 in D, D2.
apply UN; [exact Hb | clear - Hn D D2 Hii; lia].
- apply (tframes_at_upd2 _ _ s1 2 1 (Some fn) fn' (Some fp) fp' Hf Hfne Hfpe ltac:(clear; lia)).
+ change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trasegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dpn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw. exact Vti. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii Hp4096 Hpceil C1; lia | clear - Hii Hw1 Hw2 Hpceil Hceil Hslo HTS C1 Dpn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vdisp. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne1) as Dff. rewrite Hnw in Dff.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfpe Hne0) as Dff2.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trasegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Dff2 Hii; lia]. }
split.
{ apply (af_obj_ok_upd_frame s (upd_frame s1 2 fn') N 1 fp fp' ); [| exact Hfpe1 |].
- apply (af_obj_ok_upd_frame s s1 N 2 fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity].
- rewrite cg_attr_upd_frame. split; [| right; reflexivity].
cbn [fr_attr fp' set_fr_gen_disp]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fp Hfpi)). }
rewrite (cgif_blocks_upd_frame g (upd_frame s1 2 fn') N 1 fp fp' Hfpe1 eq_refl), (cgif_blocks_upd_frame g s1 N 2 fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
-- exact Hk.
-- split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-- let R := fresh "R" in rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
-- let R := fresh "R" in rreg HS (22%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X38.
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1.
-- right; reflexivity.
-- cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite (nth_upd_frame_other _ 1 2) by (clear; lia).
rewrite (nth_error_nth _ _ _ (nth_error_upd_frame_same s1 2 (Some fn) fn' Hfne)). reflexivity.
-- exact Hnw.
*
cbn [frame_ptr] in E34.
rreg HS (12%bv : bv 5) Q12.
pose proof (st_ok_pin_reg' trasegs _ _ _ (12%bv : bv 5) 0 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q12; rewrite ?ew_ewset_other by (clear; lia); exact E34) eq_refl) as HS3.
clear HS Q12. rename HS3 into HS. norm_ss HS.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA AF_E3; [awr_x Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw + 33 <= a < nw + 34)) ->
aview trasegs (w_H Wc) (ms_mem msL) a = aview trasegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 71)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
assert (Vti : val_mem trasegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 tidx).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YQ0b.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trasegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (upd_frame s1 2 fn') 2 nw fn' CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trasegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- rewrite (tcgif_vals_upd_frame s1 2 fn fn' Hfne eq_refl).
apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview trasegs). apply UN; [clear - Hii HZg; lia | clear - Hii HZg Dgn; lia].
- rewrite cg_raw_upd_frame, traw_vals_upd_frame.
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trasegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trasegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- apply (tframes_at_upd _ _ s1 2 (Some fn) fn' Hf Hfne).
+ change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trasegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trasegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw. exact Vti. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+ intros j x Hjx Hne ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne) as Dff. rewrite Hnw in Dff.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trasegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split.
{ apply (af_obj_ok_upd_frame s s1 N 2 fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity]. }
rewrite (cgif_blocks_upd_frame g s1 N 2 fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
-- exact Hk.
-- split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-- let R := fresh "R" in rreg HS (8%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X32u; reflexivity.
-- let R := fresh "R" in rreg HS (22%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X38.
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1.
-- right; reflexivity.
-- cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite (nth_error_nth _ _ _ (nth_error_upd_frame_same s1 2 (Some fn) fn' Hfne)). reflexivity.
-- exact Hnw.
Qed.
End h.
End c.
