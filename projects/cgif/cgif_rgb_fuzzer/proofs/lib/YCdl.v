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
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdn YCdp YCdg YCdh YCdm.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsE3 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff 32 88)) 21 (SOff 38 0)) 22 (shq 32 88)) 9 (SOff 46 0)) 10 (SOff 23 33)) 13 (shq 23 33).
Definition af_nwrE : YQ0b.region := YQ0b.mkRegion (Some 23%nat) 0 40 33 34 [].
Section h.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsE3_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more nw,
af_regs_atE B regs regs1 g -> getr regs1 9 = w64 cfp ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= nw -> nw + 40 <= alloc_ceiling ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp cf more)) regsE3 regs1.
Proof.
intros regs regs1 g s1 cfp cf more nw (R2 & R3 & R4 & R8 & R27 & R26) R9 R23 R10 R13 Hg0 Hgc Hc0 Hcc Hn0 Hnc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp cf more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [
lazymatch goal with |- getr _ _ = sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff 38 0)) =>
first [ rewrite R26 | rewrite R13 ]; symmetry; unfold w64;
first [ apply (denot_shx E 32 38 c g SB E32 E38) | apply (denot_shx E 23 38 c nw SB E23 E38) ]; unfold SB; lia end
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; rewrite unsigned_lit_small by lia; exact R8
| rewrite E38; exact R27
| rewrite E46; exact R9
| rewrite E23; rewrite unsigned_lit_small by lia; exact R10 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_E3 : AF_RET_stmt B -> AF_E3_stmt B.
Proof.
intros PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw fn
CX MID Hk HRE R9 R23 R11 R10 R13 HL Hi Hfn Hnw.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HRE as (Rsp & Rgp & Rtp & R8 & R27 & R26).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
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
destruct (frames_bounds trbsegs _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
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
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx]. cbn [snd] in Rtidx.
pose proof (obj_at_nth trbsegs _ _ _ _ 8 (33, 1%N) (fr_tidx fn) (proj2 (proj2 HT1) fn Hfin1) eq_refl eq_refl) as [Vft Rft]. cbn [fst snd] in Vft, Rft. rewrite Hnw in Vft.
destruct (af_reseedE B TL LAWS AF_E3 regsE3 88 92 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 [fr_tidx fn]
CX MID Rsp HL ltac:(clear; lia) ltac:(clear; lia)
(regsE3_ok regs regs1 g s1 cfp _ _ nw HRE R9 R23 R10 R13 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp) ltac:(lia) Hnceil)
ltac:(vm_compute; reflexivity)) as [HS SHOK].
set (E := Ereg regs1 _) in HS, SHOK.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [Z.land fattr 4; fr_tidx fn]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38.
pose proof (ES 46%nat ltac:(lia)) as E46. pose proof (ES 53%nat ltac:(lia)) as E53. pose proof (ES 67%nat ltac:(lia)) as E67. pose proof (ES 68%nat ltac:(lia)) as E68.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E37, E38, E46, E53, E67, E68.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
assert (B11 : bv_unsigned (ew E 11) = g + 8 * i) by (rewrite (EEo 11%nat 11%bv eq_refl), R11; apply unsigned_lit_small; clear - Hi HZg; lia).
pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr.
assert (Ha4 : 0 <= Z.land fattr 4 < 2 ^ 64) by (pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; clear - Xl; lia).
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 11%nat hfact3 HS
ltac:(clear HS; unfold afact_ok, hfact3; cbn [af_lo af_hi af_al2]; rewrite B11; change (2 ^ 3) with 8;
split; [clear - Hi Hg4096 Hgceil C1; lia|]; split; [apply mod8_of_16; exact Hg16 | clear; lia])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 23%nat) 0 40 33 34 [YQ0b.mkChunk 33 (CVal 1 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs _ _ nw 33 1 (SOff 68 0) (fr_tidx fn));
[ cbn [sv_denot]; rewrite E68, unsigned_lit_small, Z.add_0_r by (clear - Rft; cbn in Rft; lia); reflexivity
| clear - Rft; exact Rft | cbn; clear; lia | exact Vft ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok trbsegs Bxa af_SH23 E (mrestrict (w_H Wc) memc)).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ _ g s N _ cfp 32 HJ HAR0 HPerm HFO) as (_ & _ & HRA1).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block trbsegs B LAWS lyc Sc Wc memc mdc E Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range trbsegs (w_H Wc) memc E Bxa 46 cfp 32 cfp 0 32 HRA1).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block trbsegs B LAWS lyc Sc Wc memc mdc E Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR HnwIn).
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
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
{ awr_x Usp E32u Hing HTS Bnw Anw HnwIn. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq4 end.
rewrite branch_eq_U, U_lit in Hq4 by (clear; lia).
rewrite (U_atom _ 67 _ ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E67)) in Hq4 by (clear - Ha4; lia).
assert (Hf4 : Z.land fattr 4 = 0) by (clear - Hq4; apply Z.eqb_eq; exact Hq4). clear Hq4.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_RET; [awr_x Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 69)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg end.
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_tidx fn)) by (rewrite AGx by lia; exact E68).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 0) CX) end.
+
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hgceil Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
-
apply (obj_cgif_setcur _ _ g s1 0 Ho).
+ intros ii Hii Hnc. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii HZg; lia | clear - Hii Hnc HZg Dgn; lia].
+ lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SLit 0) 0 HRg X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbn; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V.
+ clear; lia.
- change (cg_raw (cl_set_cur s1 0)) with (cg_raw s1). change (traw_vals g (cl_set_cur s1 0)) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- change (cg_frames (cl_set_cur s1 0)) with (cg_frames s1). intros f Hfi.
destruct (In_nth_error _ _ Hfi) as [j Hj].
destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
+
rewrite Hfne in Hj. injection Hj as <-.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (frame_vals fn) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trbsegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rft]. cbn [fst]. rewrite Hnw.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SOff 68 0) (fr_tidx fn) HRn X23u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X68, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rft; exact Rft) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
{ intros j' Hj'. reflexivity. }
+
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hj Hfne Hne) as Dff. rewrite Hnw in Dff.
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZf f ii Hfi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split; [exact (af_obj_ok_set_cur s s1 N 0 HOK)|]. split; [exact HPerm1 | exact Hnew].
+ exact Hk.
+
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| rewrite X32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq4 end.
rewrite branch_eq_U, U_lit in Hq4 by (clear; lia).
rewrite (U_atom _ 67 _ ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E67)) in Hq4 by (clear - Ha4; lia).
assert (Hf4 : Z.land fattr 4 <> 0) by (clear - Hq4; apply Z.eqb_neq; exact Hq4). clear Hq4.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_RET; [awr_x Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 69)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg end.
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0) CX) end.
+
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hgceil Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
-
rewrite tcgif_vals_set_cur_ls, (tcgif_vals_upd_frame s1 (Z.to_nat i) fn fn' Hfne eq_refl), <- tcgif_vals_set_cur_ls.
apply (obj_cgif_setcur _ _ g s1 0 Ho).
+ intros ii Hii Hnc. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii HZg; lia | clear - Hii Hnc HZg Dgn; lia].
+ lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SLit 0) 0 HRg X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbn; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V.
+ clear; lia.
- change (cg_raw (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (cg_raw s1). change (traw_vals g (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- change (cg_frames (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (cg_frames (upd_frame s1 (Z.to_nat i) fn')).
apply (tframes_at_upd _ _ s1 (Z.to_nat i) (Some fn) fn' Hf Hfne).
+
change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview trbsegs). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw.
lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YQ0b.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
{ intros j' Hj'. rewrite YI1h.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+
intros j x Hjx Hne ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne) as Dff. rewrite Hnw in Dff.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split.
{ apply af_obj_ok_set_cur. apply (af_obj_ok_upd_frame s s1 N (Z.to_nat i) fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity]. }
change (cgif_blocks g (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0) N) with (cgif_blocks g (upd_frame s1 (Z.to_nat i) fn') N).
rewrite (cgif_blocks_upd_frame g s1 N (Z.to_nat i) fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
+ exact Hk.
+
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| rewrite X32u; reflexivity
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
Qed.
End h.
End d.
