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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdn YCdp YCdg YCdh YCdi YCdt YCdm YCdl YCdk.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Lemma val_mem_byte1 : forall H mem a v, aview trbsegs H mem a = Some v -> val_mem trbsegs (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv. destruct (aview_byte trbsegs H mem a v Hv) as (b & Hb & -> & Hr).
intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YP0g.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia).
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsE1 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 21 (SOff 38 0)) 22 (shq 32 88))
20 (SOff 32 40)) 26 (shq 32 40)) 9 (SOff 46 0)) 17 (SOff 32 92)) 19 (SOff 46 16)) 25 (shq 46 16).
Section e.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsE1_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp lpal img fattr fgen delay nlp tidx more,
af_regs_at B regs regs1 g -> getr regs1 9 = w64 cfp -> getr regs1 17 = w64 (g + 92) -> getr regs1 19 = w64 (cfp + 16) -> getr regs1 25 = w64 (SB + (cfp + 16) / 8) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= fattr < 2 ^ 32 ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)) regsE1 regs1.
Proof.
intros regs regs1 g s1 cfp lpal img fattr fgen delay nlp tidx more (R2 & R3 & R4 & R18 & R8 & R27 & R26 & R19 & R25) R9 R17 RC16 RSC16 Hg0 Hgc Hc0 Hcc Hfattr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
assert (E49 : ew E 49 = Z_to_bv 64 fattr) by (subst E; change 49%nat with (32 + 17)%nat; rewrite (ew_Ereg_extra regs1 _ 17); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [
lazymatch goal with |- getr _ _ = sv_denot _ (SAlu ALU_ADD (SAlu ALU_SRL (SOff ?n ?c) (SLit 3)) (SOff 38 0)) =>
first [ rewrite R26 | rewrite R25 | rewrite RSC16 ]; symmetry; unfold w64;
first [ apply (denot_shx E 32 38 c g SB E32 E38) | apply (denot_shx E 46 38 c cfp SB E46 E38) ]; unfold SB; lia end
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; first [exact R8 | exact R19 | exact R17]]
| rewrite E38; exact R27
| rewrite E46; first [exact R9 | rewrite unsigned_lit_small by lia; exact RC16] ] ]
| ]); try (destruct Hr; fail).
Qed.

Lemma af_E1 : AF_E2_stmt B -> AF_E_stmt B.
Proof.
intros PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw nimg npal
CX MID Hk HR R9 R24i R23 R17 RC16 RSC16 HL HnoTab Hi Hnone Hs1 HnwIn HNC HV8.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R27 & R26 & R19 & R25s).
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
pose proof HWF1 as (_ & HWge & HHge & HNWH & HNmax & _).
assert (HN1 : 1 <= N <= 100000000) by (clear - HWge HHge HNWH HNmax; nia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_img _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (SEPw : forall y, In y (cgif_blocks g s1 N) -> zdisjoint (block_rng y) (block_rng (nw, FRAME_SIZE))).
{ intros y Hy. apply (sep_app B LAWS lyc Sc Wc memc mdc y (nw, FRAME_SIZE) (cgif_blocks g s1 N) (af_newblocks N fattr nlp nw nimg npal ++ af_cblocks img N fattr lpa nlp rest) HAR HPerm1 Hy).
apply in_app_iff. left. left. reflexivity. }
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof (SEPw (g, CGIF_SIZE) ltac:(left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
assert (Dgc : g + 96 <= cfp \/ cfp + 32 <= g).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ g CGIF_SIZE cid pos HAR Hing Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D Hflo Hfhi. lia. }
assert (Dfn : forall f ii, In (Some f) (cg_frames s1) -> 0 <= ii < 40 -> ~ (nw <= fr_ptr f + ii < nw + 40)).
{ intros f ii Hf Hii. pose proof (SEPw (fr_ptr f, FRAME_SIZE) ltac:(apply af_frame_in_blocks; exact Hf)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hii. lia. }
assert (Hgd : exists gp dp, gp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_gen fp | None => 0 end /\
dp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_disp fp | None => 0 end /\
0 <= gp < 2 ^ 32 /\ 0 <= dp < 2 ^ 8).
{ destruct (nth (Z.to_nat i - 1) (cg_frames s1) None) as [fp|] eqn:Hop.
- assert (Hfpi : In (Some fp) (cg_frames s1)) by (rewrite <- Hop; apply nth_In; rewrite Hlen1; clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rg]. cbn [snd] in Rg.
pose proof (obj_at_nth trbsegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rd]. cbn [snd] in Rd.
exists (fr_gen fp), (fr_disp fp). split; [reflexivity|]. split; [reflexivity|]. clear - Rg Rd. cbn in Rg, Rd. lia.
- exists 0, 0. clear. repeat split; lia. }
destruct Hgd as (gp & dp & Egp & Edp & Hgpr & Hdpr).
destruct (aview trbsegs (w_H Wc) memc (nw + 28)) as [v28|] eqn:Hv28; [| exfalso; exact (aview_some_of_apresent trbsegs _ _ _ (proj1 (HnP (nw + 28) ltac:(clear; lia))) Hv28)].
destruct (aview_byte trbsegs _ _ _ _ Hv28) as (b28 & _ & _ & Rv28).
pose proof (val_mem_byte1 _ _ _ _ Hv28) as Vv28.
set (ctx := if Z.land fattr 6 =? 0 then v28 else tidx).
pose proof (obj_at_nth trbsegs _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx]. cbn [snd] in Rtidx.
assert (Rctx : 0 <= ctx < 2 ^ 8) by (subst ctx; destruct (Z.land fattr 6 =? 0); [clear - Rv28; lia | clear - Rtidx; cbn in Rtidx; lia]).
assert (Vctx : val_mem trbsegs (mrestrict (w_H Wc) memc) (nw + 28) 1 ctx).
{ subst ctx. destruct (Z.land fattr 6 =? 0) eqn:Hb; [exact Vv28|]. apply (proj2 (proj2 (proj2 (proj2 (proj2 HNC))))). clear - Hb. intros H6. rewrite H6 in Hb. discriminate. }
pose proof HNC as (Vlp & Vfa & Vfg & Vde & Vnl & _).
pose proof (obj_at_nth trbsegs _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth trbsegs _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth trbsegs _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth trbsegs _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp].
cbn [snd] in Rlpal, Rfattr, Rfgen, Rdelay, Rnlp.
assert (Ha4 : 0 <= Z.land fattr 4 < 2 ^ 64) by (pose proof (land_small_r fattr 4 ltac:(clear - Rfattr; cbn in Rfattr; lia) ltac:(clear; lia)) as Xl; cbn in Xl; clear - Xl; lia).
pose proof (obj_at_nth trbsegs _ _ _ _ 5 (40, 4%N) (cg_attr s1) (proj1 HT1) eq_refl eq_refl) as [_ Rattr]. cbn [snd] in Rattr.
assert (HniIn : In (nimg, N) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. right. apply in_app_iff. left. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ nimg N HAR HniIn) as (_ & Hm4096 & Hmceil & _).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0) as [He | Hne]; [exfalso; clear - HN1 He; lia | reflexivity]). rewrite HrqN in Hmceil.
assert (HlpE : 0 <= (if Z.land fattr 1 =? 0 then lpal else npal) < 2 ^ 64).
{ destruct (Z.land fattr 1 =? 0) eqn:Hb; [clear - Rlpal; cbn in Rlpal; lia|].
assert (HnpIn : In (npal, 3 * nlp) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. right. apply in_app_iff. left. unfold af_newblocks. rewrite Hb. right. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ npal (3 * nlp) HAR HnpIn) as (_ & Hq4096 & Hqceil & _). pose proof (req_size_pos (3 * nlp) ltac:(clear - Rnlp; cbn in Rnlp; lia)). clear - Hq4096 Hqceil C1 H; lia. }
destruct Hi as [-> | ->].
+
change (Z.to_nat 1) with 1%nat in Hnone. change (Z.to_nat 1 - 1)%nat with 0%nat in Egp, Edp.
destruct (af_reseedD B TL LAWS AF_E regsE1 8 16 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) [gp; dp] nw
CX MID Rsp R23 HnwIn HL ltac:(apply Forall_nil) ltac:(clear; lia) ltac:(clear; lia)
(regsE1_ok regs regs1 g s1 cfp lpal img fattr fgen delay nlp tidx _ HR R9 R17 RC16 RSC16 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp) ltac:(clear - Rfattr; cbn in Rfattr; lia))
ltac:(vm_compute; reflexivity)) as [HS SHOK].
rewrite app_nil_r in HS.
set (E := Ereg regs1 _) in HS, SHOK. norm_ss HS.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [Z.land fattr 4; gp; dp]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34. pose proof (ES 35%nat ltac:(lia)) as E35.
pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38. pose proof (ES 40%nat ltac:(lia)) as E40.
pose proof (ES 46%nat ltac:(lia)) as E46. pose proof (ES 49%nat ltac:(lia)) as E49. pose proof (ES 67%nat ltac:(lia)) as E67. pose proof (ES 68%nat ltac:(lia)) as E68. pose proof (ES 69%nat ltac:(lia)) as E69.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E35, E37, E38, E40, E46, E49, E67, E68, E69.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_submem trbsegs Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part trbsegs Ex _ (Some 32%nat) 0 96 8 16 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 32%nat) 0 88 8 16 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part trbsegs Ex _ (Some 32%nat) 0 96 8 16 cs 0 88 8 16 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
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
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
rreg HS (24%bv : bv 5) Q24.
pose proof (st_ok_pin_reg' trbsegs _ _ _ (24%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Q24; rewrite ?ew_ewset_other by (clear; lia); rewrite (EEo 24%nat 24%bv eq_refl), R24i; reflexivity) eq_refl) as HS3.
clear HS Q24. rename HS3 into HS. norm_ss HS.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96)) HAR
ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hstk ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
assert (Hrnw : forall ii, 0 <= ii < 48 -> ~ (nw + 32 <= cg_raw s1 + ii < nw + 34)).
{ intros ii Hii. pose proof (SEPw (cg_raw s1, RAW_SIZE) ltac:(right; left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hii. lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 = 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_E2; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 70)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 4 0).
assert (Vslot : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 4).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 4) 4 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte trbsegs (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at trbsegs (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 1 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
set (s2 := set_ihead (upd_frame s1 1 fnew) 1).
assert (Hfr2 : cg_frames s2 = list_set (cg_frames s1) 1 (Some fnew)) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| left; reflexivity]. apply (cgif_wf_ins_frame s1 N 1 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; left; reflexivity]. }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead.
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 1 fnew Hfne1). }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite tcgif_vals_set_ihead_ls, (tcgif_vals_ins_frame s1 1 fnew ltac:(clear; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (tcgif_vals s1) (list_set (list_set (tcgif_vals s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals g s2) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 1 (Some fnew)) with (cg_frames (upd_frame s1 1 fnew)).
apply (tframes_at_upd _ _ s1 1 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
-- clear - Hk HEVA HEVF; lia.
--
split; [|split; [|split; [|split; [|split]]]]; regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
--   let R := fresh "R" in rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X32.
--   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
--   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
--   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
--   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; rewrite X32u; f_equal; clear; lia.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
--
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi 56 8 (SOff 67 0) (Z.land fattr 4) HR0 Xsp ltac:(cbn; tauto));
[cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ha4 | cbn; clear; lia] end.
-- left; reflexivity.
-- rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
-- reflexivity.
-- reflexivity.
*
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 <> 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (nth 0 (cg_frames s1) None) as [fp|] eqn:Hop.
--
cbn [frame_ptr] in E33. cbn in Egp, Edp. subst gp dp.
assert (Hfpe : nth_error (cg_frames s1) 0 = Some (Some fp)) by (rewrite <- Hop; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpi : In (Some fp) (cg_frames s1)) by (eapply nth_error_In; exact Hfpe).
assert (HfpC : In (fr_ptr fp, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N fp Hfpi).
assert (HfpIn : In (fr_ptr fp, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HfpC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE HAR HfpIn) as (Hp16 & Hp4096 & Hpceil & Hph_ia & HpP & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
assert (Dpn : fr_ptr fp + 40 <= nw \/ nw + 40 <= fr_ptr fp).
{ pose proof (SEPw (fr_ptr fp, FRAME_SIZE) HfpC) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth trbsegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 33) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear; lia); rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E69) end.
assert (Vg2 : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 33%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 33%nat) 0 32 20 24 [YQ0b.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 33%nat) 32 40 32 33 [YQ0b.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok trbsegs Bxa (af_SH23 ++ [mkSHE 33 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS lyc Sc Wc _ _ _ Bxa 33 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
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
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_E2; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E33 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 70)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0 end.
assert (X33u : bv_unsigned (ew EL 33) = fr_ptr fp) by (rewrite AGx by lia; rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E68).
set (gen' := Z.land (fr_gen fp) 18446744073709551612).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 68 0) (SLit (-4))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 68 (fr_gen fp) X68) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-4)) with 18446744073709551612. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vgen : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vpd : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte trbsegs (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn Dpn; lia]. }
assert (Hfnew : obj_at trbsegs (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 1 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 1 fnew)) 0 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear; lia); exact Hfpe).
set (s2 := set_ihead (upd_frame (upd_frame s1 1 fnew) 0 fp') 1).
assert (Hfr2 : cg_frames s2 = list_set (list_set (cg_frames s1) 1 (Some fnew)) 0 (Some fp')) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| left; reflexivity]. apply (cgif_wf_upd_frame _ N 0 fp fp'); [| exact Hfpe1 |].
- apply (cgif_wf_ins_frame s1 N 1 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; right; reflexivity].
- rewrite cg_attr_upd_frame. split; [| right; reflexivity].
cbn [fr_attr fp' set_fr_gen_disp]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fp Hfpi)). }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead, (cgif_blocks_upd_frame g (upd_frame s1 1 fnew) N 0 fp fp' Hfpe1 eq_refl).
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 1 fnew Hfne1). }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite tcgif_vals_set_ihead_ls, (tcgif_vals_upd_frame (upd_frame s1 1 fnew) 0 fp fp' Hfpe1 eq_refl), (tcgif_vals_ins_frame s1 1 fnew ltac:(clear; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (tcgif_vals s1) (list_set (list_set (tcgif_vals s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals g s2) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D.
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; right; left; reflexivity) HfpIn
ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D2. cbn [fst snd] in D2. change (req_size RAW_SIZE) with 48 in D2. rewrite HFS in D2. change (req_size 40) with 40 in D2.
apply UN; [exact Hb | clear - Hn Hii D D2; lia].
- rewrite Hfr2. change (list_set (list_set (cg_frames s1) 1 (Some fnew)) 0 (Some fp')) with (cg_frames (upd_frame (upd_frame s1 1 fnew) 0 fp')).
apply (tframes_at_upd2 _ _ s1 1 0 None fnew (Some fp) fp' Hf Hfne1 Hfpe ltac:(clear; lia)); [exact Hfnew | |].
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
pose proof (HZf fp ii Hfpi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Hii Hw1 Hw2 Dpn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vpd. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hlen1 Hjx Hfpe Hne0) as Dff2.
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Dff2 Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++
split; [|split; [|split; [|split; [|split]]]]; regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
++   let R := fresh "R" in rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X32.
++   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
++   let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; rewrite X32u; f_equal; clear; lia.
++ let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi 56 8 (SOff 67 0) (Z.land fattr 4) HR0 Xsp ltac:(cbn; tauto));
[cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ha4 | cbn; clear; lia] end.
++ left; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite YI1h.nth_list_set_other by (clear; lia). rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
--
cbn [frame_ptr] in E33.
rreg HS (14%bv : bv 5) Q14.
pose proof (st_ok_pin_reg' trbsegs _ _ _ (14%bv : bv 5) 0 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q14; rewrite ?ew_ewset_other by (clear; lia); exact E33) eq_refl) as HS3.
clear HS Q14. rename HS3 into HS. norm_ss HS.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_E2; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 70)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte trbsegs (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at trbsegs (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 1 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
set (s2 := set_ihead (upd_frame s1 1 fnew) 1).
assert (Hfr2 : cg_frames s2 = list_set (cg_frames s1) 1 (Some fnew)) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| left; reflexivity]. apply (cgif_wf_ins_frame s1 N 1 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; right; reflexivity]. }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead.
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 1 fnew Hfne1). }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite tcgif_vals_set_ihead_ls, (tcgif_vals_ins_frame s1 1 fnew ltac:(clear; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (tcgif_vals s1) (list_set (list_set (tcgif_vals s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals g s2) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 1 (Some fnew)) with (cg_frames (upd_frame s1 1 fnew)).
apply (tframes_at_upd _ _ s1 1 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++
split; [|split; [|split; [|split; [|split]]]]; regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
++   let R := fresh "R" in rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X32.
++   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
++   let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; rewrite X32u; f_equal; clear; lia.
++ let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi 56 8 (SOff 67 0) (Z.land fattr 4) HR0 Xsp ltac:(cbn; tauto));
[cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ha4 | cbn; clear; lia] end.
++ left; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
+
change (Z.to_nat 2) with 2%nat in Hnone. change (Z.to_nat 2 - 1)%nat with 1%nat in Egp, Edp.
destruct (af_reseedD B TL LAWS AF_E regsE1 16 24 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) [gp; dp] nw
CX MID Rsp R23 HnwIn HL ltac:(apply Forall_nil) ltac:(clear; lia) ltac:(clear; lia)
(regsE1_ok regs regs1 g s1 cfp lpal img fattr fgen delay nlp tidx _ HR R9 R17 RC16 RSC16 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp) ltac:(clear - Rfattr; cbn in Rfattr; lia))
ltac:(vm_compute; reflexivity)) as [HS SHOK].
rewrite app_nil_r in HS.
set (E := Ereg regs1 _) in HS, SHOK. norm_ss HS.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [Z.land fattr 4; gp; dp]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 33%nat ltac:(lia)) as E33. pose proof (ES 34%nat ltac:(lia)) as E34. pose proof (ES 35%nat ltac:(lia)) as E35.
pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38. pose proof (ES 40%nat ltac:(lia)) as E40.
pose proof (ES 46%nat ltac:(lia)) as E46. pose proof (ES 49%nat ltac:(lia)) as E49. pose proof (ES 67%nat ltac:(lia)) as E67. pose proof (ES 68%nat ltac:(lia)) as E68. pose proof (ES 69%nat ltac:(lia)) as E69.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E35, E37, E38, E40, E46, E49, E67, E68, E69.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_submem trbsegs Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part trbsegs Ex _ (Some 32%nat) 0 96 16 24 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
lazymatch type of HRg with region_ok _ ?Ex _ (YQ0b.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok _ _ _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 32%nat) 0 88 16 24 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part trbsegs Ex _ (Some 32%nat) 0 96 16 24 cs 0 88 16 24 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end end.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
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
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
rreg HS (24%bv : bv 5) Q24.
pose proof (st_ok_pin_reg' trbsegs _ _ _ (24%bv : bv 5) 2 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Q24; rewrite ?ew_ewset_other by (clear; lia); rewrite (EEo 24%nat 24%bv eq_refl), R24i; reflexivity) eq_refl) as HS3.
clear HS Q24. rename HS3 into HS. norm_ss HS.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96)) HAR
ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hstk ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
assert (Hrnw : forall ii, 0 <= ii < 48 -> ~ (nw + 32 <= cg_raw s1 + ii < nw + 34)).
{ intros ii Hii. pose proof (SEPw (cg_raw s1, RAW_SIZE) ltac:(right; left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hii. lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 = 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_E2; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 70)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 4 0).
assert (Vslot : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 16) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 16 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 2).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 2) 2 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 4).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 4) 4 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte trbsegs (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at trbsegs (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 2 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
set (s2 := set_ihead (upd_frame s1 2 fnew) 2).
assert (Hfr2 : cg_frames s2 = list_set (cg_frames s1) 2 (Some fnew)) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| right; split; [reflexivity | unfold upd_frame; cbn [cg_frames set_frames]; rewrite YI1h.nth_list_set_other by (clear; lia); exact (Hs1 eq_refl)]]. apply (cgif_wf_ins_frame s1 N 2 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; left; reflexivity]. }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead.
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 2 fnew Hfne1). }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 2 nw fnew CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite tcgif_vals_set_ihead_ls, (tcgif_vals_ins_frame s1 2 fnew ltac:(clear; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (tcgif_vals s1) (list_set (list_set (tcgif_vals s1) 2 nw) 16 2) [2; 16]%nat [(16, 24); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals g s2) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 2 (Some fnew)) with (cg_frames (upd_frame s1 2 fnew)).
apply (tframes_at_upd _ _ s1 2 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
-- clear - Hk HEVA HEVF; lia.
--
split; [|split; [|split; [|split; [|split]]]]; regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
--   let R := fresh "R" in rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X32.
--   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
--   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
-- let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
--   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
--   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
--   let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; rewrite X32u; f_equal; clear; lia.
-- let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
--
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi 56 8 (SOff 67 0) (Z.land fattr 4) HR0 Xsp ltac:(cbn; tauto));
[cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ha4 | cbn; clear; lia] end.
-- right; reflexivity.
-- rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
-- reflexivity.
-- reflexivity.
*
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 <> 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
all: try (awr_y Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (nth 1 (cg_frames s1) None) as [fp|] eqn:Hop.
--
cbn [frame_ptr] in E34. cbn in Egp, Edp. subst gp dp.
assert (Hfpe : nth_error (cg_frames s1) 1 = Some (Some fp)) by (rewrite <- Hop; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpi : In (Some fp) (cg_frames s1)) by (eapply nth_error_In; exact Hfpe).
assert (HfpC : In (fr_ptr fp, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N fp Hfpi).
assert (HfpIn : In (fr_ptr fp, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HfpC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE HAR HfpIn) as (Hp16 & Hp4096 & Hpceil & Hph_ia & HpP & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
assert (Dpn : fr_ptr fp + 40 <= nw \/ nw + 40 <= fr_ptr fp).
{ pose proof (SEPw (fr_ptr fp, FRAME_SIZE) HfpC) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth trbsegs _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 34) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear; lia); rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear; lia); exact E69) end.
assert (Vg2 : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview trbsegs).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ 34%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 34%nat) 0 32 20 24 [YQ0b.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
pose proof (ast_ok_add_region trbsegs Ex _ _ (YQ0b.mkRegion (Some 34%nat) 32 40 32 33 [YQ0b.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable trbsegs); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); unfold A_GOT_shadow, A_shadow_glob;
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok trbsegs Bxa (af_SH23 ++ [mkSHE 34 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS lyc Sc Wc _ _ _ Bxa 34 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
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
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_E2; [awr_y Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E34 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview trbsegs (w_H Wc) (ms_mem msL) a = aview trbsegs (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 70)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_region) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_region) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_region) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0 end.
assert (X33u : bv_unsigned (ew EL 34) = fr_ptr fp) by (rewrite AGx by lia; rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E68).
set (gen' := Z.land (fr_gen fp) 18446744073709551612).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 68 0) (SLit (-4))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 68 (fr_gen fp) X68) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-4)) with 18446744073709551612. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vgen : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vpd : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X49 : ew EL 49 = Z_to_bv 64 fattr) by (rewrite AGx by lia; exact E49).
assert (X67 : ew EL 67 = Z_to_bv 64 (Z.land fattr 4)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 16) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 16 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 2).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 2) 2 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte trbsegs (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte trbsegs (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn Dpn; lia]. }
assert (Hfnew : obj_at trbsegs (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 2 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 2 fnew)) 1 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear; lia); exact Hfpe).
set (s2 := set_ihead (upd_frame (upd_frame s1 2 fnew) 1 fp') 2).
assert (Hfr2 : cg_frames s2 = list_set (list_set (cg_frames s1) 2 (Some fnew)) 1 (Some fp')) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| right; split; [reflexivity | unfold upd_frame at 1; cbn [cg_frames set_frames]; rewrite nth_list_set_same by (unfold upd_frame; cbn [cg_frames set_frames]; rewrite YI1h.length_list_set, Hlen1; clear; lia); discriminate]]. apply (cgif_wf_upd_frame _ N 1 fp fp'); [| exact Hfpe1 |].
- apply (cgif_wf_ins_frame s1 N 2 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; right; reflexivity].
- rewrite cg_attr_upd_frame. split; [| right; reflexivity].
cbn [fr_attr fp' set_fr_gen_disp]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fp Hfpi)). }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead, (cgif_blocks_upd_frame g (upd_frame s1 2 fnew) N 1 fp fp' Hfpe1 eq_refl).
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 2 fnew Hfne1). }
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 2 nw fnew CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite tcgif_vals_set_ihead_ls, (tcgif_vals_upd_frame (upd_frame s1 2 fnew) 1 fp fp' Hfpe1 eq_refl), (tcgif_vals_ins_frame s1 2 fnew ltac:(clear; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (tcgif_vals s1) (list_set (list_set (tcgif_vals s1) 2 nw) 16 2) [2; 16]%nat [(16, 24); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals g s2) with (traw_vals g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview trbsegs). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D.
pose proof (sep_blocks trbsegs B LAWS _ _ _ _ _ _ _ _ _ HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; right; left; reflexivity) HfpIn
ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D2. cbn [fst snd] in D2. change (req_size RAW_SIZE) with 48 in D2. rewrite HFS in D2. change (req_size 40) with 40 in D2.
apply UN; [exact Hb | clear - Hn Hii D D2; lia].
- rewrite Hfr2. change (list_set (list_set (cg_frames s1) 2 (Some fnew)) 1 (Some fp')) with (cg_frames (upd_frame (upd_frame s1 2 fnew) 1 fp')).
apply (tframes_at_upd2 _ _ s1 2 1 None fnew (Some fp) fp' Hf Hfne1 Hfpe ltac:(clear; lia)); [exact Hfnew | |].
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd trbsegs (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview trbsegs).
pose proof (HZf fp ii Hfpi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Hii Hw1 Hw2 Dpn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vpd. }
{ intros j' Hj'. rewrite !YI1h.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hlen1 Hjx Hfpe Hne0) as Dff2.
apply (mbyte_of_aview trbsegs). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Dff2 Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++
split; [|split; [|split; [|split; [|split]]]]; regvE HS AGx EEo X32 X32u X38 Rsp Rgp Rtp HZg Hgceil C1.
++   let R := fresh "R" in rreg HS (18%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X32.
++   let R := fresh "R" in rreg HS (9%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in rreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in rreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in rreg HS (19%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++   let R := fresh "R" in rreg HS (25%bv : bv 5) R; rewrite R; unfold w64; apply (shq_word EL 46 38 16 _ SB X46 X38); clear - Hcfp C1; unfold SB; lia.
++   let R := fresh "R" in rreg HS (11%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; unfold w64; rewrite X32u; f_equal; clear; lia.
++ let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++
lazymatch type of HR0 with region_ok _ ?Ex _ (YQ0b.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
apply (field_of_region Ex _ 2 (sp0 - 224) cs lo hi wlo whi 56 8 (SOff 67 0) (Z.land fattr 4) HR0 Xsp ltac:(cbn; tauto));
[cbn [sv_denot]; rewrite X67, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Ha4 | cbn; clear; lia] end.
++ right; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite YI1h.nth_list_set_other by (clear; lia). rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
--
exfalso. exact (Hs1 eq_refl eq_refl).
Qed.
End e.
End d.
