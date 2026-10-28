(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgz ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgl ACgb ACgc ACgd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma val_mem_byte1 : forall H mem a v, aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv. destruct (aview_byte SEGS H mem a v Hv) as (b & Hb & -> & Hr).
intros j Hj. destruct j; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. cbn [Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia).
rewrite (Z.mod_small (bv_unsigned b) 256) by (clear - Hr; lia). reflexivity.
Qed.
End e.
End d.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition regsE1 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88).
Section p.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma regsE1_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> 0 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))) regsE1 regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R18 & R8 & R22) R9s Hg0 Hgc. unfold af_s1_at in R9s.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9s
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; exact R8]
| rewrite E38; exact R22 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma LAY_Frame_split' : LAY_Frame = LAY_FrameConfig ++ [(32, 1%N); (33, 1%N)].
Proof. reflexivity. Qed.
Lemma af_E1X : AF_E2_stmtX K MT XN B -> AF_E_stmtX K MT XN B.
Proof.
intros PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw nimg npal GPAL IMG LPAL gs gsF gs1
CX MID Hk HR HR9 R25 R23 HL HnoTab Hi Hnone Hs1 HnwIn HNC HV8 XE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp & R18 & R8 & R22).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
assert (HEVF : EV_FLUSH = 35) by reflexivity. assert (HEVA : EV_ADDFRAME = 12 + EV_FLUSH) by reflexivity.
assert (HFS : FRAME_SIZE = 40) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof HFO as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
assert (Hcfp : 4096 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
pose proof (in_app_sub _ _ cfp 32 Hfhigh ltac:(clear - Hflo; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hfhi; lia)) as Hcfp_ia.
clear Hfin Hcid0 Hfal Hflo Hfhi Hf4096 Hfceil Hfhigh Hfhigh_img Hcal HRA cid pos.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
pose proof HWF1 as (_ & HWge & HHge & HNWH & HNmax & _).
assert (HN1 : 1 <= N <= 100000000) by (clear - HWge HHge HNWH HNmax; nia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_imgP _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (SEPw : forall y, In y (cgif_blocks g s1 N) -> zdisjoint (block_rng y) (block_rng (nw, FRAME_SIZE))).
{ intros y Hy. apply (sep_app B LAWS lyc Sc Wc memc mdc y (nw, FRAME_SIZE) (cgif_blocks g s1 N) (af_newblocks N fattr nlp nw nimg npal ++ af_cblocks img N fattr lpa nlp rest) HAR HPerm1 Hy).
apply in_app_iff. left. left. reflexivity. }
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof (SEPw (g, CGIF_SIZE) ltac:(left; reflexivity)) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D.
change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
assert (Dgc : g + 96 <= cfp \/ cfp + 32 <= g).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ g CGIF_SIZE cid pos HAR Hing Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. clear - D Hflo Hfhi. lia. }
assert (Dfn : forall f ii, In (Some f) (cg_frames s1) -> 0 <= ii < 40 -> ~ (nw <= fr_ptr f + ii < nw + 40)).
{ intros f ii Hf Hii. pose proof (SEPw (fr_ptr f, FRAME_SIZE) ltac:(apply af_frame_in_blocks; exact Hf)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hii. lia. }
assert (Hgd : exists gp dp, gp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_gen fp | None => 0 end /\
dp = match nth (Z.to_nat i - 1) (cg_frames s1) None with Some fp => fr_disp fp | None => 0 end /\
0 <= gp < 2 ^ 32 /\ 0 <= dp < 2 ^ 8).
{ destruct (nth (Z.to_nat i - 1) (cg_frames s1) None) as [fp|] eqn:Hop.
- assert (Hfpi : In (Some fp) (cg_frames s1)) by (rewrite <- Hop; apply nth_In; rewrite Hlen1; clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rg]. cbn [snd] in Rg.
pose proof (obj_at_nth SEGS _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [_ Rd]. cbn [snd] in Rd.
exists (fr_gen fp), (fr_disp fp). split; [reflexivity|]. split; [reflexivity|]. clear - Rg Rd. cbn in Rg, Rd. lia.
- exists 0, 0. clear. repeat split; lia. }
destruct Hgd as (gp & dp & Egp & Edp & Hgpr & Hdpr).
destruct (aview SEGS (w_H Wc) memc (nw + 28)) as [v28|] eqn:Hv28; [| exfalso; exact (aview_some_of_apresent SEGS _ _ _ (proj1 (HnP (nw + 28) ltac:(clear - PBASE PBLO; lia))) Hv28)].
destruct (aview_byte SEGS _ _ _ _ Hv28) as (b28 & _ & _ & Rv28).
pose proof (val_mem_byte1 _ _ _ _ Hv28) as Vv28.
set (ctx := if Z.land fattr 6 =? 0 then v28 else tidx).
pose proof (obj_at_nth SEGS _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx]. cbn [snd] in Rtidx.
assert (Rctx : 0 <= ctx < 2 ^ 8) by (subst ctx; destruct (Z.land fattr 6 =? 0); [clear - Rv28; lia | clear - Rtidx; cbn in Rtidx; lia]).
assert (Vctx : val_mem SEGS (mrestrict (w_H Wc) memc) (nw + 28) 1 ctx).
{ subst ctx. destruct (Z.land fattr 6 =? 0) eqn:Hb; [exact Vv28|]. apply (proj2 (proj2 (proj2 (proj2 (proj2 HNC))))). clear - Hb. intros H6. rewrite H6 in Hb. discriminate. }
pose proof HNC as (Vlp & Vfa & Vfg & Vde & Vnl & _).
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr].
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) fgen HCF eq_refl eq_refl) as [_ Rfgen]. pose proof (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) delay HCF eq_refl eq_refl) as [_ Rdelay].
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp].
cbn [snd] in Rlpal, Rfattr, Rfgen, Rdelay, Rnlp.
pose proof (obj_at_nth SEGS _ _ _ _ 5 (40, 4%N) (cg_attr s1) (proj1 HT1) eq_refl eq_refl) as [_ Rattr]. cbn [snd] in Rattr.
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
destruct (af_reseedxEX B TL LAWS AF_E regsE1 8 16 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) [gp; dp]
(proj1 CX) MID Rsp HL ltac:(apply Forall_nil) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsE1_ok regs regs1 g s1 cfp _ _ HR HR9 ltac:(lia) Hgceil)
ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
rewrite app_nil_r in HS.
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env). norm_ss HS.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0; gp; dp]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 40%nat ltac:(unfold A_TEXT; lia)) as E40.
pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. pose proof (ES 68%nat ltac:(unfold A_TEXT; lia)) as E68. pose proof (ES 69%nat ltac:(unfold A_TEXT; lia)) as E69.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E35, E37, E38, E40, E46, E67, E68, E69.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg | st_ok _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_pi_submem Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_submem SEGS Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end  end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 8 16 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 8 16 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end end.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 0 88 8 16 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 8 16 cs 0 88 8 16 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 0 88 8 16 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 8 16 cs 0 88 8 16 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH23 E (mrestrict (w_H Wc) memc)).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ _ g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as (_ & _ & HRA1).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H Wc) memc E Bxa 46 cfp 32 cfp 0 32 HRA1).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR HnwIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
prreg HS (24%bv : bv 5) Q25.
pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) 1 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Q25; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite (EEo 24%nat 24%bv eq_refl), R25; reflexivity) eq_refl) as HS3.
clear HS Q25. rename HS3 into HS. norm_ss HS.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
all: try (awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
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
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 = 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_E2; [awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 | st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0  end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 4 0).
assert (Vslot : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 4).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 4) 4 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte SEGS (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at SEGS (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
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
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew GPAL IMG LPAL gs gsF (af_gs4 (cg_attr s) gs1 1) CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite xcgif_vals_set_ihead_ls, (xcgif_vals_ins_frame path hw pf s1 1 fnew ltac:(clear - PBASE PBLO; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (xcgif_vals path hw pf s1) (list_set (list_set (xcgif_vals path hw pf s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals wfn g s2) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 1 (Some fnew)) with (cg_frames (upd_frame s1 1 fnew)).
apply (tframes_at_upd _ _ s1 1 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
-- clear - Hk HEVA HEVF; lia.
-- unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
-- let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
-- let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
--   let R := fresh "R" in prreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
--   let R := fresh "R" in prreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
-- let R := fresh "R" in prreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1 Rfattr.
-- left; reflexivity.
-- rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
-- reflexivity.
-- reflexivity.
--
af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] ((nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)])) ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb XZi.
pose proof (af_xe1_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N 1 nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ _ UN XZb XZi Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XE) as XE2.
assert (XFN : af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx).
{ unfold af_fnew_ok, fnew. cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros H6; unfold ctx; destruct (Z.eqb_spec (Z.land fattr 6) 0); [exfalso; exact (H6 ltac:(assumption)) | reflexivity]|].
split; [rewrite <- Hattr1; clear - Hq8; destruct (Z.eqb_spec (Z.land (cg_attr s1) 8) 0); [first [reflexivity | exfalso; exact (Hq8 ltac:(assumption))] | first [reflexivity | exfalso; apply n; exact Hq8]]|].
split; [reflexivity|]. split; [reflexivity|]. intros Hz. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | reflexivity]. }
exact (af_xe1_e2_plain K MT XN S Sc _ _ s s1 N 1 fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (or_introl eq_refl) Hlen1 ltac:(rewrite <- Hattr1; exact Hq8) XFN XE2).
*
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 <> 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
all: try (awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
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
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
assert (Dpn : fr_ptr fp + 40 <= nw \/ nw + 40 <= fr_ptr fp).
{ pose proof (SEPw (fr_ptr fp, FRAME_SIZE) HfpC) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth SEGS _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 33) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E69) | st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 33) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E69)  end.
assert (Vg2 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 33%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 33%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 33%nat) 0 32 20 24 [YP09.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 33%nat) 0 32 20 24 [YP09.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 33%nat) 32 40 32 33 [YP09.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 33%nat) 32 40 32 33 [YP09.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok SEGS Bxa (af_SH23 ++ [mkSHE 33 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc _ _ _ Bxa 33 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia). rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Y33.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (Afp : forall blc ii lyq ownq, In (fr_ptr fp, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (fr_ptr fp + ii)).
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HfpC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists (fr_ptr fp), FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_E2; [awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E33 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0 | st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0  end.
assert (X33u : bv_unsigned (ew EL 33) = fr_ptr fp) by (rewrite AGx by lia; rewrite E33; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E68).
set (gen' := Z.land (fr_gen fp) 18446744073709551612).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 68 0) (SLit (-4))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 68 (fr_gen fp) X68) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-4)) with 18446744073709551612. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vgen : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vpd : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YP09.mkRegion (Some 33%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 33 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte SEGS (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn Dpn; lia]. }
assert (Hfnew : obj_at SEGS (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 1 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 1 fnew)) 0 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear - PBASE PBLO; lia); exact Hfpe).
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
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew GPAL IMG LPAL gs gsF (af_gs4 (cg_attr s) gs1 1) CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite xcgif_vals_set_ihead_ls, (xcgif_vals_upd_frame path hw pf (upd_frame s1 1 fnew) 0 fp fp' Hfpe1 eq_refl), (xcgif_vals_ins_frame path hw pf s1 1 fnew ltac:(clear - PBASE PBLO; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (xcgif_vals path hw pf s1) (list_set (list_set (xcgif_vals path hw pf s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals wfn g s2) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; right; left; reflexivity) HfpIn
ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D2. cbn [fst snd] in D2. change (req_size RAW_SIZE) with 48 in D2. rewrite HFS in D2. change (req_size 40) with 40 in D2.
apply UN; [exact Hb | clear - Hn Hii D D2; lia].
- rewrite Hfr2. change (list_set (list_set (cg_frames s1) 1 (Some fnew)) 0 (Some fp')) with (cg_frames (upd_frame (upd_frame s1 1 fnew) 0 fp')).
apply (tframes_at_upd2 _ _ s1 1 0 None fnew (Some fp) fp' Hf Hfne1 Hfpe ltac:(clear - PBASE PBLO; lia)); [exact Hfnew | |].
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
pose proof (HZf fp ii Hfpi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Hii Hw1 Hw2 Dpn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vpd. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hlen1 Hjx Hfpe Hne0) as Dff2.
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Dff2 Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
++   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
++ let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in prreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in prreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++ let R := fresh "R" in prreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++ unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1 Rfattr.
++ left; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite YI5v.nth_list_set_other by (clear - PBASE PBLO; lia). rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
++
af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] ((nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)])) ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb XZi.
pose proof (af_xe1_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N 1 nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ _ UN XZb XZi Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XE) as XE2.
assert (XFN : af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx).
{ unfold af_fnew_ok, fnew. cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros H6; unfold ctx; destruct (Z.eqb_spec (Z.land fattr 6) 0); [exfalso; exact (H6 ltac:(assumption)) | reflexivity]|].
split; [rewrite <- Hattr1; clear - Hq8; destruct (Z.eqb_spec (Z.land (cg_attr s1) 8) 0); [first [reflexivity | exfalso; exact (Hq8 ltac:(assumption))] | first [reflexivity | exfalso; apply n; exact Hq8]]|].
split; [reflexivity|]. split; [reflexivity|]. intros Hz. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | reflexivity]. }
exact (af_xe1_e2_tr_some K MT XN S Sc _ _ s s1 N 1 fnew fp nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (or_introl eq_refl) Hlen1 ltac:(rewrite <- Hattr1; exact Hq8) Hop ltac:(clear - Rg; cbn in Rg; lia) XFN XE2).
--
cbn [frame_ptr] in E33.
prreg HS (12%bv : bv 5) Q12.
pose proof (st_ok_pi_pin_reg' _ _ _ (12%bv : bv 5) 0 HS
ltac:(cbn [ms_regs restrict mkst]; rewrite Q12; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E33) eq_refl) as HS3.
clear HS Q12. rename HS3 into HS. norm_ss HS.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_E2; [awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 8 <= a < g + 16) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 | st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0  end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 8) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 8 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 1).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 1) 1 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte SEGS (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at SEGS (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
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
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 1 nw fnew GPAL IMG LPAL gs gsF (af_gs4 (cg_attr s) gs1 1) CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite xcgif_vals_set_ihead_ls, (xcgif_vals_ins_frame path hw pf s1 1 fnew ltac:(clear - PBASE PBLO; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (xcgif_vals path hw pf s1) (list_set (list_set (xcgif_vals path hw pf s1) 1 nw) 16 1) [1; 16]%nat [(8, 16); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals wfn g s2) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 1 (Some fnew)) with (cg_frames (upd_frame s1 1 fnew)).
apply (tframes_at_upd _ _ s1 1 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
++   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
++ let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in prreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in prreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++ let R := fresh "R" in prreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++ unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1 Rfattr.
++ left; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
++
af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] ((nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)])) ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb XZi.
pose proof (af_xe1_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N 1 nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ _ UN XZb XZi Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XE) as XE2.
assert (XFN : af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx).
{ unfold af_fnew_ok, fnew. cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros H6; unfold ctx; destruct (Z.eqb_spec (Z.land fattr 6) 0); [exfalso; exact (H6 ltac:(assumption)) | reflexivity]|].
split; [rewrite <- Hattr1; clear - Hq8; destruct (Z.eqb_spec (Z.land (cg_attr s1) 8) 0); [first [reflexivity | exfalso; exact (Hq8 ltac:(assumption))] | first [reflexivity | exfalso; apply n; exact Hq8]]|].
split; [reflexivity|]. split; [reflexivity|]. intros Hz. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | reflexivity]. }
exact (af_xe1_e2_tr_none K MT XN S Sc _ _ s s1 N 1 fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (or_introl eq_refl) Hlen1 Hop XFN XE2).
+
change (Z.to_nat 2) with 2%nat in Hnone. change (Z.to_nat 2 - 1)%nat with 1%nat in Egp, Edp.
destruct (af_reseedxEX B TL LAWS AF_E regsE1 16 24 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 (af_newblocks N fattr nlp nw nimg npal) [gp; dp]
(proj1 CX) MID Rsp HL ltac:(apply Forall_nil) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsE1_ok regs regs1 g s1 cfp _ _ HR HR9 ltac:(lia) Hgceil)
ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
rewrite app_nil_r in HS.
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env). norm_ss HS.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0; gp; dp]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 33%nat ltac:(unfold A_TEXT; lia)) as E33. pose proof (ES 34%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (ES 35%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 40%nat ltac:(unfold A_TEXT; lia)) as E40.
pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. pose proof (ES 68%nat ltac:(unfold A_TEXT; lia)) as E68. pose proof (ES 69%nat ltac:(unfold A_TEXT; lia)) as E69.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E33, E34, E35, E37, E38, E40, E46, E67, E68, E69.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg | st_ok _ ?Ex ?ssx ?msx =>
let rg := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 4 rg HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_pi_submem Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end | st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
lazymatch rs with [?r0; ?r1; ?r2; ?r3; ?r4; ?r5] =>
pose proof (st_ok_submem SEGS Ex ssx msx [r0; r1; r2; r3; r5] HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3 end  end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 16 24 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 88 96 92 96 (chunks_between 88 96 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 16 24 cs 88 96 92 96 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end end.
lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
lazymatch type of HS with st_ok_pi _ _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 0 88 16 24 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 16 24 cs 0 88 16 24 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ _ _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 32%nat) 0 88 16 24 (chunks_between 0 88 cs)) HS eq_refl
ltac:(apply (region_ok_part SEGS Ex _ (Some 32%nat) 0 96 16 24 cs 0 88 16 24 HRg); [clear; lia | clear; lia |
cbn [base_val]; rewrite E32u; intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HgP (g + o) ltac:(clear - Ho; lia)))])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Hcfp HZg Hgh Hgh_img Hgh_ia Hgceil Hceil Hslo HTS C1 C3 Dgc Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 68%nat (mkAF 0 4294967295 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E68, unsigned_lit_small by (clear - Hgpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hgpr; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 69%nat (mkAF 0 255 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E69, unsigned_lit_small by (clear - Hdpr; lia); change (2 ^ 0) with 1; rewrite Z.mod_1_r; clear - Hdpr; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 32 34 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH23 E (mrestrict (w_H Wc) memc)).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ _ g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as (_ & _ & HRA1).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H Wc) memc E Bxa 46 cfp 32 cfp 0 32 HRA1).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR HnwIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
prreg HS (24%bv : bv 5) Q25.
pose proof (st_ok_pi_pin_reg' _ _ _ (24%bv : bv 5) 2 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Q25; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite (EEo 24%nat 24%bv eq_refl), R25; reflexivity) eq_refl) as HS3.
clear HS Q25. rename HS3 into HS. norm_ss HS.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
all: try (awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
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
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
*
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_eq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 = 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_E2; [awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0 | st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 1 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 2 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 3 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRn, HRg1, HRg2, HR0  end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 4 0).
assert (Vslot : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 16) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 16 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 2).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 2) 2 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 4).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 4) 4 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte SEGS (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
assert (Hfnew : obj_at SEGS (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 2 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
set (s2 := set_ihead (upd_frame s1 2 fnew) 2).
assert (Hfr2 : cg_frames s2 = list_set (cg_frames s1) 2 (Some fnew)) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| right; split; [reflexivity | unfold upd_frame; cbn [cg_frames set_frames]; rewrite YI5v.nth_list_set_other by (clear - PBASE PBLO; lia); exact (Hs1 eq_refl)]]. apply (cgif_wf_ins_frame s1 N 2 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; left; reflexivity]. }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead.
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 2 fnew Hfne1). }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 2 nw fnew GPAL IMG LPAL gs gsF (af_gs4 (cg_attr s) gs1 2) CX) end.
--
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite xcgif_vals_set_ihead_ls, (xcgif_vals_ins_frame path hw pf s1 2 fnew ltac:(clear - PBASE PBLO; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (xcgif_vals path hw pf s1) (list_set (list_set (xcgif_vals path hw pf s1) 2 nw) 16 2) [2; 16]%nat [(16, 24); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals wfn g s2) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D. apply UN; [exact Hb | clear - Hn Hii D; lia].
- rewrite Hfr2. change (list_set (cg_frames s1) 2 (Some fnew)) with (cg_frames (upd_frame s1 2 fnew)).
apply (tframes_at_upd _ _ s1 2 None fnew Hf Hfne1); [exact Hfnew|].
intros j x Hjx Hne ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
-- clear - Hk HEVA HEVF; lia.
-- unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
--   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
-- let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
-- let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
--   let R := fresh "R" in prreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
--   let R := fresh "R" in prreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
-- let R := fresh "R" in prreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
-- let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
-- unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1 Rfattr.
-- right; reflexivity.
-- rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
-- reflexivity.
-- reflexivity.
--
af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] ((nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)])) ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb XZi.
pose proof (af_xe1_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N 2 nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ _ UN XZb XZi Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XE) as XE2.
assert (XFN : af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx).
{ unfold af_fnew_ok, fnew. cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros H6; unfold ctx; destruct (Z.eqb_spec (Z.land fattr 6) 0); [exfalso; exact (H6 ltac:(assumption)) | reflexivity]|].
split; [rewrite <- Hattr1; clear - Hq8; destruct (Z.eqb_spec (Z.land (cg_attr s1) 8) 0); [first [reflexivity | exfalso; exact (Hq8 ltac:(assumption))] | first [reflexivity | exfalso; apply n; exact Hq8]]|].
split; [reflexivity|]. split; [reflexivity|]. intros Hz. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | reflexivity]. }
exact (af_xe1_e2_plain K MT XN S Sc _ _ s s1 N 2 fnew nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (or_intror eq_refl) Hlen1 ltac:(rewrite <- Hattr1; exact Hq8) XFN XE2).
*
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq8 end.
rewrite branch_eq_U, U_and_lit, U_lit in Hq8 by (clear - PBASE PBLO; lia). apply (proj1 (Z.eqb_neq _ _)) in Hq8.
lazymatch type of Hq8 with Z.land (U ?Ex _) 8 <> 0 =>
rewrite U_zext, (U_atom Ex 40 (cg_attr s1) ltac:(rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E40) ltac:(clear - Rattr; cbn in Rattr; lia)) in Hq8 end.
change (2 ^ Z.of_N 8) with (2 ^ 8) in Hq8. rewrite land_mod2p in Hq8 by (clear - Rattr; cbn in Rattr; lia).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
all: try (awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Bnw Anw HnwIn).
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34)) HFr
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
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR HfpIn) as Hph_img.
rewrite HFS in Hpceil. rewrite HFS in HpP. change (req_size 40) with 40 in Hpceil, HpP, Hph_img.
assert (Dpn : fr_ptr fp + 40 <= nw \/ nw + 40 <= fr_ptr fp).
{ pose proof (SEPw (fr_ptr fp, FRAME_SIZE) HfpC) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dgp : g + 96 <= fr_ptr fp \/ fr_ptr fp + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr fp, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; apply af_frames_blocks_ptr_in; exact Hfpi)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcp : cfp + 32 <= fr_ptr fp \/ fr_ptr fp + 40 <= cfp).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE cid pos HAR HfpIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 3 (20, 4%N) (fr_gen fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vg Rg]. cbn [fst snd] in Vg, Rg.
pose proof (obj_at_nth SEGS _ _ _ _ 7 (32, 1%N) (fr_disp fp) (proj2 (proj2 HT1) fp Hfpi) eq_refl eq_refl) as [Vd Rd]. cbn [fst snd] in Vd, Rd.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 34) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E69) | st_ok _ ?Ex _ _ =>
assert (Y33 : bv_unsigned (ew Ex 34) = fr_ptr fp) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia);
assert (Y68 : ew Ex 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E68);
assert (Y69 : ew Ex 69 = Z_to_bv 64 (fr_disp fp)) by (rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia); exact E69)  end.
assert (Vg2 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 20) 4 (fr_gen fp)).
{ apply (val_mem_keptZ _ _ _ 4%nat _ Vg). intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
assert (Vd2 : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms0)) (fr_ptr fp + 32) 1 (fr_disp fp)).
{ apply (val_mem_keptZ _ _ _ 1%nat _ Vd). intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
etransitivity; [apply UN2; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]|].
apply UN1; [clear - Hx Hp4096 Hpceil C1; lia | clear - Hx Dpn Dgp Hpceil Hceil Hslo HTS C1; lia]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 34%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 34%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Y33; change (2 ^ 4) with 16; clear - Hp4096 Hph Hpceil Hp16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr fp) FRAME_SIZE (proj1 HJ) HfpIn) as (_ & _ & _ & _ & HpP0 & _). rewrite HFS in HpP0. change (req_size 40) with 40 in HpP0.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 34%nat) 0 32 20 24 [YP09.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 34%nat) 0 32 20 24 [YP09.mkChunk 20 (CVal 4 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 20 4 (SOff 68 0) (fr_gen fp));
[ cbn [sv_denot]; rewrite Y68, unsigned_lit_small, Z.add_0_r by (clear - Rg; cbn in Rg; lia); reflexivity
| clear - Rg; exact Rg | cbn; clear; lia | exact Vg2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 34%nat) 32 40 32 33 [YP09.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 34%nat) 32 40 32 33 [YP09.mkChunk 32 (CVal 1 (SOff 69 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Y33; split; [clear - Hp4096 Hpceil C1; lia|]; split; [clear - Hp4096 Hpceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HpP0 (fr_ptr fp + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ (fr_ptr fp) 32 1 (SOff 69 0) (fr_disp fp));
[ cbn [sv_denot]; rewrite Y69, unsigned_lit_small, Z.add_0_r by (clear - Rd; cbn in Rd; lia); reflexivity
| clear - Rd; exact Rd | cbn; clear; lia | exact Vd2 ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Y33; rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia);
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgp Dcp Dpn Hp4096 Hph Hph_img Hph_ia Hpceil Hcfp HZg Hnceil Hn4096 Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of SHOK with sh_ok _ _ _ ?Ex ?mx =>
assert (SHOK2 : sh_ok SEGS Bxa (af_SH23 ++ [mkSHE 34 0 FRAME_SIZE]) Ex mx) end.
{ unfold sh_ok. apply Forall_app. split; [exact SHOK|]. constructor; [|constructor].
apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc _ _ _ Bxa 34 (fr_ptr fp) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) HfpIn).
+ unfold U, Bxa. cbn [sv_denot]. rewrite ?ew_ewset_other by (clear - PBASE PBLO; lia). rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Y33.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
clear SHOK. rename SHOK2 into SHOK.
assert (Afp : forall blc ii lyq ownq, In (fr_ptr fp, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (fr_ptr fp + ii)).
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HfpC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists (fr_ptr fp), FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_E2; [awr_yX Usp E32u Hing HTS Bnw Anw HnwIn Y33 Afp HfpIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw, ?E34 in Hrr; rewrite ?(unsigned_lit_small (fr_ptr fp)) in Hrr by (clear - Hp4096 Hpceil C1; lia);
cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN3.
cbv beta in UN3. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 16 <= a < g + 24) \/ (g + 92 <= a < g + 96) \/ (nw + 32 <= a < nw + 34) \/ (fr_ptr fp + 20 <= a < fr_ptr fp + 24) \/ (fr_ptr fp + 32 <= a < fr_ptr fp + 33)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN3 a Ha Hn)|]. etransitivity; [apply (UN2 a Ha); clear - Hn; tauto | apply (UN1 a Ha); clear - Hn; tauto]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_pi_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_pi_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_pi_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0 | st_ok _ ?Ex ?ssx ?msx =>
let rq := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rp := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
let rg1 := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
let rg2 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
let r0 := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rq HS ltac:(vm_compute; reflexivity)) as HRq;
pose proof (st_ok_region_nth Ex ssx msx 1 rp HS ltac:(vm_compute; reflexivity)) as HRp;
pose proof (st_ok_region_nth Ex ssx msx 2 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 3 rg1 HS ltac:(vm_compute; reflexivity)) as HRg1;
pose proof (st_ok_region_nth Ex ssx msx 4 rg2 HS ltac:(vm_compute; reflexivity)) as HRg2;
pose proof (st_ok_region_nth Ex ssx msx 5 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
cbn [ms_mem restrict mkst] in HRq, HRp, HRn, HRg1, HRg2, HR0  end.
assert (X33u : bv_unsigned (ew EL 34) = fr_ptr fp) by (rewrite AGx by lia; rewrite E34; apply unsigned_lit_small; clear - Hp4096 Hpceil C1; lia).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_gen fp)) by (rewrite AGx by lia; exact E68).
set (gen' := Z.land (fr_gen fp) 18446744073709551612).
assert (Hgen' : 0 <= gen' <= fr_gen fp) by (subst gen'; split; [apply (proj2 (Z.land_nonneg _ _)); left; clear - Rg; lia | apply Z_land_upper_l; clear - Rg; lia]).
assert (Dgen : sv_denot EL (SAlu ALU_AND (SOff 68 0) (SLit (-4))) = Z_to_bv 64 gen').
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom EL 68 (fr_gen fp) X68) by (clear - Rg; cbn in Rg; lia). rewrite U_SLit.
change (zcanon (-4)) with 18446744073709551612. subst gen'. apply zcanon_id. unfold M64. clear - Hgen' Rg. cbn in Rg. lia. }
set (fp' := set_fr_gen_disp fp gen' 8).
assert (Hfp' : frame_vals fp' = list_set (list_set (frame_vals fp) 3 gen') 7 8) by reflexivity.
assert (Vgen : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 20) 4 gen').
{ lazymatch type of HRp with region_ok _ ?Ex _ (YP09.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 20 4 _ gen' HRp X33u ltac:(cbn; tauto) Dgen ltac:(clear - Hgen' Rg; cbn in Rg |- *; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vpd : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (fr_ptr fp + 32) 1 8).
{ lazymatch type of HRq with region_ok _ ?Ex _ (YP09.mkRegion (Some 34%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 34 (fr_ptr fp) cs lo hi wlo whi 32 1 (SLit 8) 8 HRq X33u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp).
set (fnew := mkFrame nw (if Z.land fattr 1 =? 0 then lpal else npal) nimg fattr fgen delay nlp ctx 8 0).
assert (Vslot : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 16) 8 nw).
{ lazymatch type of HRg1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 16 8 (SOff 23 0) nw HRg1 X32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hn4096 Hnceil C1; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vih : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (g + 92) 4 2).
{ lazymatch type of HRg2 with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 92 4 (SLit 2) 2 HRg2 X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vdisp : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 32) 1 8).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 32 1 (SLit 8) 8 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Vtix : val_mem SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + 33) 1 0).
{ lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SLit 0) 0 HRn X23u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(cbn; clear; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
assert (Hnwk : forall ii, 0 <= ii < 32 -> mbyte SEGS (mrestrict (w_H Wc) (ms_mem msL)) (nw + ii) = mbyte SEGS (mrestrict (w_H Wc) memc) (nw + ii)).
{ intros ii Hii. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hnceil Hceil Hslo HTS C1 Dgn Dpn; lia]. }
assert (Hfnew : obj_at SEGS (mrestrict (w_H Wc) (ms_mem msL)) nw LAY_Frame (frame_vals fnew)).
{ apply obj_at_of_fields; [reflexivity|]. intros j f v Hf Hv.
destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; [| | | | | | | | | destruct j; discriminate Hf]; cbn in Hf, Hv; injection Hf as <-; injection Hv as <-;
unfold field_ok; cbn [fst snd Z.of_N]; cbv [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite ?Z.add_0_r.
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ Vlp); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); exact HlpE].
- split; [apply (val_mem_keptZ _ _ _ 8%nat _ HV8); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | change (2 ^ (8 * 8)) with (2 ^ 64); clear - Hm4096 Hmceil C1 HN1; lia].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfa); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfattr; exact Rfattr].
- split; [apply (val_mem_keptZ _ _ _ 4%nat _ Vfg); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rfgen; exact Rfgen].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vde); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rdelay; exact Rdelay].
- split; [apply (val_mem_keptZ _ _ _ 2%nat _ Vnl); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rnlp; exact Rnlp].
- split; [apply (val_mem_keptZ _ _ _ 1%nat _ Vctx); intros x Hx; cbn in Hx; replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia); apply Hnwk; clear - Hx; lia | clear - Rctx; exact Rctx].
- split; [exact Vdisp | cbn; clear; lia].
- split; [exact Vtix | cbn; clear; lia]. }
assert (Hfne1 : nth_error (cg_frames s1) 2 = Some None) by (rewrite <- Hnone; apply nth_error_nth'; rewrite Hlen1; clear; lia).
assert (Hfpe1 : nth_error (cg_frames (upd_frame s1 2 fnew)) 1 = Some (Some fp)) by (rewrite nth_error_upd_frame_other by (clear - PBASE PBLO; lia); exact Hfpe).
set (s2 := set_ihead (upd_frame (upd_frame s1 2 fnew) 1 fp') 2).
assert (Hfr2 : cg_frames s2 = list_set (list_set (cg_frames s1) 2 (Some fnew)) 1 (Some fp')) by reflexivity.
assert (HWF2 : cgif_wf s2 N).
{ apply cgif_wf_set_ihead; [| right; split; [reflexivity | unfold upd_frame at 1; cbn [cg_frames set_frames]; rewrite nth_list_set_same by (unfold upd_frame; cbn [cg_frames set_frames]; rewrite YI5v.length_list_set, Hlen1; clear; lia); discriminate]]. apply (cgif_wf_upd_frame _ N 1 fp fp'); [| exact Hfpe1 |].
- apply (cgif_wf_ins_frame s1 N 2 fnew HWF1 Hfne1).
split; [cbn [fr_attr fnew]; rewrite Hattr1; intros H1; destruct HnoTab as [Hx | Hx]; [exfalso; exact (Hx H1) | exact Hx] | cbn; right; reflexivity].
- rewrite cg_attr_upd_frame. split; [| right; reflexivity].
cbn [fr_attr fp' set_fr_gen_disp]. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fp Hfpi)). }
assert (HB2 : Permutation (cgif_blocks g s2 N) (af_newblocks N fattr nlp nw nimg npal ++ cgif_blocks g s1 N)).
{ unfold s2. rewrite cgif_blocks_set_ihead, (cgif_blocks_upd_frame g (upd_frame s1 2 fnew) N 1 fp fp' Hfpe1 eq_refl).
replace (af_newblocks N fattr nlp nw nimg npal) with (frame_blocks N fnew) by (unfold af_newblocks, frame_blocks; cbn [fr_ptr fr_img fr_attr fr_lpal fr_nlp fnew]; destruct (Z.land fattr 1 =? 0); reflexivity).
exact (cgif_blocks_ins_frame g s1 N 2 fnew Hfne1). }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE2 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k s2 2 nw fnew GPAL IMG LPAL gs gsF (af_gs4 (cg_attr s) gs1 2) CX) end.
++
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hgceil Hpceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- unfold s2. rewrite xcgif_vals_set_ihead_ls, (xcgif_vals_upd_frame path hw pf (upd_frame s1 2 fnew) 1 fp fp' Hfpe1 eq_refl), (xcgif_vals_ins_frame path hw pf s1 2 fnew ltac:(clear - PBASE PBLO; lia) Hlen1). cbn [fr_ptr fnew].
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF g LAY_CGIF 96 (xcgif_vals path hw pf s1) (list_set (list_set (xcgif_vals path hw pf s1) 2 nw) 16 2) [2; 16]%nat [(16, 24); (92, 96)] Ho lay_inside_CGIF) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
apply UN; [clear - Hii HZg; lia | clear - Hii Hw1 Hw2 HZg Dgn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [cbn [fst]; exact Vslot | cbn; clear - Hn4096 Hnceil C1; lia].
- split; [cbn [fst]; exact Vih | cbn; clear; lia]. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
- change (cg_raw s2) with (cg_raw s1). change (traw_vals wfn g s2) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
pose proof (Hrnw ii Hii) as D.
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR ltac:(eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; right; left; reflexivity) HfpIn
ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D2.
unfold zdisjoint in D2. cbn [fst snd] in D2. change (req_size RAW_SIZE) with 48 in D2. rewrite HFS in D2. change (req_size 40) with 40 in D2.
apply UN; [exact Hb | clear - Hn Hii D D2; lia].
- rewrite Hfr2. change (list_set (list_set (cg_frames s1) 2 (Some fnew)) 1 (Some fp')) with (cg_frames (upd_frame (upd_frame s1 2 fnew) 1 fp')).
apply (tframes_at_upd2 _ _ s1 2 1 None fnew (Some fp) fp' Hf Hfne1 Hfpe ltac:(clear - PBASE PBLO; lia)); [exact Hfnew | |].
+ change (fr_ptr fp') with (fr_ptr fp). rewrite Hfp'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF (fr_ptr fp) LAY_Frame 40 (frame_vals fp) (list_set (list_set (frame_vals fp) 3 gen') 7 8) [3; 7]%nat [(20, 24); (32, 33)] (Hf fp Hfpi) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw1 Hw]. apply in_wins_cons_false in Hw as [Hw2 _]. apply (mbyte_of_aview SEGS).
pose proof (HZf fp ii Hfpi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Hii Hw1 Hw2 Dpn Dgp; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | [<- | []]]; cbn in Hf'; injection Hf' as <-; cbn in Hv'; injection Hv' as <-.
- split; [| clear - Hgen' Rg; cbn in Rg |- *; lia]. cbn [fst]. exact Vgen.
- split; [| cbn; clear; lia]. cbn [fst]. exact Vpd. }
{ intros j' Hj'. rewrite !YI5v.nth_error_list_set_other; [reflexivity| |]; intros Hq; apply Hj'; subst j'; cbn; tauto. }
+ intros j x Hjx Hne1 Hne0 ii Hii. assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR ltac:(eapply Permutation_trans; [exact HPerm1 | apply Permutation_refl]) Hlen1 Hjx Hfpe Hne0) as Dff2.
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | pose proof (Dfn x ii Hxi Hii) as D; clear - Hn D Dff2 Hii; lia]. }
split; [split; [exact HWF2 | exact (proj2 HOK)]|].
split; [eapply Permutation_trans; [exact HPerm1|]; rewrite app_assoc; apply Permutation_app; [apply Permutation_sym; eapply Permutation_trans; [exact HB2 | apply Permutation_app_comm] | apply Permutation_refl]|].
intros b Hb. pose proof (Permutation_in _ HB2 Hb) as Hb2. apply in_app_iff in Hb2. destruct Hb2 as [Hb2 | Hb2]; [right; exact (HnewX _ Hb2) | exact (Hnew _ Hb2)].
++ clear - Hk HEVA HEVF; lia.
++ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact X32 | exact X38 | rewrite X32u; reflexivity
| rewrite (AGx 2%nat ltac:(clear; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
++   unfold af_s1_at. let R := fresh "R" in rregD HS (9%bv : bv 5) R; rewrite R; unfold w64; apply (denot_shx EL 32 38 88 g SB X32 X38); clear - HZg Hgceil C1; unfold SB; lia.
++ let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; reflexivity.
++ let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
++   let R := fresh "R" in prreg HS (16%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X46.
++   let R := fresh "R" in prreg HS (17%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X46, unsigned_lit_small by (clear - Hcfp C1; lia); reflexivity.
++ let R := fresh "R" in prreg HS (10%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite X23u; reflexivity.
++ let R := fresh "R" in rregD HS (13%bv : bv 5) R; rewrite R; exact (denot_shx EL 23 38 33 nw SB X23 X38 ltac:(clear - Hn4096; lia) ltac:(clear - PBASE PBLO; lia) ltac:(clear - Hnceil C1; lia) ltac:(unfold SB; clear; lia)).
++ unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locv2 HR0 sp0 X32 X32u X38 X46 X67 Xsp Hcfp HZg Hgceil C1 Rfattr.
++ right; reflexivity.
++ rewrite Hfr2. cbn [Z.to_nat Z.to_pos Pos.to_nat Pos.iter_op Nat.add]. rewrite YI5v.nth_list_set_other by (clear - PBASE PBLO; lia). rewrite nth_list_set_same by (rewrite Hlen1; clear; lia). reflexivity.
++ reflexivity.
++ reflexivity.
++
af_xunz2 UN B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] ((nimg, N) :: (if Z.land fattr 1 =? 0 then [] else [(npal, 3 * nlp)])) ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb XZi.
pose proof (af_xe1_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N 2 nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ _ UN XZb XZi Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XE) as XE2.
assert (XFN : af_fnew_ok s fnew nimg npal fattr fgen delay nlp tidx).
{ unfold af_fnew_ok, fnew. cbn [fr_attr fr_gen fr_delay fr_nlp fr_ctidx fr_disp fr_tidx fr_img fr_lpal].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [intros H6; unfold ctx; destruct (Z.eqb_spec (Z.land fattr 6) 0); [exfalso; exact (H6 ltac:(assumption)) | reflexivity]|].
split; [rewrite <- Hattr1; clear - Hq8; destruct (Z.eqb_spec (Z.land (cg_attr s1) 8) 0); [first [reflexivity | exfalso; exact (Hq8 ltac:(assumption))] | first [reflexivity | exfalso; apply n; exact Hq8]]|].
split; [reflexivity|]. split; [reflexivity|]. intros Hz. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | reflexivity]. }
exact (af_xe1_e2_tr_some K MT XN S Sc _ _ s s1 N 2 fnew fp nimg npal fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF (or_intror eq_refl) Hlen1 ltac:(rewrite <- Hattr1; exact Hq8) Hop ltac:(clear - Rg; cbn in Rg; lia) XFN XE2).
--
exfalso. exact (Hs1 eq_refl eq_refl).
Qed.
End p.
End l.
End h.
