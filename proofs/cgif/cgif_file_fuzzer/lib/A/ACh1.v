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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a YC80 YC1f YC81 YC4b YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp AC8h ACh9 AChc ACh8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c YC5d YC7z YC7x YC21 YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACh7 ACh6 ACh4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
#[local] Notation WFN_ADDR := (BASE + WFN_OFF).
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Variable hw : Z.
Variable CTX : list (list Z).
Variable path pf : Z.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Variable XN : xnums.
Hypothesis HXM : forall N, cl_msum MT XN N <= xm_close XN N.
Hypothesis AFM : afile_meter SEGS B MT.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Variable rctrace : list Z.
Hypothesis HUrc : In rctrace (as_universe B).
Hypothesis RAWCLOSEX : trawclose_specX SEGS K B MT (SIGMA AS_cgif_raw_close) rctrace WFN_ADDR hw.
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_spec SEGS B K (SIGMA AS_fclose) ra_fc1 ra_fc2 pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Definition CL_PF : Z := 0x2c38.
Definition CL_RET_FCLOSE : Z := 0x2c58.
Definition CL_RC_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX B hw CTX path pf ly S W regs mem md ch g s N rest -> cl_xent pf K MT XN ly S W mem md s N aM GPAL gs ->
cl_midX B pf (tcgif_atIX hw path pf 0) ly S W regs mem md g s N ((pf, FILE_BLOCK) :: rest) lyc Sc Wc memc mdc k s1 (fr_blocks g s N 0) -> k <= 2 * EV_FLUSH + 1 ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
cl_xopen pf K MT S s GPAL Sc Wc memc mdc s1 (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) (cl_macc_b XN N + mo_free MT) 0 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_RET_RAWCLOSE)) memc (seg_rom SEGS)) mdc) (cl_postX B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs (k + 15)).
Definition CL_PF_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX B hw CTX path pf ly S W regs mem md ch g s N rest -> cl_xent pf K MT XN ly S W mem md s N aM GPAL gs ->
cl_midX B pf (tcgif_atIX hw path pf 0) ly S W regs mem md g s N ((pf, FILE_BLOCK) :: rest) lyc Sc Wc memc mdc k s1 (fr_blocks g s N 0) -> k <= 2 * EV_FLUSH + 1 ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
cl_xopen pf K MT S s GPAL Sc Wc memc mdc s1 (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) (cl_macc_b XN N + mo_free MT) 0 ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_PF)) memc (seg_rom SEGS)) mdc) (cl_postX B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs (k + 15)).
Definition CL_FC_stmtX : Prop :=
forall ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1,
cl_cxX B hw CTX path pf ly S W regs mem md ch g s N rest -> cl_xent pf K MT XN ly S W mem md s N aM GPAL gs ->
cl_midX B pf (tcgif_atIX hw path pf 0) ly S W regs mem md g s N rest lyc Sc Wc memc mdc k s1 (fr_blocks g s N 0) -> k <= 2 * EV_FLUSH + 3 ->
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB -> getr regs1 10 = w64 0 ->
cl_xclosed K MT S Sc Wc memc mdc (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) (cl_macc_fr MT XN N 0) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + CL_RET_FCLOSE)) memc (seg_rom SEGS)) mdc) (cl_postX B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs (k + 13)).
Lemma regsB_okX : forall (regs regs1 : bvmap 5 word) g s1,
cl_regs_at B regs regs1 g -> getr regs1 20 = w64 SB ->
4096 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) regsB regs1.
Proof.
intros regs regs1 g s1 (R2 & R3 & R4 & R9 & R8 & R19 & _) R20 Hlo Hhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))). assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia); exact R19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; exact R9
| rewrite E38; exact R20
| rewrite E32, unsigned_lit_small by lia; exact R8 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_FC_okX : CL_FR_stmtX B hw CTX path pf K MT XN 0 -> CL_FC_stmtX.
Proof.
intros FRN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk HR R20 R10 XC.
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XC as (HSN & Hlk & MLE).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seedX B LAWS TL hw path pf CL_RET_FCLOSE regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_okX regs regs1 g s1 HR R20 Hgh Hgceil) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E50 : ew E 51 = Z_to_bv 64 pf) by (change 51%nat with (32 + 19)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
assert (E10 : ew E 10 = Z_to_bv 64 0) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_FR.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc rg mm mdq k s1 CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (xcgif_vals path hw pf s1) (cg_cur s1) (proj1 HT1)) end.
* intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
* reflexivity.
* exact Vcur.
-           intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. exact HPerm1.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q18. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q20, E38, E32, cl_srl3X by (clear - Hgceil Hg4096 C1; lia). rewrite cl_alu64_addwX. unfold w64. f_equal. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
+ rewrite Q21. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q22. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+
split; [| split; [exact Hlk | exact MLE]].
destruct (asink_none_frame SEGS K (mrestrict (w_H Wc) memc) _ mdc
ltac:(intros a Ha; apply (mbyte_of_aview SEGS); apply UN;
[ pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; unfold off_img in Hgh_img; clear - Hr Hgh_img; lia ]) HSN) as (N1 & N2 & N3).
split; [exact N1 | split; [exact N2 | exact N3]].
-
exfalso. rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
rewrite (U_atom E 10 0 E10) in Hc by (clear; lia). discriminate Hc.
Qed.
Lemma cl_PF_okX : CL_FC_stmtX -> CL_PF_stmtX.
Proof.
intros FCN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk HR R20 XO.
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XO as (HSINK & MLE & HROOM & HGC).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (HPf : Permutation (ablocks B lyc Sc) ((pf, FILE_BLOCK) :: fr_blocks g s N 0 ++ rest))
by (eapply Permutation_trans; [exact HPerm1|]; apply Permutation_sym; apply Permutation_middle).
destruct (cl_seedX B LAWS TL hw path pf CL_PF regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_okX regs regs1 g s1 HR R20 Hgh Hgceil) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E50 : ew E 51 = Z_to_bv 64 pf) by (change 51%nat with (32 + 19)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
{ awr_clX Usp E32u Hing HTS. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
exfalso. rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
rewrite (U_atom E 51 pf E50) in Hc by (clear - Hpf4096 Hpfceil C1; lia). apply Z.eqb_eq in Hc. clear - Hc Hpf4096. lia.
-
paj_run_tok RUN HS HJ SHOK RBspanC.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19; prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
lazymatch type of UN2 with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ (g + 88 <= a < g + 92) -> aview SEGS (w_H Wc) m2 a = aview SEGS (w_H Wc) memc a)
by (intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)) end.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (HTg : obj_at SEGS (mrestrict (w_H Wc) mm) g LAY_CGIF (xcgif_vals path hw pf s1))
by (apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (xcgif_vals path hw pf s1) (cg_cur s1) (proj1 HT1));
[ intros i Hi Hni; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia | reflexivity | exact Vcur ]) end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (HSINKc : asink_at SEGS K (mrestrict (w_H Wc) mm) mdq pf (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]))
by (apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; unfold off_img in Hgh_img; clear - Hr Hgh_img; lia ]);
assert (HAMc : ameta_inv SEGS K lyc (mrestrict (w_H Wc) mm) aM) by exact (ameta_inv_kept SEGS B K AIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HAM0);
assert (HRODc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H Wc) mm)) by (eapply arodata_ok_journalP; [apply pa_relro_img | exact RO | exact HJ | exact HROD]) end.
assert (HEVf : st_nev Sc + 2 <= EV_MAX) by (clear - Hnev Hk Hev Hk0; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 pf) by (rewrite Q10, E50; reflexivity);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u, unsigned_lit_small by lia; clear - Hgceil; lia)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPcX g s N pf) ly S W mem md [] lyc Sc mdq k AFCLOSE_STK
(asink_fp pf) 2 (-80) (Z_to_bv 64 (BASE + CL_RET_FCLOSE)) []
(fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = w64 0 /\ Permutation (ablocks B ly3 S3) (fr_blocks g s N 0 ++ rest) /\ frames S3 = frames Sc /\
asink_none SEGS K (mrestrict (w_H W3) mem3) md3 /\
Fs.fs_lookup (m_fs md3) sink_path = Some (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]))) HJ Qsp);
[ reflexivity | lia | unfold AFCLOSE_STK; lia | rewrite HTS; unfold AFCLOSE_STK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | unfold CL_RET_FCLOSE; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (AFCLOSE Wc lyc Sc rg mm _ [] pf aM _ (fr_blocks g s N 0 ++ rest) HPRE1 Q10' HPf HSINKc HAMc HRODc HEVf HUfc1 HUfc2)
| cbv beta; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
|
intros a (r & Hr & Hrr); left; exists r; split; [unfold FPcX; apply in_or_app; right; exact Hr | exact Hrr] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & Ha02 & HPerm2 & Hfrs2 & HSN2 & Hlk2).
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFb : forall b n, 4096 <= b -> (b + n <= pf \/ pf + 1264 <= b) -> forall i, 0 <= i < n -> ~ inFP (asink_fp pf) (b + i)).
{ intros b n Hb4096 Dbp i Hi Ha. apply in_asink_fp in Ha. unfold FILE_BLOCK in Ha. clear - Ha Hi Dbp Hb4096. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm2 _) _) _ =>
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
assert (Kg : blk_kept (w_H Wc) (w_H W2) mm mm2 g 96)
by (eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; apply (HnFb g 96 Hg4096); clear - Dgp; lia]) end end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm2 _) ?md2) _ =>
eapply SRr_mono; [apply (FCN ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg2 mm2 md2 (k + 2) s1 CX XE)
| intros Wf cf _ HPf'; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf'); clear; lia] end.
+
split; [exact HJ2|]. split; [clear - Hk0; lia|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold AFCLOSE_STK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- exact (obj_at_blk_kept (w_H Wc) (w_H W2) _ _ g LAY_CGIF _ 96 HTg lay_inside_CGIF Kg).
-           intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. apply in_or_app. left. right. apply in_or_app. right. exact Hfin. }
assert (Dpf : pf + 1264 <= fr_ptr f \/ fr_ptr f + 40 <= pf).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc pf FILE_BLOCK (fr_ptr f) FRAME_SIZE HAR Hinpf Hfc ltac:(unfold FRAME_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size FRAME_SIZE) with 40 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_at_blk_kept (w_H Wc) (w_H W2) mm _ (fr_ptr f) LAY_Frame _ 40); [| exact lay_inside_Frame |] end.
+ apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia.
+ pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
apply Kf. change (req_size FRAME_SIZE) with 40. apply (HnFb (fr_ptr f) 40 Hf4096). clear - Dpf. lia. }
split; [exact HOK |]. exact HPerm2.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)), Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
* rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
* rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)), Q9. exact E32.
* rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)), Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)), Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)), Q20. exact E38.
+ exact Ha02.
+
split; [exact HSN2|]. split; [exact Hlk2|].
apply (mle_weaken MT S S2 _ _ MLAW (mle_station MT S Sc S2 _ _ MLAW MLE (afm_close SEGS B MT AFM _ _ _ _ _ _ _ _ _ _ _ _ _ _ pf _ HJc2 HPf HPerm2))).
unfold cl_macc_fr. clear. lia.
Qed.
Lemma cl_RC_okX : CL_PF_stmtX -> CL_RC_stmtX.
Proof.
intros FRN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk HR R20 XO.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XO as (HSINK & MLE & HROOM & HGC).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
destruct (cl_seedX B LAWS TL hw path pf CL_RET_RAWCLOSE regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_okX regs regs1 g s1 HR R20 Hgh Hgceil) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
psrr_branch_tok RUN BR HS SHOK RBspanC.
-
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_PF.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc rg mm mdq k s1 CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (xcgif_vals path hw pf s1) (cg_cur s1) (proj1 HT1)) end.
* intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
* reflexivity.
* exact Vcur.
- intros j f Hj Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. exact HPerm1.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q20. exact E38.
+
split; [| split; [exact MLE | split; [exact HROOM | exact HGC]]].
apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; unfold off_img in Hgh_img; clear - Hr Hgh_img; lia ].
-
paj_run_to_tok RUNTO HS HJ SHOK RBspanC CL_PF.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19.
prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20; prreg HS (21%bv : bv 5) Q21; prreg HS (22%bv : bv 5) Q22.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
set (cR := bv_unsigned (getr regs1 10) mod 2 ^ 32).
pose proof (field_of_region_any E _ 32 g _ _ _ _ _ 88 4 (SOff 10 0) HRg E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur.
cbn [sv_denot] in Vcur. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl) in Vcur.
change (N.to_nat 4) with 4%nat in Vcur. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur. change (bv_unsigned (getr regs1 10) mod 2 ^ 32) with cR in Vcur.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (FRN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc rg mm mdq k (cl_set_cur s1 cR) CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); clear; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- lazymatch goal with |- obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_cgif_setcurX SEGS path hw pf (mrestrict (w_H Wc) memc) _ g s1 cR (proj1 HT1)) end.
* intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia.
* exact Vcur.
* exact RcR.
- intros j f Hj Hfj. cbn [cg_frames cl_set_cur] in Hfj. pose proof (proj2 HT1 j f Hj Hfj) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia. }
split; [exact HOK |]. exact HPerm1.
+ clear - Hk. lia.
+
split; [|split; [|split; [|split; [|split; [|split]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3, (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4, (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q9. exact E32.
* rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
* intros r Hr.
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q20. exact E38.
+
split; [| split; [exact MLE | split; [exact HROOM | exact HGC]]].
apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; unfold off_img in Hgh_img; clear - Hr Hgh_img; lia ].
Qed.
Lemma cl_B_okX : CL_RC_stmtX -> CL_B_stmtX B hw CTX path pf K MT XN.
Proof.
intros RCN ly S W regs mem md ch g s N aM rest GPAL gs lyc Sc Wc regs1 memc mdc k s1 CX XE MID Hk HR R20 XO.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof XE as (Hpf0 & HREL & HLEN & HAM0 & HMOK). pose proof XO as (HSINK & MLE & HROOM & HGC).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R9 & R8 & R19 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
assert (HPr : Permutation (ablocks B lyc Sc) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ (pf, FILE_BLOCK) :: rest)).
{ eapply Permutation_trans; [exact HPerm1|]. unfold cgif_blocks. cbn [app]. rewrite <- app_assoc. apply perm_swap. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPr|]; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (Hr16 & Hr4096 & Hrceil & Hrh_ia & _ & _). pose proof (proj1 Hrh_ia) as Hrh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hinr) as Hrh_img.
change (req_size RAW_SIZE) with 48 in Hrceil, Hrh, Hrh_img.
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (cg_raw s, RAW_SIZE) (g, CGIF_SIZE) _ HAR HPr ltac:(left; reflexivity)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D. clear - D. lia. }
assert (HPrX : Permutation (ablocks B lyc Sc) ((cg_raw s, RAW_SIZE) :: (g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ rest)).
{ eapply Permutation_trans; [exact HPr|]. apply perm_skip. apply perm_skip. rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle. }
assert (Hinpf : In (pf, FILE_BLOCK) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPrX|]; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pf FILE_BLOCK HAR Hinpf) as (_ & Hpf4096 & Hpfceil & _). change (req_size FILE_BLOCK) with 1264 in Hpfceil.
assert (Dgp : g + 96 <= pf \/ pf + 1264 <= g).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc g CGIF_SIZE pf FILE_BLOCK HAR Hing Hinpf ltac:(unfold CGIF_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (Drp : cg_raw s + 48 <= pf \/ pf + 1264 <= cg_raw s).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc (cg_raw s) RAW_SIZE pf FILE_BLOCK HAR Hinr Hinpf ltac:(unfold RAW_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
destruct (cl_seedX B LAWS TL hw path pf CL_B regsB true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsB_okX regs regs1 g s1 HR R20 Hgh Hgceil) (fun _ => HFR) (proj1 HT1)) as [HS SHOK].
set (E := Eimg (Ereg regs1 (cl_extraX regs g s1 pf))) in *. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, (j < 100)%nat -> ew E (32 + j) = nth j (cl_extraX regs g s1 pf) (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E36 : ew E 36 = Z_to_bv 64 (cg_raw s1)) by (change 36%nat with (32 + 4)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo by (clear; lia); reflexivity).
assert (E50 : ew E 51 = Z_to_bv 64 pf) by (change 51%nat with (32 + 19)%nat; rewrite EXo by (clear; lia); reflexivity).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
paj_run_tok RUN HS HJ SHOK RBspanC.
{ awr_clX Usp E32u Hing HTS. }
pmkst HS.
prreg HS (2%bv : bv 5) Q2; prreg HS (10%bv : bv 5) Q10; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4; prreg HS (1%bv : bv 5) Q1; prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9; prreg HS (19%bv : bv 5) Q19; prreg HS (18%bv : bv 5) Q18; prreg HS (20%bv : bv 5) Q20.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN.
lazymatch type of HS with
| st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg
| st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) _) _ =>
assert (HTg : obj_at SEGS (mrestrict (w_H Wc) mm) g LAY_CGIF (xcgif_vals path hw pf s1))
by (apply (obj_cgif_rebuild (mrestrict (w_H Wc) memc) _ g (xcgif_vals path hw pf s1) (cg_cur s1) (proj1 HT1));
[ intros i Hi Hni; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Hni Hgh Hgceil C1 C3; lia | reflexivity | exact Vcur ]);
assert (HTr : obj_at SEGS (mrestrict (w_H Wc) mm) (cg_raw s) LAY_Raw (traw_vals WFN_ADDR g s1))
by (rewrite <- Hraw1; apply (obj_at_kept _ _ (cg_raw s1) LAY_Raw _ 48 (proj1 (proj2 HT1)) lay_inside_Raw); rewrite Hraw1;
intros i Hi; apply (mbyte_of_aview SEGS); apply UN; clear - Hi Dgr Hgh Hgceil Hr4096 Hrceil C1 C3; lia) end.
pose proof (obj_at_nth SEGS _ _ _ _ 11 (56, 8%N) hw HTg eq_refl eq_refl) as [Vwfn _].
pose proof (obj_at_nth SEGS _ _ _ _ 12 (64, 8%N) 0 HTg eq_refl eq_refl) as [Vctx _].
pose proof (obj_at_nth SEGS _ _ _ _ 14 (80, 8%N) pf HTg eq_refl eq_refl) as [Vfile _].
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) WFN_ADDR HTr eq_refl eq_refl) as [Vrw _].
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) g HTr eq_refl eq_refl) as [Vrg _].
pose proof (obj_at_nth SEGS _ _ _ _ 8 (40, 4%N) (rw_cur s1) HTr eq_refl eq_refl) as [Vrc Rrc].
cbn [fst snd] in Vwfn, Vctx, Vfile, Vrw, Vrg, Vrc, Rrc. rewrite Z.add_0_r in Vrw.
change (N.to_nat 8) with 8%nat in Vwfn, Vctx, Vfile, Vrw, Vrg. change (N.to_nat 4) with 4%nat in Vrc.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 (cg_raw s)) by (rewrite Q10, E36, Hraw1; reflexivity);
assert (Qs0 : achain lyc (aview SEGS (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u, unsigned_lit_small by lia; clear - Hgceil; lia);
assert (HEVc : st_nev Sc + EV_RAWCLOSE <= EV_MAX) by (unfold EV_RAWCLOSE; clear - Hnev Hk Hev Hk0; lia)
end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm _) ?mdq) _ =>
assert (HSINKc : asink_at SEGS K (mrestrict (w_H Wc) mm) mdq pf (concat (YO07.close_gif (gcfg_of s GPAL) gs)))
by (apply (asink_at_kept_mm SEGS K (mrestrict (w_H Wc) memc) _ mdc _ pf _); [| reflexivity | reflexivity | exact HSINK];
intros a [Ha | Ha]; apply (mbyte_of_aview SEGS); apply UN;
[ unfold FILE_BLOCK in Ha; clear - Ha Hpf4096 Hpfceil C1; lia | unfold FILE_BLOCK in Ha; clear - Ha Dgp; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; clear - Hr; lia
| pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))) as Hr; unfold off_img in Hgh_img; clear - Hr Hgh_img; lia ]) end.
assert (HMOKc : mo_ok MT Sc (mo_free MT)).
{ apply (mok_station MT S Sc (xm_close XN N) (cl_macc_b XN N) (mo_free MT) MLAW HMOK MLE); [exact (mo_free_nonneg MT MLAW)|].
pose proof (HXM N) as Hx. pose proof (mo_free_nonneg MT MLAW) as M5. unfold cl_msum, cl_macc_fr in Hx. clear - Hx M5. lia. }
pose proof HUrc as HU1.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_callS B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPcX g s N pf) ly S W mem md [] lyc Sc mdq k TRAWCLOSE_STK
(ablocks_fp [(cg_raw s, RAW_SIZE)] ++ asink_fp pf) EV_RAWCLOSE (-80) (Z_to_bv 64 (BASE + CL_RET_RAWCLOSE)) []
(fun ly3 S3 W3 regs3 mem3 md3 => getr regs3 10 = w64 (rc_int (rw_cur s1)) /\
Permutation (ablocks B ly3 S3) ((g, CGIF_SIZE) :: (pf, FILE_BLOCK) :: pal_blocks s ++ frames_blocks N (cg_frames s) ++ rest) /\
asink_at SEGS K (mrestrict (w_H W3) mem3) md3 pf (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59]) /\
mo_le MT Sc S3 (mo_free MT)) HJ Qsp);
[ reflexivity | lia | unfold TRAWCLOSE_STK, ASTACK; lia | rewrite HTS; unfold TRAWCLOSE_STK, ASTACK; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_codeptr_v; [cbv; split; [congruence | reflexivity] | reflexivity] | unfold CL_RET_RAWCLOSE; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (RAWCLOSEX lyc Sc Wc rg mm _ [] (cg_raw s) g (rw_cur s1) pf 0 _ _ HPRE1 Q10' HPrX
Vrw Vrg Vrc ltac:(clear - Rrc; lia) Vwfn Vctx ltac:(lia) Vfile HSINKc ltac:(clear - HROOM; lia) HEVc HU1 HMOKc)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
|
intros a (r & Hr & Hrr); left; apply in_app_or in Hr; destruct Hr as [Hr | Hr];
[ destruct (inFP_ablocks_fp_inv _ a (ex_intro _ r (conj Hr Hrr))) as (p & n & Hpn & Hpa);
destruct Hpn as [Hpn | []]; injection Hpn as <- <-;
assert (Hq : inFP (FPc g s N) a)
by (unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| clear - Hpa; lia];
unfold cgif_blocks; right; left; reflexivity);
destruct Hq as (r' & Hr' & Hrr'); exists r'; split; [unfold FPcX; apply in_or_app; left; exact Hr' | exact Hrr']
| exists r; split; [unfold FPcX; apply in_or_app; right; exact Hr | exact Hrr] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & Ha02 & HPerm2 & HSINK2 & MLEc).
pose proof (proj1 HJ2) as HAR2.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFb : forall b n, 4096 <= b -> (b + n <= cg_raw s \/ cg_raw s + 48 <= b) -> (b + n <= pf \/ pf + 1264 <= b) ->
forall i, 0 <= i < n -> ~ inFP (ablocks_fp [(cg_raw s, RAW_SIZE)] ++ asink_fp pf) (b + i)).
{ intros b n Hb4096 Dbr Dbp i Hi (r & Hr & Hrr). apply in_app_or in Hr. destruct Hr as [Hr | Hr].
- destruct (inFP_ablocks_fp_inv _ _ (ex_intro _ r (conj Hr Hrr))) as (p & n' & Hpn & Hpa). destruct Hpn as [Hpn | []]. injection Hpn as <- <-.
change (req_size RAW_SIZE) with 48 in Hpa. clear - Hi Hpa Dbr. lia.
- assert (Ha : inFP (asink_fp pf) (b + i)) by (exists r; split; [exact Hr | exact Hrr]).
apply in_asink_fp in Ha. unfold FILE_BLOCK in Ha. clear - Ha Hi Dbp Hb4096. lia. }
assert (HnFg : forall i, 0 <= i < 96 -> ~ inFP (ablocks_fp [(cg_raw s, RAW_SIZE)] ++ asink_fp pf) (g + i))
by (apply (HnFb g 96 Hg4096); [clear - Dgr; lia | clear - Dgp; lia]).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?mm2 _) _) _ =>
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
assert (Kg : blk_kept (w_H Wc) (w_H W2) mm mm2 g 96)
by (eapply (blk_kept_call B); [exact HJc2 | exact Hing | exact Hing2 | change (req_size CGIF_SIZE) with 96; exact HnFg]) end end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ ?mm2 _) ?md2) _ =>
eapply SRr_mono; [apply (RCN ly S W regs mem md ch g s N aM rest GPAL gs ly2 S2 W2 rg2 mm2 md2 (k + EV_RAWCLOSE) s1 CX XE)
| intros Wf cf _ HPf; apply (cl_postX_mono B pf K MT XN ly S W regs mem md g s N aM rest GPAL gs _ _ Wf cf HPf); unfold EV_RAWCLOSE; clear; lia] end.
-
split; [exact HJ2|]. split; [unfold EV_RAWCLOSE; clear - Hk0; lia|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (unfold TRAWCLOSE_STK, ASTACK; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split.
{ split.
- exact (obj_at_blk_kept (w_H Wc) (w_H W2) _ _ g LAY_CGIF _ 96 HTg lay_inside_CGIF Kg).
- intros j f Hj Hfj. change (Z.to_nat 0) with 0%nat in Hj.
assert (Hinf : In (Some f) (cg_frames s1)) by (eapply nth_error_In; exact Hfj).
pose proof (proj2 (proj2 HT1) f Hinf) as Hof.
destruct (slot_frame g s s1 N j f HOK HWF Hfj) as (f' & Hfj' & Efb).
assert (Hfin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (skipn 0 (cg_frames s)))).
{ apply (frames_blocks_in N (cg_frames s) _ j f' _ Hj Hfj'). rewrite Efb. left. reflexivity. }
cbn [skipn] in Hfin.
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPr|]. right. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Hf2 : In (fr_ptr f, FRAME_SIZE) (ablocks B ly2 S2)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]. right. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
assert (Dpf : pf + 1264 <= fr_ptr f \/ fr_ptr f + 40 <= pf).
{ pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc pf FILE_BLOCK (fr_ptr f) FRAME_SIZE HAR Hinpf Hfc ltac:(unfold FRAME_SIZE, FILE_BLOCK; intros X; injection X; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size FRAME_SIZE) with 40 in D. change (req_size FILE_BLOCK) with 1264 in D. clear - D. lia. }
assert (Dgf' : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfin. }
assert (Drf : cg_raw s + 48 <= fr_ptr f \/ fr_ptr f + 40 <= cg_raw s).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (cg_raw s, RAW_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPr) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. right. apply in_or_app. right. apply in_or_app. left. exact Hfin. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
lazymatch type of HTg with obj_at _ (mrestrict _ ?mm) _ _ _ =>
apply (obj_at_blk_kept (w_H Wc) (w_H W2) mm _ (fr_ptr f) LAY_Frame _ 40); [| exact lay_inside_Frame |] end.
+ apply (obj_at_kept _ _ (fr_ptr f) LAY_Frame _ 40 Hof lay_inside_Frame).
intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi Dgf' Hgh Hgceil Hf4096 Hfceil C1 C3; lia.
+ pose proof (blk_kept_call B _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fr_ptr f) FRAME_SIZE HJc2 Hfc Hf2) as Kf.
apply Kf. change (req_size FRAME_SIZE) with 40. apply (HnFb (fr_ptr f) 40 Hf4096); [clear - Drf; lia | clear - Dpf; lia]. }
split; [exact HOK |]. unfold fr_blocks. cbn [skipn app]. eapply Permutation_trans; [exact HPerm2|]. apply perm_skip. rewrite !app_assoc. apply Permutation_middle.
- unfold EV_RAWCLOSE. clear - Hk. lia.
-
split; [|split; [|split; [|split; [|split; [|split]]]]].
+ rewrite (CS 2%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
+ rewrite (CS 3%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q3'.
+ rewrite (CS 4%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). exact Q4'.
+ rewrite (CS 9%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q9. exact E32.
+ rewrite (CS 8%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q8. cbn [sv_denot]. rewrite E32u. reflexivity.
+ rewrite (CS 19%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q19.
exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)).
+ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)).
assert (Hr4 : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | [-> | ->]]];
((first [rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS) | rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS)]); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
- rewrite (CS 20%bv ltac:(unfold acallee_saved; rewrite bv_unsigned_BV; lia)). rewrite Q20. exact E38.
-
split; [exact HSINK2|]. split; [exact (mle_station MT S Sc S2 _ _ MLAW MLE MLEc)|]. split; [| exact HGC].
rewrite length_app. cbn [length]. clear - HROOM. lia.
Qed.
Theorem cl_BX_of_FR0 : CL_FR_stmtX B hw CTX path pf K MT XN 0 -> CL_B_stmtX B hw CTX path pf K MT XN.
Proof. intros H. exact (cl_B_okX (cl_RC_okX (cl_PF_okX (cl_FC_okX H)))). Qed.
End e.
End d.
End c.
