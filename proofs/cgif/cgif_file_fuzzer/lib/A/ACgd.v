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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgb ACgc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition af_lcxD3 : list YP09.chunk :=
[YP09.mkChunk 8 (CVal 8 (shq 46 0)); YP09.mkChunk 16 (CVal 8 (shq 23 0)); YP09.mkChunk 24 (CVal 8 (shq 46 26)); YP09.mkChunk 112 (CVal 8 (shq 23 8))].
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
Lemma af_newcfg_kept0 : forall (m m' : word -> option byte) nw lpal lpal' fattr fgen delay nlp tidx,
af_newcfg m nw lpal fattr fgen delay nlp tidx ->
(forall a, nw + 8 <= a < nw + 40 -> mbyte SEGS m' a = mbyte SEGS m a) ->
val_mem SEGS m' nw 8 lpal' ->
af_newcfg m' nw lpal' fattr fgen delay nlp tidx.
Proof.
intros m m' nw lpal lpal' fattr fgen delay nlp tidx (V0 & V16 & V20 & V24 & V26 & V28) HK V0'.
assert (T : forall a (n : nat) v, val_mem SEGS m a n v -> nw + 8 <= a -> a + Z.of_nat n <= nw + 40 -> val_mem SEGS m' a n v).
{ intros a n v Hv H1 H2 j Hj. rewrite (HK (a + Z.of_nat j)) by lia. exact (Hv j Hj). }
split; [exact V0'|]. split; [apply (T _ 4%nat _ V16); cbn; lia|]. split; [apply (T _ 4%nat _ V20); cbn; lia|].
split; [apply (T _ 2%nat _ V24); cbn; lia|]. split; [apply (T _ 2%nat _ V26); cbn; lia|].
intros H6. apply (T _ 1%nat _ (V28 H6)); cbn; lia.
Qed.
End e.
End d.
Lemma denot_3x : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = w64 (3 * v).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_mul_smallD; rewrite (U_atom E n v Hn), U_lit by lia; lia.
Qed.
Lemma U_mul3h16 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
U E (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) = 3 * v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext, U_lit, (U_atom E n v Hn) by lia.
change (Z.of_N 16) with 16. rewrite (Z.mod_small v (2 ^ 16)) by lia. change (Z.land 1 63) with 1. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (v * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_3xz : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 16 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SExt false 16 (SOff n 0)) (SLit 1)) (SExt false 16 (SOff n 0))) = w64 (3 * v).
Proof. intros E n v Hn Hv. rewrite denot_lit_U. unfold w64. f_equal. exact (U_mul3h16 E n v Hn Hv). Qed.
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
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Lemma val_mem_keptZ : forall (m m' : word -> option byte) a (n : nat) v,
val_mem SEGS m a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hv HK j Hj. rewrite (HK (a + Z.of_nat j)) by lia. exact (Hv j Hj). Qed.
End l.
End h.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section q.
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
Definition regsD3 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 32 0)) 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88)) 19 (SOff 46 26).
Definition af_nwr3 : YP09.region := YP09.mkRegion (Some 23%nat) 0 40 0 8 [].
Section u.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Hypothesis HTR : forall t, In t (af_sites B) -> In t (as_universe B).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma regsD3_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 19 = w64 (cfp + 26) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))) regsD3 regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R18 & R8 & R22) R9 R19 Hg0 Hgc Hc0 Hcc. unfold af_s1_at in R9.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R18 | rewrite unsigned_lit_small by lia; exact R8]
| rewrite E38; exact R22
| rewrite E46; rewrite unsigned_lit_small by lia; exact R19 ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_D3X : AF_E_stmtX K MT XN B -> AF_D3_stmtX K MT XN B.
Proof.
intros PE ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw nimg GPAL IMG LPAL gs gsF gs1
CX MID Hk HBB HR HR9 R24 R23 R19 R10 HL Hft Hi Hnone Hs1 HnwIn HniIn HNC HV8 XD.
destruct XD as [XDV XM].
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
assert (HTS : TADDFRAME_STK = 17664) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
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
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0) as [He | Hne]; [exfalso; clear - HN1 He; lia | reflexivity]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_imgP _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (HPn : Permutation (ablocks B lyc Sc) ((nw, FRAME_SIZE) :: (nimg, N) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ eapply Permutation_trans; [exact HPerm1|].
apply (Permutation_app_swap_app (cgif_blocks g s1 N) [(nw, FRAME_SIZE); (nimg, N)] (af_cblocks img N fattr lpa nlp rest)). }
assert (SEPw : forall b m, In (b, m) ((nimg, N) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> nw + 40 <= b \/ b + req_size m <= nw).
{ intros b m Hb. pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (nw, FRAME_SIZE) (b, m) _ HAR HPn Hb) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (HPi : Permutation (ablocks B lyc Sc) ((nimg, N) :: (nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest)).
{ eapply Permutation_trans; [exact HPn|]. apply perm_swap. }
assert (SEPi : forall b m, In (b, m) ((nw, FRAME_SIZE) :: cgif_blocks g s1 N ++ af_cblocks img N fattr lpa nlp rest) -> nimg + N <= b \/ b + req_size m <= nimg).
{ intros b m Hb. pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (nimg, N) (b, m) _ HAR HPi Hb) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite HrqN in D. clear - D. lia. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ nimg N HAR HniIn) as (Hm16 & Hm4096 & Hmceil & Hmh_ia & HmP & _). pose proof (proj1 Hmh_ia) as Hmh. rewrite HrqN in Hmceil. rewrite HrqN in HmP.
pose proof (blk_off_imgP _ _ _ _ _ _ nimg N HAR HniIn) as Hmh_img.
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof (SEPw g CGIF_SIZE ltac:(right; left; reflexivity)) as D. change (req_size CGIF_SIZE) with 96 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal.
pose proof (obj_at_nth SEGS _ _ _ _ 5 (26, 2%N) nlp HCF eq_refl eq_refl) as [_ Rnlp]. cbn [snd] in Rnlp.
assert (Hp3x : 0 <= 3 * nlp < 3 * 65536) by (clear - Rnlp; cbn in Rnlp; lia).
pose proof (req_size_pos (3 * nlp) ltac:(clear - Hp3x; lia)) as [Hrq1 Hrq2].
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 36%nat ltac:(unfold A_TEXT; lia)) as E36. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38.
pose proof (ES 42%nat ltac:(unfold A_TEXT; lia)) as E42. pose proof (ES 43%nat ltac:(unfold A_TEXT; lia)) as E43. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46.
pose proof (ES 47%nat ltac:(unfold A_TEXT; lia)) as E47. pose proof (ES 48%nat ltac:(unfold A_TEXT; lia)) as E48. pose proof (ES 49%nat ltac:(unfold A_TEXT; lia)) as E49. pose proof (ES 50%nat ltac:(unfold A_TEXT; lia)) as E50.
pose proof (ES 51%nat ltac:(unfold A_TEXT; lia)) as E51. pose proof (ES 52%nat ltac:(unfold A_TEXT; lia)) as E52. pose proof (ES 53%nat ltac:(unfold A_TEXT; lia)) as E53. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E36, E37, E38, E42, E43, E46, E47, E48, E49, E50, E51, E52, E53, E67.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E9 : ew E 10 = Z_to_bv 64 nlp) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
pose proof HL as (HLE & L8 & L16 & L24 & L112).
assert (HLX : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (sp0 - 224 - 0)) af_lcxD3).
{ assert (Dsh : forall n c v, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c <= 40 -> v + c <= alloc_ceiling ->
sv_denot E (shq n c) = Z_to_bv 64 (SB + (v + c) / 8) /\ 0 <= SB + (v + c) / 8 < 2 ^ (8 * Z.of_N 8)).
{ intros n c v Hn Hv Hc Hvc. split; [apply (denot_shx E n 38 c v SB Hn E38); unfold SB; clear - Hv Hc Hvc C1; lia|].
assert (Hd : 0 <= (v + c) / 8 < 2 ^ 61) by (clear - Hv Hc Hvc C1; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). clear - Hd. unfold SB. lia. }
unfold af_lcxD3. repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 ?e)) =>
lazymatch e with
| shq 46 ?c => destruct (Dsh 46%nat c cfp E46 ltac:(clear - Hcfp; lia) ltac:(clear; lia) ltac:(clear - Hcfp; lia)) as [Dd Dr];
apply (chunk_ok_val SEGS E _ (sp0 - 224 - 0) off 8 e _ Dd Dr); [cbn; clear; lia | replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption]
| shq 23 ?c => destruct (Dsh 23%nat c nw E23 ltac:(clear - Hn4096; lia) ltac:(clear; lia) ltac:(clear - Hnceil; lia)) as [Dd Dr];
apply (chunk_ok_val SEGS E _ (sp0 - 224 - 0) off 8 e _ Dd Dr); [cbn; clear; lia | replace (sp0 - 224 - 0 + off) with (sp0 - 224 + off) by (clear; lia); assumption]
end end. }
destruct (af_reseedxEX B TL LAWS AF_D3 regsD3 0 0 af_lcxD3 ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc regs1 memc mdc k s1 [(nw, FRAME_SIZE); (nimg, N)] []
(proj1 CX) MID Rsp HLE HLX ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsD3_ok regs regs1 g s1 cfp _ _ HR HR9 R19 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp))
ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
change (Eimg (Ereg regs1 _)) with E in HS, SHOK.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
{ awr_aX Usp E32u Hing HTS. }
rregD HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pmkst HS.
ppcs.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre lyc (aview SEGS (w_H Wc) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre lyc _ (sp0 - 224) (g + 88) []).
- apply achain_low; clear - Hgceil; lia.
- unfold spZ; rewrite Qsp, Usp; clear - Hceil Hslo HTS; lia.
- unfold s0Z; rewrite Qs0; cbn [sv_denot]; rewrite E32u; apply unsigned_lit_small; clear - HZg; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
assert (HliveC : blocks_bytes Sc + 3 * nlp <= LIVE_MAX) by (clear - HBB Hlive HN1 HFS Hp3x; unfold LIVE_ADDFRAME in Hlive; lia).
assert (XMOKn : mo_ok MT Sc (mo_malloc MT (3 * nlp))).
{ apply (af_xmtr_ok MT XN S Sc N _ _ _ MLAW XMOK (mo_malloc_nonneg MT MLAW (3 * nlp) ltac:(clear - Hp3x; lia)) XM). unfold af_need3. clear. lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub SEGS B LAWS Hsegs MT AMALLOC4 Wc (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPb g s N) ly S W mem md []
lyc Sc _ k (3 * nlp) (-224) (Z_to_bv 64 (BASE + 0xe58)) [] HJ);
[ rewrite Ra0; exact (denot_3x E 10 nlp E9 ltac:(clear - Rnlp; cbn in Rnlp; lia))
| unfold MALLOC_MAX; clear - Hp3x; lia
| exact HliveC
| unfold spZ; rewrite Qsp, Usp; lia
| reflexivity
| clear; lia
| rewrite HTS, Has; clear; lia
| rewrite Qgp, (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite Qtp, (EEo 4%nat 4%bv eq_refl); exact Rtp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| clear - Hnev Hev Hk HEVF HEVA; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite (proj2 (Z.eqb_neq _ _)) by (pose proof (pal_rt_below B TL) as Hrtb; clear - Hrtb PBASE; lia);
apply HTR; cbn [af_sites In]; repeat (first [left; reflexivity | right])
| exact XMOKn ] end. }
cbv beta. clear Ra0 Rra Qsp Qgp Qtp Qs0 CH.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & Hr4096X & EblX & HKX & MLE2 & HJf).
mresX Hr4096X EblX HKX Hres.
pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & HLY2 & _ & _ & _ & _ & Hnev2 & _).
destruct (mres_kept B lyc Sc Wc _ W2 mem2 ly2 S2 _ _ res (3 * nlp) Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 lyc Sc res (3 * nlp) _ _ HAR2 Hres) as Hrng.
pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & _ & _).
assert (EFA2 : frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct HLY2 as (_ & _ & _ & _ & _ & E6 & _). destruct HLY as (_ & _ & _ & _ & _ & E6' & _). rewrite E6, <- E6'. reflexivity. }
assert (SEPn : forall b m ii, In (b, m) (ablocks B lyc Sc) -> 0 <= ii < req_size m -> ~ (res <> 0 /\ res <= b + ii < res + req_size (3 * nlp))).
{ intros b m ii Hb Hii [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
pose proof (sep_tmp_entry B LAWS ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res (3 * nlp) b m HAR2 ltac:(rewrite Ebl; apply Permutation_refl) Hb) as D.
clear - D Hii Hin. lia. }
assert (HnewG : forall a, g + 0 <= a < g + 96 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (g + (a - g)) by (clear - PBASE PBLO; lia). apply (SEPn g CGIF_SIZE (a - g) Hing). change (req_size CGIF_SIZE) with 96. clear - Ha. lia. }
assert (HnewN : forall a, nw + 0 <= a < nw + 40 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (nw + (a - nw)) by (clear - PBASE PBLO; lia). apply (SEPn nw FRAME_SIZE (a - nw) HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha. lia. }
assert (HnewI : forall a, nimg <= a < nimg + N -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha. replace a with (nimg + (a - nimg)) by (clear - PBASE PBLO; lia). apply (SEPn nimg N (a - nimg) HniIn). rewrite HrqN. clear - Ha. lia. }
assert (HnewF : forall a, cfp + 0 <= a < cfp + 32 -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2; exact Hfin)) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin Hflo Hfhi. lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3; 4; 5]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | apply Forall_nil].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- eapply (region_kept_stack_aj SEGS B); [exact HK | exact HJ2 | exact Usp | clear; lia | rewrite HTS; clear; lia | clear; lia | cbn; clear; lia | cbn; clear; lia].
- lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | clear; lia] end.
- lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell1) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | clear; lia] end.
- eapply (region_kept_block_aj SEGS B); [exact HK | exact E32u | exact Hing | clear; lia | change (req_size CGIF_SIZE) with 96; clear; lia | clear; lia | exact HnewG].
- eapply (region_kept_frame_aj SEGS B); [exact HK | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia | exact Hfin | clear - Hflo; lia | clear - Hfhi; lia | clear; lia | exact HnewF]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. try (let Hx := fresh "HEIo" in rename HEI2 into Hx). assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 516 = Z_to_bv 64 res) by (rewrite HE2; change 516%nat with (512 + 4)%nat; rewrite (YN3v.ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Ha0).
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
assert (E49_2 : ew E2 49 = Z_to_bv 64 fattr) by (rewrite OLD2 by lia; exact E49).
assert (E9_2 : ew E2 10 = Z_to_bv 64 nlp) by (rewrite OLD2 by lia; exact E9).
assert (E67_2 : ew E2 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD2 by lia; exact E67).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 512)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD2 by exact Hn68; exact (EEo n rr Hn)).
assert (Kblk : forall b m, In (b, m) (ablocks B lyc Sc) -> blk_kept (w_H Wc) (w_H W2) memc mem2 b (req_size m)).
{ intros b m Hb ii Hii. pose proof HK as (_ & K2 & _). etransitivity; [exact (K2 b m ii Hb Hii (SEPn b m ii Hb Hii))|].
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & Hb4096 & Hbceil & _). apply UN1; clear - Hii Hb4096 Hbceil C1 Hceil Hslo HTS; lia. }
assert (HT2 : xcgif_at SEGS wfn path hw pf (mrestrict (w_H W2) mem2) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- exact (obj_at_blk_kept _ _ _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF (Kblk g CGIF_SIZE Hing)).
- apply (obj_at_blk_kept _ _ _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). apply (Kblk (cg_raw s1) RAW_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. right. left. reflexivity.
- intros f Hfi. apply (obj_at_blk_kept _ _ _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). apply (Kblk (fr_ptr f) FRAME_SIZE).
eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfi). }
assert (HFR2 : af_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (af_frame_kept _ _ sp0 regs HFR). intros a Ha. pose proof HK as (K1 & _). apply (mbyte_of_aview SEGS).
etransitivity; [apply (K1 a); clear - Ha Hceil Hslo Hshi H47 HTS Has C1; lia|]. apply UN1; clear - Ha Hceil Hslo Hshi H47 HTS C1; lia. }
assert (HNC2 : af_newcfg (mrestrict (w_H W2) mem2) nw lpal fattr fgen delay nlp tidx).
{ apply (af_newcfg_kept _ _ nw lpal fattr fgen delay nlp tidx HNC). intros a Ha Hn. apply (mbyte_of_aview SEGS).
replace a with (nw + (a - nw)) by (clear - PBASE PBLO; lia). apply (Kblk nw FRAME_SIZE HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Ha; lia. }
assert (HV8_2 : val_mem SEGS (mrestrict (w_H W2) mem2) (nw + 8) 8 nimg).
{ apply (val_mem_keptZ _ _ _ 8%nat nimg HV8). intros x Hx. apply (mbyte_of_aview SEGS).
replace x with (nw + (x - nw)) by (clear - PBASE PBLO; lia). apply (Kblk nw FRAME_SIZE HnwIn). rewrite HFS. change (req_size 40) with 40. clear - Hx; cbn in Hx; lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
pose proof (HBin _ HnwIn) as HnwIn2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR2 HnwIn2) as (_ & _ & _ & _ & HnP2 & _). rewrite HFS in HnP2. change (req_size 40) with 40 in HnP2.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw2; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw2; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ af_nwr3 HS eq_refl
ltac:(unfold region_ok, af_nwr3; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw2; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP2 (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_nwr3; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw2, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ af_nwr3 HS eq_refl
ltac:(unfold region_ok, af_nwr3; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw2; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP2 (nw + o) ltac:(clear - Ho; lia))) | apply Forall_nil])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, af_nwr3; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw2, Usp2, E32u2, E46_2, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH23 E2 (mrestrict (w_H W2) mem2)).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ2 HAR0 HPerm HFO Hpfcb) as (_ & _ & HRA2).
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 E2 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE HAR2 (HBin _ HnwIn)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw2.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (Anw : forall blc ii lyq ownq, In (nw, FRAME_SIZE) blc -> 0 <= ii < req_size 40 -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (nw + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (proj2 (HnewX _ (or_introl eq_refl)) blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
pose proof (HBin _ HniIn) as HniIn2.
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{   exfalso. clear - Hres0 Hr4096X. lia. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
prreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres.
cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Rres. rewrite ?ew_ewset_other in Rres by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Rres.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 516%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2 ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E2r, unsigned_lit_small by lia; change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1 Hrq1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 516%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2 ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E2r, unsigned_lit_small by lia; change (2 ^ 4) with 16; clear - Hr4096 HrHi HrCeil Hr16 C1 Hrq1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (3 * nlp) HAR2 HrIn) as (_ & _ & _ & _ & HrP & _).
assert (Bres : bv_unsigned (ew E2 516) = res) by (rewrite E2r; apply unsigned_lit_small; lia).
pose proof (aftok_new_block SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) HJ HAR2 Ebl ltac:(clear - Hp3x; lia)) as Tnew.
assert (Anew : forall blc ii lyq ownq, In (res, 3 * nlp) blc -> 0 <= ii < req_size (3 * nlp) -> awr_byte TADDFRAME_STK sp0 (FPb g s N) (ablocks B ly S) blc lyq ownq (res + ii)).
{ intros blc ii lyq ownq Hbl Hii. exact (awr_new_block_any SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) blc ii lyq ownq HJ HAR2 Ebl ltac:(clear - Hp3x; lia) Hbl Hii). }
assert (HpalC : In (lpa, 3 * nlp) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. right. apply in_app_iff. right. right.
unfold af_cblocks. apply in_app_iff. left. destruct (Z.land fattr 1 =? 0) eqn:Hb; [exfalso; apply Hft; apply Z.eqb_eq; exact Hb | left; reflexivity]. }
pose proof (HBin _ HpalC) as Hpal2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) HAR2 Hpal2) as (_ & Hi4096 & Hiceil & Hih_ia & HiP & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR2 Hpal2) as Hih_img.
assert (Dri : res + req_size (3 * nlp) <= lpa \/ lpa + req_size (3 * nlp) <= res).
{ pose proof (SEPn lpa (3 * nlp) 0 HpalC ltac:(clear - Hrq1; lia)) as D1. pose proof (SEPn lpa (3 * nlp) (req_size (3 * nlp) - 1) HpalC ltac:(clear - Hrq1; lia)) as D2.
clear - D1 D2 Hr4096 Hrq1. lia. }
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK RBspanA.
{ awr_xX Usp2 E32u2 ltac:(exact (HBin _ Hing)) HTS Bnw2 Anw HnwIn2. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp2, ?E32u2, ?Bnw2 in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2b & _ & Kgot2b & _). rewrite HBgot, HBcell in Kgot2b. rewrite HBcell in Kcell2b.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lpa (3 * nlp) (proj1 HJ2) Hpal2) as (_ & _ & _ & _ & HiP0 & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. rregD HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
pmkst HS.
change (Z_to_bv 64 333176) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY _ (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPb g s N) ly S W mem md []
ly2 S2 _ (k + 1) res lpa (3 * nlp) (-224) (Z_to_bv 64 (BASE + 0xe9c)) HJ2);
[ rewrite Ra0; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E2r
| rewrite Ra1; cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E47_2; unfold w64; rewrite Hlpa; reflexivity
|
rewrite Ra2; rewrite denot_lit_U; unfold w64; f_equal;
lazymatch goal with |- U ?Ex _ = _ =>
exact (U_mul3h16 Ex 52 nlp ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite OLD2 by (clear - PBASE PBLO; lia); exact E52) ltac:(clear - Rnlp; cbn in Rnlp; lia)) end
| clear - Hp3x; lia | clear - Hr4096; lia | clear - HrCeil Hrq1 C1 Hrq2; lia
| unfold spZ; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; lia
| reflexivity
| clear; lia
| rewrite HTS; unfold ESTACK; clear; lia
| rewrite Qgp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 3%nat 3%bv eq_refl ltac:(clear - PBASE PBLO; lia)); exact Rgp
| rewrite Qtp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (EEo2 4%nat 4%bv eq_refl ltac:(clear - PBASE PBLO; lia)); exact Rtp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| intros a Ha; split; [replace a with (res + (a - res)) by (clear - PBASE PBLO; lia); apply Anew; [exact HrIn | clear - Ha Hrq2; lia] | unfold ESTACK; intro; clear - Ha H Hr4096 HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia]
| apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2; lia
| apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2; lia
| intros Hn0; apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 _ _ res (3 * nlp) _ _ (proj1 HJ2) HrIn); clear - Hrq2 Hn0; lia
| split; [clear - Hi4096; lia|]; split; [clear - Hiceil C1 Hrq2; lia|]; split;
[ intros a Ha; split; [| unfold spZ, ESTACK; rewrite Qsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp2; intro; clear - Ha H Hi4096 Hiceil Hceil Hslo HTS C1 Hrq2; lia];
apply (aview_some_of_apresent SEGS); apply (proj1 (HiP0 a ltac:(clear - Ha Hrq2; lia)))
| split; [clear - Dri Hrq2; lia|];
split; [apply (amem_range_of_block SEGS B LAWS ly2 S2 W2 _ _ lpa (3 * nlp) _ _ (proj1 HJ2) Hpal2); clear - Hrq2; lia|]; split;
[ apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 _ _ lpa (3 * nlp) _ _ (proj1 HJ2) Hpal2); clear - Hrq2; lia
| intros Hn0; apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 _ _ lpa (3 * nlp) _ _ (proj1 HJ2) Hpal2); clear - Hrq2 Hn0; lia ] ] ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & HSM3).
replace (sp0 + -224 - ESTACK) with (sp0 - 224 - ESTACK) in Hfr3 by (clear - PBASE PBLO; lia). replace (sp0 + -224) with (sp0 - 224) in Hfr3 by (clear - PBASE PBLO; lia).
assert (HES : ESTACK = 4096) by reflexivity.
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa af_SH23 ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa af_SH23 ss)  end in
jafter_call_keep_hi HS K regs3 (mrestrict (w_H W2) mem3) HP3 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell3 & _ & Kgot3 & _). rewrite HBgot, HBcell in Kgot3. rewrite HBcell in Kcell3.
cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil];
first
[ eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact Bnw2 | exact Usp2 | exact E32u2 | rewrite E46_2; apply unsigned_lit_small; clear - Hcfp C1; lia]
| intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr3;
[ clear - Ha Hn4096 Hnceil HZg Hcfp HrCeil Hrq1 Hceil Hslo Hshi H47 HTS C1; lia
| intros X;
first [ pose proof (HnewN a) as D; clear - Ha X D Hr4096 Hrq2; lia
| pose proof (HnewG a) as D; clear - Ha X D Hr4096 Hrq2; lia
| pose proof (HnewF a) as D; clear - Ha X D Hr4096 Hrq2; lia
| clear - Ha X HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia ]
| rewrite HES; clear - Ha Hn4096 Hnceil HZg Hcfp Hgceil Hceil Hslo Hshi H47 HTS C1; lia ]
| exact Hpres3 ]
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2b) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3) | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2b) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3) | clear; lia] end
| match goal with |- ?gg => idtac "KEPTFAIL" gg end ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => set (E3 := Ex) in HS | st_ok _ ?Ex _ _ => set (E3 := Ex) in HS  end. try (let Hx := fresh "HEIo" in rename HEI3 into Hx). assert (HEI3 : img_env VAL A_LIM E3) by hei_prove.
assert (OLD3 : forall n, (n < 528)%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; rewrite YN3v.ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (Usp3 : bv_unsigned (ew E3 2) = sp0 - 224) by (rewrite OLD3 by lia; exact Usp2).
assert (E32u3 : bv_unsigned (ew E3 32) = g) by (rewrite OLD3 by lia; exact E32u2).
assert (E32_3 : ew E3 32 = Z_to_bv 64 g) by (rewrite OLD3 by lia; exact E32_2).
assert (E23_3 : ew E3 23 = Z_to_bv 64 nw) by (rewrite OLD3 by lia; exact E23_2).
assert (Bnw3 : bv_unsigned (ew E3 23) = nw) by (rewrite OLD3 by lia; exact Bnw2).
assert (E38_3 : ew E3 38 = Z_to_bv 64 SB) by (rewrite OLD3 by lia; exact E38_2).
assert (E46_3 : ew E3 46 = Z_to_bv 64 cfp) by (rewrite OLD3 by lia; exact E46_2).
assert (E47_3 : ew E3 47 = Z_to_bv 64 lpal) by (rewrite OLD3 by lia; exact E47_2).
assert (E67_3 : ew E3 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite OLD3 by lia; exact E67_2).
assert (E72_3 : ew E3 516 = Z_to_bv 64 res) by (rewrite OLD3 by lia; exact E2r).
assert (Bres3 : bv_unsigned (ew E3 516) = res) by (rewrite OLD3 by lia; exact Bres).
assert (EEo3 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 512)%nat -> ew E3 n = getr regs1 rr) by (intros n rr Hn Hn68; rewrite OLD3 by lia; exact (EEo2 n rr Hn Hn68)).
clear SHOK. assert (SHOK : sh_ok SEGS Bxa af_SH23 E3 (mrestrict (w_H W2) mem3)).
{ assert (HRA3 : range_addressable (aview SEGS (w_H W2) mem3) SHADOW_OFF cfp 32).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] ly2 S2 W2 _ _ _ g s N _ cfp 32 HJ3 HAR0 HPerm HFO Hpfcb) as (_ & _ & HRA3). exact HRA3. }
unfold sh_ok, af_SH23, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ3) (HBin _ Hing)).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u3.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W2) mem3 E3 Bxa 46 cfp 32 cfp 0 32 HRA3).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + shent_range_app.
- apply (shent_ok_of_block SEGS B LAWS ly2 S2 W2 mem3 md3 E3 Bxa 23 nw FRAME_SIZE 0 FRAME_SIZE (proj1 HJ3) HnwIn2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38_3, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact Bnw3.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (AGx : forall n, (n < 528)%nat -> ew EL n = ew E2 n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; apply OLD3; exact Hn).
assert (K23 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) -> ~ (res <= a < res + 3 * nlp) -> ~ (sp0 - 224 - ESTACK <= a < sp0 - 224) ->
aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hn1 Hn2 Hn3. etransitivity; [exact (Hfr3 a Ha Hn2 Hn3)|]. exact (UN2 a Ha Hn1). }
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk ltac:(intros a Ha; cbv beta in Ha; left; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn | st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 1 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
cbn [ms_mem restrict mkst] in HR0, HRn  end.
assert (X32 : ew EL 32 = Z_to_bv 64 g) by (rewrite AGx by lia; exact E32_2).
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u2).
assert (X38 : ew EL 38 = Z_to_bv 64 SB) by (rewrite AGx by lia; exact E38_2).
assert (X46 : ew EL 46 = Z_to_bv 64 cfp) by (rewrite AGx by lia; exact E46_2).
assert (X47 : ew EL 47 = Z_to_bv 64 lpal) by (rewrite AGx by lia; exact E47_2).
assert (X67 : ew EL 67 = Z_to_bv 64 (if Z.land fattr 4 =? 0 then 1 else 0)) by (rewrite AGx by lia; exact E67_2).
assert (X23 : ew EL 23 = Z_to_bv 64 nw) by (rewrite AGx by lia; exact E23_2).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw2).
assert (X72 : ew EL 516 = Z_to_bv 64 res) by (rewrite AGx by lia; exact E2r).
assert (X72u : bv_unsigned (ew EL 516) = res) by (rewrite AGx by lia; exact Bres).
assert (Xsp : bv_unsigned (ew EL 2) = sp0 - 224) by (rewrite AGx by lia; exact Usp2).
assert (HX1 : (if Z.land fattr 1 =? 0 then [] else [(res, 3 * nlp)]) = [(res, 3 * nlp)] /\ (if Z.land fattr 1 =? 0 then lpal else res) = res).
{ destruct (Z.land fattr 1 =? 0) eqn:Hb; [exfalso; apply Hft; apply Z.eqb_eq; exact Hb | split; reflexivity]. }
destruct HX1 as [HX1 HX2].
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
pose proof (af_xmtr_step MT XN S Sc S2 N _ _ _ 0 0 MLAW (mo_malloc_nonneg MT MLAW (3 * nlp) ltac:(clear - Hp3x; lia)) XM MLE2 ltac:(unfold af_need3; clear; lia) ltac:(unfold af_need3; clear; lia)) as XM2.
af_xunz2 UN1 B LAWS lyc Sc Wc memc mdc g s1 N [(nw, FRAME_SIZE)] [(nimg, N)] ly sp0 HAR HPerm1 Hstk HTS HnwIn XZb1 XZi1.
lazymatch type of HJf with ajournal _ _ _ _ _ _ _ _ _ ?mdq _ _ _ _ _ _ _ =>
pose proof (af_xdv_unz B K AIL (w_H Wc) memc _ mdc mdq s s1 N i nimg lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF [(nimg, N)] _ _ UN1 XZb1 XZi1 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XDV) as XDV1 end.
pose proof (af_xdv_subj B K AIL _ _ lyc Sc Wc _ _ _ ly2 S2 W2 mem2 md2 _ g s s1 N i nimg lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF _ _ HJf HPerm1 HBin Hpfcb
(or_intror (or_introl eq_refl)) ltac:(intros Hz; right; right; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) Hlen1 XDV1) as XDV2.
assert (HPerm2 : Permutation (ablocks B ly2 S2) (cgif_blocks g s1 N ++ ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)]) ++ af_cblocks img N fattr lpa nlp rest))
by (rewrite Ebl; exact (perm_new_own _ _ _ _ (res, 3 * nlp) HPerm1)).
af_xunz3 UN2 B LAWS ly2 S2 W2 mem2 md2 g s1 N ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)]) [(nw, FRAME_SIZE)] [(nimg, N); (res, 3 * nlp)] ly sp0 HAR2 HPerm2
(Permutation_refl ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)])) Hstk HTS HnwIn XZb2 XZi2.
lazymatch type of HSM3 with same_but_materialized ?mdq _ =>
pose proof (af_xdv_unz B K AIL (w_H W2) mem2 _ md2 mdq s s1 N i nimg lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF [(nimg, N); (res, 3 * nlp)] _ _ UN2 XZb2 XZi2 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; right; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) eq_refl eq_refl Hlen1 XDV2) as XDV3 end.
assert (UN3 : forall a, 0 <= a < 2 ^ 64 -> ~ ((res <= a < res + 3 * nlp) \/ (sp0 - 224 - ESTACK <= a < sp0 - 224)) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) (ms_mem ms0) a)
by (intros a Ha Hn; apply (Hfr3 a Ha); intros Hq; apply Hn; [left | right]; exact Hq).
destruct (af_xfoot_unz3 B LAWS ly2 S2 W2 mem2 md2 g s1 N ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)]) [(nw, FRAME_SIZE); (res, 3 * nlp)] [(nimg, N)] _ ly sp0
(fun a => (res <= a < res + 3 * nlp) \/ (sp0 - 224 - ESTACK <= a < sp0 - 224)) HAR2 HPerm2
ltac:(cbn [app]; apply perm_skip; apply perm_swap) Hstk
ltac:(intros a [Ha | Ha]; [right; exists res, (3 * nlp); split; [apply in_app_iff; right; right; left; reflexivity | clear - Ha Hrq2; lia] | left; rewrite HTS; unfold ESTACK in Ha; clear - Ha; lia])) as [XZb3 XZi3].
pose proof (same_but_materialized_frame _ _ HSM3) as (_ & _ & _ & _ & _ & _ & _ & _ & Qfds3 & _ & _ & Qfs3 & _).
pose proof (af_xdv_unz B K AIL (w_H W2) _ mem3 _ md3 s s1 N i nimg lpa fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF [(nimg, N)] _ _ UN3 XZb3 XZi3 Hpfcb
(or_introl eq_refl) ltac:(intros Hz; right; right; destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | left; reflexivity]) Qfs3 Qfds3 Hlen1 XDV3) as XDV4.
assert (XPAL4 : Z.land fattr 1 <> 0 -> garr8 SEGS (mrestrict (w_H W2) mem3) res LPAL).
{ intros Hz. pose proof XDV3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XGL & _). destruct (XGL Hz) as [XG XGlen].
apply (garr8_aview SEGS (w_H W2) (w_H W2) (ms_mem ms0) mem3 lpa res LPAL); [| exact XG].
intros j Hj. apply Heff3. rewrite XGlen in Hj. exact Hj. }
pose proof (af_xdv_set_pal K _ _ s s1 N i nimg lpa res fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF XDV4 XPAL4) as XDV5.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PE ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ly2 S2 W2 rg mm mdq (k + 1) s1 i nw nimg res GPAL IMG LPAL gs gsF gs1 CX) end.
+
split; [exact HJ3|]. split; [clear - Hk0; lia|].
split; [apply (af_frame_kept _ _ sp0 regs HFR2); intros a Ha; apply (mbyte_of_aview SEGS); apply K23;
[clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | clear - Ha HrCeil Hrq1 Hceil Hslo HTS C1 Hrq2; lia | rewrite HES; clear - Ha; lia] |].
split.
{ pose proof HT2 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros ii Hii. apply (mbyte_of_aview SEGS). apply K23;
[clear - Hii HZg; lia | clear - Hii HZg Dgn; lia | pose proof (HnewG (g + ii)) as D; clear - Hii D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hgceil Hceil Hslo HTS C1; lia].
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & _ & Hrc & _). change (req_size RAW_SIZE) with 48 in Hrc.
pose proof (SEPn _ _ ii Hinr ltac:(change (req_size RAW_SIZE) with 48; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; right; left; reflexivity)) as Dw. change (req_size RAW_SIZE) with 48 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hrc Hceil Hslo HTS C1; lia].
- intros f Hfi. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZf f ii Hfi Hii) as [Hb Hn].
assert (Hfb' : In (fr_ptr f, FRAME_SIZE) (cgif_blocks g s1 N)) by exact (af_frame_in_blocks g s1 N f Hfi).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact Hfb').
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & _ & Hfc & _). rewrite HFS in Hfc. change (req_size 40) with 40 in Hfc.
pose proof (SEPn _ _ ii Hfb ltac:(rewrite HFS; change (req_size 40) with 40; clear - Hii; lia)) as D.
pose proof (SEPw _ _ ltac:(right; apply in_app_iff; left; exact Hfb')) as Dw. rewrite HFS in Dw. change (req_size 40) with 40 in Dw.
apply K23; [exact Hb | clear - Hn Dw Hii; lia | clear - D Hr4096 Hrq2; lia | rewrite HES; clear - Hii Hfc Hceil Hslo HTS C1; lia]. }
split; [exact HOK|]. split.
{ unfold af_newblocks. rewrite HX1, Ebl.
eapply Permutation_trans; [apply Permutation_app; [exact HPerm1 | apply Permutation_refl]|].
rewrite <- !app_assoc. apply Permutation_app_head. cbn [app].
apply perm_skip. apply perm_skip. apply Permutation_sym. apply (Permutation_cons_append (af_cblocks img N fattr lpa nlp rest) (res, 3 * nlp)). }
split; [exact Hnew|]. unfold af_newblocks. rewrite HX1.
intros b [<- | [<- | [<- | []]]]; [exact (HnewX _ (or_introl eq_refl)) | exact (HnewX _ (or_intror (or_introl eq_refl))) |].
split; [exact Tnew | intros blc lyq ownq ii Hbl Hii; exact (Anew blc ii lyq ownq Hbl Hii)].
+ clear - Hk HEVF; lia.
+ unfold af_regs_at; change (spZ regs) with sp0.
split; [|split; [|split; [|split; [|split]]]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
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
let R := fresh "R" in prreg HS (24%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, (AGx 24%nat ltac:(clear - PBASE PBLO; lia)), (EEo2 24%nat 24%bv eq_refl ltac:(clear - PBASE PBLO; lia)); exact R24.
+ let R := fresh "R" in prreg HS (23%bv : bv 5) R; rewrite R; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact X23.
+
unfold af_locsE; change (spZ regs) with sp0;
repeat match goal with |- _ /\ _ => split end; locvD2 HR0 sp0 X32 X32u X38 X46 X67 X23 X23u Xsp Hcfp HZg Hgceil Hn4096 Hnceil C1.
+ clear - Hft; left; exact Hft.
+ exact Hi.
+ exact Hnone.
+ exact Hs1.
+ exact HnwIn2.
+
rewrite HX2.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 0 8 (SOff 516 0) res HRn X23u ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite X72, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hr4096 HrCeil Hrq1 C1 Hrq2; lia) ltac:(cbn; lia)) as V0 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V0. rewrite Z.add_0_r in V0.
apply (af_newcfg_kept0 _ _ nw lpal res fattr fgen delay nlp tidx HNC2); [| exact V0].
intros a Ha. apply (mbyte_of_aview SEGS). apply K23;
[clear - Ha Hn4096 Hnceil C1; lia | clear - Ha Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN a) as D; clear - Ha D Hr4096 Hrq2; lia | rewrite HES; clear - Ha Hnceil Hceil Hslo HTS C1; lia].
+
apply (val_mem_keptZ _ _ _ 8%nat nimg HV8_2). intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS). apply K23;
[clear - Hx Hn4096 Hnceil C1; lia | clear - Hx Hnceil Hceil Hslo HTS C1; lia | pose proof (HnewN x) as D; clear - Hx D Hr4096 Hrq2; lia | rewrite HES; clear - Hx Hnceil Hceil Hslo HTS C1; lia].
+
assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (nw <= a < nw + 8)) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem3 a) by (intros; reflexivity).
af_xunz3 UN4 B LAWS ly2 S2 W2 mem2 md2 g s1 N ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)]) [(nw, FRAME_SIZE)] [(nimg, N); (res, 3 * nlp)] ly sp0 HAR2 HPerm2
(Permutation_refl ([(nw, FRAME_SIZE); (nimg, N)] ++ [(res, 3 * nlp)])) Hstk HTS HnwIn XZb4 XZi4.
apply af_xd_e1. split; [| exact XM2].
exact (af_xdv_unz B K AIL (w_H W2) mem3 _ md3 _ s s1 N i nimg res fattr fgen delay nlp tidx GPAL IMG LPAL gs gs1 gsF [(nimg, N); (res, 3 * nlp)] _ _ UN4 XZb4 XZi4 Hpfcb
(or_introl eq_refl) ltac:(intros _; right; left; reflexivity) eq_refl eq_refl Hlen1 XDV5).
Qed.
End u.
End q.
End p.
