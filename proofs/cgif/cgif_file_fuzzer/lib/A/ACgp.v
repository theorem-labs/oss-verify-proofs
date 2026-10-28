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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs.
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
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition regsX : list sv := Eval vm_compute in sr_set sr_atoms 8 (SOff 32 88).
Section h.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma regsX_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_ret B regs regs1 g -> 0 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))) regsX regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R8) Hg0 Hgc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; rewrite unsigned_lit_small by lia; exact R8 ]
| ]); try (destruct Hr; fail).
Qed.
Local Ltac mid_facts CX MID :=
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive);
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK);
lazymatch type of HPerm with Permutation _ (_ ++ ?cb) => assert (Hpfcb : In (pf, FILE_BLOCK) cb) by (right; apply in_app_iff; right; exact Hpfr) end;
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew);
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
Lemma af_RETX : AF_RET_stmtX K MT XN B.
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 GPAL IMG LPAL gs gsF CX MID Hk HR XR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
mid_facts CX MID.
pose proof HR as (Rsp & Rgp & Rtp & R8).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seedX B TL LAWS AF_RET regsX 0 true [] (cg_ihead s1) 0 0 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsX_ok regs regs1 g s1 cfp _ _ HR ltac:(lia) Hgceil) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)) as [HS SHOK].
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38.
assert (ESV : forall j (r : bv 5), nth_error af_saved j = Some (bv_unsigned r) -> ew E (54 + j) = getr regs r).
{ intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as Hr; lazymatch goal with |- ew _ ?m = _ => rewrite (ES m ltac:(clear; cbv; lia)) end;
cbn [Nat.sub Nat.add nth af_extra af_saved map app firstn repeat]; rewrite Hr, Z_to_bv_bv_unsigned; reflexivity|]).
exfalso. clear - Hj. do 8 (destruct j as [|j]; [discriminate Hj|]). cbn in Hj. destruct j; discriminate Hj. }
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E37, E38.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth SEGS _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
{ awr_aX Usp E32u Hing HTS. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN.
cbv beta in UN.
clear HF HFr HG.
prreg HS (1%bv : bv 5) R1.
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold af_postX.
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyc, Sc, rg, mm, mdx end.
split; [rewrite R1; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; change 54%nat with (54 + 0)%nat; rewrite (ESV 0%nat (1%bv : bv 5) eq_refl); rewrite Hra; reflexivity|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k SEGS _); [apply (ajournal_materialize SEGS _ LAWS Hsegs); exact HJ | exact Hk]|].
split.
{ apply aregs_preserved_eqs;
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ lazymatch goal with |- ew _ ?n = getr _ ?rr => let j := eval vm_compute in (n - 54)%nat in change n with (54 + j)%nat; exact (ESV j rr eq_refl) end
| rewrite Usp; unfold sp0, spZ; rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)) at 2; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl), Rgp, Hgp; reflexivity
| rewrite (EEo 4%nat 4%bv eq_refl), Rtp, Htp; reflexivity
| match goal with |- ?gg => idtac "AREGS-FAIL" gg end ]). }
exists s1.
assert (HT2 : xcgif_at SEGS wfn path hw pf (mrestrict (w_H Wc) (ms_mem ms)) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros i Hi. apply (mbyte_of_aview SEGS). apply UN; clear - Hi HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS).
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
apply UN; clear - Hi Hr4096 Hrceil C1 Hceil Hslo HTS; lia.
- intros f Hfin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfin). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply UN; clear - Hi Hf4096 Hfceil C1 Hceil Hslo HTS; lia. }
split; [exact HT2|]. split; [exact HWF1|]. split; [exact HW1|]. split; [exact HH1|]. split; [exact Hattr1|]. split; [exact Hraw1|].
split; [exact Hgen1|]. split; [exact Hngp1|]. split; [exact Hpal1|].
split; [exact HPerm1|].
split.
{ intros b Hb. destruct (Hnew b Hb) as [Hold | [Htok Hwr]].
- split.
+ intros _ i Hi. unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. rewrite (surjective_pairing b) in Hold. exact (inFP_ablocks_fp _ _ _ i Hold Hi).
+ intros blc i Hbl Hi. right. left. split.
* unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. rewrite (surjective_pairing b) in Hold. exact (inFP_ablocks_fp _ _ _ i Hold Hi).
* exists (fst b), (snd b). split; [rewrite <- surjective_pairing; exact Hbl | lia].
- split; [exact Htok | intros blc i Hbl Hi; exact (Hwr blc lyc [] i Hbl Hi)]. }
destruct XR as (XREL & XOUT & (acc & Hacc0 & XMLE & _ & HaccN)).
pose proof (af_xfoot_unz B LAWS lyc Sc Wc memc mdc g s1 N [] _ ly sp0 (fun a => sp0 - 224 <= a < sp0 - 104) HAR HPerm1 Hstk
ltac:(intros a Ha; left; cbv beta in Ha; clear - Ha HTS; lia)) as [XZb XZi].
split; [| split; [exact XOUT | exact (mle_weaken MT S Sc acc (xn_addframe XN N) MLAW XMLE ltac:(clear - HaccN; lia))]].
apply (cgif_relA_unz B K AIL (w_H Wc) memc (ms_mem ms) mdc _ s1 N _ GPAL gsF _ UN XZb XZi Hpfcb HWF1 eq_refl eq_refl XREL).
Qed.
Lemma cl_set_cur_frames : forall s1 c, cg_frames (cl_set_cur s1 c) = cg_frames s1. Proof. reflexivity. Qed.
Lemma af_RETCX : AF_RET_stmtX K MT XN B -> AF_RETC_stmtX K MT XN B.
Proof.
intros PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 v GPAL IMG LPAL gs gsF CX MID Hk HR Hv XRC.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
mid_facts CX MID.
pose proof HR as (Rsp & Rgp & Rtp & R8).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seedX B TL LAWS AF_RETC regsX 0 true [] (cg_ihead s1) 88 92 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsX_ok regs regs1 g s1 cfp _ _ HR ltac:(lia) Hgceil) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)) as [HS SHOK].
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E38.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_RET.
{ awr_aX Usp E32u Hing HTS. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear - Ha HTS; lia)) as [HZr HZf]. cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4; cbn [ms_mem restrict mkst] in HR4 | st_ok _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4; cbn [ms_mem restrict mkst] in HR4  end.
lazymatch type of HR4 with region_ok _ ?Ex _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YP09.mkChunk 88 (CVal 4 ?e88)] =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi 88 4%N e88 HR4 E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc; cbn [sv_denot] in Vc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Vc;
rewrite (EEo 23%nat 23%bv eq_refl) in Vc;     change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vc; rewrite Hv in Vc end end.
assert (Rv : 0 <= v < 2 ^ 32) by (rewrite <- Hv; apply Z.mod_pos_bound; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 v) GPAL IMG LPAL gs gsF CX) end.
-
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HZg Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_cgif_setcurX SEGS path hw pf _ _ g s1 v Ho); [| exact Vc | exact Rv].
intros i Hi Hni. apply (mbyte_of_aview SEGS). apply UN; [clear - Hi HZg; lia | clear - Hi Hni HZg; lia].
- cbn [cg_raw cl_set_cur]. apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview SEGS). destruct (HZr i Hi) as [Hb Hn]. exact (UN _ Hb Hn).
- rewrite cl_set_cur_frames. intros f Hfin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview SEGS).
destruct (HZf f i Hfin Hi) as [Hb Hn]. exact (UN _ Hb Hn). }
split; [exact HOK|]. split; [exact HPerm1 | exact Hnew].
- exact Hk.
- unfold af_regs_ret; change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E32 | exact E38 | rewrite E32u; reflexivity
| rewrite (EEo 2%nat 2%bv eq_refl); exact Rsp | rewrite (EEo 3%nat 3%bv eq_refl); exact Rgp | rewrite (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "RETC-REG-FAIL" gg end ]).
-
pose proof (af_xretc_ret K MT XN S Sc _ _ s1 N GPAL gs gsF v XRC) as (XREL & XOUT & XM).
pose proof (af_xfoot_unz B LAWS lyc Sc Wc memc mdc g s1 N [] _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha | Ha]; [left; clear - Ha HTS; lia | right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]])) as [XZb XZi].
split; [| split; [exact XOUT | exact XM]].
apply (cgif_relA_unz B K AIL (w_H Wc) memc _ mdc _ (cl_set_cur s1 v) N _ GPAL gsF _ UN XZb XZi Hpfcb HWF1 eq_refl eq_refl XREL).
Qed.
End h.
End e.
End d.
