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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0 ACgy ACgv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgb ACgc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
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
Definition regsE3 : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff 32 88)) 22 (SOff 38 0)) 9 (shq 32 88)) 16 (SOff 46 0)) 10 (SOff 23 33)) 13 (shq 23 33).
Definition af_nwrE : YP09.region := YP09.mkRegion (Some 23%nat) 0 40 33 34 [].
Section l.
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
Lemma regsE3_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more nw,
af_regs_at0 B regs regs1 -> getr regs1 8 = w64 (g + 88) -> getr regs1 22 = w64 SB -> af_s1_at regs1 g -> getr regs1 16 = w64 cfp ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= nw -> nw + 40 <= alloc_ceiling ->
regs_ok (Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))) regsE3 regs1.
Proof.
intros regs regs1 g s1 cfp cf more nw (R2 & R3 & R4) R8 R22 R9s R9 R23 R10 R13 Hg0 Hgc Hc0 Hcc Hn0 Hnc. unfold af_s1_at in R9s.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs1 (af_extra regs g s1 cfp cf more))). try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
assert (E46 : ew E 46 = Z_to_bv 64 cfp) by (subst E; change 46%nat with (32 + 14)%nat; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs1 _ 14); reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 23 38 33 nw SB E23 E38) by (unfold SB; lia); exact R13
| rewrite (denot_shx E 32 38 88 g SB E32 E38) by (unfold SB; lia); exact R9s
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; rewrite unsigned_lit_small by lia; exact R8
| rewrite E38; exact R22
| rewrite E46; exact R9
| rewrite E23; rewrite unsigned_lit_small by lia; exact R10 ] ]
| ]); try (destruct Hr; fail).
Qed.
Definition regsX0 : list sv := Eval vm_compute in sr_atoms.
Lemma regsX0_ok : forall (regs1 : bvmap 5 word) extra, regs_ok (Eimg (Ereg regs1 extra)) regsX0 regs1.
Proof. intros regs1 extra. change regsX0 with sr_atoms. apply regs_ok_Eimg_Ereg. Qed.
Local Ltac mid_facts CX MID :=
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive);
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK);
lazymatch type of HPerm with Permutation _ (_ ++ ?cb) => assert (Hpfcb : In (pf, FILE_BLOCK) cb) by (right; apply in_app_iff; right; exact Hpfr) end;
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew);
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
Lemma af_RET0X : AF_RET0_stmtX K MT XN B.
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 GPAL IMG LPAL gs gsF CX MID Hk HR XR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
mid_facts CX MID.
pose proof HR as (Rsp & Rgp & Rtp).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seedX B TL LAWS AF_RET regsX0 0 true [] (cg_ihead s1) 0 0 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsX0_ok regs1 _) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
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
Lemma af_E3X : AF_RET_stmtX K MT XN B -> AF_E3_stmtX K MT XN B.
Proof.
intros PRET_ ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 i nw fn GPAL IMG LPAL gs gsF
CX MID Hk HR0 R8 R22 HR9 R9 R23 R10 R13 HL Hi Hfn Hnw XF.
pose proof af_RET0X as PRET. clear PRET_.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR0 as (Rsp & Rgp & Rtp).
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
assert (Hilt : (Z.to_nat i < length (cg_frames s1))%nat) by (rewrite Hlen1; clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
assert (Hfne : nth_error (cg_frames s1) (Z.to_nat i) = Some (Some fn)) by (rewrite <- Hfn; apply nth_error_nth'; exact Hilt).
assert (Hfin1 : In (Some fn) (cg_frames s1)) by (rewrite <- Hfn; apply nth_In; exact Hilt).
assert (HnwC : In (nw, FRAME_SIZE) (cgif_blocks g s1 N)) by (rewrite <- Hnw; exact (af_frame_in_blocks g s1 N fn Hfin1)).
assert (HnwIn : In (nw, FRAME_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; apply in_app_iff; left; exact HnwC).
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as (Hn16 & Hn4096 & Hnceil & Hnh_ia & HnP & _). pose proof (proj1 Hnh_ia) as Hnh.
pose proof (blk_off_imgP _ _ _ _ _ _ nw FRAME_SIZE HAR HnwIn) as Hnh_img.
rewrite HFS in Hnceil. rewrite HFS in HnP. change (req_size 40) with 40 in Hnceil, HnP, Hnh_img.
assert (Dgn : g + 96 <= nw \/ nw + 40 <= g).
{ pose proof HPerm1 as P1. unfold cgif_blocks in P1. cbn [app] in P1.
pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (nw, FRAME_SIZE) _ HAR P1
ltac:(right; apply in_or_app; left; apply in_or_app; right; rewrite <- Hnw; apply af_frames_blocks_ptr_in; exact Hfin1)) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D. lia. }
assert (Dcn : cfp + 32 <= nw \/ nw + 40 <= cfp).
{ pose proof (afobj_journalX B LAWS sp0 ly S W mem md [] lyc Sc Wc _ _ k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as ((cid & pos & Hfin & _ & _ & Hflo & Hfhi) & _ & _).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ nw FRAME_SIZE cid pos HAR HnwIn Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite HFS in D. change (req_size 40) with 40 in D. clear - D Hflo Hfhi. lia. }
pose proof (obj_at_nth SEGS _ _ _ _ 6 (28, 1%N) tidx HCF eq_refl eq_refl) as [_ Rtidx]. cbn [snd] in Rtidx.
pose proof (obj_at_nth SEGS _ _ _ _ 8 (33, 1%N) (fr_tidx fn) (proj2 (proj2 HT1) fn Hfin1) eq_refl eq_refl) as [Vft Rft]. cbn [fst snd] in Vft, Rft. rewrite Hnw in Vft.
destruct (af_reseedxEX B TL LAWS AF_E3 regsE3 88 92 [] ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 [] [fr_tidx fn]
(proj1 CX) (af_midxX_nil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MID) Rsp HL (Forall_nil _) ltac:(clear - PBASE PBLO; lia) ltac:(clear - PBASE PBLO; lia)
(regsE3_ok regs regs1 g s1 cfp _ _ nw HR0 R8 R22 HR9 R9 R23 R10 R13 ltac:(lia) Hgceil ltac:(lia) (proj2 Hcfp) ltac:(lia) Hnceil)
ltac:(vm_compute; reflexivity) Hpfr) as [HS SHOK].
set (E := Eimg (Ereg regs1 _)) in HS, SHOK. try (let Hx := fresh "HEIo" in rename HEIs into Hx). assert (HEIs : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0; fr_tidx fn]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 37%nat ltac:(unfold A_TEXT; lia)) as E37. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38.
pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 53%nat ltac:(unfold A_TEXT; lia)) as E53. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. pose proof (ES 68%nat ltac:(unfold A_TEXT; lia)) as E68.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E37, E38, E46, E53, E67, E68.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (Bnw : bv_unsigned (ew E 23) = nw) by (rewrite E23; apply unsigned_lit_small; clear - Hn4096 Hnceil C1; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 23%nat hfactA HS
ltac:(clear HS; unfold afact_ok, hfactA; cbn [af_lo af_hi af_al2]; rewrite Bnw; change (2 ^ 4) with 16; clear - Hn4096 Hnh Hnceil Hn16 C1; lia)) as HS3;
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 33 34 [YP09.mkChunk 33 (CVal 1 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ nw 33 1 (SOff 68 0) (fr_tidx fn));
[ cbn [sv_denot]; rewrite E68, unsigned_lit_small, Z.add_0_r by (clear - Rft; cbn in Rft; lia); reflexivity
| clear - Rft; exact Rft | cbn; clear; lia | exact Vft ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Bnw, Usp, E32u, E46, (unsigned_lit_small cfp) by (clear - Hcfp C1; lia); img_words_vals;
try (pose proof (pa_obj_img 0 ltac:(clear; lia)) as Hob241; cbv [A_OBJ Nat.add] in Hob241); try (pose proof (pa_obj_img 12 ltac:(clear; lia)) as Hob253; cbv [A_OBJ Nat.add] in Hob253);
clear - Dgn Dcn Hn4096 Hnh Hnh_img Hnh_ia Hnceil Hcfp HZg Hceil Hslo HTS C1 C3 Hob241 Hob253; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_region Ex _ _ (YP09.mkRegion (Some 23%nat) 0 40 33 34 [YP09.mkChunk 33 (CVal 1 (SOff 68 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite Bnw; split; [clear - Hn4096 Hnceil C1; lia|]; split; [clear - Hn4096 Hnceil C1; lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HnP (nw + o) ltac:(clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS _ _ nw 33 1 (SOff 68 0) (fr_tidx fn));
[ cbn [sv_denot]; rewrite E68, unsigned_lit_small, Z.add_0_r by (clear - Rft; cbn in Rft; lia); reflexivity
| clear - Rft; exact Rft | cbn; clear; lia | exact Vft ] ])
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
{ intros blc ii lyq ownq Hbl Hii. destruct (Hnew _ HnwC) as [Hold | [Htok Hwr]].
- right. left. split.
+ unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. exact (inFP_ablocks_fp _ _ _ ii Hold ltac:(cbn [snd]; rewrite HFS; exact Hii)).
+ exists nw, FRAME_SIZE. split; [exact Hbl | rewrite HFS; clear - Hii; lia].
- exact (Hwr blc lyq ownq ii Hbl ltac:(cbn [snd]; rewrite HFS; exact Hii)). }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA.
{ awr_xX Usp E32u Hing HTS Bnw Anw HnwIn. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN1.
cbv beta in UN1. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
-
lazymatch goal with H : branch_taken _ _ _ = true |- _ => rename H into Hq4 end.
rewrite branch_ne_U, U_lit in Hq4 by (clear - PBASE PBLO; lia).
rewrite (U_atom E 67 _ E67) in Hq4 by (clear; destruct (Z.land fattr 4 =? 0); lia).
assert (Hf4 : Z.land fattr 4 = 0) by (clear - Hq4; destruct (Z.land fattr 4 =? 0) eqn:Hb; [apply Z.eqb_eq; exact Hb | cbn in Hq4; discriminate]). clear Hq4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_RET; [awr_xX Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg | st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg  end.
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X68 : ew EL 68 = Z_to_bv 64 (fr_tidx fn)) by (rewrite AGx by lia; exact E68).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 0) GPAL IMG LPAL gs gsF CX) end.
+
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hgceil Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
-
apply (obj_cgif_setcurX SEGS path hw pf _ _ g s1 0 Ho).
+ intros ii Hii Hnc. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii HZg; lia | clear - Hii Hnc HZg Dgn; lia].
+ lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SLit 0) 0 HRg X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbn; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V.
+ clear; lia.
- change (cg_raw (cl_set_cur s1 0)) with (cg_raw s1). change (traw_vals wfn g (cl_set_cur s1 0)) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- change (cg_frames (cl_set_cur s1 0)) with (cg_frames s1). intros f Hfi.
destruct (In_nth_error _ _ Hfi) as [j Hj].
destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne].
+
rewrite Hfne in Hj. injection Hj as <-.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (frame_vals fn) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rft]. cbn [fst]. rewrite Hnw.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 (SOff 68 0) (fr_tidx fn) HRn X23u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite X68, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rft; exact Rft) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
{ intros j' Hj'. reflexivity. }
+
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hj Hfne Hne) as Dff. rewrite Hnw in Dff.
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfi) lay_inside_Frame). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZf f ii Hfi Hii) as [Hb Hn].
apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split; [exact (af_obj_ok_set_cur s s1 N 0 HOK)|]. split; [exact HPerm1 | exact Hnew].
+ exact Hk.
+ split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear - PBASE PBLO; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear - PBASE PBLO; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear - PBASE PBLO; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
pose proof (af_xfoot_unz B LAWS lyc Sc Wc memc mdc g s1 N [] _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha | [Ha | Ha]];
[ left; clear - Ha HTS; lia
| right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]
| right; exists nw, FRAME_SIZE; split; [apply in_app_iff; left; rewrite <- Hnw; exact (af_wblocks_frame g s1 fn Hfin1) | rewrite HFS; change (req_size 40) with 40; clear - Ha; lia] ])) as [XZb XZi].
pose proof (af_xfin_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF _ _ _ UN XZb XZi Hpfcb eq_refl eq_refl Hi Hlen1 Hfn XF) as XF2.
apply (af_xfin_ret K MT XN S Sc _ _ s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF Hi Hlen1 Hfn).
rewrite (nf_trans_noset (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG Hf4). exact XF2.
-
lazymatch goal with H : branch_taken _ _ _ = false |- _ => rename H into Hq4 end.
rewrite branch_ne_U, U_lit in Hq4 by (clear - PBASE PBLO; lia).
rewrite (U_atom E 67 _ E67) in Hq4 by (clear; destruct (Z.land fattr 4 =? 0); lia).
assert (Hf4 : Z.land fattr 4 <> 0) by (clear - Hq4; destruct (Z.land fattr 4 =? 0) eqn:Hb; [cbn in Hq4; discriminate | apply Z.eqb_neq; exact Hb]). clear Hq4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_RET; [awr_xX Usp E32u Hing HTS Bnw Anw HnwIn |].
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?Usp, ?E32u, ?Bnw in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN2.
cbv beta in UN2. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in * | st_ok _ ?Ex _ (restrict _ ?msq) => set (EL := Ex) in HS; set (msL := msq) in *  end.
assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) ->
aview SEGS (w_H Wc) (ms_mem msL) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. etransitivity; [exact (UN2 a Ha Hn) | exact (UN1 a Ha Hn)]. }
assert (AGx : forall n, (n < 512)%nat -> ew EL n = ew E n) by (intros n Hn; subst EL; rewrite ?ew_ewset_other by lia; reflexivity).
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear -Ha HTS; lia)) as [HZr HZf].
cbv beta in HZr, HZf.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_pi_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg | st_ok _ ?Ex ?ssx ?msx =>
let rn := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
let rg := eval vm_compute in (nth 5 (ss_mem ssx) got_regionP) in
pose proof (st_ok_region_nth Ex ssx msx 0 rn HS ltac:(vm_compute; reflexivity)) as HRn;
pose proof (st_ok_region_nth Ex ssx msx 5 rg HS ltac:(vm_compute; reflexivity)) as HRg;
cbn [ms_mem restrict mkst] in HRn, HRg  end.
assert (X32u : bv_unsigned (ew EL 32) = g) by (rewrite AGx by lia; exact E32u).
assert (X23u : bv_unsigned (ew EL 23) = nw) by (rewrite AGx by lia; exact Bnw).
assert (X53 : ew EL 53 = Z_to_bv 64 tidx) by (rewrite AGx by lia; exact E53).
set (fn' := set_fr_tidx fn tidx).
assert (Hfn' : frame_vals fn' = list_set (frame_vals fn) 8 tidx) by reflexivity.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc] | st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst SEGS Hh Ex _ msq HS eq_refl); cbn [ss_pc]  end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0) GPAL IMG LPAL gs gsF CX) end.
+
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview SEGS); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha Hgceil Hnceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
-
rewrite xcgif_vals_set_cur_ls, (xcgif_vals_upd_frame path hw pf s1 (Z.to_nat i) fn fn' Hfne eq_refl), <- xcgif_vals_set_cur_ls.
apply (obj_cgif_setcurX SEGS path hw pf _ _ g s1 0 Ho).
+ intros ii Hii Hnc. apply (mbyte_of_aview SEGS). apply UN; [clear - Hii HZg; lia | clear - Hii Hnc HZg Dgn; lia].
+ lazymatch type of HRg with region_ok _ ?Ex _ (YP09.mkRegion (Some 32%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 32 g cs lo hi wlo whi 88 4 (SLit 0) 0 HRg X32u ltac:(cbn; tauto) ltac:(reflexivity) ltac:(clear; cbn; lia) ltac:(cbn; clear; lia)) as V end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V.
+ clear; lia.
- change (cg_raw (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (cg_raw s1). change (traw_vals wfn g (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (traw_vals wfn g s1).
apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros ii Hii. apply (mbyte_of_aview SEGS). destruct (HZr ii Hii) as [Hb Hn].
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hinr HnwIn ltac:(intros Hq; pose proof (f_equal snd Hq) as Hq2; cbn [snd] in Hq2; unfold RAW_SIZE, FRAME_SIZE in Hq2; clear - Hq2; lia)) as D.
unfold zdisjoint in D. cbn [fst snd] in D. change (req_size RAW_SIZE) with 48 in D. rewrite HFS in D. change (req_size 40) with 40 in D.
apply UN; [exact Hb | clear - Hn D Hii; lia].
- change (cg_frames (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0)) with (cg_frames (upd_frame s1 (Z.to_nat i) fn')).
apply (tframes_at_upd _ _ s1 (Z.to_nat i) (Some fn) fn' Hf Hfne).
+
change (fr_ptr fn') with (fr_ptr fn). rewrite Hfn'.
lazymatch goal with |- obj_at _ ?mF _ _ _ =>
eapply (obj_at_upd SEGS (mrestrict (w_H Wc) memc) mF (fr_ptr fn) LAY_Frame 40 (frame_vals fn) (list_set (frame_vals fn) 8 tidx) [8]%nat [(33, 34)] (Hf fn Hfin1) lay_inside_Frame) end.
{ vm_compute; reflexivity. }
{ reflexivity. }
{ intros ii Hii Hw. apply in_wins_cons_false in Hw as [Hw _]. apply (mbyte_of_aview SEGS). rewrite Hnw. apply UN; [clear - Hii Hn4096 Hnceil C1; lia | clear - Hii Hw Hnceil Hceil Hslo HTS C1 Dgn; lia]. }
{ intros j' f' v' Hj' Hf' Hv'. cbn [In] in Hj'. destruct Hj' as [<- | []]. cbn in Hf'. injection Hf' as <-. cbn in Hv'. injection Hv' as <-.
split; [| exact Rtidx]. cbn [fst]. rewrite Hnw.
lazymatch type of HRn with region_ok _ ?Ex _ (YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with [YP09.mkChunk 33 (CVal 1 ?e)] =>
pose proof (field_of_region Ex _ 23 nw cs lo hi wlo whi 33 1 e tidx HRn X23u ltac:(cbn; tauto)) as V end end.
specialize (V ltac:(rewrite denot_lit_U; f_equal; apply (U_zext_small EL 8 _ tidx (U_atom EL 53 tidx X53 ltac:(clear - Rtidx; cbn in Rtidx; lia))); [clear - Rtidx; cbn in Rtidx |- *; lia | cbn; clear; lia])).
specialize (V ltac:(clear - Rtidx; exact Rtidx) ltac:(cbn; clear; lia)).
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V. exact V. }
{ intros j' Hj'. rewrite YI5v.nth_error_list_set_other; [reflexivity|]. intros Hq; apply Hj'; subst j'; left; reflexivity. }
+
intros j x Hjx Hne ii Hii.
pose proof (af_frames_sep2 B LAWS _ _ _ _ _ g s1 N _ _ _ _ _ HAR HPerm1 Hlen1 Hjx Hfne Hne) as Dff. rewrite Hnw in Dff.
assert (Hxi : In (Some x) (cg_frames s1)) by (eapply nth_error_In; exact Hjx).
apply (mbyte_of_aview SEGS). destruct (HZf x ii Hxi Hii) as [Hb Hn]. apply UN; [exact Hb | clear - Hn Dff Hii; lia]. }
split.
{ apply af_obj_ok_set_cur. apply (af_obj_ok_upd_frame s s1 N (Z.to_nat i) fn fn' HOK Hfne).
apply (frame_wf_fields (cg_attr s1) fn fn'); [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HWF1)))))) fn Hfin1) | reflexivity | reflexivity]. }
change (cgif_blocks g (cl_set_cur (upd_frame s1 (Z.to_nat i) fn') 0) N) with (cgif_blocks g (upd_frame s1 (Z.to_nat i) fn') N).
rewrite (cgif_blocks_upd_frame g s1 N (Z.to_nat i) fn fn' Hfne eq_refl). split; [exact HPerm1 | exact Hnew].
+ exact Hk.
+ split; [|split];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => prreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ rewrite (AGx 2%nat ltac:(clear - PBASE PBLO; lia)), (EEo 2%nat 2%bv eq_refl); exact Rsp
| rewrite (AGx 3%nat ltac:(clear - PBASE PBLO; lia)), (EEo 3%nat 3%bv eq_refl); exact Rgp
| rewrite (AGx 4%nat ltac:(clear - PBASE PBLO; lia)), (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "REG-FAIL" gg end ]).
+
pose proof (af_xfoot_unz B LAWS lyc Sc Wc memc mdc g s1 N [] _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92) \/ (nw + 33 <= a < nw + 34)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; destruct Ha as [Ha | [Ha | Ha]];
[ left; clear - Ha HTS; lia
| right; exists g, CGIF_SIZE; split; [left; reflexivity | change (req_size CGIF_SIZE) with 96; clear - Ha; lia]
| right; exists nw, FRAME_SIZE; split; [apply in_app_iff; left; rewrite <- Hnw; exact (af_wblocks_frame g s1 fn Hfin1) | rewrite HFS; change (req_size 40) with 40; clear - Ha; lia] ])) as [XZb XZi].
pose proof (af_xfin_unz B K MT XN AIL (w_H Wc) memc (ms_mem msL) mdc _ S Sc s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF _ _ _ UN XZb XZi Hpfcb eq_refl eq_refl Hi Hlen1 Hfn XF) as XF2.
pose proof (af_xfin_tidx K MT XN S Sc _ _ s s1 N i fn fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF _ tidx Hi Hlen1 XF2) as XF3. fold fn' in XF3.
assert (Hi3 : (Z.to_nat i < 3)%nat) by (clear - Hi; destruct Hi as [-> | ->]; cbn; lia).
apply (af_xfin_ret K MT XN S Sc _ _ s (upd_frame s1 (Z.to_nat i) fn') N i fn' fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF Hi).
* unfold upd_frame, set_frames. cbn [cg_frames]. rewrite length_list_set. exact Hlen1.
* rewrite (nth_upd_frame s1 (Z.to_nat i) fn' (Z.to_nat i) Hlen1 Hi3), Nat.eqb_refl. reflexivity.
* rewrite (nf_trans_set (gcfg_of s GPAL) fattr fgen delay tidx nlp LPAL IMG Hf4). exact XF3.
Qed.
End l.
End h.
End d.
