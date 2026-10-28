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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgy ACgz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq.
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
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_FPb_blocks : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> In (pf, FILE_BLOCK) cb -> inFP (FPb g s N) x ->
(exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n) \/ (0 <= x < 1).
Proof.
intros ly S W mem md g s N cb x HAR HP Hpf HF. unfold FPb in HF. destruct HF as (r & Hr & Hx). apply in_app_iff in Hr as [Hr | Hr].
- left. destruct (inFP_ablocks_fp_inv _ x (ex_intro _ r (conj Hr Hx))) as (p & n & Hpn & Hxx).
exists p, n. split; [|exact Hxx]. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hpn.
- destruct (proj1 (in_asink_fp pf x) (ex_intro _ r (conj Hr Hx))) as [Hb | Ht]; [left | right; exact Ht].
exists pf, FILE_BLOCK. split; [eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; right; exact Hpf|].
change (req_size FILE_BLOCK) with 1264. unfold FILE_BLOCK in Hb. lia.
Qed.
Lemma af_FPb_high : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> In (pf, FILE_BLOCK) cb -> inFP (FPb g s N) x ->
x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof.
intros ly S W mem md g s N cb x HAR HP Hpf HF. destruct (af_FPb_blocks ly S W mem md g s N cb x HAR HP Hpf HF) as [(p & n & Hin & Hx) | Ht].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & Hceil & Hh_ia & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *. lia.
- left. unfold kLowShadowBeg. lia.
Qed.
Lemma af_FPn_blocks : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> inFP (FPn g) x ->
exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n.
Proof.
intros ly S W mem md g s N cb x HAR HP (r & [<- | []] & Hx). cbn [fst snd] in Hx.
exists g, CGIF_SIZE. split; [eapply Permutation_in; [apply Permutation_sym; exact HP|]; left; reflexivity|].
change (req_size CGIF_SIZE) with 96. lia.
Qed.
Lemma af_FPn_high : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> inFP (FPn g) x ->
x < kLowShadowBeg \/ kHighShadowEnd <= x.
Proof.
intros ly S W mem md g s N cb x HAR HP HF. destruct (af_FPn_blocks ly S W mem md g s N cb x HAR HP HF) as (p & n & Hin & Hx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & Hceil & Hh_ia & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *. lia.
Qed.
Lemma afobj_journalG : forall sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n,
ajournal SEGS B TADDFRAME_STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> (forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
afobj SEGS B ly S W mem p n -> afobj SEGS B lyc Sc Wc memc p n.
Proof.
intros sp0 FP ly S W mem md own lyc Sc Wc memc mdc k p n HJ HAR0 HFP ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA).
pose proof HJ as (HAR1 & HLY & _ & _ & _ & Hfrs & _).
assert (EFA : frame_addr lyc cid pos = frame_addr ly cid pos) by (unfold frame_addr; destruct HLY as (_ & _ & _ & _ & _ & -> & _); reflexivity).
split; [| split; [exact Hp8|]].
- exists cid, pos. rewrite Hfrs, EFA. split; [apply in_app_iff; right; exact Hin|]. repeat split; assumption.
- eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hin | exact Hcid | exact Hlo | exact Hhi | exact Hal | exact HFP | exact HAR0 | exact HRA].
Qed.
Lemma cfp_obj_journalG : forall sp0 FP ly S W mem md own lyc Sc Wc memc mdc k cfp vals,
ajournal SEGS B TADDFRAME_STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md ->
(forall x, inFP FP x -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n) \/ (0 <= x < 1)) ->
afobj SEGS B ly S W mem cfp 32 ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig vals ->
obj_at SEGS (mrestrict (w_H Wc) memc) cfp LAY_FrameConfig vals.
Proof.
intros sp0 FP ly S W mem md own lyc Sc Wc memc mdc k cfp vals HJ HAR0 HFP ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA) HO.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (obj_at_kept _ _ cfp LAY_FrameConfig vals 32 HO lay_inside_FrameConfig).
intros i Hi. apply (mbyte_of_aview SEGS). apply (F4 cid pos _ Hin).
- left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros HF. destruct (HFP _ HF) as [(p & n & Hpn & Hx) | Ht].
+ pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n cid pos HAR0 Hpn Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
+ destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR0 Hin) as (Hf4096 & _). lia.
Qed.
Lemma afobj_journalX : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n,
ajournal SEGS B TADDFRAME_STK sp0 (FPb g s N) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem p n -> In (pf, FILE_BLOCK) cb -> afobj SEGS B lyc Sc Wc memc p n.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n HJ HAR0 HP HO Hpf.
exact (afobj_journalG sp0 _ ly S W mem md own lyc Sc Wc memc mdc k p n HJ HAR0 (fun x Hx => af_FPb_high ly S W mem md g s N cb x HAR0 HP Hpf Hx) HO).
Qed.
Lemma cfp_obj_journalX : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals,
ajournal SEGS B TADDFRAME_STK sp0 (FPb g s N) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem cfp 32 ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig vals -> In (pf, FILE_BLOCK) cb ->
obj_at SEGS (mrestrict (w_H Wc) memc) cfp LAY_FrameConfig vals.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals HJ HAR0 HP HFO HO Hpf.
exact (cfp_obj_journalG sp0 _ ly S W mem md own lyc Sc Wc memc mdc k cfp vals HJ HAR0 (fun x Hx => af_FPb_blocks ly S W mem md g s N cb x HAR0 HP Hpf Hx) HFO HO).
Qed.
Lemma afobj_journalN : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n,
ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem p n -> afobj SEGS B lyc Sc Wc memc p n.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n HJ HAR0 HP HO.
exact (afobj_journalG sp0 _ ly S W mem md own lyc Sc Wc memc mdc k p n HJ HAR0 (fun x Hx => af_FPn_high ly S W mem md g s N cb x HAR0 HP Hx) HO).
Qed.
Lemma cfp_obj_journalN : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals,
ajournal SEGS B TADDFRAME_STK sp0 (FPn g) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem cfp 32 ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig vals ->
obj_at SEGS (mrestrict (w_H Wc) memc) cfp LAY_FrameConfig vals.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals HJ HAR0 HP HFO HO.
exact (cfp_obj_journalG sp0 _ ly S W mem md own lyc Sc Wc memc mdc k cfp vals HJ HAR0
(fun x Hx => or_introl (af_FPn_blocks ly S W mem md g s N cb x HAR0 HP Hx)) HFO HO).
Qed.
Lemma af_fp_coverX : forall ly S (regs : bvmap 5 word) g s N lyc Sc b a,
(In b (cgif_blocks g s N) \/ af_newtokX B ly S regs g s N b) -> In b (ablocks B lyc Sc) ->
fst b <= a < fst b + req_size (snd b) ->
(inFP (FPb g s N) a /\ exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a.
Proof.
intros ly S regs g s N lyc Sc [p n] a Hb Hlive Ha. cbn [fst snd] in Ha.
assert (LIVE : exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= a < p0 + req_size n0) by (exists p, n; split; [exact Hlive | exact Ha]).
destruct Hb as [Hb | [Htok _]].
- left. split; [|exact LIVE]. unfold FPb. apply (proj2 (YI04.inFP_app _ _ _)). left. replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n (a - p) Hb). lia.
- assert (EQD : forall x y : Z * Z, {x = y} + {x <> y}) by (intros [x1 x2] [y1 y2]; decide equality; apply Z.eq_dec).
destruct (in_dec EQD (p, n) (ablocks B ly S)) as [Hin | Hnin].
+ left. split; [|exact LIVE]. replace a with (p + (a - p)) by lia. apply (Htok Hin (a - p)). cbn [snd]. lia.
+ right. exists p, n. split; [exact Hlive | split; [exact Hnin | exact Ha]].
Qed.
Lemma af_reseedX : forall pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 more,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cxS B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 ->
getr regs1 2 = w64 (spZ regs - 224) ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regionsX 0 true af_lcD (cg_ihead s1) wlo whi) = true ->
In (pf, FILE_BLOCK) rest ->
st_ok_pi SEGS VAL E (ss_afX pc sregs 0 true af_lcD (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 more a4v E
CX MID Rsp HL Hwlo Hwhi HREG HWFR Hpfr.
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof (proj1 HJ) as HAR1. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing1 : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof (afobj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as HFO1.
pose proof HFO1 as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR1 Hfin) as Hfhigh_img.
assert (Hcfp : 0 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E38, E46, E67.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (Ha4 : 0 <= a4v < 2 ^ 64) by (subst a4v; destruct (Z.land fattr 4 =? 0); lia).
exact (af_seedX B TL LAWS pc sregs 0 true af_lcD (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(af_lcD_ok E _ sp0 g cfp a4v HL E32 E38 E46 E67 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) Ha4)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)).
Qed.
Lemma af_reseedxX : forall pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 X more,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cxS B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 X ->
getr regs1 2 = w64 (spZ regs - 224) ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 224 - 0)) lcx ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regionsX 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi) = true ->
In (pf, FILE_BLOCK) rest ->
st_ok_pi SEGS VAL E (ss_afX pc sregs 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 X more a4v E
CX MID Rsp HL HLX Hwlo Hwhi HREG HWFR Hpfr.
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof (proj1 HJ) as HAR1. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing1 : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof (afobj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as HFO1.
pose proof HFO1 as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR1 Hfin) as Hfhigh_img.
assert (Hcfp : 0 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E38, E46, E67.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (Ha4 : 0 <= a4v < 2 ^ 64) by (subst a4v; destruct (Z.land fattr 4 =? 0); lia).
exact (af_seedX B TL LAWS pc sregs 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(proj2 (Forall_app _ _ _) (conj (af_lcD_ok E _ sp0 g cfp a4v HL E32 E38 E46 E67 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) Ha4) HLX))
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)).
Qed.
Lemma af_reseedDX : forall pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 X more nw,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cxS B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midxX B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 X ->
getr regs1 2 = w64 (spZ regs - 224) -> getr regs1 23 = w64 nw -> In (nw, FRAME_SIZE) (ablocks B lyc Sc) ->
af_locsD (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v nw ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 224 - 0)) lcx ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regionsX 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi) = true ->
In (pf, FILE_BLOCK) rest ->
st_ok_pi SEGS VAL E (ss_afX pc sregs 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 X more nw a4v E
CX MID Rsp R23 HnwIn HL HLX Hwlo Hwhi HREG HWFR Hpfr.
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew & HnewX).
pose proof (proj1 HJ) as HAR1. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing1 : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR1 Hing1) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP.
destruct (al_blocks _ _ LAWS _ _ _ _ _ nw FRAME_SIZE HAR1 HnwIn) as (Hn16 & Hn4096 & Hnceil & _).
change (req_size FRAME_SIZE) with 40 in Hnceil.
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof (afobj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO Hpfcb) as HFO1.
pose proof HFO1 as ((cid & pos & Hfin & Hcid0 & Hfal & Hflo & Hfhi) & Hcal & HRA).
destruct (frames_bounds SEGS _ LAWS _ _ _ _ _ _ _ HAR1 Hfin) as (Hf4096 & Hfceil & Hfhigh).
assert (Hcfp : 0 <= cfp /\ cfp + 32 <= alloc_ceiling) by (clear - Hflo Hfhi Hf4096 Hfceil; lia).
assert (Rsp' : bv_unsigned (getr regs1 2) = sp0 - 224 - 0) by (rewrite Rsp; rewrite unsigned_lit_small by lia; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m < A_TEXT)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more)) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; rewrite Eimg_low by lia; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (ES 38%nat ltac:(unfold A_TEXT; lia)) as E38. pose proof (ES 47%nat ltac:(unfold A_TEXT; lia)) as E47. pose proof (ES 48%nat ltac:(unfold A_TEXT; lia)) as E48.
pose proof (ES 49%nat ltac:(unfold A_TEXT; lia)) as E49. pose proof (ES 67%nat ltac:(unfold A_TEXT; lia)) as E67. pose proof (ES 46%nat ltac:(unfold A_TEXT; lia)) as E46.
cbn [Nat.sub nth af_extra map app firstn repeat] in E32, E38, E46, E47, E48, E49, E67.
assert (E23 : ew E 23 = Z_to_bv 64 nw) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
pose proof (obj_at_nth SEGS _ _ _ _ 0 (0, 8%N) lpal HCF eq_refl eq_refl) as [_ Rlpal]. cbn [snd] in Rlpal. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rlpal.
pose proof (obj_at_nth SEGS _ _ _ _ 1 (8, 8%N) img HCF eq_refl eq_refl) as [_ Rimg]. cbn [snd] in Rimg. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in Rimg.
pose proof (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) fattr HCF eq_refl eq_refl) as [_ Rfattr]. cbn [snd] in Rfattr. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Rfattr.
assert (Ha4r : 0 <= a4v < 2 ^ 64) by (subst a4v; destruct (Z.land fattr 4 =? 0); lia).
exact (af_seedX B TL LAWS pc sregs 0 true (af_lcDD ++ lcx) (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(proj2 (Forall_app _ _ _) (conj (af_lcDD_ok E _ sp0 g cfp a4v nw HL E32 E38 E46 E67 E23 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) ltac:(lia) Hnceil Ha4r) HLX))
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journalX sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF Hpfcb)).
Qed.
Definition af_wblocks (g : Z) (s : cgif_st) : list (Z * Z) :=
(g, CGIF_SIZE) :: (cg_raw s, RAW_SIZE) :: flat_map (fun o => match o with Some f => [(fr_ptr f, FRAME_SIZE)] | None => [] end) (cg_frames s).
Lemma frames_blocks_wv : forall N l,
Permutation (frames_blocks N l)
(flat_map (fun o => match o with Some f => [(fr_ptr f, FRAME_SIZE)] | None => [] end) l ++ flat_map (af_xfvb N) l).
Proof.
intros N l. induction l as [|o l IH]; [reflexivity|]. unfold frames_blocks in *. cbn [flat_map].
destruct o as [f|]; [|exact IH]. unfold frame_blocks, af_xfvb at 1.
set (V := (fr_img f, N) :: (if Z.land (fr_attr f) 1 =? 0 then [] else [(fr_lpal f, 3 * fr_nlp f)])).
change (Permutation (((fr_ptr f, FRAME_SIZE) :: V) ++ flat_map (fun o : option frame_st => match o with Some f0 => (fr_ptr f0, FRAME_SIZE) :: (fr_img f0, N) :: (if Z.land (fr_attr f0) 1 =? 0 then [] else [(fr_lpal f0, 3 * fr_nlp f0)]) | None => [] end) l)
(([(fr_ptr f, FRAME_SIZE)] ++ flat_map (fun o : option frame_st => match o with Some f0 => [(fr_ptr f0, FRAME_SIZE)] | None => [] end) l) ++ (V ++ flat_map (af_xfvb N) l))).
cbn [app]. apply perm_skip.
eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma cgif_blocks_wv : forall g s N, Permutation (cgif_blocks g s N) (af_wblocks g s ++ af_xvblocks s N).
Proof.
intros g s N. unfold cgif_blocks, af_wblocks. rewrite af_xvblocks_eq. cbn [app]. do 2 apply perm_skip.
eapply Permutation_trans; [apply Permutation_app_head; apply frames_blocks_wv|].
rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma af_wblocks_frame : forall g s f, In (Some f) (cg_frames s) -> In (fr_ptr f, FRAME_SIZE) (af_wblocks g s).
Proof. intros g s f Hf. unfold af_wblocks. right. right. apply in_flat_map. exists (Some f). split; [exact Hf | left; reflexivity]. Qed.
Lemma asep_app : forall ly S W mem md (l1 l2 : list (Z * Z)) x y,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (l1 ++ l2) -> In x l1 -> In y l2 -> zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S W mem md l1 l2 x y HAR HP Hx Hy. destruct (in_split _ _ Hx) as (a1 & a2 & ->). destruct (in_split _ _ Hy) as (b1 & b2 & ->).
apply (sep_blocks_perm SEGS B LAWS ly S W mem md x y ((a1 ++ a2) ++ b1 ++ b2) HAR).
eapply Permutation_trans; [exact HP|].
eapply Permutation_trans; [apply (Permutation_app (Permutation_sym (Permutation_middle a1 a2 x)) (Permutation_sym (Permutation_middle b1 b2 y)))|].
cbn [app]. apply perm_skip. exact (Permutation_sym (Permutation_middle (a1 ++ a2) (b1 ++ b2) y)).
Qed.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Lemma af_xfoot_unz : forall ly S W mem md g s1 N X cb lya sp0 (Zs : Z -> Prop),
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ X ++ cb) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall a, Zs a -> (sp0 - TADDFRAME_STK <= a < sp0) \/ exists b n, In (b, n) (af_wblocks g s1 ++ X) /\ b <= a < b + req_size n) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) /\
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a).
Proof.
intros ly S W mem md g s1 N X cb lya sp0 Zs HAR HP Hstk HZ.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). pose proof asan_consts as (C1 & _).
assert (HP' : Permutation (ablocks B ly S) ((af_wblocks g s1 ++ X) ++ (af_xvblocks s1 N ++ cb))).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_tail; apply cgif_blocks_wv|].
rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
split.
- intros p n k Hin Hk.
assert (Hlive : In (p, n) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; right; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hlive) as (_ & Hp4096 & Hpceil & _).
split; [lia|]. intros Hz. destruct (HZ _ Hz) as [Hs | (b & m & Hbm & Hb)]; [lia|].
pose proof (asep_app ly S W mem md _ _ (b, m) (p, n) HAR HP' Hbm Hin) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
- intros a Hi. pose proof (pa_img_range a Hi) as Hr. split; [lia|]. intros Hz. destruct (HZ _ Hz) as [Hs | (b & m & Hbm & Hb)]; [lia|].
assert (Hlive : In (b, m) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; left; exact Hbm).
pose proof (blk_off_imgP _ _ _ _ _ _ b m HAR Hlive) as Ho. unfold off_img in Ho. lia.
Qed.
Lemma af_xfoot_unz2 : forall ly S W mem md g s1 N Xw Xv cb lya sp0 (Zs : Z -> Prop),
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ (Xw ++ Xv) ++ cb) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall a, Zs a -> (sp0 - TADDFRAME_STK <= a < sp0) \/ exists b n, In (b, n) (af_wblocks g s1 ++ Xw) /\ b <= a < b + req_size n) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ Xv ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) /\
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a).
Proof.
intros ly S W mem md g s1 N Xw Xv cb lya sp0 Zs HAR HP Hstk HZ.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). pose proof asan_consts as (C1 & _).
assert (HP' : Permutation (ablocks B ly S) ((af_wblocks g s1 ++ Xw) ++ (af_xvblocks s1 N ++ Xv ++ cb))).
{ eapply Permutation_trans; [exact HP|]. eapply Permutation_trans; [apply Permutation_app_tail; apply cgif_blocks_wv|].
rewrite <- !app_assoc. apply Permutation_app_head. rewrite !app_assoc. do 2 apply Permutation_app_tail. apply Permutation_app_comm. }
split.
- intros p n k Hin Hk.
assert (Hlive : In (p, n) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; right; exact Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hlive) as (_ & Hp4096 & Hpceil & _).
split; [lia|]. intros Hz. destruct (HZ _ Hz) as [Hs | (b & m & Hbm & Hb)]; [lia|].
pose proof (asep_app ly S W mem md _ _ (b, m) (p, n) HAR HP' Hbm Hin) as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
- intros a Hi. pose proof (pa_img_range a Hi) as Hr. split; [lia|]. intros Hz. destruct (HZ _ Hz) as [Hs | (b & m & Hbm & Hb)]; [lia|].
assert (Hlive : In (b, m) (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP'|]; apply in_app_iff; left; exact Hbm).
pose proof (blk_off_imgP _ _ _ _ _ _ b m HAR Hlive) as Ho. unfold off_img in Ho. lia.
Qed.
Lemma perm_new_own : forall (bl A X C : list (Z * Z)) b,
Permutation bl (A ++ X ++ C) -> Permutation (bl ++ [b]) (A ++ (X ++ [b]) ++ C).
Proof.
intros bl A X C b HP. eapply Permutation_trans; [apply Permutation_app_tail; exact HP|].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma af_xfoot_unz3 : forall ly S W mem md g s1 N X Xw Xv cb lya sp0 (Zs : Z -> Prop),
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ X ++ cb) -> Permutation X (Xw ++ Xv) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall a, Zs a -> (sp0 - TADDFRAME_STK <= a < sp0) \/ exists b n, In (b, n) (af_wblocks g s1 ++ Xw) /\ b <= a < b + req_size n) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ Xv ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) /\
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a).
Proof.
intros ly S W mem md g s1 N X Xw Xv cb lya sp0 Zs HAR HP HX Hstk HZ.
apply (af_xfoot_unz2 ly S W mem md g s1 N Xw Xv cb lya sp0 Zs HAR); [| exact Hstk | exact HZ].
eapply Permutation_trans; [exact HP|]. apply Permutation_app_head. apply Permutation_app_tail. exact HX.
Qed.
Lemma cgif_relA_unz : forall H (m m' : word -> option byte) md md' s1 N cb GPAL gs (Zs : Z -> Prop),
(forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS H m' a = aview SEGS H m a) ->
(forall p n k, In (p, n) (af_xvblocks s1 N ++ cb) -> 0 <= k < req_size n -> 0 <= p + k < 2 ^ 64 /\ ~ Zs (p + k)) ->
(forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ Zs a) ->
In (pf, FILE_BLOCK) cb -> cgif_wf s1 N -> m_fs md' = m_fs md -> m_fds md' = m_fds md ->
cgif_relA SEGS K (mrestrict H m) md s1 pf N GPAL gs -> cgif_relA SEGS K (mrestrict H m') md' s1 pf N GPAL gs.
Proof.
intros H m m' md md' s1 N cb GPAL gs Zs UN XZb XZi Hpf Hwf Efs Efd HR.
apply (cgif_relA_kept SEGS K (mrestrict H m) (mrestrict H m') md md' s1 pf N GPAL gs Hwf); [| | exact Efs | exact Efd | exact HR].
- intros a n k Hin Hk. apply (mbyte_of_aview SEGS).
destruct (XZb a n k ltac:(apply in_app_iff; left; exact Hin) ltac:(pose proof (req_size_pos n); lia)) as [Hr Hn]. exact (UN _ Hr Hn).
- intros a [Ha | Ha]; apply (mbyte_of_aview SEGS).
+ replace a with (pf + (a - pf)) by lia.
destruct (XZb pf FILE_BLOCK (a - pf) ltac:(apply in_app_iff; right; exact Hpf) ltac:(change (req_size FILE_BLOCK) with 1264; unfold FILE_BLOCK in Ha; lia)) as [Hr Hn].
exact (UN _ Hr Hn).
+ destruct (XZi a (proj1 (ail_env _ _ _ AIL a Ha))) as [Hr Hn]. exact (UN _ Hr Hn).
Qed.
End e.
End d.
End c.
