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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Lemma af_FP_blocks : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> inFP (FPa g s N) x ->
exists p n, In (p, n) (ablocks B ly S) /\ p <= x < p + req_size n.
Proof.
intros ly S W mem md g s N cb x HAR HP HF. unfold FPa in HF. destruct (inFP_ablocks_fp_inv _ _ HF) as (p & n & Hpn & Hx).
exists p, n. split; [|exact Hx]. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hpn.
Qed.
Lemma af_FP_high : forall ly S W mem md g s N cb x,
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) -> inFP (FPa g s N) x ->
(x < kLowShadowBeg \/ kHighShadowEnd <= x) /\ x < alloc_ceiling.
Proof.
intros ly S W mem md g s N cb x HAR HP HF. destruct (af_FP_blocks ly S W mem md g s N cb x HAR HP HF) as (p & n & Hin & Hx).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & Hceil & Hh_ia & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, kHighShadowEnd in *. lia.
Qed.
Lemma afobj_journal : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n,
ajournal SEGS B TADDFRAME_STK sp0 (FPa g s N) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem p n -> afobj SEGS B lyc Sc Wc memc p n.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb p n HJ HAR0 HP ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA).
pose proof HJ as (HAR1 & HLY & _ & _ & _ & Hfrs & _).
assert (EFA : frame_addr lyc cid pos = frame_addr ly cid pos) by (unfold frame_addr; destruct HLY as (_ & _ & _ & _ & _ & -> & _); reflexivity).
split; [| split; [exact Hp8|]].
- exists cid, pos. rewrite Hfrs, EFA. split; [apply in_app_iff; right; exact Hin|]. repeat split; assumption.
- eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hin | exact Hcid | exact Hlo | exact Hhi | exact Hal | | exact HAR0 | exact HRA].
intros x Hx. exact (proj1 (af_FP_high ly S W mem md g s N cb x HAR0 HP Hx)).
Qed.
Lemma cfp_obj_journal : forall sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals,
ajournal SEGS B TADDFRAME_STK sp0 (FPa g s N) ly S W mem md own lyc Sc Wc memc mdc k ->
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s N ++ cb) ->
afobj SEGS B ly S W mem cfp 32 ->
obj_at SEGS (mrestrict (w_H W) mem) cfp LAY_FrameConfig vals ->
obj_at SEGS (mrestrict (w_H Wc) memc) cfp LAY_FrameConfig vals.
Proof.
intros sp0 ly S W mem md own lyc Sc Wc memc mdc k g s N cb cfp vals HJ HAR0 HP ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & Hp8 & HRA) HO.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
apply (obj_at_kept _ _ cfp LAY_FrameConfig vals 32 HO lay_inside_FrameConfig).
intros i Hi. apply (mbyte_of_aview SEGS). apply (F4 cid pos _ Hin).
- left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- intros HF. destruct (af_FP_blocks ly S W mem md g s N cb _ HAR0 HP HF) as (p & n & Hpn & Hx).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n cid pos HAR0 Hpn Hin) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma af_frame_kept : forall (m m' : word -> option byte) sp0 regs,
af_frame m sp0 regs -> (forall a, sp0 - 104 <= a < sp0 -> mbyte SEGS m' a = mbyte SEGS m a) -> af_frame m' sp0 regs.
Proof.
intros m m' sp0 regs HF HK j r Hj.
assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some af_saved j)); rewrite Hj; discriminate).
intros kk Hkk. rewrite (HK _) by lia. exact (HF j r Hj kk Hkk).
Qed.
Lemma af_lcD_ok : forall E (m : word -> option byte) sp0 g cfp a4v,
af_locs m sp0 g cfp a4v ->
ew E 32 = Z_to_bv 64 g -> ew E 38 = Z_to_bv 64 SB -> ew E 46 = Z_to_bv 64 cfp -> ew E 67 = Z_to_bv 64 a4v ->
0 <= g -> g + 96 <= alloc_ceiling -> 0 <= cfp -> cfp + 32 <= alloc_ceiling -> 0 <= a4v < 2 ^ 64 ->
Forall (YP09.chunk_ok SEGS E m (sp0 - 224 - 0)) af_lcD.
Proof.
intros E m sp0 g cfp a4v (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9) E32 E38 E46 E67 Hg0 Hgc Hc0 Hcc Ha4.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (D1 : forall o, 0 <= o <= 96 -> sv_denot E (shq 32 o) = Z_to_bv 64 (SB + (g + o) / 8) /\ 0 <= SB + (g + o) / 8 < 2 ^ 64).
{ intros o Ho. split; [apply (denot_shx E 32 38 o g SB E32 E38); unfold SB; lia|].
assert (Hd : 0 <= (g + o) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
assert (D2 : sv_denot E (shq 46 16) = Z_to_bv 64 (SB + (cfp + 16) / 8) /\ 0 <= SB + (cfp + 16) / 8 < 2 ^ 64).
{ split; [apply (denot_shx E 46 38 16 cfp SB E46 E38); unfold SB; lia|].
assert (Hd : 0 <= (cfp + 16) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). unfold SB. lia. }
replace (sp0 - 224 - 0) with (sp0 - 224) by lia. unfold af_lcD. change (2 ^ 64) with (2 ^ (8 * Z.of_N 8)) in D1, D2, Ha4.
repeat apply Forall_cons; try apply Forall_nil;
lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 ?e)) =>
lazymatch e with
| shq 32 ?o => destruct (D1 o ltac:(lia)) as [Dd Dr]; apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e _ Dd Dr); [cbn; lia | assumption]
| shq 46 16 => destruct D2 as [Dd Dr]; apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e _ Dd Dr); [cbn; lia | assumption]
| SOff 32 ?o => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e (g + o));
[ cbn [sv_denot]; rewrite E32, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 46 0 => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e cfp);
[ cbn [sv_denot]; rewrite E46, unsigned_lit_small, Z.add_0_r by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 46 ?o => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e (cfp + o));
[ cbn [sv_denot]; rewrite E46, unsigned_lit_small by lia; reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | assumption ]
| SOff 67 0 => apply (chunk_ok_val SEGS E m (sp0 - 224) off 8 e a4v);
[ cbn [sv_denot]; rewrite E67, unsigned_lit_small, Z.add_0_r by exact Ha4; reflexivity | exact Ha4 | cbn; lia | assumption ]
end end.
Qed.
Lemma af_side_sep : forall ly S W mem md g s1 N cb lya sp0 (Zs : Z -> Prop),
AR SEGS B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> astk_ok TADDFRAME_STK lya sp0 ->
(forall a, Zs a -> (sp0 - TADDFRAME_STK <= a < sp0) \/ (g <= a < g + 96)) ->
(forall i, 0 <= i < 48 -> 0 <= cg_raw s1 + i < 2 ^ 64 /\ ~ Zs (cg_raw s1 + i)) /\
(forall f i, In (Some f) (cg_frames s1) -> 0 <= i < 40 -> 0 <= fr_ptr f + i < 2 ^ 64 /\ ~ Zs (fr_ptr f + i)).
Proof.
intros ly S W mem md g s1 N cb lya sp0 Zs HAR HP Hstk HZ.
pose proof Hstk as (_ & Hstk0 & Hceil & Hslo & _). pose proof asan_consts as (C1 & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
assert (HP' : Permutation (ablocks B ly S) ((g, CGIF_SIZE) :: ((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)) by exact HP.
assert (Hraw : In (cg_raw s1, RAW_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. apply in_app_iff. left. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hraw) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (cg_raw s1, RAW_SIZE) _ HAR HP' ltac:(apply in_app_iff; left; left; reflexivity)) as HdGR.
unfold zdisjoint, block_rng in HdGR. cbn [fst snd] in HdGR. change (req_size CGIF_SIZE) with 96 in HdGR. change (req_size RAW_SIZE) with 48 in HdGR.
split.
- intros i Hi. split; [lia|]. intros Hz. destruct (HZ _ Hz); lia.
- intros f i Hf Hi.
assert (Hft : In (fr_ptr f, FRAME_SIZE) (((cg_raw s1, RAW_SIZE) :: pal_blocks s1 ++ frames_blocks N (cg_frames s1)) ++ cb)).
{ apply in_app_iff. left. right. apply in_app_iff. right. unfold frames_blocks. apply in_flat_map. exists (Some f). split; [exact Hf | left; reflexivity]. }
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HP'|]. right. exact Hft. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
pose proof (sep_hd_in B LAWS ly S W mem md (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HP' Hft) as HdGF.
unfold zdisjoint, block_rng in HdGF. cbn [fst snd] in HdGF. change (req_size CGIF_SIZE) with 96 in HdGF. change (req_size FRAME_SIZE) with 40 in HdGF.
split; [lia|]. intros Hz. destruct (HZ _ Hz); lia.
Qed.
Lemma af_fp_cover : forall ly S (regs : bvmap 5 word) g s N lyc Sc b a,
(In b (cgif_blocks g s N) \/ af_newtok B ly S regs g s N b) -> In b (ablocks B lyc Sc) ->
fst b <= a < fst b + req_size (snd b) ->
(inFP (FPa g s N) a /\ exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a.
Proof.
intros ly S regs g s N lyc Sc [p n] a Hb Hlive Ha. cbn [fst snd] in Ha.
assert (LIVE : exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= a < p0 + req_size n0) by (exists p, n; split; [exact Hlive | exact Ha]).
destruct Hb as [Hb | [Htok _]].
- left. split; [|exact LIVE]. unfold FPa. replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n (a - p) Hb). lia.
- assert (EQD : forall x y : Z * Z, {x = y} + {x <> y}) by (intros [x1 x2] [y1 y2]; decide equality; apply Z.eq_dec).
destruct (in_dec EQD (p, n) (ablocks B ly S)) as [Hin | Hnin].
+ left. split; [|exact LIVE]. replace a with (p + (a - p)) by lia. apply (Htok Hin (a - p)). cbn [snd]. lia.
+ right. exists p, n. split; [exact Hlive | split; [exact Hnin | exact Ha]].
Qed.
Lemma af_obj_ok_flush : forall s s1 N i gen' rwcur',
af_obj_ok s s1 N -> cgif_wf (flush_upd s1 i gen' rwcur') N -> af_obj_ok s (flush_upd s1 i gen' rwcur') N.
Proof.
intros s s1 N i gen' rwcur' (_ & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) HWF.
split; [exact HWF|]. cbn. repeat (split; [assumption|]). assumption.
Qed.
Lemma af_reseed : forall pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 more,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 ->
getr regs1 2 = w64 (spZ regs - 224) ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regions 0 true af_lcD (cg_ihead s1) wlo whi) = true ->
st_ok_pi SEGS VAL E (ss_af pc sregs 0 true af_lcD (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 more a4v E
CX MID Rsp HL Hwlo Hwhi HREG HWFR.
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
pose proof (afobj_journal sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) as HFO1.
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
exact (af_seed B TL LAWS pc sregs 0 true af_lcD (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(af_lcD_ok E _ sp0 g cfp a4v HL E32 E38 E46 E67 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) Ha4)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)).
Qed.
Lemma af_reseedx : forall pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest
lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k s1 X more,
let a4v := (if Z.land fattr 4 =? 0 then 1 else 0) in
let E := Eimg (Ereg regs1 (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] (a4v :: more))) in
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_midx B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 X ->
getr regs1 2 = w64 (spZ regs - 224) ->
af_locs (mrestrict (w_H Wc) memc) (spZ regs) g cfp a4v ->
Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (spZ regs - 224 - 0)) lcx ->
0 <= wlo -> whi <= 96 ->
regs_ok E sregs regs1 ->
regions_wf (af_regions 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi) = true ->
st_ok_pi SEGS VAL E (ss_af pc sregs 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi) (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa af_SH E (mrestrict (w_H Wc) memc).
Proof.
intros pc sregs wlo whi lcx ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 X more a4v E
CX MID Rsp HL HLX Hwlo Hwhi HREG HWFR.
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
pose proof (afobj_journal sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) as HFO1.
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
exact (af_seed B TL LAWS pc sregs 0 true (af_lcD ++ lcx) (cg_ihead s1) wlo whi Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx (a4v :: more)
HAR1 Hing1 HFO1 Hstk Hpres Rsp' (or_introl eq_refl) Hwlo Hwhi HREG HWFR
(proj2 (Forall_app _ _ _) (conj (af_lcD_ok E _ sp0 g cfp a4v HL E32 E38 E46 E67 ltac:(lia) Hgceil (proj1 Hcfp) (proj2 Hcfp) Ha4) HLX))
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)).
Qed.
End h.
End d.
End c.
