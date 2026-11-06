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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w YC0j YC0v YC0r YC0t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition AF_E2 : Z := 0x8656c.
Definition AF_E3 : Z := 0x8660c.
Definition af_regs_at0 (B : asyms) (regs regs1 : bvmap 5 word) : Prop :=
getr regs1 2 = w64 (spZ regs - 224) /\ getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B).
Definition AF_RET0_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1,
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 ->
SRr trasegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 AF_RET) memc (seg_rom trasegs)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_E3_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at0 B regs regs1 -> getr regs1 8 = w64 (g + 88) -> getr regs1 22 = w64 SB -> af_s1_at regs1 g -> getr regs1 16 = w64 cfp ->
getr regs1 23 = w64 nw -> getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw ->
SRr trasegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 AF_E3) memc (seg_rom trasegs)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Definition AF_E2_stmt (B : asyms) : Prop :=
forall ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 (i nw : Z) (fn : frame_st),
af_cx B ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest ->
af_mid B ly S W regs mem md g cfp s N img fattr lpa nlp rest lyc Sc Wc memc mdc k s1 -> k <= EV_ADDFRAME ->
af_regs_at B regs regs1 g -> af_s1_at regs1 g -> getr regs1 24 = w64 i -> getr regs1 23 = w64 nw ->
getr regs1 16 = w64 cfp -> getr regs1 17 = w64 (cfp + 16) ->
getr regs1 10 = w64 (nw + 33) -> getr regs1 13 = w64 (SB + (nw + 33) / 8) ->
af_locsE (mrestrict (w_H Wc) memc) (spZ regs) g cfp (if Z.land fattr 4 =? 0 then 1 else 0) ->
(i = 1 \/ i = 2) -> nth (Z.to_nat i) (cg_frames s1) None = Some fn -> fr_ptr fn = nw -> cg_ihead s1 = i ->
SRr trasegs Wc (mkCfg (mkst regs1 (Z_to_bv 64 AF_E2) memc (seg_rom trasegs)) mdc)
(af_post B ly S W regs mem md g s N img fattr lpa nlp rest EV_ADDFRAME).
Lemma tcgif_vals_upd_frame : forall s i f f',
nth_error (cg_frames s) i = Some (Some f) -> fr_ptr f' = fr_ptr f -> tcgif_vals (upd_frame s i f') = tcgif_vals s.
Proof.
intros s i f f' Hi Hp. unfold upd_frame. rewrite tcgif_vals_set_frames. unfold tcgif_vals.
assert (E : forall k, frame_ptr (nth k (list_set (cg_frames s) i (Some f')) None) = frame_ptr (nth k (cg_frames s) None)).
{ intros k. destruct (Nat.eq_dec k i) as [->|Hne].
- rewrite nth_list_set_same by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
rewrite (nth_error_nth _ _ _ Hi). cbn. exact Hp.
- rewrite YI1h.nth_list_set_other by lia. reflexivity. }
rewrite !E. reflexivity.
Qed.
Lemma tcgif_vals_ins_frame : forall s i f', (i < 3)%nat -> length (cg_frames s) = 3%nat ->
tcgif_vals (upd_frame s i f') = list_set (tcgif_vals s) i (fr_ptr f').
Proof.
intros s i f' Hi Hlen. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold upd_frame. rewrite Hfr. unfold tcgif_vals, set_frames. cbn [cg_frames cg_pal cg_attr cg_gen cg_W cg_H cg_ngp cg_loops cg_raw cg_cur cg_ihead].
rewrite Hfr. destruct i as [|[|[|i]]]; try lia; reflexivity.
Qed.
Lemma tcgif_vals_set_ihead_ls : forall s ih, tcgif_vals (set_ihead s ih) = list_set (tcgif_vals s) 16 ih.
Proof. intros. reflexivity. Qed.
Lemma tcgif_vals_set_cur_ls : forall s c, tcgif_vals (cl_set_cur s c) = list_set (tcgif_vals s) 15 c.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_upd_frame : forall g s i f', traw_vals g (upd_frame s i f') = traw_vals g s.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_set_ihead : forall g s ih, traw_vals g (set_ihead s ih) = traw_vals g s.
Proof. intros. reflexivity. Qed.
Lemma traw_vals_set_cur : forall g s c, traw_vals g (cl_set_cur s c) = traw_vals g s.
Proof. intros. reflexivity. Qed.
Lemma tframes_at_upd : forall m m' s i (f : option frame_st) f',
(forall x, In (Some x) (cg_frames s) -> obj_at trasegs m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i = Some f ->
obj_at trasegs m' (fr_ptr f') LAY_Frame (frame_vals f') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i ->
forall k, 0 <= k < 40 -> mbyte trasegs m' (fr_ptr x + k) = mbyte trasegs m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame s i f')) -> obj_at trasegs m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof.
intros m m' s i f f' Hfr Hi Hnew Hkept x Hx. unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hne)].
- injection Hx' as ->. exact Hnew.
- apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hfr x ltac:(eapply nth_error_In; exact Hj)) lay_inside_Frame).
intros k Hk. apply (Hkept j x Hj Hne k Hk).
Qed.
Lemma tframes_at_upd2 : forall m m' s i1 i2 (f1 : option frame_st) f1' (f2 : option frame_st) f2',
(forall x, In (Some x) (cg_frames s) -> obj_at trasegs m (fr_ptr x) LAY_Frame (frame_vals x)) ->
nth_error (cg_frames s) i1 = Some f1 -> nth_error (cg_frames s) i2 = Some f2 -> i1 <> i2 ->
obj_at trasegs m' (fr_ptr f1') LAY_Frame (frame_vals f1') ->
obj_at trasegs m' (fr_ptr f2') LAY_Frame (frame_vals f2') ->
(forall j x, nth_error (cg_frames s) j = Some (Some x) -> j <> i1 -> j <> i2 ->
forall k, 0 <= k < 40 -> mbyte trasegs m' (fr_ptr x + k) = mbyte trasegs m (fr_ptr x + k)) ->
forall x, In (Some x) (cg_frames (upd_frame (upd_frame s i1 f1') i2 f2')) -> obj_at trasegs m' (fr_ptr x) LAY_Frame (frame_vals x).
Proof.
intros m m' s i1 i2 f1 f1' f2 f2' Hfr H1 H2 Hne Ho1 Ho2 Hkept x Hx.
unfold upd_frame, set_frames in Hx. cbn [cg_frames] in Hx.
destruct (In_list_set _ _ _ _ Hx) as [Hx'|(j & Hj & Hj2)]; [injection Hx' as ->; exact Ho2|].
destruct (Nat.eq_dec j i1) as [->|Hj1].
- rewrite YI1h.nth_error_list_set_same in Hj by (apply (proj1 (nth_error_Some _ _)); rewrite H1; discriminate).
injection Hj as ->. exact Ho1.
- rewrite YI1h.nth_error_list_set_other in Hj by lia.
apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hfr x ltac:(eapply nth_error_In; exact Hj)) lay_inside_Frame).
intros k Hk. apply (Hkept j x Hj Hj1 Hj2 k Hk).
Qed.
Lemma af_obj_ok_upd_frame : forall s s1 N i f f',
af_obj_ok s s1 N -> nth_error (cg_frames s1) i = Some (Some f) -> frame_wf (cg_attr s1) f' -> af_obj_ok s (upd_frame s1 i f') N.
Proof.
intros s s1 N i f f' (HWF & H) Hi Hf. split; [exact (cgif_wf_upd_frame s1 N i f f' HWF Hi Hf) | exact H].
Qed.
Lemma af_obj_ok_set_cur : forall s s1 N c, af_obj_ok s s1 N -> af_obj_ok s (cl_set_cur s1 c) N.
Proof. intros s s1 N c (HWF & H). split; [exact HWF | exact H]. Qed.
Definition regsX0 : list sv := Eval vm_compute in sr_atoms.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws trasegs B.
Lemma af_frames_sep : forall ly S W mem md g s1 N cb j1 j2 f1 f2,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> length (cg_frames s1) = 3%nat ->
nth_error (cg_frames s1) j1 = Some (Some f1) -> nth_error (cg_frames s1) j2 = Some (Some f2) -> (j1 < j2)%nat ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1.
Proof.
intros ly S W mem md g s1 N cb j1 j2 f1 f2 HAR HP Hlen H1 H2 Hlt.
destruct (cg_frames s1) as [|o0 [|o1 [|o2 [|x l]]]] eqn:Hfr; cbn in Hlen; try discriminate.
unfold cgif_blocks in HP. rewrite Hfr, frames_blocks_3 in HP.
assert (FB : forall f, In (fr_ptr f, FRAME_SIZE) (frames_blocks N [Some f])) by (intros f; rewrite frames_blocks_some; left; reflexivity).
assert (D : forall l1 l2, Permutation (ablocks B ly S) (l1 ++ l2) -> In (fr_ptr f1, FRAME_SIZE) l1 -> In (fr_ptr f2, FRAME_SIZE) l2 ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1).
{ intros l1 l2 HP' Ha Hb. pose proof (sep_app B LAWS ly S W mem md _ _ l1 l2 HAR HP' Ha Hb) as X.
unfold zdisjoint, block_rng in X. cbn [fst snd] in X. change (req_size FRAME_SIZE) with 40 in X. lia. }
destruct j1 as [|[|[|j1]]]; destruct j2 as [|[|[|j2]]]; cbn in H1, H2; try lia; try (destruct j2; discriminate); try (destruct j1; discriminate);
injection H1 as ->; injection H2 as ->.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [Some f1]) (frames_blocks N [Some f2] ++ frames_blocks N [o2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply FB.
+ apply in_app_iff. left. apply FB.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [Some f1] ++ frames_blocks N [o1]) (frames_blocks N [Some f2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply in_app_iff. left. apply FB.
+ apply in_app_iff. left. apply FB.
- apply (D (((g, CGIF_SIZE) :: (cg_raw s1, RAW_SIZE) :: pal_blocks s1) ++ frames_blocks N [o0] ++ frames_blocks N [Some f1]) (frames_blocks N [Some f2] ++ cb)).
+ eapply Permutation_trans; [exact HP|]. cbn [app]. rewrite <- ?app_assoc. cbn [app]. apply Permutation_refl.
+ apply in_app_iff. right. apply in_app_iff. right. apply FB.
+ apply in_app_iff. left. apply FB.
Qed.
Lemma af_frames_sep2 : forall ly S W mem md g s1 N cb j1 j2 f1 f2,
AR trasegs B ly S W mem md -> Permutation (ablocks B ly S) (cgif_blocks g s1 N ++ cb) -> length (cg_frames s1) = 3%nat ->
nth_error (cg_frames s1) j1 = Some (Some f1) -> nth_error (cg_frames s1) j2 = Some (Some f2) -> j1 <> j2 ->
fr_ptr f1 + 40 <= fr_ptr f2 \/ fr_ptr f2 + 40 <= fr_ptr f1.
Proof.
intros ly S W mem md g s1 N cb j1 j2 f1 f2 HAR HP Hlen H1 H2 Hne.
destruct (Nat.lt_ge_cases j1 j2) as [Hlt | Hge].
- exact (af_frames_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HP Hlen H1 H2 Hlt).
- pose proof (af_frames_sep _ _ _ _ _ _ _ _ _ _ _ _ _ HAR HP Hlen H2 H1 ltac:(lia)) as X. lia.
Qed.
End e.
Section h.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsX0_ok : forall (regs1 : bvmap 5 word) extra, regs_ok (Ereg regs1 extra) regsX0 regs1.
Proof.
intros regs1 extra. set (E := Ereg regs1 extra).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity ]
| ]); try (destruct Hr; fail).
Qed.
Lemma af_RET0 : AF_RET0_stmt B.
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR.
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew).
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
pose proof HR as (Rsp & Rgp & Rtp).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seed B TL LAWS AF_RET regsX0 0 true [] (cg_ihead s1) 0 0 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear; lia) ltac:(clear; lia)
(regsX0_ok regs1 _) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)) as [HS SHOK].
set (E := Ereg regs1 _) in HS, SHOK.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 37%nat ltac:(lia)) as E37. pose proof (ES 38%nat ltac:(lia)) as E38.
assert (ESV : forall j (r : bv 5), nth_error af_saved j = Some (bv_unsigned r) -> ew E (54 + j) = getr regs r).
{ intros j r Hj. do 13 (destruct j as [|j]; [cbn in Hj; injection Hj as Hr; lazymatch goal with |- ew _ ?m = _ => rewrite (ES m ltac:(clear; cbn; lia)) end;
cbn [Nat.sub Nat.add nth af_extra af_saved map app firstn repeat]; rewrite Hr, Z_to_bv_bv_unsigned; reflexivity|]).
exfalso. clear - Hj. do 8 (destruct j as [|j]; [discriminate Hj|]). cbn in Hj. destruct j; discriminate Hj. }
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E37, E38.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (obj_at_nth trasegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA.
{ awr_a Usp E32u Hing HTS. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN.
cbv beta in UN.
clear HF HFr HG.
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trasegs tratbl_lib tratbl_lib_ok Hwx Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold af_post.
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyc, Sc, rg, mm, mdx end.
split; [rewrite R1; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; change 54%nat with (54 + 0)%nat; rewrite (ESV 0%nat (1%bv : bv 5) eq_refl); rewrite Hra; reflexivity|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k trasegs _); [apply (ajournal_materialize trasegs _ LAWS Hsegs); exact HJ | exact Hk]|].
split.
{ apply aregs_preserved_eqs;
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ lazymatch goal with |- ew _ ?n = getr _ ?rr => let j := eval vm_compute in (n - 54)%nat in change n with (54 + j)%nat; exact (ESV j rr eq_refl) end
| rewrite Usp; unfold sp0, spZ; rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)) at 2; f_equal; clear; lia
| rewrite (EEo 3%nat 3%bv eq_refl), Rgp, Hgp; reflexivity
| rewrite (EEo 4%nat 4%bv eq_refl), Rtp, Htp; reflexivity
| match goal with |- ?gg => idtac "AREGS-FAIL" gg end ]). }
exists s1.
assert (HT2 : tcgif_at (mrestrict (w_H Wc) (ms_mem ms)) g s1).
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros i Hi. apply (mbyte_of_aview trasegs). apply UN; clear - Hi HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview trasegs).
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
apply UN; clear - Hi Hr4096 Hrceil C1 Hceil Hslo HTS; lia.
- intros f Hfin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview trasegs).
assert (Hfb : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. apply in_app_iff. left. exact (af_frame_in_blocks g s1 N f Hfin). }
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hfb) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
apply UN; clear - Hi Hf4096 Hfceil C1 Hceil Hslo HTS; lia. }
split; [exact HT2|]. split; [exact HWF1|]. split; [exact HW1|]. split; [exact HH1|]. split; [exact Hattr1|]. split; [exact Hraw1|].
split; [exact HPerm1|].
intros b Hb. destruct (Hnew b Hb) as [Hold | [Htok Hwr]].
- split.
+ intros _ i Hi. unfold FPa. rewrite (surjective_pairing b) in Hold. exact (inFP_ablocks_fp _ _ _ i Hold Hi).
+ intros blc i Hbl Hi. right. left. split.
* unfold FPa. rewrite (surjective_pairing b) in Hold. exact (inFP_ablocks_fp _ _ _ i Hold Hi).
* exists (fst b), (snd b). split; [rewrite <- surjective_pairing; exact Hbl | lia].
- split; [exact Htok | intros blc i Hbl Hi; exact (Hwr blc lyc [] i Hbl Hi)].
Qed.
End h.
End d.
