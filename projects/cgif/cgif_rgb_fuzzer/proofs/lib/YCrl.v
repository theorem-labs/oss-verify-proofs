(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YG0e YCcz YCd0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrp YCrb YChy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rf_R5 : rf_from B ss_EPI (INV_EPI B) -> rf_from B ss_R5 (INV_R5 B).
Proof.
intros REPI. rf_prelude.
destruct HINV as (Hk0 & (curi & Ecur & Hcuri) & fmt & img & HIMG). destruct HIMG as (Efmt & Hfmt & Eimg & Hr4096 & HrHi & HrCeil & Hr16 & Ebl & Timg & Aimg).
cbn [x_N x_lyc x_Sc x_FP x_ly x_S x_STK x_sp0 x_own] in Efmt, Hfmt, Eimg, Hr4096, HrHi, HrCeil, Hr16, Ebl, Timg, Aimg.
unfold rf_IMG in Eimg.
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; left; exact Hpdc).
assert (HrIn : In (img, fmt * N) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: Bb)).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm]. }
pose proof (req_size_pos (fmt * N) ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as [HrqN1 HrqN2].
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop & Htop2).
reshok HS.
aj_run_tok trbtbl_lib_ok HS HJ3 SHOK RBspan.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ3.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
norm_ss HS.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan RRFC_EPI.
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ3.
rregD HS (10%bv : bv 5) Ra0D.
assert (Ra0 : forall rg e, getr rg 10 = sv_denot E (SAlu ALU_SLTU e (SLit 1)) -> branch_taken BC_EQ (sv_denot E e) (sv_denot E (SLit 0)) = true -> getr rg 10 = Z_to_bv 64 1).
{ intros rg e H1 H2. rewrite H1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite branch_eq_U in H2. apply Z.eqb_eq in H2. rewrite (U_lit E 0) in H2 by lia. rewrite H2, (U_lit E 1) by lia. reflexivity. }
pose proof (Ra0 _ _ Ra0D Hc) as Ra01. clear Ra0 Ra0D Hc.
rfb_epi_arrive HS curi img fmt ltac:(rfb_old_atom Ecur) ltac:(rfb_old_atom Eimg) ltac:(rfb_old_atom Efmt) E390 E391 E392.
rfj_join HS ss_EPI 400%nat rf_EPI_deads_bv.
rf_hand REPI HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 1, curi, img, fmt.
split; [rewrite (ew_havoc_new _ 400 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Ra01|].
split; [rewrite ew_havoc_old by (cbn; lia); exact E390|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E391|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E392|].
split; [exact Hcuri|]. right. right. split; [reflexivity|]. split; [exact Hfmt|]. split; [clear - Hr4096 HrCeil HrqN1 C1; lia|].
split; [exact HPerm3|]. split; [exact Timg | exact Aimg].
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => first [rename Hb into Hc | idtac] end.
rregD HS (21%bv : bv 5) R21D.
rewrite branch_eq_U in Hc.
lazymatch type of R21D with getr ?rg _ = sv_denot ?Ex ?e =>
assert (Hs5 : bv_unsigned (getr rg 21) <> 0)
by (rewrite R21D; change (U Ex e <> 0); intros Hz; rewrite Hz in Hc; rewrite (U_lit Ex 0) in Hc by lia; discriminate Hc) end.
clear Hc R21D.
norm_ss HS.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) [21%bv : bv 5]) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trbsegs 350 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
assert (E350 : bv_unsigned (ew (havoc Ex 350 vals') 350) <> 0)
by (rewrite (ew_havoc_new _ 350 vals' 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Hs5);
clear HS; rename HS3 into HS;
set_regs_rec HS 350%nat vals' 0%nat [21%bv : bv 5] end.
lazymatch type of HS with st_ok _ ?Ev2 ?ssx2 ?msx2 =>
pose proof (st_ok_add_fact trbsegs Ev2 ssx2 msx2 350%nat (mkAF 1 18446744073709551615 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Z.pow_0_r, Z.mod_1_r;
pose proof (bv_unsigned_in_range 64 (ew Ev2 350)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; clear - Hq E350; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. clear E350 Hs5.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ3 SHOK RBspan 340932.
all: try (oblsA HJ3 Hpd3 HRAst HRAdst E10 E11 E11 E32).
{ awrRFB AG fpos F EFA3 ltac:(right; exact Hown). }
rfb_after_run AG HJ3.
rfb_chain HS HJ3 Hch1.
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
aconstsF HJ3 Kgot1 Kcell1 Kguar1 Kuar1.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 340932) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_free_atD trbsegs B LAWS Hsegs errno_low ML AFREE W3 (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
ly3 S3 _ kk img (fmt * N) (sp1 - sp0) (Z_to_bv 64 RRFC_free_ra) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3 HrIn) end;
[ rewrite Ra0; evalE AG
| unfold spZ; rewrite Rsp; evalE AG
| rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity
| clear - Hsp1 Hwhi; lia
| clear - Hsp1 Hwlo HTS; lia
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold EV_RRFC in Hev; destruct HJB as [HVB _]; clear - HVB Hev Hk0; lia
| apply (achain_chain_pre ly3 _ sp1 (spZ regs) _ _ Hch1);
[ unfold spZ at 1 2; rewrite Rsp; evalE AG; clear - Hsp1 HSPB HTS Has C1; lia
| unfold s0Z; rewrite Rs0; evalE AG
| unfold raZ; rewrite Rra, unsigned_lit_small by (unfold RRFC_free_ra; clear; lia); unfold RRFC_free_ra; clear; lia ]
| rewrite call_trace_of_spine; cbn [spine map fst snd]; fold (spine ch); unfold raZ at 1; rewrite Rra, unsigned_lit_small by (unfold RRFC_free_ra; clear; lia);
rewrite HBcode, (tl_universe B TL); apply TRACES_read_frameconfig_U; apply memZL_In;
cbn [CTX_read_frameconfig In] in HCTX; destruct HCTX as [Hc | [Hc | [Hc | [Hc | []]]]]; injection Hc as <- <-; vm_compute; reflexivity
| intros Hin0 i Hi; exact (Timg Hin0 i Hi) ]. }
cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 Hch1.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl2 & Ebl3) & Hfrs2 & HBD & HK).
assert (HJB2 : jbud Sc S2 (kk + 1 - k)).
{ replace (kk + 1 - k) with ((kk - k) + 1) by (clear; lia).
apply (jbud_step Sc S3 S2 (kk - k) 1 1 0 0 0); [rewrite Hk0; clear; lia | clear; lia | exact HJB | exact HBD | clear; lia | clear; lia | clear; lia | unfold HULL_UNIT; clear; lia]. }
unfold ASTACK in HK. replace (sp0 + (sp1 - sp0) - 16384) with (sp1 - 16384) in HK by (clear; lia). replace (sp0 + (sp1 - sp0)) with sp1 in HK by (clear; lia).
pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & Hly2 & _).
assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HPerm2 : Permutation (ablocks B ly2 S2) Bb).
{ rewrite Ebl3. apply Permutation_sym. apply (@Permutation_cons_app_inv _ Bb l1 l2 (img, fmt * N)). rewrite <- Ebl2. apply Permutation_sym. exact HPerm3. }
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin3).
assert (Hfin02 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin0).
assert (Hfrs2' : frames S2 = (0, fpos) :: frames Sc) by (rewrite Hfrs2; exact Hfrs3).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin02) as (_ & _ & HF0pres2 & HF0Spres2).
change (fs_frame_bytes 0) with 64 in HF0pres2, HF0Spres2. change (64 / 8) with 8 in HF0Spres2. rewrite !EFA2 in HF0pres2, HF0Spres2. fold F in HF0pres2, HF0Spres2.
aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
assert (HBb3 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly3 S3))
by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | right; exact Hb]).
assert (HsepB : forall b m, In (b, m) Bb -> img + req_size (fmt * N) <= b \/ b + req_size m <= img).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1' & l2' & El).
assert (HP' : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: (b, m) :: l1' ++ l2')).
{ eapply Permutation_trans; [exact HPerm3|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm trbsegs B LAWS _ _ _ _ _ _ _ _ HAR3 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
assert (HimgFS : forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ (img <= a < img + req_size (fmt * N))).
{ intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ img (fmt * N) c p HAR3 HrIn ltac:(rewrite Hfrs3; right; exact Hcp)) as D.
rewrite EFA3 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin HrqN2. lia.
+ destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ c p HAR3 ltac:(rewrite Hfrs3; right; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA3 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. lia. }
assert (HimgD : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (img <= a < img + req_size (fmt * N)))
by (intros a Ha; apply (HimgFS cid pos a Hfin); left; unfold in_zr, frame_rng; cbn [fst snd]; exact Ha).
assert (HimgF0 : forall a, F <= a < F + 64 -> ~ (img <= a < img + req_size (fmt * N))).
{ intros a Ha Hin. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ img (fmt * N) 0 fpos HAR3 HrIn Hfin0) as D.
rewrite EFA3 in D. fold F in D. change (fs_frame_bytes 0) with 64 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
assert (HimgS0 : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> ~ (img <= a < img + req_size (fmt * N)))
by (intros a Ha Hin; unfold SB in Ha; clear - Ha Hin HrHi HF8lo HF8hi HrqN2; lia).
pose proof (rfc_kept_callF B _ _ _ _ _ _ _ _ _ _ ly3 S3 _ _ _ _ _ HKEPT HK ltac:(clear - Hsp1 HTS Has; lia) ltac:(clear - Hsp1; lia) HBb3
ltac:(intros b m i Hb Hi Hin; pose proof (HsepB b m Hb) as Hq; clear - Hi Hin Hq; lia)
ltac:(intros c p Hcp; rewrite Hfrs3; right; exact Hcp) EFA3 HimgFS) as KEPT2.
clear HKEPT. rename KEPT2 into HKEPT.
rfb_RA HKEPT HJ2 HRAst HRAdst.
rbox HrHi.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ2 HP2 l AG
ltac:(idtac; first [ keptRFB HK HJ2 AG Kgot1 Kgot2 Kcell1 Kcell2 Kguar1 Kguar2 Kuar1 Kuar2 Hfin3 Hfin0 HFpres2 HF0pres2 HF0Spres2
ltac:(first [ apply HimgD; rewrite_frame_addr; lia | apply HimgF0; lia | apply HimgS0; unfold SB; lia ])
| match goal with |- ?g => idtac "KEPTFAIL" g end]) end.
clear HimgFS HimgD HimgF0 HimgS0 HsepB.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hpd]).
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan RRFC_EPI.
all: try (oblsA HJ2 Hpd2 HRAst HRAdst E10 E11 E11 E32).
{ awrRFB AG fpos F EFA2 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rfb_epi_arrive HS curi img fmt ltac:(rfb_old_atom Ecur) ltac:(rfb_old_atom Eimg) ltac:(rfb_old_atom Efmt) E390 E391 E392.
rfj_join HS ss_EPI 400%nat rf_EPI_deads_bv.
rf_hand REPI HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 0, curi, img, fmt.
split; [rewrite (ew_havoc_new _ 400 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Ra0|].
split; [rewrite ew_havoc_old by (cbn; lia); exact E390|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E391|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E392|].
split; [exact Hcuri|]. right. left. split; [reflexivity | exact HPerm2].
Qed.
End f.
End d.
