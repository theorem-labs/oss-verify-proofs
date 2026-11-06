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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC1b YC2u YC4o YC4q YC4h YC27 YC2r YC20 YC16 YC4u YCct YC4z YCcq YCcp YCcv YCcu YCcw YCcr YCcy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trasegs B.
Hypothesis USH : unw_short_ok.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma rf_F : rf_from B ss_RET (INV_RET B) -> rf_from B ss_F (INV_F B).
Proof.
intros RRET. rf_prelude.
pose proof HINV as (Hk0 & HOK & fmt & img & HIMG). pose proof HIMG as (Efmt & Hfmt & Eimg & Hr4096 & HrHi & HrCeil & Hr16 & Ebl & Timg & Aimg).
cbn [x_N x_lyc x_Sc x_FP x_ly x_S x_STK x_sp0 x_own] in Efmt, Hfmt, Eimg, Hr4096, HrHi, HrCeil, Hr16, Ebl, Timg, Aimg.
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; left; exact Hpdc).
assert (HrIn : In (img, fmt * N) (ablocks B ly3 S3)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HPerm3 : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: Bb)).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm]. }
pose proof (req_size_pos (fmt * N) ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as [HrqN1 HrqN2].
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rf_stream_words HS B10 E33 E34 nb ltac:(rewrite sv_denot_SOff0; exact E34) Vp Vn Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
pose proof (rdword_of_val_mem trasegs _ _ _ _ Vp ltac:(clear - Hp4096 Hpceil Hrq1 C1; lia)) as RWp.
pose proof (rdword_of_val_mem trasegs _ _ _ _ Vn ltac:(clear - Hnb HnbM; lia)) as RWn.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). change (ss_pc ss_F) with 340224.
replace (Z_to_bv 64 340224) with (Z_to_bv 64 (pc_wrap_free (as_code B))) by (rewrite HBcode; reflexivity).
destruct (rrfc_chain USH ly3 (aview trasegs (w_H W3) (ms_mem ms3)) (ms_regs ms3) (as_universe B) st nb pdata RRFC_free_ra (pc_free_ra0 (as_code B)))
as (ch & CH & HTR).
{ unfold s0Z; rewrite Rs0, B10. apply unsigned_lit_small. clear - HSTB C1; lia. }
{ unfold raZ; rewrite Rra. apply unsigned_lit_small. unfold RRFC_free_ra; clear; lia. }
{ unfold RRFC_free_ra; clear; lia. }
{ rewrite HBcode. vm_compute. discriminate. }
{ unfold spZ; rewrite Rsp, Usp; fold (spZ regs); rewrite unsigned_lit_small by (clear - HSPB HTS Has C1; lia); clear - HSTB; lia. }
{ exact Hst8. }
{ exact RWn. }
{ exact RWp. }
{ clear - Hpceil Hrq1 HSTB; lia. }
{ clear - Hnb; lia. }
{ rewrite HBcode. apply (tl_universe B TL). apply TRACES_read_frameconfig_U. apply memZL_In. vm_compute. reflexivity. }
{ intros H4096. exact (proj2 (HXU H4096)). }
eapply SRr_bind.
{ eapply (aj_free_atD trasegs B LAWS Hsegs errno_low ML AFREE W3 (ms_regs ms3) (ms_mem ms3) STK sp0 FP ly S W0 mem0 md0 own
ly3 S3 _ kk img (fmt * N) (spZ regs - 128 - sp0) (Z_to_bv 64 RRFC_free_ra) ch HJ3 HrIn);
[ rewrite Ra0; exact Eimg
| unfold spZ; rewrite Rsp, Usp; fold (spZ regs); rewrite unsigned_lit_small by (clear - HSPB HTS Has C1; lia); clear; lia
| replace (spZ regs - 128 - sp0) with (spZ regs - sp0 + (-8) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| clear - Hwhi; lia
| clear - Hwlo HTS; lia
| rewrite Rgp, (AG 3%nat) by lia; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp, (AG 4%nat) by lia; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold EV_RRFC in Hev; destruct HJB as [HVB _]; clear - HVB Hev Hk0; lia
| exact CH
| exact HTR
| intros Hin0 i Hi; exact (Timg Hin0 i Hi) ]. }
cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 CH HTR Vp Vn Vc RWp RWn.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & Ebl2 & Ebl3) & Hfrs2 & HBD & HK).
assert (HJB2 : jbud Sc S2 (kk + 1 - k)).
{ replace (kk + 1 - k) with ((kk - k) + 1) by (clear; lia).
apply (jbud_step Sc S3 S2 (kk - k) 1 1 0 0 0); [rewrite Hk0; clear; lia | clear; lia | exact HJB | exact HBD | clear; lia | clear; lia | clear; lia | unfold HULL_UNIT; clear; lia]. }
replace (sp0 + (spZ regs - 128 - sp0)) with (spZ regs - 128) in HK by (clear; lia).
pose proof (proj1 HJ2) as HAR2. pose proof HJ2 as (_ & Hly2 & _).
assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HPerm2 : Permutation (ablocks B ly2 S2) Bb).
{ rewrite Ebl3. apply Permutation_sym. apply (@Permutation_cons_app_inv _ Bb l1 l2 (img, fmt * N)). rewrite <- Ebl2. apply Permutation_sym. exact HPerm3. }
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
assert (HBb3 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly3 S3))
by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm3 | right; exact Hb]).
assert (HsepB : forall b m, In (b, m) Bb -> img + req_size (fmt * N) <= b \/ b + req_size m <= img).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1' & l2' & El).
assert (HP' : Permutation (ablocks B ly3 S3) ((img, fmt * N) :: (b, m) :: l1' ++ l2')).
{ eapply Permutation_trans; [exact HPerm3|]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm trasegs B LAWS _ _ _ _ _ _ _ _ HAR3 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
assert (HimgFS : forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ (img <= a < img + req_size (fmt * N))).
{ intros c p a Hcp Ha Hin. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ img (fmt * N) c p HAR3 HrIn ltac:(rewrite Hfrs3; exact Hcp)) as D.
rewrite EFA3 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin HrqN2. lia.
+ destruct (frames_bounds trasegs B LAWS _ _ _ _ _ c p HAR3 ltac:(rewrite Hfrs3; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA3 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. lia. }
pose proof (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ ly3 S3 _ _ _ _ _ HKEPT HK ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb3
ltac:(intros b m i Hb Hi Hin; pose proof (HsepB b m Hb); clear - Hi Hin H; lia) Hfrs3 EFA3 HimgFS) as KEPT2.
assert (RAdst2 : range_addressable (aview trasegs (w_H W2) mem2) SHADOW_OFF dst 24).
{ eapply (RA_kept_call B ly3 S3); [exact HK | exact Hfin3 | intros a Ha; cbn beta in Ha; clear - Ha HrHi HrqN2; lia | exact Hcid | rewrite EFA3; exact Hfal
| rewrite EFA3; clear - HFhi1 C3; lia | rewrite EFA3; lia | rewrite EFA3; exact Hdst1 | rewrite EFA3; exact Hdst2 | exact HRAdst]. }
assert (RAst2 : range_addressable (aview trasegs (w_H W2) mem2) SHADOW_OFF st 24).
{ pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
apply (RA_stack B LAWS ly2 S2 W2 mem2 _ st 24 HAR2); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]. }
clear HKEPT HRAst HRAdst.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4]%nat AG
ltac:(first [ eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ2 | evalER AG | lia | lia | lia | cbn; lia | cbn; lia]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword trasegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword trasegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | lia]
| eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalER AG | exact Hfin3 | left; cbn [YQ0b.r_lo YQ0b.r_hi]; rewrite EFA3; lia
| cbn [YQ0b.r_lo YQ0b.r_hi]; intros a Ha; apply (HimgFS cid pos a Hfin); left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia
| intros a Ha; apply (fun H => proj1 (HFpres2 a H)); rewrite EFA2; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2 | exact Hpd]).
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK RBspan 0x81988.
all: try (oblsA HJ2 Hpd2 RAst2 RAdst2 E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA2. }
rf_after_run Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rf_stream_words HS B10 E33 E34 nb ltac:(rewrite sv_denot_SOff0; exact E34) Vp Vn Vc.
rfj_join HS ss_RET 310%nat rf_RET_deads_bv.
rf_hand RRET HS.
- rewrite Hfrs2. exact Hfrs3.
- split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 0, nb.
split; [exact Ra0|]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcur; lia|].
right. left. split; [reflexivity | exact HPerm2].
Qed.
End e.
End d.
