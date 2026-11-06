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
Hypothesis AMALLOC : amalloc_realizes trasegs B.
Hypothesis USH : unw_short_ok.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma rf_M1 : rf_from B ss_RET (INV_RET B) -> rf_from B ss_M2 (INV_M2 B) -> rf_from B ss_M (INV_M B).
Proof.
intros RRET RN. rf_prelude.
pose proof HINV as (Hk0 & Eab3 & HOK & fmt & Efmt & Hfmt).
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpdc).
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
assert (Hlive3 : blocks_bytes S3 + fmt * N <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B lyc Sc). unfold LIVE_RRFC, RGB_NMAX in *. clear - Hlive HN Hfmt. lia. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregD HS (10%bv : bv 5) Ra0D.
assert (DN : getr (ms_regs ms3) 10 = w64 (fmt * N)).
{ rewrite Ra0D. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 12 N E12), (U_atom E 86 fmt Efmt) by (unfold RGB_NMAX in HN; clear - HN Hfmt; lia).
rewrite zcanon_id by (unfold M64, RGB_NMAX in *; clear - HN Hfmt; nia). clear; lia. }
rf_stream_words HS B10 E33 E34 (cur + 7) ltac:(rewrite denot_lit_U; f_equal; apply U_atom_off; [exact E35 | lia | lia]) Vp Vn Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
pose proof (rdword_of_val_mem trasegs _ _ _ _ Vp ltac:(clear - Hp4096 Hpceil Hrq1 C1; lia)) as RWp.
pose proof (rdword_of_val_mem trasegs _ _ _ _ Vn ltac:(clear - Hnb HnbM; lia)) as RWn.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). change (ss_pc ss_M) with 340228.
replace (Z_to_bv 64 340228) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
destruct (rrfc_chain USH ly3 (aview trasegs (w_H W3) (ms_mem ms3)) (ms_regs ms3) (as_universe B) st nb pdata RRFC_malloc_ra (pc_malloc_ra0 (as_code B)))
as (ch & CH & HTR).
{ unfold s0Z; rewrite Rs0, B10. apply unsigned_lit_small. clear - HSTB C1; lia. }
{ unfold raZ; rewrite Rra. apply unsigned_lit_small. unfold RRFC_malloc_ra; clear; lia. }
{ unfold RRFC_malloc_ra; clear; lia. }
{ rewrite HBcode. vm_compute. discriminate. }
{ unfold spZ; rewrite Rsp, Usp; fold (spZ regs); rewrite unsigned_lit_small by (clear - HSPB HTS Has C1; lia); clear - HSTB; lia. }
{ exact Hst8. }
{ exact RWn. }
{ exact RWp. }
{ clear - Hpceil Hrq1 HSTB; lia. }
{ clear - Hnb; lia. }
{ rewrite HBcode. apply (tl_universe B TL). apply TRACES_read_frameconfig_U. apply memZL_In. vm_compute. reflexivity. }
{ intros H4096. exact (proj1 (HXU H4096)). }
eapply SRr_bind.
{ eapply (aj_malloc_atD trasegs B LAWS Hsegs errno_low ML AMALLOC W3 (ms_regs ms3) (ms_mem ms3) STK sp0 FP ly S W0 mem0 md0 own
ly3 S3 _ kk (fmt * N) (spZ regs - 128 - sp0) (Z_to_bv 64 RRFC_malloc_ra) ch HJ3);
[ exact DN
| unfold MALLOC_MAX, RGB_NMAX in *; clear - HN Hfmt; lia
| exact Hlive3
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
| exact HTR ]. }
cbv beta. clear Ra0 Ra0D Rra Rsp Rgp Rtp Rs0 CH HTR DN Vp Vn Vc RWp RWn.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & HBD & Hres).
assert (HJB2 : jbud Sc S2 (kk + 1 - k)).
{ destruct (malloc_cost_coarse (fmt * N) ltac:(unfold MALLOC_MAX, RGB_NMAX in *; clear - HN Hfmt; lia)) as (_ & Cw & Ch).
replace (kk + 1 - k) with ((kk - k) + 1) by (clear; lia).
apply (jbud_step Sc S3 S2 (kk - k) 1 1 1 (wcost (fmt * N)) (hcost (fmt * N))); [rewrite Hk0; clear; lia | clear; lia | exact HJB | exact HBD | clear; lia | clear; lia | exact Cw | exact Ch]. }
pose proof (proj1 HJ2) as HAR2.
replace (sp0 + (spZ regs - 128 - sp0)) with (spZ regs - 128) in Hres by (clear; lia).
destruct (mres_kept B ly3 S3 W3 _ W2 mem2 ly2 S2 _ _ res (fmt * N) Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 ly3 S3 res (fmt * N) _ _ HAR2 Hres) as Hrng.
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin3).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
pose proof HJ2 as (_ & Hly2 & _).
assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HnewF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (res <> 0 /\ res <= a < res + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ res (fmt * N) cid pos HAR2 (HresIn Hnz) Hfin2) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
pose proof (req_size_pos (fmt * N) ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as [HrqN1 HrqN2].
assert (HBb3 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly3 S3))
by (intros b m Hb; rewrite Eab3; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
assert (KEPT2 : rfc_kept W memc W2 mem2 (spZ regs) Bb lyc Sc st dst).
{ eapply (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ ly3 S3 _ _ _ _ _ HKEPT HK ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb3 _ Hfrs3 EFA3 _).
Unshelve.
- intros b m i Hb Hi [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
destruct (in_split _ _ (HBb3 b m Hb)) as (l1 & l2 & El).
pose proof (sep_blocks_pos trasegs B LAWS ly2 S2 _ _ _ (b, m) (res, fmt * N) l1 l2 [] HAR2 ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. clear - Hd Hi Hin. lia.
- intros c p a Hcp Ha [Hnz Hin]. destruct Hrng as [Hr0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)]; [exact (Hnz Hr0)|]. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame trasegs B LAWS _ _ _ _ _ res (fmt * N) c p HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2, Hfrs3; exact Hcp)) as D.
rewrite EFA2 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin. lia.
+ destruct (frames_bounds trasegs B LAWS _ _ _ _ _ c p HAR2 ltac:(rewrite Hfrs2, Hfrs3; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA2 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. lia. }
assert (RAdst2 : range_addressable (aview trasegs (w_H W2) mem2) SHADOW_OFF dst 24).
{ eapply (RA_kept_call B ly3 S3); [exact HK | exact Hfin3 | intros a [Hnz Ha]; clear - Hnz Ha Hrng; lia | exact Hcid | rewrite EFA3; exact Hfal
| rewrite EFA3; clear - HFhi1 C3; lia | rewrite EFA3; lia | rewrite EFA3; exact Hdst1 | rewrite EFA3; exact Hdst2 | exact HRAdst]. }
assert (RAst2 : range_addressable (aview trasegs (w_H W2) mem2) SHADOW_OFF st 24).
{ pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
apply (RA_stack B LAWS ly2 S2 W2 mem2 _ st 24 HAR2); [rewrite Elo2; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi2; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]. }
clear HKEPT HRAst HRAdst.
reseat HS HJ2 HP2 [4; 5; 6; 7; 8]%nat AG
ltac:(first [ eapply (region_kept_stack_aj trasegs B); [exact HK | exact HJ2 | evalER AG | lia | lia | lia | cbn; lia | cbn; lia]
| apply (region_kept_val trasegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword trasegs _ _ _ _ Kgot1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kgot2) | lia]
| apply (region_kept_val trasegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword trasegs _ _ _ _ Kcell1) | exact (val_mem_of_rdword trasegs _ _ _ _ Kcell2) | lia]
| eapply (region_kept_ownframe_aj trasegs _); [exact HK | evalER AG | exact Hfin3 | left; cbn [YQ0b.r_lo YQ0b.r_hi]; rewrite EFA3; lia
| intros a Ha; cbn beta; apply HnewF; lia | intros a Ha; apply (fun H => proj1 (HFpres2 a H)); rewrite EFA2; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
rreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres. unfold w64 in Rres.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by (apply HBin; exact Hpd3).
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{
destruct Hres as [(_ & Ebl & _) | (Habs & _)]; [| exfalso; clear - Habs Hres0; lia].
pose proof (st_ok_pin_reg' trasegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ2 SHOK RBspan 0x81988.
all: try (oblsA HJ2 Hpd2 RAst2 RAdst2 E10 E11 E36 E32).
{ awrRFC Usp E10 E11 Hown EFA2. }
rf_after_run Usp B10 B11.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rf_stream_words HS B10 E33 E34 (cur + 7) ltac:(rewrite denot_lit_U; f_equal; apply U_atom_off; [exact E35 | lia | lia]) Vp Vn Vc.
rfj_join HS ss_RET 310%nat rf_RET_deads_bv.
rf_hand RRET HS.
- rewrite Hfrs2. exact Hfrs3.
- split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 0, (cur + 7).
split; [exact Ra0|]. split; [exact Vp|]. split; [exact Vn|]. split; [exact Vc|]. split; [clear - Hcur HOK; lia|].
right. left. split; [reflexivity|]. rewrite Ebl, Eab3. exact HPerm. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
pose proof (aftok_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (fmt * N) HJ3 HAR2 Ebl ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as Timg.
assert (Aimg : forall blc i lyq, In (res, fmt * N) blc -> 0 <= i < req_size (fmt * N) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block trasegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (fmt * N) blc i lyq HJ3 HAR2 Ebl ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia) Hin Hi). }
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trasegs Ex _ _ nx (mkAF 4096 140737479966720 4) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by (clear - Hr4096 HrCeil HrqN1 C1; lia);
change (2 ^ 4) with 16; clear - Hr4096 HrCeil Hr16 HrqN1 HrqN2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
rf_hand RN HS.
- rewrite Hfrs2. exact Hfrs3.
- split; [rewrite Hk0; reflexivity|]. split; [exact HOK|]. exists fmt, res.
split; [exact Efmt|]. split; [exact Hfmt|]. split; [exact Rres|]. split; [exact Hr4096|]. split; [exact HrHi|]. split; [exact HrCeil|]. split; [exact Hr16|].
split; [rewrite Ebl, Eab3; reflexivity|]. split; [exact Timg | exact Aimg].
Qed.
End e.
End d.
