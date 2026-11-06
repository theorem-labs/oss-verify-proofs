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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCrs YCru YCro YCrb YChy.
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
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : amalloc_realizes trbsegs B.
Hypothesis AMEMCPY : aintrin_realizes trbsegs B OCpy A_asan_memcpy_tfb.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma rf_M : rf_from B ss_EPI (INV_EPI B) -> rf_from B ss_R5 (INV_R5 B) -> rf_from B ss_M (INV_M B).
Proof.
intros REPI RN. rf_prelude.
destruct HINV as (Hk0 & Eab3 & (curi & Ecur & Hcuri) & fmt & Efmt & Hfmt).
assert (Hpd3 : In (pdata, nb) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpdc).
pose proof HJ3 as (_ & Hly3 & _ & _ & _ & _ & Hnev3 & _).
pose proof Hstk as (_ & _ & _ & _ & _ & _ & _ & Htop & Htop2).
assert (Hlive3 : blocks_bytes S3 + fmt * N <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B lyc Sc). unfold LIVE_RRFC, RGB_NMAX in *. clear - Hlive HN Hfmt. lia. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0.
rregD HS (10%bv : bv 5) Ra0D.
assert (DN : getr (ms_regs ms3) 10 = w64 (fmt * N)).
{ rewrite Ra0D. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E 12 N E12), (U_atom E 310 fmt Efmt) by (unfold RGB_NMAX in HN; clear - HN Hfmt; lia).
rewrite zcanon_id by (unfold M64, RGB_NMAX in *; clear - HN Hfmt; nia). clear; lia. }
assert (Qra : 0 <= raZ regs < 2 ^ 64) by (unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (Qs0 : 0 <= s0Z regs < 2 ^ 64) by (unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseA rs 2%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
lazymatch type of HRstk with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
ltac:(exact Usp) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qra) ltac:(cbn; lia)) as Vra;
pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
ltac:(exact Usp) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Qs0) ltac:(cbn; lia)) as Vs0 end;
clear HRstk end.
change (N.to_nat 8) with 8%nat in Vra, Vs0.
replace (spZ regs + -8) with (spZ regs - 8) in Vra by (clear; lia). replace (spZ regs + -16) with (spZ regs - 16) in Vs0 by (clear; lia).
assert (Etop3 : ly_top ly3 = ly_top lyc).
{ destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & T3 & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Tc & _). rewrite T3, Tc. reflexivity. }
assert (Etopc : ly_top lyc = ly_top ly) by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Tc & _); exact Tc).
assert (UPk : forall a, st + 24 <= a < 2 ^ 64 -> aview trbsegs (w_H W3) (ms_mem ms3) a = aview trbsegs (w_H W) memc a).
{ intros a Ha. destruct HKEPT as (K1 & _). apply K1; [clear - Ha HSTB C1; lia | clear - Ha HSTB; lia | clear - Ha HSTB HDSTB; lia | clear - Ha; lia]. }
assert (Hch1 : achain ly3 (aview trbsegs (w_H W3) (ms_mem ms3)) sp1 (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ apply (rf_chain_push lyc ly3 (aview trbsegs (w_H W) memc) (aview trbsegs (w_H W3) (ms_mem ms3)) st (spZ regs) (s0Z regs) (raZ regs) ch sp1 HCH Etop3);
[ rewrite Etopc; clear - Htop2 H47; lia | exact UPk | exact Hst1
| exact (rdword_of_val_mem trbsegs _ _ _ _ Vra Qra) | exact (rdword_of_val_mem trbsegs _ _ _ _ Vs0 Qs0) | exact Hra4
| clear - HSPB HTS Has; lia
| pose proof (Z.div_mod (spZ regs) 16 ltac:(clear; lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by (clear; lia); apply Z_mod_mult
| rewrite Etopc; clear - Htop Hst1 Hst2; lia
| clear - Hsp1; lia ]. }
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). change (ss_pc ss_M) with 340936.
replace (Z_to_bv 64 340936) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
eapply SRr_bind.
{ eapply (aj_malloc_atD trbsegs B LAWS Hsegs errno_low ML AMALLOC W3 (ms_regs ms3) (ms_mem ms3) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
ly3 S3 _ kk (fmt * N) (sp1 - sp0) (Z_to_bv 64 RRFC_malloc_ra) ((spZ regs, raZ regs, s0Z regs) :: ch) HJ3);
[ exact DN
| unfold MALLOC_MAX, RGB_NMAX in *; clear - HN Hfmt; lia
| exact Hlive3
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
| unfold raZ; rewrite Rra, unsigned_lit_small by (unfold RRFC_malloc_ra; clear; lia); unfold RRFC_malloc_ra; clear; lia ]
| rewrite call_trace_of_spine; cbn [spine map fst snd]; fold (spine ch); unfold raZ at 1; rewrite Rra, unsigned_lit_small by (unfold RRFC_malloc_ra; clear; lia);
rewrite HBcode, (tl_universe B TL); apply TRACES_read_frameconfig_U; apply memZL_In;
cbn [CTX_read_frameconfig In] in HCTX; destruct HCTX as [Hc | [Hc | [Hc | [Hc | []]]]]; injection Hc as <- <-; vm_compute; reflexivity ]. }
cbv beta. clear Ra0 Ra0D Rra Rsp Rgp Rtp Rs0 Hch1 DN Vra Vs0 UPk.
intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha0 & Hfrs2 & HBD & Hres).
assert (HJB2 : jbud Sc S2 (kk + 1 - k)).
{ destruct (malloc_cost_coarse (fmt * N) ltac:(unfold MALLOC_MAX, RGB_NMAX in *; clear - HN Hfmt; lia)) as (_ & Cw & Ch).
replace (kk + 1 - k) with ((kk - k) + 1) by (clear; lia).
apply (jbud_step Sc S3 S2 (kk - k) 1 1 1 (wcost (fmt * N)) (hcost (fmt * N))); [rewrite Hk0; clear; lia | clear; lia | exact HJB | exact HBD | clear; lia | clear; lia | exact Cw | exact Ch]. }
pose proof (proj1 HJ2) as HAR2.
unfold ASTACK in Hres. replace (sp0 + (sp1 - sp0) - 16384) with (sp1 - 16384) in Hres by (clear; lia). replace (sp0 + (sp1 - sp0)) with sp1 in Hres by (clear; lia).
destruct (mres_kept B ly3 S3 W3 _ W2 mem2 ly2 S2 _ _ res (fmt * N) Hres) as (HK & HBin & HresIn).
pose proof (mres_range B LAWS ly2 S2 W2 mem2 md2 ly3 S3 res (fmt * N) _ _ HAR2 Hres) as Hrng.
assert (Hfin2 : In (cid, pos) (frames S2)) by (rewrite Hfrs2; exact Hfin3).
assert (Hfin02 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin0).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin02) as (_ & _ & HF0pres2 & HF0Spres2).
aconstsF HJ3 Kgot1 Kcell1 Kguar1 Kuar1. aconstsF HJ2 Kgot2 Kcell2 Kguar2 Kuar2.
pose proof HJ2 as (_ & Hly2 & _).
assert (EFA2 : forall c p, frame_addr ly2 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly2 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
change (fs_frame_bytes 0) with 64 in HF0pres2, HF0Spres2. change (64 / 8) with 8 in HF0Spres2. rewrite !EFA2 in HF0pres2, HF0Spres2. fold F in HF0pres2, HF0Spres2.
pose proof (req_size_pos (fmt * N) ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as [HrqN1 HrqN2].
assert (HnewF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (res <> 0 /\ res <= a < res + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (fmt * N) cid pos HAR2 (HresIn Hnz) Hfin2) as D.
rewrite EFA2 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
assert (HnewF0 : forall a, F <= a < F + 64 -> ~ (res <> 0 /\ res <= a < res + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (fmt * N) 0 fpos HAR2 (HresIn Hnz) Hfin02) as D.
rewrite EFA2 in D. fold F in D. change (fs_frame_bytes 0) with 64 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
assert (HnewS0 : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> ~ (res <> 0 /\ res <= a < res + req_size (fmt * N))).
{ intros a Ha [Hnz Hin]. destruct Hrng as [Hr0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)]; [exact (Hnz Hr0)|]. unfold SB in Ha. clear - Ha Hin HrHi HF8lo HF8hi HrqN2. lia. }
assert (HBb3 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly3 S3))
by (intros b m Hb; rewrite Eab3; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
assert (KEPT2 : rfc_kept W memc W2 mem2 (spZ regs) Bb lyc Sc st dst).
{ eapply (rfc_kept_callF B _ _ _ _ _ _ _ _ _ _ ly3 S3 _ _ _ _ _ HKEPT HK ltac:(clear - Hsp1 HTS Has; lia) ltac:(clear - Hsp1; lia) HBb3 _ ltac:(intros c p Hcp; rewrite Hfrs3; right; exact Hcp) EFA3 _).
Unshelve.
- intros b m i Hb Hi [Hnz Hin]. destruct Hres as [(Habs & _) | (_ & Ebl & _)]; [exact (Hnz Habs)|].
destruct (in_split _ _ (HBb3 b m Hb)) as (l1 & l2 & El).
pose proof (sep_blocks_pos trbsegs B LAWS ly2 S2 _ _ _ (b, m) (res, fmt * N) l1 l2 [] HAR2 ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. clear - Hd Hi Hin. lia.
- intros c p a Hcp Ha [Hnz Hin]. destruct Hrng as [Hr0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)]; [exact (Hnz Hr0)|]. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (fmt * N) c p HAR2 (HresIn Hnz) ltac:(rewrite Hfrs2, Hfrs3; right; exact Hcp)) as D.
rewrite EFA2 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin. lia.
+ destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ c p HAR2 ltac:(rewrite Hfrs2, Hfrs3; right; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA2 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi HrqN2 C2 C3. lia. }
clear HKEPT. rename KEPT2 into HKEPT.
rfb_RA HKEPT HJ2 HRAst HRAdst.
rbox Hrng. rbox Hres.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ2 HP2 l AG
ltac:(idtac; first [ keptRFB HK HJ2 AG Kgot1 Kgot2 Kcell1 Kcell2 Kguar1 Kguar2 Kuar1 Kuar2 Hfin3 Hfin0 HFpres2 HF0pres2 HF0Spres2
ltac:(first [ apply HnewF; rewrite_frame_addr; lia | apply HnewF0; lia | apply HnewS0; unfold SB; lia ])
| match goal with |- ?g => idtac "KEPTFAIL" g end]) end.
unfold rboxed in Hrng, Hres.
rreg HS (10%bv : bv 5) Rres. rewrite Ha0 in Rres. symmetry in Rres. unfold w64 in Rres.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
assert (Hpd2 : In (pdata, nb) (ablocks B ly2 S2)) by (apply HBin; exact Hpd3).
assert (Hfrs2' : frames S2 = (0, fpos) :: frames Sc) by (rewrite Hfrs2; exact Hfrs3).
destruct Hrng as [Hres0 | (Hr4096 & HrHi & HrCeil & Hr16 & HrIn)].
{
destruct Hres as [(_ & Ebl & _) | (Habs & _)]; [| exfalso; clear - Habs Hres0; lia].
pose proof (st_ok_pin_reg' trbsegs _ _ _ (10%bv : bv 5) 0 HS ltac:(cbn [ms_regs restrict mkst]; rewrite Ha0, Hres0; reflexivity) eq_refl) as HS3.
norm_ss HS3. clear HS. rename HS3 into HS. reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan RRFC_EPI.
all: try (oblsA HJ2 Hpd2 HRAst HRAdst E10 E11 E11 E32).
{ awrRFB AG fpos F EFA2 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
rebaseE HS AG HEv; clear HEv. rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rreg HS (10%bv : bv 5) Ra0.
rfb_epi_arrive HS curi 0 fmt ltac:(rfb_old_atom Ecur) ltac:(reflexivity) ltac:(rfb_old_atom Efmt) E390 E391 E392.
rfj_join HS ss_EPI 400%nat rf_EPI_deads_bv.
rf_hand REPI HS.
split; [rewrite Hk0; unfold EV_RRFC; clear; lia|]. exists 0, curi, 0, fmt.
split; [rewrite (ew_havoc_new _ 400 _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact Ra0|].
split; [rewrite ew_havoc_old by (cbn; lia); exact E390|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E391|]. split; [rewrite ew_havoc_old by (cbn; lia); exact E392|].
split; [exact Hcuri|]. right. left. split; [reflexivity|]. rewrite Ebl, Eab3. exact HPerm. }
destruct Hres as [(Habs & _ & _) | (_ & Ebl & _)]; [exfalso; clear - Habs Hr4096; lia|].
assert (EblC : ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, fmt * N)]) by (rewrite Ebl, Eab3; reflexivity).
pose proof (aftok_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (fmt * N) HJ HAR2 EblC ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia)) as Timg.
assert (Aimg : forall blc i lyq, In (res, fmt * N) blc -> 0 <= i < req_size (fmt * N) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (fmt * N) blc i lyq HJ HAR2 EblC ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia) Hin Hi). }
assert (Aimg' : forall blc i lyq, In (res, fmt * N) blc -> 0 <= i < req_size (fmt * N) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq ((0, fpos) :: own) (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block trbsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (fmt * N) blc i lyq HJ3 HAR2 Ebl ltac:(unfold RGB_NMAX in HN; clear - HN Hfmt; nia) Hin Hi). }
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact trbsegs Ex _ _ nx (mkAF 4096 140737479966720 4) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by (clear - Hr4096 HrCeil HrqN1 C1; lia);
change (2 ^ 4) with 16; clear - Hr4096 HrCeil Hr16 HrqN1 HrqN2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS.
reshok HS.
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspan A_readdata.
all: try (oblsA HJ2 Hpd2 HRAst HRAdst E10 E11 E11 E32).
{ awrRFB AG fpos F EFA2 ltac:(right; exact Hown). }
rfb_after_run AG HJ2.
rf_stream_words2 HS B10 E33 E34 Vp Vn. rf_stream_cur HS B10 303%nat Ecur Vc.
change (N.to_nat 8) with 8%nat in Vp, Vn, Vc.
rfb_drop_cur HS.
clear Kgot1 Kcell1 Kguar1 Kuar1 Kgot2 Kcell2 Kguar2 Kuar2. aconstsF HJ2 Kgot0 Kcell0 Kguar0 Kuar0.
pose proof (proj1 HJ2) as HAR2b.
assert (Dpi : rboxed (pdata + req_size nb <= res \/ res + req_size (fmt * N) <= pdata)).
{ destruct (in_split _ _ Hpd3) as (l1 & l2 & El).
pose proof (sep_blocks_pos trbsegs B LAWS ly2 S2 _ _ _ (pdata, nb) (res, fmt * N) l1 l2 [] HAR2b ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd.
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd. exact Hd. }
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rregD HS (12%bv : bv 5) Ra2D.
lazymatch type of Ra2D with getr ?rg _ = _ => assert (DN2 : getr rg 12 = w64 (fmt * N)) end.
{ rewrite Ra2D. rewrite denot_lit_U. unfold w64. f_equal. rewrite U_SMd. cbn [zmd_raw].
lazymatch goal with |- context [U ?Ex (SOff 12 0)] =>
assert (E12n : ew Ex 12 = Z_to_bv 64 N)
by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 12%nat) by lia; rewrite (EE 12%nat 12%bv eq_refl); exact G12);
assert (E310n : ew Ex 310 = Z_to_bv 64 fmt) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact Efmt);
rewrite (U_atom Ex 12 N E12n), (U_atom Ex 310 fmt E310n) by (unfold RGB_NMAX in HN; clear - HN Hfmt; lia) end.
rewrite zcanon_id by (unfold M64, RGB_NMAX in *; clear - HN Hfmt; nia). clear; lia. }
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 531812) with (Z_to_bv 64 A_readdata).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) ly2 S2 _ (kk + 1)
st res (fmt * N) pdata nb curi (sp1 - sp0) _);
[ exact HJ2
| rewrite Ra0; evalE AG
| rewrite Ra1; evalE AG
| exact DN2
| rewrite Rgp; evalE AG; rewrite (EE 3%nat 3%bv eq_refl); exact Hgp
| rewrite Rtp; evalE AG; rewrite (EE 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; evalE AG
| rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hsp0al; reflexivity
| clear - Hsp1 Hwhi; lia
| rewrite Hes; clear - Hsp1 Hwlo HTS Has; lia
| exact Hst8
| clear - Hsp1 Hst1; lia
| exact Hst2
| exact HRAst
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpd2] | clear - Hcuri Hcur; lia
| unfold RGB_NMAX in HN; clear - HN Hfmt; lia | clear - Hr4096; lia
| intros a Ha; split; [replace a with (res + (a - res)) by (clear; lia); apply (Aimg' (ablocks B ly2 S2) (a - res) ly2 HrIn); clear - Ha HrqN2; lia
| rewrite Hes; clear - Ha HrCeil HrqN2 HSPB Hsp1 C1 HTS Has; lia]
| apply amem_range_high; [unfold RGB_NMAX in HN; clear - HN Hfmt; nia | clear - HrHi HrqN2; lia | clear - HrCeil HrqN2; lia]
| apply (range_addressable_of_block trbsegs B LAWS ly2 S2 W2 _ _ res (fmt * N) _ _ (proj1 HJ2) HrIn); clear - HrqN2; lia
| intros Hn0; apply (shadow_hull_vis_of_block trbsegs B LAWS ly2 S2 W2 _ _ res (fmt * N) _ _ (proj1 HJ2) HrIn); [clear; lia | clear - HrqN2; lia | exact Hn0]
| right; left; clear - HSTB HrCeil HrqN2; lia
| unfold rboxed in Dpi; clear - Dpi Hrq2 HrqN2; lia ] end. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & r5 & cur5 & -> & HJ4 & HP4 & Ha04 & Hr5 & Vp' & Vn' & Vc' & Hfr4 & Hpres4).
rewrite Hes in Hfr4. replace (sp0 + (sp1 - sp0)) with sp1 in Hfr4 by (clear; lia).
clear Ra0 Ra1 Ra2D DN2 Rra Rsp Rgp Rtp Vp Vn Vc.
assert (HfN0 : 0 <= fmt * N) by (unfold RGB_NMAX in HN; clear - HN Hfmt; nia).
assert (Hcb5 : cur <= cur5 <= nb) by (clear - Hr5 Hcuri Hcur Hnb HfN0; destruct Hr5 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia). clear Hr5 Ha04.
aconstsF HJ4 Kgot1 Kcell1 Kguar1 Kuar1.
assert (HBb2 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B ly2 S2)) by (intros b m Hb; apply HBin; exact (HBb3 b m Hb)).
lazymatch type of HKEPT with rfc_kept _ _ _ ?mN _ _ _ _ _ _ =>
pose proof (rfc_kept_stepE _ _ _ mN mem4 _ _ _ _ _ _ (fun a => (res <= a < res + fmt * N) \/ (st + 16 <= a < st + 24) \/ (sp1 - 32 - 4096 <= a < sp1))
(fun a => res <= a < res + req_size (fmt * N)) HKEPT HSEP
ltac:(intros a Ha Hn; apply Hfr4; [exact Ha | clear - Hn; tauto | clear - Hn; tauto | clear - Hn; tauto])
ltac:(intros a Ha; cbn beta in *; clear - Ha Hsp1 HTS Has HrqN2; lia) ltac:(clear - HSPB; lia)
ltac:(intros a Ha; cbn beta in Ha; clear - Ha HrCeil; lia)
ltac:(intros b m i Hb Hi Hin; cbn beta in Hin; destruct (in_split _ _ (HBb3 b m Hb)) as (l1 & l2 & El);
pose proof (sep_blocks_pos trbsegs B LAWS ly2 S2 _ _ _ (b, m) (res, fmt * N) l1 l2 [] HAR2b ltac:(rewrite Ebl, El, <- app_assoc; reflexivity)) as Hd;
unfold zdisjoint, block_rng in Hd; cbn [fst snd] in Hd; clear - Hd Hi Hin; lia)
ltac:(intros c p a Hcp Ha Hin; cbn beta in Hin; destruct Ha as [Ha | Ha];
[ pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ res (fmt * N) c p HAR2b HrIn ltac:(rewrite Hfrs2'; right; exact Hcp)) as D;
rewrite EFA2 in D; unfold zdisjoint, frame_rng, in_zr in D, Ha; cbn [fst snd] in D, Ha; clear - D Ha Hin; lia
| destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ c p HAR2b ltac:(rewrite Hfrs2'; right; exact Hcp)) as (F0 & Fc & Fh); rewrite EFA2 in F0, Fc, Fh;
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow; clear - Hlow Hin HrHi HrqN2 C2 C3; lia ])) as KEPT4 end.
clear HKEPT. rename KEPT4 into HKEPT.
rfb_RA HKEPT HJ4 HRAst HRAdst.
lazymatch type of HS with st_ok _ _ ?ssx _ => let l := eval vm_compute in (seq 0 (length (ss_mem ssx))) in
reseat HS HJ4 HP4 l AG
ltac:(first [ eapply region_kept_aview; [evalE AG | intros a Ha; apply Hfr4;
[ clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| first [ clear - Ha Hsp1 HSPB HSTB HrCeil HrqN2 HTS Has C1 C3; lia
| intros Hin; apply (HnewF a); [clear - Ha Hdst1 Hdst2; lia | split; [clear - Hr4096; lia | clear - Hin HrqN2; lia]]
| intros Hin; apply (HnewF0 a); [clear - Ha; lia | split; [clear - Hr4096; lia | clear - Hin HrqN2; lia]]
| intros Hin; apply (HnewS0 a); [clear - Ha; unfold SB in *; lia | split; [clear - Hr4096; lia | clear - Hin HrqN2; lia]] ]
| unfold rboxed in Hsd; clear - Ha Hsp1 HSPB HSTB HDSTB Hsd HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia
| clear - Ha Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi HTS Has C1 C3; unfold SB in *; lia ] | exact Hpres4]
| apply (region_kept_val trbsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact Kgot0 | exact Kgot1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact Kcell0 | exact Kcell1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_GOT_uar 8 A_uar_glob); [exact Kguar0 | exact Kguar1 | lia]
| apply (region_kept_val trbsegs _ _ _ A_uar_glob 4 1); [exact Kuar0 | exact Kuar1 | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]) end.
rfb_add_atom HS 304%nat (Z_to_bv 64 cur5) E304.
rebaseE HS AG HEv; clear HEv.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch type of HS with st_ok _ ?Ev2 _ _ =>
pose proof (ast_ok_add_region trbsegs Ev2 _ _ (cur_region 304) HS eq_refl
ltac:(unfold cur_region, region_ok; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val ms_mem restrict mkst];
evalE AG; split; [clear - HSTB C1; lia|]; split; [clear - HSTB; lia|]; split;
[ intros o Ho; apply (apresent_writable trbsegs); apply HJpres; clear - Ho Hst1 Hst2 Hwlo HTS Has; lia
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val trbsegs Ev2 _ st 16 8 (SOff 304 0) cur5); [rewrite sv_denot_SOff0; exact E304 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - Hcb5 Hcur HnbM; lia | clear; cbn; lia | exact Vc'] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold cur_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]; evalE AG;
unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob; unfold rboxed in Hsd;
clear - Hsd Hsp1 HSPB HSTB HDSTB HF4096 HFceil HF8lo HF8hi C1 C3 HTS Has; unfold SB in *; repeat split; zone_lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
clear HJpres.
rf_relow HS AG X2 X10 X11 EX32 Usp E10 E11 E32 B10 B11.
rf_hand RN HS.
split; [rewrite Hk0; reflexivity|]. split; [exists cur5; split; [exact E304 | exact Hcb5]|]. exists fmt, res.
split; [exact Efmt|]. split; [exact Hfmt|]. split; [exact Rres|]. split; [exact Hr4096|]. split; [exact HrHi|]. split; [exact HrCeil|]. split; [exact Hr16|].
split; [exact EblC|]. split; [exact Timg | exact Aimg].
Qed.
End e.
End d.
