(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YH00 YH03 YH02 YN3a YI06 YI5b YI09 YI08 YI0r YI1w YI1v YI4l YI21 YI2m YI5o YI5l YI6b YI5n YI20 YI1d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI1n YI1e YI1f YI1c YI1g YI1l.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI5c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 YI3u YI22 YI5a YI5d YI0f YI2w YI2v YI0o YI2s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI25 YI2n YI1x.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b YI1o YI1m YI1p.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Ltac lia_try := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [YM03.lf_prune1; YM03.lf_lia_orig] ].
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ /\ (_ \/ _) |- _ => clear H | H : (_ \/ _) /\ _ |- _ => clear H end.
Ltac liaND := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_prune1; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_lia_orig] | lia ].
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI1h.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI src0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws src0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws src0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Lemma af_slow :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z)
(GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound) (HD : YO07.frame),
B_pre API L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx ->
B_preX L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb HD ->
negb (YO07.flag fattr 1) && negb (YO07.flag (YO07.f_attr HD) 1) && negb (YO07.flag fattr 4) && negb (YO07.flag (YO07.f_attr HD) 4) = false ->
SR src0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom src0segs)) mdc)
(af_postX API regs0 g N s0 ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb HD
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hgeom & Hfh & HnoCT & Hcf & Hcf8 & Hcflo & Hcfhi & Hlpa & HFP & HB & HSV & G2 & G8 & G9 & G18 & G19 & G23 & G24 & HUT)
(Xgen & Xfile & XSK & XLOW & XMAX & Xsp47 & XLV & XCUR & XLIVE & XIMG0 & XIL & XLPA & XRq & XROOM & XHD & XFD & XKEEP & G22) XCOND.
pose proof HUT as (G3 & G4 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ADDFRAME_STK = 9728) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HFSv : FRAME_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
pose proof Hwf as (Hlen & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (HN1 : 1 <= N) by (rewrite HN; clear - HW1 HH1; nia).
assert (Hfin : In (Some fh) (cg_frames s)) by (eapply nth_error_In; exact Hfh).
pose proof XSK as (XSK1 & XSK2 & XFIN & XSK4 & XSK5 & HFPX).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as ((XHrc & XHra & XHih & XHgp) & XSL).
pose proof (proj1 (af_live_iff _ _ _ _ _) XLIVE) as (XH & _).
assert (Hih3 : (Z.to_nat (cg_ihead s) < 3)%nat) by (clear - Hih; lia).
assert (XihN : YO07.s_ihead gs = Z.of_nat (Z.to_nat (cg_ihead s))) by (rewrite <- XHih; clear - Hih; lia).
pose proof (XSL (Z.to_nat (cg_ihead s)) Hih3 I) as FR. rewrite (@nth_error_nth _ (cg_frames s) _ (Some fh) None Hfh), XHD in FR. cbn [oframe_relb] in FR.
pose proof FR as (FRa & FRg & FRd & FRn & FRc & FRdisp & FRt & FRimg & FRil & FRlp).
assert (XMG : af_merged (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs = (if (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) then Some (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))) else None)).
{ apply (af_merged_head (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (Z.to_nat (cg_ihead s)) HD XihN Hih3 XHD XFD). apply (proj2 (flag1_false_iff _)). exact XKEEP. }
destruct (af_cgif_geom0 API Lc Ac memc mdc g s N _ HH0 HB) as (_ & Hfgeom & (Hg0 & Hg1 & Hg16)).
destruct (Hfgeom fh Hfin) as (Hf0 & Hf1 & Hfg).
destruct (af_frame_geom0 API Lc Ac memc mdc g s N _ fh HH0 HB Hfin) as (Hfblk & Hfimgblk & Hflpal).
destruct (heap_blocks_range _ _ LAWS Lc Ac memc mdc (fr_ptr fh) FRAME_SIZE HH0 Hfblk ltac:(lia)) as (_ & _ & Hf16).
assert (Himgin : In (img, N) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. left. reflexivity. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc img N HH0 Himgin) as [Him0 Him1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc (fr_img fh) N HH0 Hfimgblk) as [Hfi0 Hfi1].
pose proof Hat as (Hobj & Hraw & Hfrs). pose proof (Hfrs fh Hfin) as Hfobj.
pose proof (obj_at_range _ _ _ _ _ Hcf) as Rcf. pose proof (obj_at_range _ _ _ _ _ Hobj) as Rg. pose proof (obj_at_range _ _ _ _ _ Hfobj) as Rf.
pose proof (Rcf 2%nat fattr eq_refl) as Rfattr. pose proof (Rcf 0%nat lpal eq_refl) as Rlpal. pose proof (Rcf 5%nat nlp eq_refl) as Rnlp.
cbn [nth snd LAY_FrameConfig Z.of_N] in Rfattr, Rlpal, Rnlp.
pose proof (Rg 7%nat (cg_W s) eq_refl) as RW. pose proof (Rg 8%nat (cg_H s) eq_refl) as RH. cbn [nth snd LAY_CGIF Z.of_N] in RW, RH.
pose proof (Rf 2%nat (fr_attr fh) eq_refl) as Rfa. pose proof (Rf 4%nat (fr_delay fh) eq_refl) as Rfd. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfa, Rfd.
set (E := af_E regs1 regs0 [lpal; img; fattr; fgen; delay; nlp; tidx] s (frame_vals fh)).
pose proof (af_HE regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n rr, _ -> ew E n = _) as HE.
pose proof (af_HK regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HK.
pose proof (af_HC regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HC.
pose proof (af_HX regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HX.
pose proof (af_HM regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) : forall n j v, _ -> _ -> ew E n = _) as HM.
assert (HU2 : bv_unsigned (ew E 2) = spZ regs0 - 96) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HU9 : bv_unsigned (ew E 9) = cfp) by (rewrite (HE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (HU18 : bv_unsigned (ew E 18) = fr_ptr fh) by (rewrite (HE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; lia).
assert (HR0 : region_ok src0segs E memc (YP09.mkRegion (Some 2%nat) 0 96 0 0 (af_stk_chunks 32))).
{ pose proof (af_Rstk_ok _ memc (spZ regs0) regs0 32 HU2 ltac:(lia) ltac:(lia) HSV (fun j v Hj => HK _ j v eq_refl Hj) (fun a Ha => Hstw a ltac:(lia))) as R.
unfold af_Rstk in R. unfold region_ok in R |- *. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val] in R |- *.
destruct R as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [intros o Ho; lia | exact R4]. }
pose proof (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc g None None None (Some (cg_ihead s)) HU8 ltac:(lia) ltac:(lia) Hobj I I I eq_refl) as HR1.
pose proof (af_Rcf_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc cfp HU9 ltac:(lia) ltac:(lia) Hcf) as HR2.
assert (HR3 : region_ok src0segs E memc (af_Rfr_part 18 68 0 40 0 0)).
{ eapply (af_Rfr_part_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc 18 (fr_ptr fh) fh 68);
[exact HU18 | reflexivity | lia | lia | exact Hfobj | lia | intros j v Hj; rewrite Nat.sub_diag; exact Hj | lia | lia | intros k Hk; lia]. }
assert (HPD : pairwise_disjoint E (B_regions (cg_ihead s))).
{ unfold B_regions, af_Rg, af_Rcf, af_Rfr_part. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU8, HU9, HU18. clear - Hg1 Hf1 Hfg Hceil Hcflo HASv HGSv HFSv Hac. repeat split; lia. }
assert (HFA : atoms_ok E B_facts).
{ unfold B_facts. apply atoms_ok_app; [| apply atoms_ok_app; [exact (cf_facts_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc cfp Hcf) |]].
- cbn [atoms_ok af_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HU9.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try lia_try.
replace (spZ regs0 - 96) with (spZ regs0 + (-6) * 16) by lia. rewrite Z.mod_add by lia. exact Hal16.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), HU18,
(HM 69%nat 1%nat (fr_img fh) eq_refl eq_refl), (HM 70%nat 2%nat (fr_attr fh) eq_refl eq_refl), (HM 72%nat 4%nat (fr_delay fh) eq_refl eq_refl).
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
clear - RW RH HW1 HH1 Hf0 Hf1 Hf16 Hfi0 Hfi1 Rfa Rfd HFSv HN HNle Hac. repeat split; try lia; nia. }
assert (HS : st_ok src0segs E (ss_slow (cg_ihead s)) (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom src0segs))).
{ unfold ss_slow. apply entry_st_ok_full; [apply regs_ok_Ereg | destruct Hih as [H1|[H2 _]]; rewrite ?H1, ?H2; vm_compute; reflexivity | | exact HPD | split; [exact HFA | split; exact I]].
unfold B_regions. constructor; [exact HR0|]. constructor; [exact HR1|]. constructor; [exact HR2|]. constructor; [exact HR3|]. constructor. }
clear HR0 HR1 HR2 HR3 HPD HFA.
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom src0segs))) in HJ.
assert (GO_SAME : forall E' ss ms', st_ok src0segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = AF_SAME -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 18%bv = SOff 18 0 -> sr_get (ss_regs ss) 22%bv = SOff 22 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
(af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) = true ->
journal src0_msyms MR ADDFRAME_STK (spZ regs0) FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte src0segs (ms_mem ms') a = mbyte src0segs memc a) ->
SR src0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros E' ss ms' HS' HA Hpc Hrv Q2 Q3 Q4 Q18 Q22 Q26 Q27 XSM HJ' K. rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg src0segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
rewrite (af_from_merge_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD))))) by (rewrite XMG, ?XSM; reflexivity).
eapply (YI1n.af_same API IMG L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh
GPAL gs HD (delay + YO07.f_delay HD) (af_rb brb N (qcount gs) (qcount (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q18 ltac:(lia)); rewrite (HE 18%nat 18%bv eq_refl); exact G18
| split; [|split; [|split]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]
| exact Xgen | exact Xfile | exact HFPX | exact XCUR | exact (af_slots_occ _ _ _ _ XSL)
| exact (proj1 (af_sink_at API ADDFRAME_STK (spZ regs0) g s0 s N rest FP _ L A mem md Lc Ac (ms_mem ms') mdc HJ' XSK))
| exact XFIN
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]
| exact Hih3 | exact XHD
| rewrite (RG _ _ _ Q22 ltac:(lia) (HE 22%nat 22%bv eq_refl)); exact G22
| rewrite (qcount_q_set_some gs (Z.to_nat (cg_ihead s)) HD _ Hih3 XHD); exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (GO_C : forall E' ss ms', st_ok src0segs E' ss ms' -> env_agree 32 E E' -> ss_pc ss = AF_C -> ss_resv ss = None ->
sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
sr_get (ss_regs ss) 8%bv = SOff 8 0 -> sr_get (ss_regs ss) 9%bv = SOff 9 0 -> sr_get (ss_regs ss) 21%bv = SOff 21 0 ->
sr_get (ss_regs ss) 20%bv = SOff 20 0 -> sr_get (ss_regs ss) 19%bv = SOff 19 0 -> sr_get (ss_regs ss) 26%bv = SOff 26 0 -> sr_get (ss_regs ss) 27%bv = SOff 27 0 ->
(af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) = false ->
journal src0_msyms MR ADDFRAME_STK (spZ regs0) FP L A mem md Lc Ac (ms_mem ms') mdc ->
(forall a, mbyte src0segs (ms_mem ms') a = mbyte src0segs memc a) ->
SR src0segs (mkCfg ms' mdc) (af_postX API regs0 g N s0 ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md)).
{ intros E' ss ms' HS' HA Hpc Hrv Q2 Q3 Q4 Q8 Q9 Q19 Q23 Q24 Q26 Q27 XSM HJ' K. rewrite (st_ok_mkst src0segs _ _ _ HS' Hrv), Hpc.
assert (RG : forall (r : reg) n w, sr_get (ss_regs ss) r = SOff n 0 -> (n < 32)%nat -> ew E n = w -> getr (ms_regs ms') r = w).
{ intros r n w Hr Hn Hw. rewrite (st_ok_reg src0segs E' ss ms' r HS'), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, <- Hw. apply (proj1 HA). exact Hn. }
pose proof (land_le fattr 4 ltac:(lia)) as Rt4.
rewrite (af_from_merge_none (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) by (rewrite XMG, ?XSM; reflexivity).
eapply (af_C API IMG FLUSHX L A mem md regs0 (ms_regs ms') Lc Ac (ms_mem ms') mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4) GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply K] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply K]
| apply (RG _ _ _ Q2 ltac:(lia)); rewrite (HE 2%nat 2%bv eq_refl); exact G2
| apply (RG _ _ _ Q8 ltac:(lia)); rewrite (HE 8%nat 8%bv eq_refl); exact G8
| apply (RG _ _ _ Q9 ltac:(lia)); rewrite (HE 9%nat 9%bv eq_refl); exact G9
| apply (RG _ _ _ Q19 ltac:(lia)); rewrite (HE 21%nat 21%bv eq_refl); exact G19
| apply (RG _ _ _ Q23 ltac:(lia)); rewrite (HE 20%nat 20%bv eq_refl); exact G23
| lia
| apply (RG _ _ _ Q24 ltac:(lia)); rewrite (HE 19%nat 19%bv eq_refl); exact G24
| split; [|split; [|split]]; [ apply (RG _ _ _ Q3 ltac:(lia)); rewrite (HE 3%nat 3%bv eq_refl); exact G3
| apply (RG _ _ _ Q4 ltac:(lia)); rewrite (HE 4%nat 4%bv eq_refl); exact G4
| apply (RG _ _ _ Q26 ltac:(lia)); rewrite (HE 26%nat 26%bv eq_refl); exact G26
| apply (RG _ _ _ Q27 ltac:(lia)); rewrite (HE 27%nat 27%bv eq_refl); exact G27 ]
| exact Xgen | exact Xfile | reflexivity | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply K | exact XH] | apply (af_slots_kept memc); [intros; apply K | exact XSL]]
| eapply garr8_frame; [exact XIMG0 | intros a _; apply K]
| exact XIL
| intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply K]
| exact XRq | exact XROOM ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply K]. }
assert (CTB : forall attr lp nl, 0 <= lp < 2 ^ 64 -> 0 <= nl ->
(Z.land attr 1 = 0 -> Z.land (cg_attr s) 4 = 0) ->
(Z.land attr 1 <> 0 -> exists lp', Z_to_bv 64 lp' = Z_to_bv 64 lp /\ In (lp', 3 * nl) (blocks Lc Ac)) ->
In (ct_sel attr lp (cg_pal s), 3 * ct_sel attr nl (cg_ngp s)) (blocks Lc Ac)).
{ intros attr lp nl Rlp Rnl0 Hg Hl. unfold ct_sel. destruct (Z.eqb_spec (Z.land attr 1) 0) as [Hz|Hz].
- apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. left. right. right. apply in_app_iff. left.
unfold pal_blocks. rewrite (Hg Hz). cbn. left. reflexivity.
- destruct (Hl Hz) as (lp' & Heq & Hin). destruct (blocks_range _ _ LAWS Lc Ac memc mdc lp' (3 * nl) HH0 Hin) as [R0 R1].
assert (lp' = lp).
{ apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq. }
subst lp'. exact Hin. }
assert (CTc : In (ct_sel fattr lpal (cg_pal s), 3 * ct_sel fattr nlp (cg_ngp s)) (blocks Lc Ac)).
{ apply CTB; [lia | lia | exact HnoCT |]. intros Hz. exists lpa. split; [exact Hlpa|].
apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hz1|Hz1]; [exfalso; first [clear - Hz Hz1; lia | lia]|]. right. left. reflexivity. }
assert (CTb : In (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s), 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) (blocks Lc Ac)).
{ pose proof (Rf 0%nat (fr_lpal fh) eq_refl) as Rflp. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rflp.
pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl0. cbn [nth snd LAY_Frame LAY_FrameConfig app Z.of_N] in Rfnl0.
apply CTB; [lia | lia | exact (proj1 (Hfwf fh Hfin)) |]. intros Hz. exists (fr_lpal fh). split; [reflexivity | exact (Hflpal Hz)]. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTc) as [Sc0 Sc1].
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 CTb) as [Sb0 Sb1].
assert (Elpa : Z.land fattr 1 <> 0 -> lpa = lpal).
{ intros Hz. assert (Hin : In (lpa, 3 * nlp) (blocks Lc Ac)).
{ apply (Permutation_in _ (Permutation_sym HB)). apply in_app_iff. right. destruct (Z.eqb_spec (Z.land fattr 1) 0); [exfalso; exact (Hz ltac:(assumption)) | right; left; reflexivity]. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc _ _ HH0 Hin) as [R0 R1]. pose proof (f_equal bv_unsigned Hlpa) as EE.
rewrite !unsigned_lit_small in EE by lia. exact EE. }
pose proof (Rcf 5%nat nlp eq_refl) as Rnl. pose proof (Rf 5%nat (fr_nlp fh) eq_refl) as Rfnl. pose proof (Rg 9%nat (cg_ngp s) eq_refl) as Rngp.
cbn [nth snd LAY_Frame LAY_FrameConfig LAY_CGIF app Z.of_N] in Rnl, Rfnl, Rngp.
assert (Hszc : 0 <= 3 * ct_sel fattr nlp (cg_ngp s)) by (unfold ct_sel; destruct (Z.land fattr 1 =? 0); lia).
assert (Hszb : 0 <= 3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s)) by (unfold ct_sel; destruct (Z.land (fr_attr fh) 1 =? 0); lia).
destruct (rdn_of_present src0_msyms memc (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) (ct_sel fattr lpal (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTc ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
destruct (rdn_of_present src0_msyms memc (Z.to_nat (3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s))) (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTb ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (Dif : img + N <= fr_img fh \/ fr_img fh + N <= img).
{ pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks0 g s N) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) (fr_img fh, N) (img, N) HH0 HB
ltac:(apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | right; left; reflexivity]) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. lia. }
assert (Hfhcf : obj_at src0segs memc (fr_ptr fh) LAY_FrameConfig (firstn 7 (frame_vals fh))).
{ rewrite LAY_Frame_split in Hfobj. apply (proj1 (obj_at_app src0segs memc (fr_ptr fh) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals fh)) (skipn 7 (frame_vals fh)) eq_refl)). exact Hfobj. }
assert (Hfg' : g + CGIF_SIZE <= fr_ptr fh \/ fr_ptr fh + 29 <= g) by (clear - Hfg HFSv; lia).
assert (Hf8 : fr_ptr fh mod 8 = 0).
{ clear - Hf16 Hf0. rewrite <- (Z.mod_mod_divide (fr_ptr fh) 16 8) by (exists 2; reflexivity). rewrite Hf16. reflexivity. }
destruct Hih as [Hih1 | [Hih2 _]].
- rewrite Hih1 in HS.
jrun LAWS src0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
jbranch src0tbl HS.
+
exfalso. rewrite branch_eq_U, U_lit in Hc by lia.
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s)) in Hc; [| apply (U_atom _ 59 (cg_H s) (HX 59%nat 8%nat _ eq_refl eq_refl)); first [clear - RW RH; lia | lia] | apply (U_atom _ 58 (cg_W s) (HX 58%nat 7%nat _ eq_refl eq_refl)); first [clear - RW RH; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; nia | nia]].
destruct (Z.eqb_spec (cg_H s * cg_W s) 0); [clear - HN HN1 e; nia | discriminate Hc].
+
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K0. }
clear HF.
assert (KM : forall a, mbyte src0segs (ms_mem ms0) a = mbyte src0segs memc a) by (intros a; apply mbyte_of_eq; exact K1).
assert (HNN : U E (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff 59 0) (SOff 58 0)) (SLit 32)) (SLit 32)) = N).
{ apply U_zext32_shifts; [| lia]. rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s)); [first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; lia | lia] | | | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; nia | nia]].
- apply (U_atom _ 59 (cg_H s) (HX 59%nat 8%nat _ eq_refl eq_refl)). lia.
- apply (U_atom _ 58 (cg_W s) (HX 58%nat 7%nat _ eq_refl eq_refl)). lia. }
assert (RUNM : cmp_run (cmpPixel_fn fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef) (ms_mem ms0) img (fr_img fh) 0 (Z.to_nat N) = (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD)).
{ unfold YI0b.af_same. rewrite XCOND.
rewrite (cmp_run_forallb (cmpPixel_fn fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef) (YO07.cmp_pixel (gcfg_of s GPAL) (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) HD) (ms_mem ms0) img (fr_img fh) IMGv (YO07.f_img HD));
[ reflexivity
| eapply garr8_frame; [exact XIMG0 | intros a _; apply KM]
| eapply garr8_frame; [exact FRimg | intros a _; apply KM]
| apply Nat2Z.inj; rewrite FRil, XIL; reflexivity
| exact (cmpPixel_model (gcfg_of s GPAL) (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) HD fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef
eq_refl
ltac:(intros F4; cbn [YO07.f_ctrans YO07.new_frame]; unfold YO07.flag in F4 |- *; destruct (Z.eqb_spec (Z.land fattr 6) 0) as [H6|H6]; [| reflexivity];
exfalso; apply (f_equal (fun x => Z.land x 4)) in H6; rewrite <- Z.land_assoc in H6; change (Z.land 6 4) with 4 in H6; rewrite Z.land_0_l in H6; rewrite H6 in F4; discriminate F4)
eq_refl FRa
ltac:(intros F4; apply FRc; unfold YO07.flag in F4; intros H6; apply (f_equal (fun x => Z.land x 4)) in H6; rewrite <- Z.land_assoc in H6;
change (Z.land 6 4) with 4 in H6; rewrite Z.land_0_l in H6; rewrite H6 in F4; discriminate F4)
FRn eq_refl
ltac:(unfold YO07.flag; cbn [YO07.g_gpal YO07.f_lpal YO07.new_frame gcfg_of]; unfold ct_sel in Rct |- *; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Yz|Yz]; cbn [negb];
[ destruct (XHgp (HnoCT Yz)) as [YG YGl]; apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rct | exact YG | rewrite <- (Nat2Z.id (length GPAL)), YGl; clear - Rngp; lia]
| destruct (XLPA Yz) as [YL YLl]; pose proof Rct as Rct'; rewrite <- (Elpa Yz) in Rct';
apply (rdn_garr8_prefix memc lpa); [exact Rct' | exact YL | rewrite <- (Nat2Z.id (length LPALv)), YLl; clear - Rnl; lia] ])
ltac:(unfold YO07.flag; cbn [YO07.g_gpal YO07.f_lpal gcfg_of]; unfold ct_sel in Rbt |- *; destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0) as [Yz|Yz]; cbn [negb];
[ destruct (XHgp (proj1 (Hfwf fh Hfin) Yz)) as [YG YGl]; apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rbt | exact YG | rewrite <- (Nat2Z.id (length GPAL)), YGl; clear - Rngp; lia]
| destruct (FRlp Yz) as [YL YLl]; apply (rdn_garr8_prefix memc (fr_lpal fh)); [exact Rbt | exact YL | rewrite <- (Nat2Z.id (length (YO07.f_lpal HD))), YLl; clear - Rfnl; lia] ])
ltac:(unfold YO07.flag, ct_sel; cbn [YO07.g_gpal YO07.f_lpal YO07.new_frame gcfg_of]; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Yz|Yz]; cbn [negb];
[ rewrite (proj2 (XHgp (HnoCT Yz))); clear - Rngp; lia | rewrite (proj2 (XLPA Yz)); clear - Rnl; lia ])
ltac:(unfold YO07.flag, ct_sel; cbn [YO07.g_gpal YO07.f_lpal gcfg_of]; destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0) as [Yz|Yz]; cbn [negb];
[ rewrite (proj2 (XHgp (proj1 (Hfwf fh Hfin) Yz))); clear - Rngp; lia | rewrite (proj2 (FRlp Yz)); clear - Rfnl; lia ]))
| lia | rewrite <- (Nat2Z.id (length IMGv)), XIL; clear; lia ]. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (af_loop API IMG (ms_mem ms0) g cfp (fr_ptr fh) img (fr_img fh) N (cgif_vals s) [lpal; img; fattr; fgen; delay; nlp; tidx] (firstn 7 (frame_vals fh))
fattr tidx nlp lpal (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (fr_lpal fh) (cg_ngp s) (cg_pal s) ctcur ctbef) with (n := Z.to_nat N) (k := 0);
[ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply KM]
| reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hfhcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| exact Hg0 | exact Hg1 | exact Hg16 | lia | exact Hcfhi | exact Hcf8 | exact Hf0 | lia | exact Hf8
| lia | exact Hfg' | lia
| rewrite (rdn_ext src0segs (ms_mem ms0) memc) by exact K1; exact Rct
| rewrite (rdn_ext src0segs (ms_mem ms0) memc) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img N i HH0 Himgin Hi))
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_img fh) N i HH0 Hfimgblk Hi))
| exact Him0 | exact Him1 | exact Hfi0 | exact Hfi1 | lia | exact Dif
| exact HJ | intros x; reflexivity | lia | clear - HN1; rewrite Z2Nat.id by lia; lia | clear - HN1; lia
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18)
| reg_nowF HS ltac:(rewrite (HC 45%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; f_equal; lia)
| reg_nowF HS ltac:(rewrite (HM 69%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; f_equal; lia)
| ].
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg src0segs Ec ssc msc 25%bv HS) as T; eval_sr_get_in T; cbn [ms_regs mkst]; rewrite T, denot_lit_U, HNN, Z2Nat.id by lia; reflexivity end. }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & Hpx & HJ' & K' & HK').
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (regs_kept_of_st_ok src0segs Ec ssc msc regs1 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
cbn [ms_regs mkst] in HKR.
assert (KF : forall a, mbyte src0segs mem' a = mbyte src0segs memc a) by (intros a; unfold mbyte; rewrite K', K1; reflexivity).
assert (RR : forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv -> getr regs' r = getr regs1 r).
{ intros r Hr. rewrite (HK' r) by (revert Hr; clear; intros Hr; cbv in Hr |- *; tauto). apply (HKR r Hr). }
clear Hpc'. rewrite RUNM in Hpx.
destruct (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) eqn:XSM; subst pc'.
*
rewrite (af_from_merge_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD))))) by (rewrite XMG, ?XSM; reflexivity).
eapply (YI1n.af_same API IMG L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh
GPAL gs HD (delay + YO07.f_delay HD) (af_rb brb N (qcount gs) (qcount (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 18%bv ltac:(cbv; auto 20)); exact G18
| split; [|split; [|split]]; [rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26 | rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27]
| exact Xgen | exact Xfile | exact HFPX | exact XCUR | exact (af_slots_occ _ _ _ _ XSL)
| exact (proj1 (af_sink_at API ADDFRAME_STK (spZ regs0) g s0 s N rest FP _ L A mem md Lc Ac mem' mdc HJ' XSK))
| exact XFIN
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply KF | exact XH] | apply (af_slots_kept memc); [intros; apply KF | exact XSL]]
| exact Hih3 | exact XHD
| rewrite (RR 22%bv ltac:(cbv; auto 20)); exact G22
| rewrite (qcount_q_set_some gs (Z.to_nat (cg_ihead s)) HD _ Hih3 XHD); exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
*
rewrite (af_from_merge_none (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) by (rewrite XMG, ?XSM; reflexivity).
eapply (af_C API IMG FLUSHX L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4) GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply KF] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8 | rewrite (RR 9%bv ltac:(cbv; auto 20)); exact G9
| rewrite (RR 21%bv ltac:(cbv; auto 20)); exact G19 | rewrite (RR 20%bv ltac:(cbv; auto 20)); exact G23 | pose proof (land_le fattr 4 ltac:(lia)); lia
| rewrite (RR 19%bv ltac:(cbv; auto 20)); exact G24
| split; [|split; [|split]]; [rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26 | rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27]
| exact Xgen | exact Xfile | reflexivity | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply KF | exact XH] | apply (af_slots_kept memc); [intros; apply KF | exact XSL]]
| eapply garr8_frame; [exact XIMG0 | intros a _; apply KF]
| exact XIL
| intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply KF]
| exact XRq | exact XROOM ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
- rewrite Hih2 in HS.
jrun LAWS src0tbl_ok HS HJ. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K0 : forall x, ms_mem ms x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
jbranch src0tbl HS.
+
exfalso. rewrite branch_eq_U, U_lit in Hc by lia.
rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s)) in Hc; [| apply (U_atom _ 59 (cg_H s) (HX 59%nat 8%nat _ eq_refl eq_refl)); first [clear - RW RH; lia | lia] | apply (U_atom _ 58 (cg_W s) (HX 58%nat 7%nat _ eq_refl eq_refl)); first [clear - RW RH; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; nia | nia]].
destruct (Z.eqb_spec (cg_H s * cg_W s) 0); [clear - HN HN1 e; nia | discriminate Hc].
+
clear Hc.
jrun_to LAWS src0tbl_ok HS HJ AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. apply K0. }
clear HF.
assert (KM : forall a, mbyte src0segs (ms_mem ms0) a = mbyte src0segs memc a) by (intros a; apply mbyte_of_eq; exact K1).
assert (HNN : U E (SAlu ALU_SRL (SAlu ALU_SLL (SMdw M_MUL (SOff 59 0) (SOff 58 0)) (SLit 32)) (SLit 32)) = N).
{ apply U_zext32_shifts; [| lia]. rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s)); [first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; lia | lia] | | | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1; lia | lia] | first [clear - RW RH HW1 HH1 HN HNle HN1 Hac; nia | nia]].
- apply (U_atom _ 59 (cg_H s) (HX 59%nat 8%nat _ eq_refl eq_refl)). lia.
- apply (U_atom _ 58 (cg_W s) (HX 58%nat 7%nat _ eq_refl eq_refl)). lia. }
assert (RUNM : cmp_run (cmpPixel_fn fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef) (ms_mem ms0) img (fr_img fh) 0 (Z.to_nat N) = (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD)).
{ unfold YI0b.af_same. rewrite XCOND.
rewrite (cmp_run_forallb (cmpPixel_fn fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef) (YO07.cmp_pixel (gcfg_of s GPAL) (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) HD) (ms_mem ms0) img (fr_img fh) IMGv (YO07.f_img HD));
[ reflexivity
| eapply garr8_frame; [exact XIMG0 | intros a _; apply KM]
| eapply garr8_frame; [exact FRimg | intros a _; apply KM]
| apply Nat2Z.inj; rewrite FRil, XIL; reflexivity
| exact (cmpPixel_model (gcfg_of s GPAL) (YO07.new_frame (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv) HD fattr tidx nlp (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (cg_ngp s) ctcur ctbef
eq_refl
ltac:(intros F4; cbn [YO07.f_ctrans YO07.new_frame]; unfold YO07.flag in F4 |- *; destruct (Z.eqb_spec (Z.land fattr 6) 0) as [H6|H6]; [| reflexivity];
exfalso; apply (f_equal (fun x => Z.land x 4)) in H6; rewrite <- Z.land_assoc in H6; change (Z.land 6 4) with 4 in H6; rewrite Z.land_0_l in H6; rewrite H6 in F4; discriminate F4)
eq_refl FRa
ltac:(intros F4; apply FRc; unfold YO07.flag in F4; intros H6; apply (f_equal (fun x => Z.land x 4)) in H6; rewrite <- Z.land_assoc in H6;
change (Z.land 6 4) with 4 in H6; rewrite Z.land_0_l in H6; rewrite H6 in F4; discriminate F4)
FRn eq_refl
ltac:(unfold YO07.flag; cbn [YO07.g_gpal YO07.f_lpal YO07.new_frame gcfg_of]; unfold ct_sel in Rct |- *; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Yz|Yz]; cbn [negb];
[ destruct (XHgp (HnoCT Yz)) as [YG YGl]; apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rct | exact YG | rewrite <- (Nat2Z.id (length GPAL)), YGl; clear - Rngp; lia]
| destruct (XLPA Yz) as [YL YLl]; pose proof Rct as Rct'; rewrite <- (Elpa Yz) in Rct';
apply (rdn_garr8_prefix memc lpa); [exact Rct' | exact YL | rewrite <- (Nat2Z.id (length LPALv)), YLl; clear - Rnl; lia] ])
ltac:(unfold YO07.flag; cbn [YO07.g_gpal YO07.f_lpal gcfg_of]; unfold ct_sel in Rbt |- *; destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0) as [Yz|Yz]; cbn [negb];
[ destruct (XHgp (proj1 (Hfwf fh Hfin) Yz)) as [YG YGl]; apply (rdn_garr8_prefix memc (cg_pal s)); [exact Rbt | exact YG | rewrite <- (Nat2Z.id (length GPAL)), YGl; clear - Rngp; lia]
| destruct (FRlp Yz) as [YL YLl]; apply (rdn_garr8_prefix memc (fr_lpal fh)); [exact Rbt | exact YL | rewrite <- (Nat2Z.id (length (YO07.f_lpal HD))), YLl; clear - Rfnl; lia] ])
ltac:(unfold YO07.flag, ct_sel; cbn [YO07.g_gpal YO07.f_lpal YO07.new_frame gcfg_of]; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Yz|Yz]; cbn [negb];
[ rewrite (proj2 (XHgp (HnoCT Yz))); clear - Rngp; lia | rewrite (proj2 (XLPA Yz)); clear - Rnl; lia ])
ltac:(unfold YO07.flag, ct_sel; cbn [YO07.g_gpal YO07.f_lpal gcfg_of]; destruct (Z.eqb_spec (Z.land (fr_attr fh) 1) 0) as [Yz|Yz]; cbn [negb];
[ rewrite (proj2 (XHgp (proj1 (Hfwf fh Hfin) Yz))); clear - Rngp; lia | rewrite (proj2 (FRlp Yz)); clear - Rfnl; lia ]))
| lia | rewrite <- (Nat2Z.id (length IMGv)), XIL; clear; lia ]. }
rewrite (st_ok_mkst src0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (af_loop API IMG (ms_mem ms0) g cfp (fr_ptr fh) img (fr_img fh) N (cgif_vals s) [lpal; img; fattr; fgen; delay; nlp; tidx] (firstn 7 (frame_vals fh))
fattr tidx nlp lpal (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (fr_lpal fh) (cg_ngp s) (cg_pal s) ctcur ctbef) with (n := Z.to_nat N) (k := 0);
[ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply KM]
| reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hfhcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| exact Hg0 | exact Hg1 | exact Hg16 | lia | exact Hcfhi | exact Hcf8 | exact Hf0 | lia | exact Hf8
| lia | exact Hfg' | lia
| rewrite (rdn_ext src0segs (ms_mem ms0) memc) by exact K1; exact Rct
| rewrite (rdn_ext src0segs (ms_mem ms0) memc) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img N i HH0 Himgin Hi))
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_img fh) N i HH0 Hfimgblk Hi))
| exact Him0 | exact Him1 | exact Hfi0 | exact Hfi1 | lia | exact Dif
| exact HJ | intros x; reflexivity | lia | clear - HN1; rewrite Z2Nat.id by lia; lia | clear - HN1; lia
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 18%nat 18%bv eq_refl); exact G18)
| reg_nowF HS ltac:(rewrite (HC 45%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; f_equal; lia)
| reg_nowF HS ltac:(rewrite (HM 69%nat 1%nat _ eq_refl eq_refl), Z_to_bv_bv_unsigned; f_equal; lia)
| ].
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg src0segs Ec ssc msc 25%bv HS) as T; eval_sr_get_in T; cbn [ms_regs mkst]; rewrite T, denot_lit_U, HNN, Z2Nat.id by lia; reflexivity end. }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & Hpx & HJ' & K' & HK').
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (regs_kept_of_st_ok src0segs Ec ssc msc regs1 _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
cbn [ms_regs mkst] in HKR.
assert (KF : forall a, mbyte src0segs mem' a = mbyte src0segs memc a) by (intros a; unfold mbyte; rewrite K', K1; reflexivity).
assert (RR : forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 26; 27]%bv -> getr regs' r = getr regs1 r).
{ intros r Hr. rewrite (HK' r) by (revert Hr; clear; intros Hr; cbv in Hr |- *; tauto). apply (HKR r Hr). }
clear Hpc'. rewrite RUNM in Hpx.
destruct (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) eqn:XSM; subst pc'.
*
rewrite (af_from_merge_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD))))) by (rewrite XMG, ?XSM; reflexivity).
eapply (YI1n.af_same API IMG L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh
GPAL gs HD (delay + YO07.f_delay HD) (af_rb brb N (qcount gs) (qcount (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 18%bv ltac:(cbv; auto 20)); exact G18
| split; [|split; [|split]]; [rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26 | rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27]
| exact Xgen | exact Xfile | exact HFPX | exact XCUR | exact (af_slots_occ _ _ _ _ XSL)
| exact (proj1 (af_sink_at API ADDFRAME_STK (spZ regs0) g s0 s N rest FP _ L A mem md Lc Ac mem' mdc HJ' XSK))
| exact XFIN
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply KF | exact XH] | apply (af_slots_kept memc); [intros; apply KF | exact XSL]]
| exact Hih3 | exact XHD
| rewrite (RR 22%bv ltac:(cbv; auto 20)); exact G22
| rewrite (qcount_q_set_some gs (Z.to_nat (cg_ihead s)) HD _ Hih3 XHD); exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
*
rewrite (af_from_merge_none (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) by (rewrite XMG, ?XSM; reflexivity).
eapply (af_C API IMG FLUSHX L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4) GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply KF] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8 | rewrite (RR 9%bv ltac:(cbv; auto 20)); exact G9
| rewrite (RR 21%bv ltac:(cbv; auto 20)); exact G19 | rewrite (RR 20%bv ltac:(cbv; auto 20)); exact G23 | pose proof (land_le fattr 4 ltac:(lia)); lia
| rewrite (RR 19%bv ltac:(cbv; auto 20)); exact G24
| split; [|split; [|split]]; [rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26 | rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27]
| exact Xgen | exact Xfile | reflexivity | exact XSK | exact XLOW | exact XMAX | exact Xsp47 | exact XLV | exact XCUR
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply KF | exact XH] | apply (af_slots_kept memc); [intros; apply KF | exact XSL]]
| eapply garr8_frame; [exact XIMG0 | intros a _; apply KF]
| exact XIL
| intros H1; destruct (XLPA H1) as [Hg Hgl]; split; [| exact Hgl]; eapply garr8_frame; [exact Hg | intros a _; apply KF]
| exact XRq | exact XROOM ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
