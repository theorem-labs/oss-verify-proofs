(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3a YI06 UI5b YI09 YI08 YI0r UI1w UI1v UI4l UI21 UI2m UI5o UI5l YI6b UI5n UI20 UI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1n UI1e UI1f UI1c UI1g UI1l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI01 UI3u UI22 YI5a UI5d YI0f YI2w UI2v YI0o UI2s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI25 UI2n UI1x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0b UI1o YI1m UI1p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Notation inFP_nil := YI04.inFP_nil (only parsing).
Import ListNotations.
Ltac lia_try := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [YM03.lf_prune1; YM03.lf_lia_orig] ].
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ /\ (_ \/ _) |- _ => clear H | H : (_ \/ _) /\ _ |- _ => clear H end.
Ltac liaND := rc_inst; first [ solve [YM03.lf_prune0; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_prune1; YM03.lf_lia_orig] | solve [clear_disj; YM03.lf_lia_orig] | lia ].
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI1h.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_slowU : sstate :=
mkSS AF_SLOW sr_atoms [af_Rg None None None None] None (mkFacts [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (67%nat, mkAF 1 2 0)] [] []).
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis FLUSHX : flushX_spec API.
Lemma af_slow :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (g N : Z) (s0 s : cgif_st) (rest FP : list (Z * Z)) (fh : frame_st)
(cfp lpal lpa img fattr fgen delay nlp tidx : Z)
(GPAL IMGv LPALv : list Z) (gs : YO07.gif_st) (brb : rbound) (HD : YO07.frame),
B_pre API L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx ->
B_preX L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb HD ->
negb (YO07.flag fattr 1) && negb (YO07.flag (YO07.f_attr HD) 1) && negb (YO07.flag fattr 4) && negb (YO07.flag (YO07.f_attr HD) 4) = false ->
SR ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs0segs)) mdc)
(af_postX API regs0 g N s0 ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)])) rest GPAL gs (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) (af_rb brb N (qcount gs) (qcount (af_from_merge (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs))) L A mem md).
Proof using FLUSHX IMG.
intros L A mem md regs0 regs1 Lc Ac memc mdc g N s0 s rest FP fh cfp lpal lpa img fattr fgen delay nlp tidx GPAL IMGv LPALv gs brb HD
(HJ & Hid & Hra0 & Hal16 & Htp0 & Hat & Hwf & Hgeom & Hfh & HnoCT & Hcf & Hcf8 & Hcflo & Hcfhi & Hlpa & HFP & HB & HSV & G2 & G8 & G9 & G12 & G19 & G20 & HUT)
(Xgen & Xfile & XSK & XLOW & XMAX & Xsp47 & XLV & XCUR & XLIVE & XIMG0 & XIL & XLPA & XRq & XROOM & XHD & XFD & XKEEP & G21) XCOND.
pose proof HUT as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
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
assert (HU8 : bv_unsigned (ew E 8) = g) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HFA : atoms_ok E [(58%nat, mkAF 1 65535 0); (59%nat, mkAF 1 65535 0); (67%nat, mkAF 1 2 0)]).
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HX 58%nat 7%nat _ eq_refl eq_refl), (HX 59%nat 8%nat _ eq_refl eq_refl), (HX 67%nat 16%nat _ eq_refl eq_refl).
rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
assert (HS : st_ok ubs0segs E ss_slowU (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs0segs))).
{ unfold ss_slowU. apply entry_st_ok_full; [apply regs_ok_Ereg | vm_compute; reflexivity | | | split; [exact HFA | split; exact I]].
- constructor; [|constructor]. exact (af_Rg_ok regs1 regs0 lpal img fattr fgen delay nlp tidx s (frame_vals fh) memc g None None None None HU8 ltac:(lia) ltac:(lia) Hobj I I I I).
- cbn [pairwise_disjoint all_disjoint]. split; exact I. }
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
destruct (rdn_of_present ubs0_msyms memc (Z.to_nat (3 * ct_sel fattr nlp (cg_ngp s))) (ct_sel fattr lpal (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTc ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctcur & Rct & _).
destruct (rdn_of_present ubs0_msyms memc (Z.to_nat (3 * ct_sel (fr_attr fh) (fr_nlp fh) (cg_ngp s))) (ct_sel (fr_attr fh) (fr_lpal fh) (cg_pal s))
ltac:(intros i Hi; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc _ _ i HH0 CTb ltac:(lia)))) ltac:(lia) ltac:(lia)) as (ctbef & Rbt & _).
assert (Dif : img + N <= fr_img fh \/ fr_img fh + N <= img).
{ pose proof (heap_sep_app API Lc Ac memc mdc (cgif_blocks0 g s N) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest) (fr_img fh, N) (img, N) HH0 HB
ltac:(apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | right; left; reflexivity]) ltac:(left; reflexivity)) as Hs. cbn [fst snd] in Hs. lia. }
assert (Hfhcf : obj_at ubs0segs memc (fr_ptr fh) LAY_FrameConfig (firstn 7 (frame_vals fh))).
{ rewrite LAY_Frame_split in Hfobj. apply (proj1 (obj_at_app ubs0segs memc (fr_ptr fh) LAY_FrameConfig [(32, 1%N); (33, 1%N)] (firstn 7 (frame_vals fh)) (skipn 7 (frame_vals fh)) eq_refl)). exact Hfobj. }
assert (Hfg' : g + CGIF_SIZE <= fr_ptr fh \/ fr_ptr fh + 29 <= g) by (clear - Hfg HFSv; lia).
assert (Hf8 : fr_ptr fh mod 8 = 0).
{ clear - Hf16 Hf0. rewrite <- (Z.mod_mod_divide (fr_ptr fh) 16 8) by (exists 2; reflexivity). rewrite Hf16. reflexivity. }
assert (Ofr : nth_error (cgif_vals s) (Z.to_nat (cg_ihead s)) = Some (fr_ptr fh)).
{ destruct Hih as [Hi | [Hi _]]; rewrite Hi in Hfh |- *; [change (Z.to_nat 1) with 1%nat in Hfh |- * | change (Z.to_nat 2) with 2%nat in Hfh |- *];
unfold cgif_vals; cbn [nth_error]; rewrite (@nth_error_nth _ (cg_frames s) _ (Some fh) None Hfh); reflexivity. }
assert (Hih' : cg_ihead s = 1 \/ cg_ihead s = 2) by (destruct Hih as [Hi | [Hi _]]; [left | right]; exact Hi).
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 AF_SLOW) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ AF_LOOP. { apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
name_ms HS ms0. cbn [ms_mem mkst] in HF.
assert (K1 : forall x, ms_mem ms0 x = memc x).
{ intros x. lazymatch type of HF with frame_of ?E1 ?rs ?m1 ?m2 => rewrite (frame_of_ro E1 rs m1 m2 ltac:(vm_compute; reflexivity) HF) end. reflexivity. }
clear HF.
assert (KM : forall a, mbyte ubs0segs (ms_mem ms0) a = mbyte ubs0segs memc a) by (intros a; apply mbyte_of_eq; exact K1).
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
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ eapply (af_loop API IMG (ms_mem ms0) g cfp (fr_ptr fh) img (fr_img fh) (cg_W s) (cg_H s) N (cg_ihead s) (cgif_vals s) [lpal; img; fattr; fgen; delay; nlp; tidx] (firstn 7 (frame_vals fh))
fattr tidx nlp lpal (fr_attr fh) (fr_ctidx fh) (fr_nlp fh) (fr_lpal fh) (cg_ngp s) (cg_pal s) ctcur ctbef) with (n := Z.to_nat N) (k := 0);
[ eapply obj_at_transport_range; [exact Hobj | exact (proj1 LAY_CGIF_ok) | intros i Hi; apply KM]
| reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| eapply obj_at_transport_range; [exact Hfhcf | exact lay_inside_FrameConfig | intros i Hi; apply KM]
| reflexivity | reflexivity | reflexivity | reflexivity
| exact Hg0 | exact Hg1 | exact Hg16 | lia | exact Hcfhi | exact Hcf8 | exact Hf0 | lia | exact Hf8
| lia | exact Hfg' | lia
| rewrite (rdn_ext ubs0segs (ms_mem ms0) memc) by exact K1; exact Rct
| rewrite (rdn_ext ubs0segs (ms_mem ms0) memc) by exact K1; exact Rbt
| exact Sc0 | exact Sc1 | exact Sb0 | exact Sb1
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc img N i HH0 Himgin Hi))
| intros i Hi; unfold present; rewrite K1; apply (proj1 (heap_blocks _ _ LAWS Lc Ac memc mdc (fr_img fh) N i HH0 Hfimgblk Hi))
| exact Him0 | exact Him1 | exact Hfi0 | exact Hfi1 | lia | exact Dif
| exact Ofr | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HN | exact Hih'
| exact HJ | intros x; reflexivity | lia | clear - HN1; rewrite Z2Nat.id by lia; lia | clear - HN1; lia
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 8%nat 8%bv eq_refl); exact G8)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 9%nat 9%bv eq_refl); exact G9)
| reg_nowF HS ltac:(reflexivity)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact (HX 67%nat 16%nat _ eq_refl eq_refl))
| reg_nowF HS ltac:(reflexivity) ]. }
cbv beta. intros c' (regs' & mem' & pc' & -> & Hpc' & Hpx & HJ' & K' & HK').
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (regs_kept_of_st_ok ubs0segs Ec ssc msc regs1 _ [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%bv HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity)) as HKR end.
cbn [ms_regs mkst] in HKR.
assert (KF : forall a, mbyte ubs0segs mem' a = mbyte ubs0segs memc a) by (intros a; unfold mbyte; rewrite K', K1; reflexivity).
assert (RR : forall r : reg, In r [2; 3; 4; 8; 9; 19; 21; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs1 r).
{ intros r Hr. rewrite (HK' r) by (revert Hr; clear; intros Hr; cbv in Hr |- *; tauto). apply (HKR r Hr). }
assert (Q20 : getr regs' 20 = Z_to_bv 64 (cg_ihead s)).
{ rewrite (HK' 20%bv ltac:(cbv; auto 20)). reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; exact (HX 67%nat 16%nat _ eq_refl eq_refl)). }
assert (UT : af_untouched regs0 regs').
{ split; [|split; [|split; [|split; [|split; [|split]]]]];
[ rewrite (RR 3%bv ltac:(cbv; auto 20)); exact G3 | rewrite (RR 4%bv ltac:(cbv; auto 20)); exact G4
| rewrite (RR 23%bv ltac:(cbv; auto 20)); exact G23 | rewrite (RR 24%bv ltac:(cbv; auto 20)); exact G24
| rewrite (RR 25%bv ltac:(cbv; auto 20)); exact G25 | rewrite (RR 26%bv ltac:(cbv; auto 20)); exact G26
| rewrite (RR 27%bv ltac:(cbv; auto 20)); exact G27 ]. }
clear Hpc'. rewrite RUNM in Hpx.
destruct (af_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv HD) eqn:XSM; subst pc'.
-
rewrite (af_from_merge_same (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD))))) by (rewrite XMG, ?XSM; reflexivity).
eapply (UI1n.af_same API IMG L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s _ rest FP (Z.to_nat (cg_ihead s)) fh
GPAL gs HD (delay + YO07.f_delay HD) (af_rb brb N (qcount gs) (qcount (YO07.q_set gs (Z.of_nat (Z.to_nat (cg_ihead s))) (Some (YO07.set_delay HD (delay + YO07.f_delay HD)))))));
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | | exact Hwf | exact Hgeom | exact Hfh
| intros a Ha; apply (HFP (fr_ptr fh) FRAME_SIZE a); [apply (frame_blocks_in_cgif0 g s N fh); [exact Hfin | left; reflexivity] | exact Ha]
| exact HB | apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8
| rewrite Q20, Z2Nat.id by lia; reflexivity | exact UT
| exact Xgen | exact Xfile | exact HFPX | exact XCUR | exact (af_slots_occ _ _ _ _ XSL)
| exact (proj1 (af_sink_at API ADDFRAME_STK (spZ regs0) g s0 s N rest FP _ L A mem md Lc Ac mem' mdc HJ' XSK))
| exact XFIN
| apply (proj2 (af_live_iff _ _ _ _ _)); split; [apply (af_hdr_kept memc); [intros _ k _; apply KF | exact XH] | apply (af_slots_kept memc); [intros; apply KF | exact XSL]]
| exact Hih3 | exact XHD
| rewrite (RR 21%bv ltac:(cbv; auto 20)); exact G21
| rewrite (qcount_q_set_some gs (Z.to_nat (cg_ihead s)) HD _ Hih3 XHD); exact (res_ok_mono _ _ _ (af_rb_same brb N (qcount gs) ltac:(clear - HN HW1 HH1; nia)) XRq) ].
eapply (cgif_at_kept0 memc _ g s N (blocks Lc Ac)); [exact HB | exact Hat | intros b n k Hb Hk; apply KF].
-
rewrite (af_from_merge_none (gcfg_of s GPAL) fattr fgen delay tidx nlp LPALv IMGv gs) by (rewrite XMG, ?XSM; reflexivity).
eapply (af_C API IMG FLUSHX L A mem md regs0 regs' Lc Ac mem' mdc g N s0 s rest FP cfp lpal lpa img fattr fgen delay nlp tidx (Z.land fattr 4) GPAL IMGv LPALv gs brb);
[ exact HJ' | exact Hid | exact Hra0 | exact Hal16 | exact Htp0 | | exact Hwf | exact Hgeom | exact HnoCT
| eapply obj_at_transport_range; [exact Hcf | exact lay_inside_FrameConfig | intros k Hk; apply KF] | exact Hcf8 | exact Hcflo | exact Hcfhi | exact Hlpa | exact HFP | exact HB
| apply (af_saved_ok_kept memc); [exact HSV | intros a Ha; apply KF]
| rewrite (RR 2%bv ltac:(cbv; auto 20)); exact G2 | rewrite (RR 8%bv ltac:(cbv; auto 20)); exact G8 | rewrite (RR 9%bv ltac:(cbv; auto 20)); exact G9
| rewrite (RR 19%bv ltac:(cbv; auto 20)); exact G19 | pose proof (land_le fattr 4 ltac:(lia)); lia | exact Q20 | exact UT
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
