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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCdy YCe9 YCfs YCfr YCgw YCfu YCe1 YCe4 YCe2 YCe0.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section d.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AFREE : afree_realizes trbsegs B.
Hypothesis FLUSH : tflush_spec B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let errno_low := tl_env B TL.
Lemma regsIT_ok : forall (i : Z) (regs regs1 : bvmap 5 word) g s1,
cl_regs_at B regs regs1 g ->
getr regs1 10 = w64 (g + 8 * (i - 1)) -> getr regs1 21 = w64 (g + 8 * i) -> getr regs1 22 = w64 (8 * i) -> getr regs1 23 = w64 24 ->
4096 <= g -> g + 96 <= alloc_ceiling ->     1 <= i <= 2 ->
regs_ok (Ereg regs1 (cl_extra regs g s1)) (regsIT i) regs1.
Proof.
intros i regs regs1 g s1 (R2 & R3 & R4 & R8 & R9 & R19 & R18 & R20' & _) R10 R21 R22 R23 Hlo Hhi Hi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (cl_extra regs g s1)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
first [ rewrite (denot_shx E 32 38 _ g SB E32 E38) by (unfold SB; lia); exact R19
| cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; first [exact R8 | rewrite R10; unfold w64; f_equal; lia]
| rewrite E38; exact R18
| rewrite E32, unsigned_lit_small by lia; first [exact R9 | rewrite R10; unfold w64; f_equal; lia | rewrite R21; unfold w64; f_equal; lia]
| rewrite R22; unfold w64; f_equal; lia
| rewrite R23; unfold w64; f_equal; lia ] ]
| ]); try (destruct Hr; fail).
Qed.
Lemma cl_IT2_ok : CL_B_stmt B -> CL_IT_stmt B 2.
Proof.
intros CLB ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk Hcur HR R10 R21 R22 R23.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HTF : TFLUSH_STK = 17440) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seed B TL LAWS CL_IT (regsIT 2) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsIT_ok 2 regs regs1 g s1 HR R10 R21 R22 R23 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Ereg regs1 (cl_extra regs g s1)) in *.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo; reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo; reflexivity).
assert (EA : ew E 35 = Z_to_bv 64 (frame_ptr (nth 2 (cg_frames s1) None))) by (change 35%nat with (32 + (1 + 2))%nat; rewrite EXo; reflexivity).
assert (EAm : ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s1) None))) by (change 34%nat with (32 + (1 + 1))%nat; rewrite EXo; reflexivity).
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanC.
all: try (awr_cl Usp E32u Hing HTS).
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
assert (HEVF : EV_FLUSH = 35) by reflexivity.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanC.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 2 (cg_frames s1) None) as [f|] eqn:Hfi.
{ exfalso. cbn [frame_ptr] in EA.
assert (HfI : nth_error (cg_frames s1) 2 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 2 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right.
apply (frames_blocks_in N (cg_frames s) 0 2 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
rewrite (U_atom E 35 (fr_ptr f) EA) in Hc by (clear - Hf4096 Hfceil C1; lia).
apply Z.eqb_eq in Hc. clear - Hc Hf4096. lia. }
cbn [frame_ptr] in EA.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC CL_B.
{ awr_cl Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H Wc) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9; rreg HS (19%bv : bv 5) Q19.
rreg HS (20%bv : bv 5) Q20; rreg HS (18%bv : bv 5) Q18; rreg HS (21%bv : bv 5) Q21; rreg HS (22%bv : bv 5) Q22; rreg HS (23%bv : bv 5) Q23.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS lyc Sc Wc memc mdc _ g s s1 N rest (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 (cg_cur s1)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s1 N _ HOK) | exact HPerm1].
+ clear - Hk HEVF. lia.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* rewrite Q18. exact E38.
* rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H Wc) E _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 2 (cg_frames s1) None) as [f|] eqn:Hfi.
2:{ exfalso. cbn [frame_ptr] in EA. rewrite (U_atom E 35 0 EA) in Hc by lia. cbn in Hc. discriminate Hc. }
cbn [frame_ptr] in EA. clear Hc.
assert (HfI : nth_error (cg_frames s1) 2 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 2 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfrin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s))).
{ apply (frames_blocks_in N (cg_frames s) 0 2 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (cg_raw s, RAW_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D.
apply D. unfold cgif_blocks. left. reflexivity. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC A_flushFrame.
{ awr_cl Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H Wc) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (10%bv : bv 5) Q10; rreg HS (11%bv : bv 5) Q11; rreg HS (12%bv : bv 5) Q12; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4.
rreg HS (1%bv : bv 5) Q1; rreg HS (8%bv : bv 5) Q8.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS lyc Sc Wc memc mdc _ g s s1 N rest (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32);
assert (Q11' : getr rg 11 = w64 (fr_ptr f)) by (rewrite Q11; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EA);
assert (Q12' : getr rg 12 = w64 (frame_ptr (nth 1 (cg_frames s1) None))) by (rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EAm);
assert (Qs0 : achain lyc (aview trbsegs (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTX_flushFrame)
by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; cbn; tauto);
assert (Htop' : spZ rg + 32 <= ly_top lyc) by (rewrite Qsp, Etopc; clear - Htop; lia);
assert (HROD' : arodata_ok B (aview trbsegs (w_H Wc) mm)) by (exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD));
assert (HEVc : vev Sc + EV_FLUSH <= VEV_MAX) by (clear - Hnev Hk Hev Hk0 HEVF; lia)
end.
assert (Hfr7' : Z.of_nat (length (frames Sc)) <= 7) by (rewrite Hfrs; exact Hfr7).
assert (HLIVEc : blocks_bytes Sc + LIVE_FLUSH <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm1), <- (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly S). exact Hlive. }
assert (HPerm1' : Permutation (ablocks B lyc Sc) (cgif_blocks g (cl_set_cur s1 (cg_cur s1)) N ++ rest)).
{ rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)). exact HPerm1. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k TFLUSH_STK
[(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s1 + 40, cg_raw s1 + 44)] EV_FLUSH (-80) (Z_to_bv 64 CL_RET_FLUSH) []
(fun ly3 S3 W3 regs3 mem3 md3 => exists r gen' rwcur' : Z,
getr regs3 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
tcgif_at (mrestrict (w_H W3) mem3) g (flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' rwcur') /\
cgif_wf (flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' rwcur') N /\
Permutation (ablocks B ly3 S3) (cgif_blocks g s N ++ rest)) HJ Qsp);
[ reflexivity | lia | rewrite HTF; lia | rewrite HTS, HTF; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_even; vm_compute; reflexivity | unfold CL_RET_FLUSH; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (FLUSH lyc Sc Wc rg mm _ [] g (cl_set_cur s1 (cg_cur s1)) N 2%nat f rest HPRE1 Hctx1 Hfr7' Htop' HROD' Q10' HT' HWF1
ltac:(clear; lia) HfI Q11' Q12' HPerm1' HEVc HLIVEc)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP |]]];
cbn [cg_raw cl_set_cur] in HK; rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)) in HK; exact HK ]
| intros a Ha; left; destruct Ha as (rr & Hrr & Hrg); cbn [In] in Hrr;
destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; split;
[ unfold FPc; replace a with (fr_ptr f + (a - fr_ptr f)) by lia; apply (inFP_ablocks_fp _ (fr_ptr f) FRAME_SIZE (a - fr_ptr f)); [| change (req_size FRAME_SIZE) with 40; clear - Hrg; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; exact Hfrin
| exists (fr_ptr f), FRAME_SIZE; split; [exact Hfc | change (req_size FRAME_SIZE) with 40; clear - Hrg; lia]
| unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| change (req_size RAW_SIZE) with 48; clear - Hrg; lia];
unfold cgif_blocks; right; left; reflexivity
| exists (cg_raw s), RAW_SIZE; split; [exact Hinr | change (req_size RAW_SIZE) with 48; clear - Hrg; lia] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hr10 & Rr & HT2 & HWF2 & HPerm2)).
pose proof (proj1 HJ2) as HAR2.
set (s2 := flush_upd (cl_set_cur s1 (cg_cur s1)) 2 gen' rwcur') in *.
assert (HOK2 : cl_obj_ok g s s2 N) by (exact (cl_obj_ok_flush g s _ N 2 gen' rwcur' (cl_obj_ok_setcur g s s1 N _ HOK) HWF2)).
assert (Hcur2 : cg_cur s2 = cg_cur s1) by reflexivity.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s1 + 40, cg_raw s1 + 44)] a).
{ intros a Ha (rr & Hrr & Hrg). cbn [In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; [clear - Ha Hrg Dgf | clear - Ha Hrg Dgr]; lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
jafter_call_keep HS 51%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub trbsegs B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgotb) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgotc) | lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcellb) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcellc) | lia].
- eapply (region_kept_block_subw B LAWS); [exact HJc2 | exact E32u | exact Hing | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | cbn; lia | cbn; unfold CGIF_SIZE; lia | intros a Ha HFP; exact (HnFg a Ha HFP)]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 51 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 51)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 55 = Z_to_bv 64 r) by (rewrite HE2; change 55%nat with (51 + 4)%nat; rewrite (YO3v.ew_havoc_new E 51 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hr10).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 80) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 51)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn50; rewrite OLD2 by exact Hn50; exact (EEo n rr Hn)).
clear SHOK. assert (SHOK : sh_ok trbsegs Bxc cl_SH E2 (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
- unfold U, Bxc. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
- lia.
- change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur2]. cbn [snd] in Rcur2.
assert (HFR2 : cl_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (rewrite ?HTF; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia).
rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanC.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 55 r E2r) in Hc by (clear - Rr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanC CL_B.
{ awr_cl Usp2 E32u2 Hing2 HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W2) E2 _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19.
rreg HS (20%bv : bv 5) P20; rreg HS (18%bv : bv 5) P18.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
set (cR := r mod 2 ^ 32).
pose proof (field_of_region_any E2 _ 32 g _ _ _ _ _ 88 4 (SOff 55 0) HRg3 E32u2 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur3.
cbn [sv_denot] in Vcur3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E2r, unsigned_lit_small in Vcur3 by (clear - Rr; lia).
change (N.to_nat 4) with 4%nat in Vcur3. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur3. change (r mod 2 ^ 32) with cR in Vcur3.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
assert (HT3 : tcgif_at (mrestrict (w_H W2) _) g (cl_set_cur s2 cR))
by (eapply (tcgif_at_stretch B LAWS ly2 S2 W2 mem2 md2 _ g s s2 N rest cR HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 RcR)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N rest ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 cR) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P8. rewrite ?OLD2 by lia; exact E32.
-- rewrite P9. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- rewrite P18. rewrite ?OLD2 by lia. exact E38.
-- rewrite P20. rewrite ?OLD2 by lia. rewrite (EEo 20%nat 20%bv eq_refl). exact R20.
-- intros r' Hr'.
assert (Hr4 : r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W2) E2 _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 55 r E2r) in Hc by (clear - Rr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanC CL_B.
{ awr_cl Usp2 E32u2 Hing2 HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W2) E2 _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19.
rreg HS (20%bv : bv 5) P20; rreg HS (18%bv : bv 5) P18; rreg HS (21%bv : bv 5) P21; rreg HS (22%bv : bv 5) P22; rreg HS (23%bv : bv 5) P23.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
pose proof (field_of_region E2 _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg3 E32u2 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37_2) ltac:(clear - Rcur2; cbn; lia) ltac:(cbn; lia)) as Vcur3.
change (N.to_nat 4) with 4%nat in Vcur3.
assert (HT3 : tcgif_at (mrestrict (w_H W2) _) g (cl_set_cur s2 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS ly2 S2 W2 mem2 md2 _ g s s2 N rest (cg_cur s1) HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 Rcur)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N rest ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 (cg_cur s1)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P8. rewrite ?OLD2 by lia; exact E32.
-- rewrite P9. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- rewrite P18. rewrite ?OLD2 by lia. exact E38.
-- rewrite P20. rewrite ?OLD2 by lia. rewrite (EEo 20%nat 20%bv eq_refl). exact R20.
-- intros r' Hr'.
assert (Hr4 : r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W2) E2 _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
Qed.
Lemma cl_IT1_ok : CL_B_stmt B -> CL_IT_stmt B 2 -> CL_IT_stmt B 1.
Proof.
intros CLB NXT ly S W regs mem md ch g s N rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk Hcur HR R10 R21 R22 R23.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & HT & HWF & HPerm & Hev & Hlive).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1).
pose proof HOK as (HWF1 & Hraw1 & Hattr1 & Hpal1 & Hngp1 & Hfrm1).
pose proof HR as (Rsp & Rgp & Rtp & R8 & R9 & R19 & R18 & R20 & Rhi).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TCLOSE_STK = 17520) by reflexivity. assert (HTF : TFLUSH_STK = 17440) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof (proj1 HWF) as Hlen. pose proof (proj1 HWF1) as Hlen1.
destruct (cl_seed B TL LAWS CL_IT (regsIT 1) true Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 HAR Hing Hstk Hpres
ltac:(unfold spZ in Rsp |- *; rewrite Rsp; rewrite unsigned_lit_small by lia; lia)
(regsIT_ok 1 regs regs1 g s1 HR R10 R21 R22 R23 Hgh Hgceil ltac:(lia)) (fun _ => HFR) (fun _ => R20) (proj1 HT1)) as [HS SHOK].
set (E := Ereg regs1 (cl_extra regs g s1)) in *.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (subst E; rewrite (ew_Ereg_nat regs1 _ 2 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (EXo : forall j, ew E (32 + j) = nth j (cl_extra regs g s1) (Z_to_bv 64 0)) by (intros j; subst E; apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (change 32%nat with (32 + 0)%nat; rewrite EXo; reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
assert (E37 : ew E 37 = Z_to_bv 64 (cg_cur s1)) by (change 37%nat with (32 + 5)%nat; rewrite EXo; reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (change 38%nat with (32 + 6)%nat; rewrite EXo; reflexivity).
assert (EA : ew E 34 = Z_to_bv 64 (frame_ptr (nth 1 (cg_frames s1) None))) by (change 34%nat with (32 + (1 + 1))%nat; rewrite EXo; reflexivity).
assert (EAm : ew E 33 = Z_to_bv 64 (frame_ptr (nth 0 (cg_frames s1) None))) by (change 33%nat with (32 + (1 + 0))%nat; rewrite EXo; reflexivity).
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanC.
all: try (awr_cl Usp E32u Hing HTS).
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN1.
clear HF HFr HG.
assert (HN0 : 0 <= N) by (clear - HWF; destruct HWF as (_ & HW1 & HH1 & HN & _); nia).
assert (HEVF : EV_FLUSH = 35) by reflexivity.
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanC.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 1 (cg_frames s1) None) as [f|] eqn:Hfi.
{ exfalso. cbn [frame_ptr] in EA.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 1 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right.
apply (frames_blocks_in N (cg_frames s) 0 1 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
rewrite (U_atom E 34 (fr_ptr f) EA) in Hc by (clear - Hf4096 Hfceil C1; lia).
apply Z.eqb_eq in Hc. clear - Hc Hf4096. lia. }
cbn [frame_ptr] in EA.
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC CL_IT.
{ awr_cl Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H Wc) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4; rreg HS (8%bv : bv 5) Q8; rreg HS (9%bv : bv 5) Q9; rreg HS (19%bv : bv 5) Q19.
rreg HS (20%bv : bv 5) Q20; rreg HS (18%bv : bv 5) Q18; rreg HS (21%bv : bv 5) Q21; rreg HS (22%bv : bv 5) Q22; rreg HS (23%bv : bv 5) Q23; rreg HS (10%bv : bv 5) Q10.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS lyc Sc Wc memc mdc _ g s s1 N rest (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (NXT ly S W regs mem md ch g s N rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 (cg_cur s1)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
+
split; [exact HJ|]. split; [exact Hk0|]. split.
{ apply (cl_frame_kept (w_H Wc) (w_H Wc) memc); [exact HFR|].
intros a Ha. rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT'|]. split; [exact (cl_obj_ok_setcur g s s1 N _ HOK) | exact HPerm1].
+ clear - Hk HEVF. lia.
+ cbn [cg_cur cl_set_cur]. exact Hcur.
+
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
* rewrite Q2. rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
* rewrite Q3. rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
* rewrite Q4. rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
* rewrite Q8. exact E32.
* rewrite Q9. cbn [sv_denot]. rewrite E32u. reflexivity.
* rewrite Q19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
* rewrite Q18. exact E38.
* rewrite Q20, (EEo 20%nat 20%bv eq_refl). exact R20.
* intros r Hr.
assert (Hr4 : r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H Wc) E _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+ rewrite Q10. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q21. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
+ rewrite Q22. apply bv_eq. vm_compute. reflexivity.
+ rewrite Q23. apply bv_eq. vm_compute. reflexivity.
-
rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
destruct (nth 1 (cg_frames s1) None) as [f|] eqn:Hfi.
2:{ exfalso. cbn [frame_ptr] in EA. rewrite (U_atom E 34 0 EA) in Hc by lia. cbn in Hc. discriminate Hc. }
cbn [frame_ptr] in EA. clear Hc.
assert (HfI : nth_error (cg_frames s1) 1 = Some (Some f)) by (rewrite (nth_error_nth' (cg_frames s1) None) by (rewrite Hlen1; lia); rewrite Hfi; reflexivity).
destruct (slot_frame g s s1 N 1 f HOK HWF HfI) as (f' & HfI' & Efb).
assert (Hfrin : In (fr_ptr f, FRAME_SIZE) (frames_blocks N (cg_frames s))).
{ apply (frames_blocks_in N (cg_frames s) 0 1 f' _ (Nat.le_0_l _) HfI'). rewrite Efb. left. reflexivity. }
assert (Hfc : In (fr_ptr f, FRAME_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Hinr : In (cg_raw s, RAW_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. unfold cgif_blocks. cbn [app]. right. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_ptr f) FRAME_SIZE HAR Hfc) as (_ & Hf4096 & Hfceil & _). change (req_size FRAME_SIZE) with 40 in Hfceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ (cg_raw s) RAW_SIZE HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
assert (Dgf : g + 96 <= fr_ptr f \/ fr_ptr f + 40 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (fr_ptr f, FRAME_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size FRAME_SIZE) with 40 in D.
apply D. unfold cgif_blocks. right. apply in_or_app. left. apply in_or_app. right. exact Hfrin. }
assert (Dgr : g + 96 <= cg_raw s \/ cg_raw s + 48 <= g).
{ pose proof (sep_hd_in B LAWS lyc Sc Wc memc mdc (g, CGIF_SIZE) (cg_raw s, RAW_SIZE) _ HAR HPerm1) as D.
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. change (req_size CGIF_SIZE) with 96 in D. change (req_size RAW_SIZE) with 48 in D.
apply D. unfold cgif_blocks. left. reflexivity. }
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanC A_flushFrame.
{ awr_cl Usp E32u Hing HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H Wc) E _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) Q2; rreg HS (10%bv : bv 5) Q10; rreg HS (11%bv : bv 5) Q11; rreg HS (12%bv : bv 5) Q12; rreg HS (3%bv : bv 5) Q3; rreg HS (4%bv : bv 5) Q4.
rreg HS (1%bv : bv 5) Q1; rreg HS (8%bv : bv 5) Q8.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; lia|]); destruct Hin)) as UN2.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg; cbn [ms_mem restrict mkst] in HRg end.
pose proof (field_of_region E _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg E32u ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37) ltac:(clear - Rcur; cbn; lia) ltac:(cbn; lia)) as Vcur.
change (N.to_nat 4) with 4%nat in Vcur.
assert (HT' : tcgif_at (mrestrict (w_H Wc) _) g (cl_set_cur s1 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS lyc Sc Wc memc mdc _ g s s1 N rest (cg_cur s1) HAR HPerm1 HOK HT1); [| exact Vcur | exact Rcur];
intros a Ha Hna; rewrite (UN2 a Ha Hna); apply (UN1 a Ha Hna)).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etopc & _).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
assert (Q3' : getr rg 3 = w64 (as_gp B)) by (rewrite Q3, (EEo 3%nat 3%bv eq_refl); exact Rgp);
assert (Q4' : getr rg 4 = w64 (as_tp B)) by (rewrite Q4, (EEo 4%nat 4%bv eq_refl); exact Rtp);
assert (Qsp : spZ rg = sp0 + -80) by (unfold spZ; rewrite Q2, Usp; lia);
assert (Q10' : getr rg 10 = w64 g) by (rewrite Q10; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E32);
assert (Q11' : getr rg 11 = w64 (fr_ptr f)) by (rewrite Q11; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EA);
assert (Q12' : getr rg 12 = w64 (frame_ptr (nth 0 (cg_frames s1) None))) by (rewrite Q12; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact EAm);
assert (Qs0 : achain lyc (aview trbsegs (w_H Wc) mm) (sp0 + -80) (s0Z rg) [])
by (apply achain_low; unfold s0Z; rewrite Q8; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E32u; clear - Hgceil; lia);
assert (Hctx1 : In (raZ rg :: spine []) CTX_flushFrame)
by (unfold raZ; rewrite Q1, unsigned_lit_small by lia; cbn; tauto);
assert (Htop' : spZ rg + 32 <= ly_top lyc) by (rewrite Qsp, Etopc; clear - Htop; lia);
assert (HROD' : arodata_ok B (aview trbsegs (w_H Wc) mm)) by (exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD));
assert (HEVc : vev Sc + EV_FLUSH <= VEV_MAX) by (clear - Hnev Hk Hev Hk0 HEVF; lia)
end.
assert (Hfr7' : Z.of_nat (length (frames Sc)) <= 7) by (rewrite Hfrs; exact Hfr7).
assert (HLIVEc : blocks_bytes Sc + LIVE_FLUSH <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B lyc Sc), (bsum_perm _ _ HPerm1), <- (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B ly S). exact Hlive. }
assert (HPerm1' : Permutation (ablocks B lyc Sc) (cgif_blocks g (cl_set_cur s1 (cg_cur s1)) N ++ rest)).
{ rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)). exact HPerm1. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ eapply (cl_call B LAWS Wc rg mm _ TCLOSE_STK sp0 (FPc g s N) ly S W mem md [] lyc Sc mdq k TFLUSH_STK
[(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s1 + 40, cg_raw s1 + 44)] EV_FLUSH (-80) (Z_to_bv 64 CL_RET_FLUSH) []
(fun ly3 S3 W3 regs3 mem3 md3 => exists r gen' rwcur' : Z,
getr regs3 10 = w64 r /\ 0 <= r < 2 ^ 64 /\
tcgif_at (mrestrict (w_H W3) mem3) g (flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' rwcur') /\
cgif_wf (flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' rwcur') N /\
Permutation (ablocks B ly3 S3) (cgif_blocks g s N ++ rest)) HJ Qsp);
[ reflexivity | lia | rewrite HTF; lia | rewrite HTS, HTF; lia
| exact Q3' | exact Q4' | exact Q1 | apply ret_ok_even; vm_compute; reflexivity | unfold CL_RET_FLUSH; rewrite unsigned_lit_small by lia; lia
| exact Qs0
| intros HPRE1; eapply SRr_mono;
[ eapply (FLUSH lyc Sc Wc rg mm _ [] g (cl_set_cur s1 (cg_cur s1)) N 1%nat f rest HPRE1 Hctx1 Hfr7' Htop' HROD' Q10' HT' HWF1
ltac:(clear; lia) HfI Q11' Q12' HPerm1' HEVc HLIVEc)
| cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
exists ly3, S3, regs3, mem3, md3; split; [rewrite Q1; reflexivity | split; [exact HJ1 | split; [exact HP |]]];
cbn [cg_raw cl_set_cur] in HK; rewrite (cgif_blocks_obj_ok g s _ N (cl_obj_ok_setcur g s s1 N _ HOK)) in HK; exact HK ]
| intros a Ha; left; destruct Ha as (rr & Hrr & Hrg); cbn [In] in Hrr;
destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; split;
[ unfold FPc; replace a with (fr_ptr f + (a - fr_ptr f)) by lia; apply (inFP_ablocks_fp _ (fr_ptr f) FRAME_SIZE (a - fr_ptr f)); [| change (req_size FRAME_SIZE) with 40; clear - Hrg; lia];
unfold cgif_blocks; right; right; apply in_or_app; right; exact Hfrin
| exists (fr_ptr f), FRAME_SIZE; split; [exact Hfc | change (req_size FRAME_SIZE) with 40; clear - Hrg; lia]
| unfold FPc; replace a with (cg_raw s + (a - cg_raw s)) by lia; apply (inFP_ablocks_fp _ (cg_raw s) RAW_SIZE (a - cg_raw s)); [| change (req_size RAW_SIZE) with 48; clear - Hrg; lia];
unfold cgif_blocks; right; left; reflexivity
| exists (cg_raw s), RAW_SIZE; split; [exact Hinr | change (req_size RAW_SIZE) with 48; clear - Hrg; lia] ] ]
| ] end.
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 & (r & gen' & rwcur' & Hr10 & Rr & HT2 & HWF2 & HPerm2)).
pose proof (proj1 HJ2) as HAR2.
set (s2 := flush_upd (cl_set_cur s1 (cg_cur s1)) 1 gen' rwcur') in *.
assert (HOK2 : cl_obj_ok g s s2 N) by (exact (cl_obj_ok_flush g s _ N 1 gen' rwcur' (cl_obj_ok_setcur g s s1 N _ HOK) HWF2)).
assert (Hcur2 : cg_cur s2 = cg_cur s1) by reflexivity.
lazymatch type of HP2 with aregs_preserved ?rg _ =>
assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr rg rr)
by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx) end.
assert (Hing2 : In (g, CGIF_SIZE) (ablocks B ly2 S2)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm2|]; left; reflexivity).
assert (HnFg : forall a, g + 0 <= a < g + 96 -> ~ inFP [(fr_ptr f + 20, fr_ptr f + 24); (cg_raw s1 + 40, cg_raw s1 + 44)] a).
{ intros a Ha (rr & Hrr & Hrg). cbn [In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Hrg; rewrite ?Hraw1 in Hrg; [clear - Ha Hrg Dgf | clear - Ha Hrg Dgr]; lia. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR2) as (Kcellc & _ & Kgotc & _). rewrite HBgot, HBcell in Kgotc. rewrite HBcell in Kcellc.
jafter_call_keep HS 51%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1; 2; 3]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | apply Forall_nil].
- eapply (region_kept_stack_sub trbsegs B); [exact HJc2 | exact HJ2 | exact Usp | lia | rewrite HTS; lia | lia | cbn; lia | cbn; lia].
- apply (region_kept_val trbsegs E _ _ A_GOT_shadow 8 A_shadow_glob);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kgotb) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kgotc) | lia].
- apply (region_kept_val trbsegs E _ _ A_shadow_glob 8 SHADOW_OFF);
[exact (val_mem_of_rdword trbsegs _ _ _ _ Kcellb) | exact (val_mem_of_rdword trbsegs _ _ _ _ Kcellc) | lia].
- eapply (region_kept_block_subw B LAWS); [exact HJc2 | exact E32u | exact Hing | exact Hing2 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | cbn; lia | cbn; unfold CGIF_SIZE; lia | intros a Ha HFP; exact (HnFg a Ha HFP)]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 51 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (OLD2 : forall n, (n < 51)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YO3v.ew_havoc_old; exact Hn).
assert (E2r : ew E2 55 = Z_to_bv 64 r) by (rewrite HE2; change 55%nat with (51 + 4)%nat; rewrite (YO3v.ew_havoc_new E 51 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hr10).
clear HE2.
assert (Usp2 : bv_unsigned (ew E2 2) = sp0 - 80) by (rewrite OLD2 by lia; exact Usp).
assert (E32u2 : bv_unsigned (ew E2 32) = g) by (rewrite OLD2 by lia; exact E32u).
assert (E32_2 : ew E2 32 = Z_to_bv 64 g) by (rewrite OLD2 by lia; exact E32).
assert (E37_2 : ew E2 37 = Z_to_bv 64 (cg_cur s1)) by (rewrite OLD2 by lia; exact E37).
assert (E38_2 : ew E2 38 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E38).
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> (n < 51)%nat -> ew E2 n = getr regs1 rr) by (intros n rr Hn Hn50; rewrite OLD2 by exact Hn50; exact (EEo n rr Hn)).
clear SHOK. assert (SHOK : sh_ok trbsegs Bxc cl_SH E2 (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, cl_SH. constructor; [|constructor].
apply (shent_ok_of_block trbsegs B LAWS ly2 S2 W2 mem2 md2 E2 Bxc 32 g CGIF_SIZE 0 CGIF_SIZE HAR2 Hing2).
- unfold U, Bxc. cbn [sv_denot]. rewrite E38_2, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u2.
- lia.
- change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia. }
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT2) eq_refl eq_refl) as [_ Rcur2]. cbn [snd] in Rcur2.
assert (HFR2 : cl_frame (mrestrict (w_H W2) mem2) sp0 regs).
{ apply (cl_frame_kept (w_H Wc) (w_H W2) memc); [exact HFR|].
intros a Ha. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
rewrite (G1 a) by (rewrite ?HTF; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia).
rewrite (UN2 a) by (clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia). apply UN1; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
srr_branch_tok trbtbl_lib_ok HS SHOK RBspanC.
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 55 r E2r) in Hc by (clear - Rr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanC CL_B.
{ awr_cl Usp2 E32u2 Hing2 HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W2) E2 _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19.
rreg HS (20%bv : bv 5) P20; rreg HS (18%bv : bv 5) P18.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let rg3 := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 rg3 HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
set (cR := r mod 2 ^ 32).
pose proof (field_of_region_any E2 _ 32 g _ _ _ _ _ 88 4 (SOff 55 0) HRg3 E32u2 ltac:(cbn; tauto) ltac:(cbn; lia)) as Vcur3.
cbn [sv_denot] in Vcur3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E2r, unsigned_lit_small in Vcur3 by (clear - Rr; lia).
change (N.to_nat 4) with 4%nat in Vcur3. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vcur3. change (r mod 2 ^ 32) with cR in Vcur3.
assert (RcR : 0 <= cR < 2 ^ 32) by (subst cR; apply Z.mod_pos_bound; lia).
assert (HT3 : tcgif_at (mrestrict (w_H W2) _) g (cl_set_cur s2 cR))
by (eapply (tcgif_at_stretch B LAWS ly2 S2 W2 mem2 md2 _ g s s2 N rest cR HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 RcR)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (CLB ly S W regs mem md ch g s N rest ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 cR) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
*
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P8. rewrite ?OLD2 by lia; exact E32.
-- rewrite P9. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- rewrite P18. rewrite ?OLD2 by lia. exact E38.
-- rewrite P20. rewrite ?OLD2 by lia. rewrite (EEo 20%nat 20%bv eq_refl). exact R20.
-- intros r' Hr'.
assert (Hr4 : r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W2) E2 _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
+
rewrite branch_ne_U in Hc. replace (U E2 (SLit 0)) with 0 in Hc by reflexivity. rewrite (U_atom E2 55 r E2r) in Hc by (clear - Rr; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ2 SHOK RBspanC CL_IT.
{ awr_cl Usp2 E32u2 Hing2 HTS. }
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ => rewrite (st_ok_restrict_mkst trbsegs (w_H W2) E2 _ msq HS eq_refl) end. cbn [ss_pc].
rreg HS (2%bv : bv 5) P2; rreg HS (3%bv : bv 5) P3; rreg HS (4%bv : bv 5) P4; rreg HS (8%bv : bv 5) P8; rreg HS (9%bv : bv 5) P9; rreg HS (19%bv : bv 5) P19.
rreg HS (20%bv : bv 5) P20; rreg HS (18%bv : bv 5) P18; rreg HS (21%bv : bv 5) P21; rreg HS (22%bv : bv 5) P22; rreg HS (23%bv : bv 5) P23; rreg HS (10%bv : bv 5) P10.
pose proof (kept_of_frame _ _ _ _ _ (fun a => g + 88 <= a < g + 92) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2, ?E32u2 in Hrr; lia|]); destruct Hin)) as UN3.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
let r := eval vm_compute in (nth 3 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth E2 ssx (restrict _ msx) 3 r HS ltac:(vm_compute; reflexivity)) as HRg3; cbn [ms_mem restrict mkst] in HRg3 end.
pose proof (field_of_region E2 _ 32 g _ _ _ _ _ 88 4 (SOff 37 0) (cg_cur s1) HRg3 E32u2 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E37_2) ltac:(clear - Rcur2; cbn; lia) ltac:(cbn; lia)) as Vcur3.
change (N.to_nat 4) with 4%nat in Vcur3.
assert (HT3 : tcgif_at (mrestrict (w_H W2) _) g (cl_set_cur s2 (cg_cur s1)))
by (eapply (tcgif_at_stretch B LAWS ly2 S2 W2 mem2 md2 _ g s s2 N rest (cg_cur s1) HAR2 HPerm2 HOK2 HT2 UN3 Vcur3 Rcur)).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_mono; [apply (NXT ly S W regs mem md ch g s N rest ly2 S2 W2 rg mm mdq (k + EV_FLUSH) (cl_set_cur s2 (cg_cur s1)) CX)
| intros Wf cf _ HPf; apply (cl_post_mono B ly S W regs mem md g s N rest _ _ Wf cf HPf); clear - HEVF; lia] end.
*
split; [exact HJ2|]. split; [clear - Hk0 HEVF; lia|]. split.
{ apply (cl_frame_kept (w_H W2) (w_H W2) mem2); [exact HFR2|]. intros a Ha. apply UN3; clear - Ha Hgceil Hceil Hslo HTS C1 H47 Hshi; lia. }
split; [exact HT3|]. split; [exact (cl_obj_ok_setcur g s s2 N _ HOK2) | exact HPerm2].
* clear - Hk HEVF. lia.
* cbn [cg_cur cl_set_cur]. exact Hcur.
*
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
-- rewrite P2. rewrite ?OLD2 by lia; rewrite (EEo 2%nat 2%bv eq_refl). exact Rsp.
-- rewrite P3. rewrite ?OLD2 by lia; rewrite (EEo 3%nat 3%bv eq_refl). exact Rgp.
-- rewrite P4. rewrite ?OLD2 by lia; rewrite (EEo 4%nat 4%bv eq_refl). exact Rtp.
-- rewrite P8. rewrite ?OLD2 by lia; exact E32.
-- rewrite P9. cbn [sv_denot]. rewrite ?OLD2 by lia; rewrite E32u. reflexivity.
-- rewrite P19. transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 88) (SLit 3)) (SOff 38 0)));
[ cbn [sv_denot]; rewrite ?OLD2 by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity
| exact (denot_shx E 32 38 88 g SB E32 E38 ltac:(lia) ltac:(lia) ltac:(clear - Hgceil C1; lia) ltac:(unfold SB; lia)) ].
-- rewrite P18. rewrite ?OLD2 by lia. exact E38.
-- rewrite P20. rewrite ?OLD2 by lia. rewrite (EEo 20%nat 20%bv eq_refl). exact R20.
-- intros r' Hr'.
assert (Hr4 : r' = 25 \/ r' = 26 \/ r' = 27) by lia.
destruct Hr4 as [-> | [-> | ->]];
(rewrite (st_ok_restrict_reg trbsegs (w_H W2) E2 _ _ _ HS); cbn [ms_regs];
lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; rewrite ?OLD2 by lia;
lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) => rewrite (EEo n (Z_to_bv 5 rr) eq_refl); apply Rhi; lia end).
* rewrite P10. cbn [sv_denot]. rewrite ?OLD2 by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
* rewrite P21. cbn [sv_denot]. rewrite ?OLD2 by lia. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, ?E32u, ?E32. unfold w64. f_equal; lia.
* rewrite P22. apply bv_eq. vm_compute. reflexivity.
* rewrite P23. apply bv_eq. vm_compute. reflexivity.
Qed.
End d. End c.
