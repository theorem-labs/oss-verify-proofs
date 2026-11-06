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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20 YI1k YI16.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCe9 YCfs YCfu YCe1 YCfq YCe4 YCe0 YCgv YCdq YCdu YCdf YCds YCdn.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsX : list sv := Eval vm_compute in sr_set sr_atoms 8 (SOff 32 88).
Section PX.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma regsX_ok : forall (regs regs1 : bvmap 5 word) g s1 cfp cf more,
af_regs_ret B regs regs1 g -> 0 <= g -> g + 96 <= alloc_ceiling ->
regs_ok (Ereg regs1 (af_extra regs g s1 cfp cf more)) regsX regs1.
Proof.
intros regs regs1 g s1 cfp cf more (R2 & R3 & R4 & R8) Hg0 Hgc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Ereg regs1 (af_extra regs g s1 cfp cf more)).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 g) by (subst E; change 32%nat with (32 + 0)%nat; rewrite (ew_Ereg_extra regs1 _ 0); reflexivity).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; change 38%nat with (32 + 6)%nat; rewrite (ew_Ereg_extra regs1 _ 6); reflexivity).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<- | Hr];
[ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) => let v := eval cbv -[Z.mul Z.add Z.sub Z.opp] in (sr_get a rr2) in change (sr_get a rr2) with v end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ symmetry; apply EE; reflexivity | symmetry; apply getr_zero | reflexivity
| rewrite E32; rewrite unsigned_lit_small by lia; exact R8 ]
| ]); try (destruct Hr; fail).
Qed.
Local Ltac mid_facts CX MID :=
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL);
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof MID as (HJ & Hk0 & HFR & HT1 & HOK & HPerm1 & Hnew);
pose proof HOK as (HWF1 & HW1 & HH1 & Hattr1 & Hraw1 & Hpal1 & Hngp1 & Hgen1 & Hloops1).
Lemma af_RET : AF_RET_stmt B.
Proof.
intros ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 CX MID Hk HR.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
mid_facts CX MID.
pose proof HR as (Rsp & Rgp & Rtp & R8).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seed B TL LAWS AF_RET regsX 0 true [] (cg_ihead s1) 0 0 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear; lia) ltac:(clear; lia)
(regsX_ok regs regs1 g s1 cfp _ _ HR ltac:(lia) Hgceil) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
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
pose proof (obj_at_nth trbsegs _ _ _ _ 15 (88, 4%N) (cg_cur s1) (proj1 HT1) eq_refl eq_refl) as [_ Rcur]. cbn [snd] in Rcur.
aj_run_tok trbtbl_lib_ok HS HJ SHOK RBspanA.
{ awr_a Usp E32u Hing HTS. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => sp0 - 224 <= a < sp0 - 104) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; clear - Hrr; lia|]); destruct Hin)) as UN.
cbv beta in UN.
clear HF HFr HG.
rreg HS (1%bv : bv 5) R1.
eapply (SRr_ret_at trbsegs trbtbl_lib trbtbl_lib_ok Hwx Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold af_post.
lazymatch goal with |- exists ly' S' regs' mem' md', mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists lyc, Sc, rg, mm, mdx end.
split; [rewrite R1; cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; change 54%nat with (54 + 0)%nat; rewrite (ESV 0%nat (1%bv : bv 5) eq_refl); rewrite Hra; reflexivity|].
split; [cbn [ms_mem]; eapply (ajournal_mono_k trbsegs _); [apply (ajournal_materialize trbsegs _ LAWS Hsegs); exact HJ | exact Hk]|].
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
- apply (obj_at_kept _ _ g LAY_CGIF _ 96 Ho lay_inside_CGIF). intros i Hi. apply (mbyte_of_aview trbsegs). apply UN; clear - Hi HZg; lia.
- apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview trbsegs).
assert (Hinr : In (cg_raw s1, RAW_SIZE) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinr) as (_ & Hr4096 & Hrceil & _). change (req_size RAW_SIZE) with 48 in Hrceil.
apply UN; clear - Hi Hr4096 Hrceil C1 Hceil Hslo HTS; lia.
- intros f Hfin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview trbsegs).
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
Lemma cl_set_cur_frames : forall s1 c, cg_frames (cl_set_cur s1 c) = cg_frames s1. Proof. reflexivity. Qed.
Lemma af_RETC : AF_RET_stmt B -> AF_RETC_stmt B.
Proof.
intros PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc regs1 memc mdc k s1 v CX MID Hk HR Hv.
pose proof Hwx_tfa as Hwx. pose proof trb_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
mid_facts CX MID.
pose proof HR as (Rsp & Rgp & Rtp & R8).
pose proof (proj1 HJ) as HAR. pose proof HJ as (_ & HLY & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B lyc Sc)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm1|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
destruct (af_seed B TL LAWS AF_RETC regsX 0 true [] (cg_ihead s1) 88 92 Wc regs regs1 memc lyc Sc mdc ly sp0 g s1 cfp lpal img fattr fgen delay nlp tidx [if Z.land fattr 4 =? 0 then 1 else 0]
HAR Hing (afobj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp 32 HJ HAR0 HPerm HFO) Hstk Hpres
ltac:(rewrite Rsp; rewrite unsigned_lit_small by lia; lia) (or_introl eq_refl) ltac:(clear; lia) ltac:(clear; lia)
(regsX_ok regs regs1 g s1 cfp _ _ HR ltac:(lia) Hgceil) ltac:(vm_compute; reflexivity) ltac:(apply Forall_nil)
(fun _ => HFR) (proj1 HT1) eq_refl
(cfp_obj_journal B LAWS sp0 ly S W mem md [] lyc Sc Wc memc mdc k g s N _ cfp _ HJ HAR0 HPerm HFO HCF)) as [HS SHOK].
set (E := Ereg regs1 _) in HS, SHOK.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros n rr Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (ES : forall m, (32 <= m)%nat -> ew E m = nth (m - 32) (af_extra regs g s1 cfp [lpal; img; fattr; fgen; delay; nlp; tidx] [if Z.land fattr 4 =? 0 then 1 else 0]) (Z_to_bv 64 0))
by (intros m Hm; replace m with (32 + (m - 32))%nat at 1 by lia; subst E; apply ew_Ereg_extra).
pose proof (ES 32%nat ltac:(lia)) as E32. pose proof (ES 38%nat ltac:(lia)) as E38.
clear ES. cbn [Nat.sub nth af_extra af_saved map app firstn repeat] in E32, E38.
assert (Usp : bv_unsigned (ew E 2) = sp0 - 224) by (rewrite (EEo 2%nat 2%bv eq_refl); unfold spZ in Rsp |- *; rewrite Rsp; apply unsigned_lit_small; lia).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
aj_run_to_tok trbtbl_lib_ok HS HJ SHOK RBspanA AF_RET.
{ awr_a Usp E32u Hing HTS. }
pose proof (kept_of_frame _ _ _ _ _ (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HFr
ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?E32u in Hrr; cbv beta; clear - Hrr; lia|]); destruct Hin)) as UN.
cbv beta in UN. clear HF HFr HG.
pose proof (af_side_sep B LAWS lyc Sc Wc memc mdc g s1 N _ ly sp0 (fun a => (sp0 - 224 <= a < sp0 - 104) \/ (g + 88 <= a < g + 92)) HAR HPerm1 Hstk
ltac:(intros a Ha; cbv beta in Ha; clear - Ha HTS; lia)) as [HZr HZf]. cbv beta in HZr, HZf.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r4 := eval vm_compute in (nth 4 (ss_mem ssx) got_region) in
pose proof (st_ok_region_nth Ex ssx msx 4 r4 HS ltac:(vm_compute; reflexivity)) as HR4; cbn [ms_mem restrict mkst] in HR4 end.
lazymatch type of HR4 with region_ok _ ?Ex _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
lazymatch cs with context [YQ0b.mkChunk 88 (CVal 4 ?e88)] =>
pose proof (field_of_region_any Ex _ 32 g cs lo hi wlo whi 88 4%N e88 HR4 E32u ltac:(cbn; tauto) ltac:(cbn; lia)) as Vc;
change (N.to_nat 4) with 4%nat in Vc; cbn [sv_denot] in Vc; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Vc;
rewrite (EEo 24%nat 24%bv eq_refl) in Vc;     change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in Vc; rewrite Hv in Vc end end.
assert (Rv : 0 <= v < 2 ^ 32) by (rewrite <- Hv; apply Z.mod_pos_bound; lia).
lazymatch type of HS with st_ok _ ?Ex _ (restrict ?Hh ?msq) =>
rewrite (st_ok_restrict_mkst trbsegs Hh Ex _ msq HS eq_refl); cbn [ss_pc] end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
apply (PRET ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest lyc Sc Wc rg mm mdq k (cl_set_cur s1 v) CX) end.
-
split; [exact HJ|]. split; [exact Hk0|].
split; [apply (af_frame_kept _ _ sp0 regs HFR); intros a Ha; apply (mbyte_of_aview trbsegs); apply UN; [clear - Ha Hceil Hslo Hshi H47 HTS C1; lia | clear - Ha HZg Hgceil Hceil Hslo HTS C1; lia] |].
split.
{ pose proof HT1 as (Ho & Hr & Hf). split; [|split].
- apply (obj_cgif_setcur _ _ g s1 v Ho); [| exact Vc | exact Rv].
intros i Hi Hni. apply (mbyte_of_aview trbsegs). apply UN; [clear - Hi HZg; lia | clear - Hi Hni HZg; lia].
- cbn [cg_raw cl_set_cur]. apply (obj_at_kept _ _ _ LAY_Raw _ 48 Hr lay_inside_Raw). intros i Hi. apply (mbyte_of_aview trbsegs). destruct (HZr i Hi) as [Hb Hn]. exact (UN _ Hb Hn).
- rewrite cl_set_cur_frames. intros f Hfin. apply (obj_at_kept _ _ _ LAY_Frame _ 40 (Hf f Hfin) lay_inside_Frame). intros i Hi. apply (mbyte_of_aview trbsegs).
destruct (HZf f i Hfin Hi) as [Hb Hn]. exact (UN _ Hb Hn). }
split; [exact HOK|]. split; [exact HPerm1 | exact Hnew].
- exact Hk.
- unfold af_regs_ret; change (spZ regs) with sp0.
split; [|split; [|split]];
(let R := fresh "R" in
lazymatch goal with |- getr _ ?r = _ => rreg HS r R; rewrite R; clear R end;
cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [ exact E32 | exact E38 | rewrite E32u; reflexivity
| rewrite (EEo 2%nat 2%bv eq_refl); exact Rsp | rewrite (EEo 3%nat 3%bv eq_refl); exact Rgp | rewrite (EEo 4%nat 4%bv eq_refl); exact Rtp
| match goal with |- ?gg => idtac "RETC-REG-FAIL" gg end ]).
Qed.
End PX.
End d.
