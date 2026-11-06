(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YC8g YC8a YChd YCjr YCj1 YCj0.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCjc.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI00.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC89.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Hypothesis TCMP : tcmp_spec B.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Definition tin_XD (W : world SEGS) (memc : word -> option byte) (lyc : alayout) (Sc : astate) (sp1 pt npt : Z) (DEC : Z -> Z -> bool)
(gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) : Prop :=
forall mN, acall_kept SEGS B lyc Sc W memc W mN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
(tcmp_zero (aview SEGS (w_H W) mN) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx x y <-> DEC x y = false).
Lemma tin_XD_kept : forall W memc memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx,
tin_XD W memc lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
acall_kept SEGS B lyc Sc W memc W memN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
tin_XD W memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W memc memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx XD K mN KN.
exact (XD mN (acall_kept_trans B _ _ _ _ _ _ _ _ _ K KN)).
Qed.
Definition tin_postX (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt g cfp bfp : Z) (DEC : Z -> Z -> bool) (tidx bimg p c idx : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2944)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 29 = Z_to_bv 64 SB /\ getr regs' 15 = Z_to_bv 64 g /\ getr regs' 16 = Z_to_bv 64 cfp /\ getr regs' 17 = Z_to_bv 64 bfp /\
acall_kept SEGS B lyc Sc W memc W mem' (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) /\
tinV DEC tidx (aview SEGS (w_H W) memc) (aview SEGS (w_H W) mem') pt npt p c bimg idx.
Lemma akept_not_p : forall E rs (W : world SEGS) (m m' : word -> option byte) p,
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> (forall a, in_wrange E rs a -> a = p) ->
forall a, 0 <= a < 2 ^ 64 -> a <> p -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros E rs W m m' p HFr Hw a Ha Hne. apply (aview_kept_out E rs _ m m' HFr a Ha). intros Hin. exact (Hne (Hw a Hin)). Qed.
Lemma akept_nowr : forall E rs (W : world SEGS) (m m' : word -> option byte),
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> (forall a, ~ in_wrange E rs a) ->
forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros E rs W m m' HFr Hw a Ha. apply (aview_kept_out E rs _ m m' HFr a Ha). exact (Hw a). Qed.
Lemma aview_of_val_mem1 : forall (H : word -> bool) (m : word -> option byte) a v,
val_mem SEGS (mrestrict H m) a 1 v -> aview SEGS H m a = Some (v mod 256).
Proof.
intros H m a v Hv. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r.
rewrite Z.mod_mod by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & Vg & Vcfp & Hnpt32 & H18 & H19 & H21).
Definition tin_stmtX (m : nat) : Prop :=
forall (c : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt ti bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) (DEC : Z -> Z -> bool),
c <= Z.of_nat m -> 1 <= c <= 65535 ->
tin_ctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
tin_XD W memc lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
0 <= ti -> ti + c <= npt -> 0 <= idx -> idx + c <= Nb ->
getr regs 29 = Z_to_bv 64 SB -> getr regs 15 = Z_to_bv 64 g -> getr regs 16 = Z_to_bv 64 cfp -> getr regs 17 = Z_to_bv 64 bfp ->
getr regs 26 = Z_to_bv 64 ti -> getr regs 20 = Z_to_bv 64 c -> getr regs 24 = Z_to_bv 64 idx ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x287c)) memc (seg_rom SEGS)) mdc)
(tin_postX W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp DEC tidx bimg (pt + ti) c idx).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Lemma fl_tin_tailX : forall m, tin_stmtX m ->
forall (c : Z) W (regs regsN : bvmap 5 word) memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt npt ti bimg Nb idx g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) (DEC : Z -> Z -> bool),
c - 1 <= Z.of_nat m -> 1 <= c <= 65535 ->
(tin_ctx B) W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
0 <= ti -> ti + c <= npt -> 0 <= idx -> idx + c <= Nb ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memN mdN k ->
acall_kept SEGS B lyc Sc W memc W memN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
tin_XD W memc lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
tinB DEC tidx (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memN) pt npt (pt + ti) bimg idx ->
(forall r : bv 5, reg_in r TIN_CLOB = false -> getr regsN r = getr regs r) ->
getr regsN 29 = Z_to_bv 64 SB -> getr regsN 15 = Z_to_bv 64 g -> getr regsN 16 = Z_to_bv 64 cfp -> getr regsN 17 = Z_to_bv 64 bfp ->
getr regsN 26 = Z_to_bv 64 ti -> getr regsN 20 = Z_to_bv 64 c -> getr regsN 24 = Z_to_bv 64 idx ->
SRr SEGS W (mkCfg (mkst regsN (Z_to_bv 64 (BASE + 0x290c)) memN (seg_rom SEGS)) mdN)
(tin_postX W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp DEC tidx bimg (pt + ti) c idx).
Proof.
intros m IH c W regs regsN memc mdc memN mdN sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC
Hm Hcnt HCTX Hti1 Hti2 Hidx1 Hidx2 HJN K XD XB HK N29 N15 N16 N17 N26 N20 N24.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJN. pose proof HJN as HJN0.
assert (HSpresN : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memN a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memN mdN pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
remember (Eimg (Ereg regsN [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsN []) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsN r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite N26 in E26.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite N20 in E20. pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite N24 in E24.
assert (HS : st_ok_pi SEGS VAL E ss_ttl (restrict (w_H W) (mkst regsN (Z_to_bv 64 (BASE + 0x290c)) memN (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ttl. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x290c) _ regsN _ _ (mrestrict (w_H W) memN)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [ttl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E20, E24, E26, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; lia. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memN).
hei_havoc HS; paj_run_tok RUN HS HJN SHOK FLBspan.
1: apply awr_ok_nil.
rename HFr into HFra. rename HG into HGa. clear HF.
pose proof (acall_kept_of_run B LAWS E _ lyc Sc W memN _ mdN (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) (proj1 HJN0) HFra HGa
ltac:(unfold ss_ttl; cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; apply HSpresN; lia)) as Ka.
pose proof (akept_nowr _ _ W _ _ HFra ltac:(unfold ss_ttl; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr)) as XKa.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJN) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJN SHOK FLBspan 0x287c.
1: apply awr_ok_nil.
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrb HGb
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kb.
pose proof (akept_nowr _ _ W _ _ HFrb ltac:(unfold ss_ttl; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr)) as XKb.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K (acall_kept_trans B _ _ _ _ _ _ _ _ _ Ka Kb)) as Kab.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsN _ TIN_KEPT19 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
assert (HK2 : forall r : bv 5, reg_in r TIN_CLOB = false -> getr (ms_regs ms0) r = getr regs r).
{ intros r Hr. transitivity (getr regsN r); [|exact (HK r Hr)].
destruct (tin_clob_cases r Hr) as [-> | Hr']; [rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')]. }
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
prreg HS (26%bv : bv 5) R26. prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R24.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
pose proof (tin_ctx_kept B LAWS W regs (ms_regs msX) memc mdc (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJN Kab ltac:(lia) ltac:(tctx_regs_of HK2)) as HCTX2 end.
eapply SRr_mono.
{ unfold tin_stmt in IH. eapply (IH (c - 1) _ _ _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt npt (ti + 1) bimg Nb (idx + 1) g cfp bfp tidx);
[ lia | lia | exact HCTX2 | eapply tin_XD_kept; [exact XD | exact Kab] | lia | lia | lia | lia
| rewrite R29, ?ew_ewset_other by lia; rewrite (EE 29%nat 29%bv eq_refl); exact N29
| rewrite R15, ?ew_ewset_other by lia; rewrite (EE 15%nat 15%bv eq_refl); exact N15
| rewrite R16, ?ew_ewset_other by lia; rewrite (EE 16%nat 16%bv eq_refl); exact N16
| rewrite R17, ?ew_ewset_other by lia; rewrite (EE 17%nat 17%bv eq_refl); exact N17
| rewrite R26, ?ew_ewset_other by lia; rewrite E26, unsigned_lit_small by lia; reflexivity
| rewrite R20, ?ew_ewset_other by lia; rewrite E20, unsigned_lit_small by lia; f_equal; lia
| rewrite R24, ?ew_ewset_other by lia; rewrite E24, unsigned_lit_small by lia; reflexivity ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & H293 & H153 & H163 & H173 & K3 & XV3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK2 r Hr)|].
split; [exact H293|]. split; [exact H153|]. split; [exact H163|]. split; [exact H173|].
split; [eapply (acall_kept_trans B); [exact Kab | exact K3]|].
replace (pt + (ti + 1)) with (pt + ti + 1) in XV3 by (clear; lia).
assert (Hp1 : pt <= pt + ti) by (clear - Hti1; lia). assert (Hp2 : pt + ti + c <= pt + npt) by (clear - Hti2; lia).
lazymatch type of XV3 with tinV _ _ (aview _ _ ?m0) _ _ _ _ _ _ _ =>
apply (tinV_step DEC tidx _ (aview SEGS (w_H W) memN) (aview SEGS (w_H W) m0) _ pt npt (pt + ti) c bimg idx);
[ clear - Hc Hcnt; lia | exact XB
| intros a Ha; cbn [ms_mem]; rewrite (XKb a ltac:(clear - Ha Hq4096 Hqceil Hrnp C1; lia)); exact (XKa a ltac:(clear - Ha Hq4096 Hqceil Hrnp C1; lia))
| intros j Hj; pose proof Kab as (_ & KB2 & _); apply (KB2 bimg Nb (idx + j) Hbi); [clear - Hj Hidx1 Hidx2 HrNb; lia | cbn beta; clear - Hj Hidx1 Hidx2 HsepI HrNb Hrnp; lia]
| exact XV3 ] end.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 20 c (-1)) in Hc by (first [exact E20 | lia]). rewrite U_lit in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJN) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJN SHOK FLBspan 0x2944.
1: apply awr_ok_nil.
rename HFr into HFrc. rename HG into HGc. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HARb HFrc HGc
ltac:(cbn [ss_mem]; intros a (r & Hr & Hw); destruct Hr)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(intros a Ha; pose proof Ka as (_ & _ & _ & _ & _ & K6); apply K6; lia)) as Kc.
pose proof (akept_nowr _ _ W _ _ HFrc ltac:(unfold ss_ttl; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr)) as XKc.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsN _ TIN_KEPT19 HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (29%bv : bv 5) R29. prreg HS (15%bv : bv 5) R15. prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJN|].
split; [intros r Hr; transitivity (getr regsN r); [destruct (tin_clob_cases r Hr) as [-> | Hr']; [cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity | exact (HKr r Hr')] | exact (HK r Hr)]|].
split; [rewrite R29, ?ew_ewset_other by lia; rewrite (EE 29%nat 29%bv eq_refl); exact N29|].
split; [rewrite R15, ?ew_ewset_other by lia; rewrite (EE 15%nat 15%bv eq_refl); exact N15|].
split; [rewrite R16, ?ew_ewset_other by lia; rewrite (EE 16%nat 16%bv eq_refl); exact N16|].
split; [rewrite R17, ?ew_ewset_other by lia; rewrite (EE 17%nat 17%bv eq_refl); exact N17|].
split; [eapply (acall_kept_trans B); [exact K | eapply (acall_kept_trans B); [exact Ka | exact Kc]]|].
replace c with 1 by (clear - Hc; lia).
apply (tinV_last DEC tidx _ _ _ pt npt (pt + ti) bimg idx XB). intros a Ha. cbn [ms_mem].
rewrite (XKc a ltac:(clear - Ha Hq4096 Hqceil Hrnp C1; lia)). exact (XKa a ltac:(clear - Ha Hq4096 Hqceil Hrnp C1; lia)).
Qed.
Lemma fl_tin_stepX : forall m, tin_stmtX m -> tin_stmtX (S m).
Proof.
intros m IH. unfold tin_stmtX.
intros c W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC
Hm Hcnt HCTX XD Hti1 Hti2 Hidx1 Hidx2 H29 H15 H16 H17 H26 H20 H24.
pose proof HCTX as HCTX0. tin_ctx_names HCTX.
tin_prelude HJ. pose proof HJ as HJ0.
assert (HSpres1 : forall a, sp1 - TCMP_STK <= a < sp1 -> apresent (w_H W) memc a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt npt HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ pt npt HAR Hpt) as Hqh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bimg Nb HAR Hbi) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & Hcpres & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bfp FRAME_SIZE HAR Hbf) as (Hb16 & Hb4096 & Hbceil & Hbfh_ia & Hbpres & _). pose proof (proj1 Hbfh_ia) as Hbfh.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hbfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' npt ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
pose proof (proj1 (proj2 HJ)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
remember (pt + ti) as p eqn:Ep.
assert (Hp1 : pt <= p) by lia. assert (Hp2 : p + c <= pt + npt) by lia.
destruct (val_mem_byte1 (w_H W) memc p (proj1 (Hqpres p ltac:(lia)))) as (vb & Rvb & Vvb).
remember (Eimg (Ereg regs [Z_to_bv 64 tidx])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 tidx]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9. pose proof (EE 29%nat 29%bv eq_refl) as E29. rewrite H29 in E29.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite H24 in E24. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite H26 in E26.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite H15 in E15. pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite H16 in E16.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite H17 in E17.
pose proof (EE 1%nat 1%bv eq_refl) as E1. pose proof (EE 2%nat 2%bv eq_refl) as E2. pose proof (EE 3%nat 3%bv eq_refl) as E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. pose proof (EE 8%nat 8%bv eq_refl) as E8.
assert (E32 : ew E 32 = Z_to_bv 64 tidx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E ss_tin (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x287c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tin, tin_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x287c) _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]. rewrite H19. cbn [sv_denot]. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]; unfold region_ok, tin_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 184 8 _ tidx); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vbfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vg]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcfp]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite E29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact Vsb]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [tin_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E29, E21, E20, E24, E26, E18, E15, E16, E17, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memc).
hei_havoc HS; paj_run_tok RUN HS HJ SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (acall_kept_of_run B LAWS E _ lyc Sc W memc _ mdc (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR HFr1 HG1
ltac:(unfold ss_tin, tin_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpres1) as K1.
pose proof (akept_not_p _ _ W _ _ p HFr1 ltac:(unfold ss_tin, tin_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)) as XK1.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (F21 : ew E1 21 = Z_to_bv 64 pt) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E21);
assert (F26 : ew E1 26 = Z_to_bv 64 ti) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26);
assert (F18 : ew E1 18 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24 : ew E1 24 = Z_to_bv 64 idx) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E1 _ _ =>
assert (F21 : ew E1 21 = Z_to_bv 64 pt) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E21);
assert (F26 : ew E1 26 = Z_to_bv 64 ti) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26);
assert (F18 : ew E1 18 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24 : ew E1 24 = Z_to_bv 64 idx) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pt npt HAR1 Hpt) as (_ & _ & _ & _ & Hqpres1 & _).
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ssv ?msv =>
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pt + ti)) (denot_add_atoms E1 21 26 pt ti F21 F26 ltac:(lia) ltac:(lia) ltac:(lia)) Rs11;
rewrite <- Ep in Rs11;
pose proof (st_ok_pi_havoc_hi 37 E1 ssv msv [Z_to_bv 64 p; Z_to_bv 64 vb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 37%nat [Z_to_bv 64 p; Z_to_bv 64 vb];
clear HS; rename HS3 into HS | st_ok _ ?E1 ?ssv ?msv =>
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pt + ti)) (denot_add_atoms E1 21 26 pt ti F21 F26 ltac:(lia) ltac:(lia) ltac:(lia)) Rs11;
rewrite <- Ep in Rs11;
pose proof (st_ok_pi_havoc_hi 37 E1 ssv msv [Z_to_bv 64 p; Z_to_bv 64 vb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 37%nat [Z_to_bv 64 p; Z_to_bv 64 vb];
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E37 : ew E3 37 = Z_to_bv 64 p) by (exact (ew_havoc_new E1 37 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E38 : ew E3 38 = Z_to_bv 64 vb) by (exact (ew_havoc_new E1 37 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
assert (Vvb1 : val_mem SEGS (ms_mem msv) p 1 vb)
by (cbn [ms_mem restrict mkst]; apply (val_mem_frame E _ _ _ _ 1 vb HFr1); [| lia | cbn [Z.of_nat]; lia | exact Vvb];
intros kk Hkk; unfold ss_tin, tin_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr;
destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia);
pose proof (st_ok_pin_rege E3 ssv msv 27%bv (SOff 37 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Rs11; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E37 : ew E3 37 = Z_to_bv 64 p) by (exact (ew_havoc_new E1 37 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E38 : ew E3 38 = Z_to_bv 64 vb) by (exact (ew_havoc_new E1 37 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
assert (Vvb1 : val_mem SEGS (ms_mem msv) p 1 vb)
by (cbn [ms_mem restrict mkst]; apply (val_mem_frame E _ _ _ _ 1 vb HFr1); [| lia | cbn [Z.of_nat]; lia | exact Vvb];
intros kk Hkk; unfold ss_tin, tin_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr;
destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia);
pose proof (st_ok_pin_rege E3 ssv msv 27%bv (SOff 37 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Rs11; cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 37 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 37 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E37, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 38 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 38 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E38, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 37%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E37, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hqpres1 (p + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ p 0 1 _ vb); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvb1])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 37%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 38 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E37, unsigned_lit_small by lia; split; [lia|]; split; [lia|];
split; [intros o Ho; apply (apresent_writable SEGS); apply (proj1 (Hqpres1 (p + o) ltac:(lia)))|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ p 0 1 _ vb); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvb1])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (F29 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29);
assert (G18 : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (G24 : ew E3 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E3 _ _ =>
assert (F29 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29);
assert (G18 : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (G24 : ew E3 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (G26 : ew E3 26 = Z_to_bv 64 ti) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26) | st_ok _ ?E3 _ _ =>
assert (G26 : ew E3 26 = Z_to_bv 64 ti) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E26)  end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ => rewrite branch_ltu_U in Hb; rewrite (U_atom _ 37 p E37), (U_atom _ 26 ti G26) in Hb by lia; apply Z.ltb_lt in Hb; lia end. }
reshok_bx HS 29%nat.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 37 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 37 p cc E37) by lia | rewrite (U_atom Ex 37 p E37) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len pt npt HAR1 Hpt); [rewrite (U_atom Ex 29 SB F29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite E37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR1 HFr2 HG2
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite E37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K1 as (_ & _ & _ & _ & _ & K6); exact K6)) as K2.
pose proof (akept_not_p _ _ W _ _ p HFr2 ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite E37, unsigned_lit_small in Hw by lia; lia | lia])) as XK2.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1 K2) as K12.
lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
assert (F18b : ew E1 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24b : ew E1 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24) | st_ok _ ?E1 _ _ =>
assert (F18b : ew E1 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F24b : ew E1 24 = Z_to_bv 64 idx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E24)  end.
pose proof (proj1 HJ) as HAR2.
assert (Hbx : bimg <= bimg + idx < bimg + req_size Nb) by lia.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bimg Nb HAR2 Hbi) as (_ & _ & _ & _ & Hipres2 & _).
destruct (val_mem_byte1 (w_H W) _ (bimg + idx) (proj1 (Hipres2 (bimg + idx) Hbx))) as (vbb & Rvbb & Vvbb).
lazymatch type of HS with st_ok_pi _ _ ?E1 ?ssv ?msv =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (bimg + idx)) (denot_add_atoms E1 18 24 bimg idx F18b F24b ltac:(lia) ltac:(lia) ltac:(lia)) Ra0;
pose proof (st_ok_pi_havoc_hi 45 E1 ssv msv [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 45%nat [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb];
clear HS; rename HS3 into HS | st_ok _ ?E1 ?ssv ?msv =>
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (bimg + idx)) (denot_add_atoms E1 18 24 bimg idx F18b F24b ltac:(lia) ltac:(lia) ltac:(lia)) Ra0;
pose proof (st_ok_pi_havoc_hi 45 E1 ssv msv [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb] HS ltac:(vm_compute; reflexivity)) as HS3; hei_pose E1 45%nat [Z_to_bv 64 (bimg + idx); Z_to_bv 64 vbb];
clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E39 : ew E3 45 = Z_to_bv 64 (bimg + idx)) by (exact (ew_havoc_new E1 45 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E40 : ew E3 46 = Z_to_bv 64 vbb) by (exact (ew_havoc_new E1 45 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
pose proof (st_ok_pin_rege E3 ssv msv 10%bv (SOff 45 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
lazymatch E3 with havoc ?E1 _ ?ws =>
assert (E39 : ew E3 45 = Z_to_bv 64 (bimg + idx)) by (exact (ew_havoc_new E1 45 ws 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E40 : ew E3 46 = Z_to_bv 64 vbb) by (exact (ew_havoc_new E1 45 ws 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
pose proof (st_ok_pin_rege E3 ssv msv 10%bv (SOff 45 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 45 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E39, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 45 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E39, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 46 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
pose proof (st_ok_pi_add_fact E3 ssv msv 46 (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E40, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 ?ssv ?msv =>
assert (G37 : ew E3 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 45%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 46 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E39, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ (bimg + idx) 0 1 _ vbb); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvbb])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite G37, E39; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?E3 ?ssv ?msv =>
assert (G37 : ew E3 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
pose proof (st_ok_pi_add_region E3 ssv msv (YP09.mkRegion (Some 45%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 46 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E39, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E3 _ (bimg + idx) 0 1 _ vbb); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vvbb])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite G37, E39; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9, !unsigned_lit_small by lia;
repeat split; lia)) as HS3;
clear HS; rename HS3 into HS  end.
norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (G18c : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18) | st_ok _ ?E3 _ _ =>
assert (G18c : ew E3 18 = Z_to_bv 64 bimg) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18)  end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ => rewrite branch_ltu_U in Hb; rewrite (U_atom _ 45 (bimg + idx) E39), (U_atom _ 18 bimg G18c) in Hb by lia; apply Z.ltb_lt in Hb; lia end. }
lazymatch type of HS with st_ok_pi _ _ ?E3 _ _ =>
assert (F6 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29) | st_ok _ ?E3 _ _ =>
assert (F6 : ew E3 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29)  end.
reshok_bx HS 29%nat.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK FLBspan AF_both3_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 45 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 45 (bimg + idx) cc E39) by lia | rewrite (U_atom Ex 45 (bimg + idx) E39) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len bimg Nb HAR2 Hbi); [rewrite (U_atom Ex 29 SB F6); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { apply awr_ok_cons_ro; [cbn; lia|].
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite G37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR2 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[lia | rewrite G37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K12 as (_ & _ & _ & _ & _ & K6); exact K6)) as K3.
pose proof (akept_not_p _ _ W _ _ p HFr3 ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[lia | rewrite G37, unsigned_lit_small in Hw by lia; lia | lia])) as XK3.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K12 K3) as K123.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TIN_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKrX. cbn [ms_regs restrict] in HKrX.
pose proof (proj1 HJ) as HARX.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) ?pcX (ms_mem _) _) ?mdX) _ =>
eapply (aj_call_sp B LAWS W (ms_regs msX) (ms_mem msX) pcX TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc mdX k TCMP_STK [] 0 (sp1 - sp0) (Z_to_bv 64 (BASE + 0x28e4)) ch1
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc /\ W2 = W /\ exists v : word, getr regs2 10 = v /\
(v = w64 0 <-> tcmp_zero (aview SEGS (w_H W) (ms_mem msX)) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx vb vbb)) HJ) end.
- unfold spZ. rewrite Qsp. rewrite Usp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite WS. lia. - rewrite WS, FFS. lia.
- rewrite Qgp, E3. exact Hgp. - rewrite Qtp, E4. exact Htp.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. - rewrite unsigned_lit_small by lia. lia.
- unfold s0Z. rewrite Qs0, E8. replace (sp0 + (sp1 - sp0)) with sp1 by lia. eapply (achain_keptK B); [exact K123 | exact Hch | lia | lia | lia].
- intros HPRE1. eapply SRr_mono.
+ eapply (TCMP lyc Sc W _ _ _ ch1 g cfp bfp vb vbb gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HPRE1).
* rewrite Qa0, E15. reflexivity. * rewrite Qa1, E16. reflexivity. * rewrite Qa2, E17. reflexivity.
* first [exact Qa3 | rewrite Qa3, E38; reflexivity | rewrite Qa3; reflexivity]. * first [exact Qa4 | rewrite Qa4, E40; reflexivity | rewrite Qa4; reflexivity]. * lia. * lia.
* exact Hg. * exact Hcf. * exact Hbf. * exact Hcb.
* eapply (obj_at_keptK B); [exact K123 | exact Hg | vm_compute; reflexivity | change (req_size CGIF_SIZE) with 96; intros i Hi Hn; lia | exact Og].
* exact Ogpal. * exact Ongp.
* eapply (obj_at_keptK B); [exact K123 | exact Hcf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Oc].
* exact Ocpal. * exact Ocattr. * exact Ocnlp. * exact Octidx.
* eapply (obj_at_keptK B); [exact K123 | exact Hbf | vm_compute; reflexivity | change (req_size FRAME_SIZE) with 40; intros i Hi Hn; lia | exact Ob].
* exact Obpal. * exact Obattr. * exact Obnlp. * exact Obtidx.
* exact HLc. * exact HLb. * exact HGp.
+ cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJc & HPc & Hv & Hz).
exists lyc, Sc, regs2, mem2, md2. split; [rewrite Qra; reflexivity|]. split; [exact HJc|]. split; [exact HPc|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. exists v. split; [exact Hv | exact Hz].
- intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & -> & -> & -> & v & Hv & Hz).
rewrite Z.add_0_r in HJ2. replace (sp0 + (sp1 - sp0)) with sp1 in HJc by lia.
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
pose proof (acall_kept_of_journal SEGS B pa_segs_low TCMP_STK sp1 [] [] lyc Sc W _ _ lyc Sc W mem2 md2 0 (fun _ => False) HJc HARX
ltac:(intros a (r & Hr & _); destruct Hr) ltac:(intros b mm i Hb _ _; exact Hb) sink_closed_nil) as Kc0.
pose proof (acall_kept_mono_E SEGS B _ _ _ _ _ _ _ _ _ (fun a => pt <= a < pt + npt) Kc0 ltac:(intros a HF; destruct HF)) as Kc.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K123 Kc) as K12c.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 29 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2 | st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 29 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [1; 2]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]
| specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_sub_ajw B LAWS _ lyc Sc W _ W mem2 _ _ _ 37 0 1 0 1 _ p pt npt lyc Sc md2);
[ exact Kc0 | exact (proj1 HJ2) | exact Hpt
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [apply unsigned_lit_small; lia | rewrite E37; apply unsigned_lit_small; lia]
| exact Hpt | lia | lia | lia | lia | intros a Ha Hn; exact Hn ]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc0 | exact HJ2
| rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia
| lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ =>
assert (H37 : ew Ecur 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
assert (G29 : ew Ecur 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29) | st_ok _ ?Ecur _ _ =>
assert (H37 : ew Ecur 37 = Z_to_bv 64 p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [reflexivity | exact E37]);
assert (G29 : ew Ecur 29 = Z_to_bv 64 SB) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E29)  end.
reshok_bx HS 29%nat.
pose proof (proj1 HJ2) as HAR3.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR3 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof Kc as (_ & _ & _ & _ & _ & K6); exact K6)) as K4.
pose proof (akept_not_p _ _ W _ _ p HFr4 ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; lia | lia])) as XK4.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K12c K4) as K1234.
assert (TAIL : forall Ex ssx msx mdx, st_ok_pi SEGS VAL Ex ssx (restrict (w_H W) msx) -> ss_pc ssx = 0x290c -> ss_resv ssx = None ->
env_agree 32 (Ereg regs [Z_to_bv 64 tidx]) Ex ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssx) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) TIN_KEPT = true ->
sr_get (ss_regs ssx) 0%bv = SLit 0 -> sr_get (ss_regs ssx) 19%bv = SLit 1 ->
sr_get (ss_regs ssx) 29%bv = SOff 29 0 -> sr_get (ss_regs ssx) 15%bv = SOff 15 0 -> sr_get (ss_regs ssx) 16%bv = SOff 16 0 -> sr_get (ss_regs ssx) 17%bv = SOff 17 0 ->
sr_get (ss_regs ssx) 26%bv = SOff 26 0 -> sr_get (ss_regs ssx) 20%bv = SOff 20 0 -> sr_get (ss_regs ssx) 24%bv = SOff 24 0 ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W (ms_mem msx) mdx k ->
acall_kept SEGS B lyc Sc W memc W (ms_mem msx) (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) ->
tinB DEC tidx (aview SEGS (w_H W) memc) (aview SEGS (w_H W) (ms_mem msx)) pt npt p bimg idx ->
SRr SEGS W (mkCfg msx mdx) (tin_postX W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt npt g cfp bfp DEC tidx bimg p c idx)).
{ intros Ex ssx msx mdx HSx Hpc Hrv HAEx Hkept H0 H19x H29x H15x H16x H17x H26x H20x H24x HJx Kx XBx.
subst p.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ TIN_KEPT HSx HAEx Hkept) as HKx. cbn [ms_regs restrict] in HKx.
assert (XX : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew Ex n = getr regs r).
{ intros n r Hn32 Hn. rewrite (proj1 HAEx n Hn32). apply ew_Ereg_nat. exact Hn. }
rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSx Hrv). rewrite Hpc.
eapply (fl_tin_tailX m IH c W regs (ms_regs msx) memc mdc (ms_mem msx) mdx sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt npt ti bimg Nb idx g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC);
[ lia | exact Hcnt | exact HCTX0 | exact Hti1 | exact Hti2 | exact Hidx1 | exact Hidx2 | exact HJx | exact Kx | exact XD | exact XBx | | | | | | | | ].
- intros r Hr. destruct (tin_clob_cases3 r Hr) as [-> | [-> | Hr']].
+ rewrite (st_ok_pi_restrict_reg _ _ _ _ 0%bv HSx), H0. rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS0). reflexivity.
+ rewrite (st_ok_pi_restrict_reg _ _ _ _ 19%bv HSx), H19x, H19. reflexivity.
+ exact (HKx r Hr').
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 29%bv HSx), H29x. cbn [sv_denot]. rewrite (XX 29%nat 29%bv ltac:(lia) eq_refl), H29, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 15%bv HSx), H15x. cbn [sv_denot]. rewrite (XX 15%nat 15%bv ltac:(lia) eq_refl), H15, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 16%bv HSx), H16x. cbn [sv_denot]. rewrite (XX 16%nat 16%bv ltac:(lia) eq_refl), H16, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 17%bv HSx), H17x. cbn [sv_denot]. rewrite (XX 17%nat 17%bv ltac:(lia) eq_refl), H17, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 26%bv HSx), H26x. cbn [sv_denot]. rewrite (XX 26%nat 26%bv ltac:(lia) eq_refl), H26, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 20%bv HSx), H20x. cbn [sv_denot]. rewrite (XX 20%nat 20%bv ltac:(lia) eq_refl), H20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (st_ok_pi_restrict_reg _ _ _ _ 24%bv HSx), H24x. cbn [sv_denot]. rewrite (XX 24%nat 24%bv ltac:(lia) eq_refl), H24, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (iff_trans Hz (XD _ K123 vb vbb Rvb Rvbb)) as XVD.
assert (XVbb0 : aview SEGS (w_H W) memc (bimg + idx) = Some (vbb mod 256)).
{ pose proof K12 as (_ & KB2 & _). rewrite <- (KB2 bimg Nb idx Hbi ltac:(clear - Hidx1 Hidx2 Hcnt HrNb; lia) ltac:(cbn beta; clear - Hidx1 Hidx2 Hcnt HsepI HrNb Hrnp; lia)). exact (aview_of_val_mem1 _ _ _ _ Vvbb). }
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x290c.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K4 as (_ & _ & _ & _ & _ & K6); exact K6)) as K5.
pose proof (akept_not_p _ _ W _ _ p HFr5 ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; lia | lia])) as XK5.
lazymatch type of Hc1 with context [sv_denot (havoc ?E1 512 ?ws) (SOff 516 0)] =>
assert (E516 : ew (havoc E1 512 ws) 516 = getr regs2 10) by (exact (ew_havoc_new E1 512 ws 4 (Z_to_bv 64 0) ltac:(rewrite length_map; unfold CLOB; cbn [length]; lia))) end.
assert (XDv : DEC vb vbb = true).
{ rewrite branch_ne_U in Hc1. destruct (DEC vb vbb) eqn:ED; [reflexivity | exfalso]. pose proof (proj2 XVD eq_refl) as Ev.
rewrite Hv, Ev in E516. unfold w64 in E516.
rewrite (U_atom _ 516 0 E516), U_lit in Hc1 by (clear; lia). discriminate Hc1. }
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact HJ2 | exact (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1234 K5) | ].
intros a Ha. destruct (Z.eqb_spec a p) as [-> | Hne].
+ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (F38 : ew Ex 38 = Z_to_bv 64 vb) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E38) end.
lazymatch type of H37 with ew ?Ex 37 = _ => assert (F37u : bv_unsigned (ew Ex 37) = p) by (rewrite H37; apply unsigned_lit_small; lia) end.
xregbyte Vp HS 0%nat p vb F37u ltac:(cbn [sv_denot]; rewrite F38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
rewrite Z.add_0_r in Vp. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp.
rewrite (aview_of_val_mem1 _ _ _ _ Vp), (aview_of_val_mem1 _ _ _ _ Vvb), XVbb0.
unfold trfa. rewrite !Z.mod_small by lia. rewrite XDv. reflexivity.
+ assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hq4096 Hqceil Hrnp C1; lia).
cbn [ms_mem]. rewrite (XK5 a Ra Hne), (XK4 a Ra Hne).
pose proof Kc0 as (_ & KC2 & _). replace a with (pt + (a - pt)) at 1 by (clear; lia).
rewrite (KC2 pt npt (a - pt) Hpt ltac:(clear - Ha Hrnp; lia) ltac:(tauto)). replace (pt + (a - pt)) with a by (clear; lia).
rewrite (XK3 a Ra Hne), (XK2 a Ra Hne). exact (XK1 a Ra Hne).
-
reshok_bx HS 29%nat. pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x290c.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 37 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 37 p cc H37) by lia | rewrite (U_atom Ex 37 p H37) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len pt npt HAR4 Hpt); [rewrite (U_atom Ex 29 SB G29); [reflexivity | unfold SB; lia] | lia | lia] end).
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 37%nat); [reflexivity | rewrite H37; apply unsigned_lit_small; lia
| intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | clear - Ha Hp1 Hp2 Hcnt; lia] |].
apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) sp1 (fun a => pt <= a < pt + npt) HAR4 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; left; lia | lia])
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 npt ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K4 as (_ & _ & _ & _ & _ & K6); exact K6)) as K5.
pose proof (akept_not_p _ _ W _ _ p HFr5 ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
[rewrite H37, unsigned_lit_small in Hw by lia; lia | lia])) as XK5.
lazymatch type of Hc1 with context [sv_denot (havoc ?E1 512 ?ws) (SOff 516 0)] =>
assert (E516 : ew (havoc E1 512 ws) 516 = getr regs2 10) by (exact (ew_havoc_new E1 512 ws 4 (Z_to_bv 64 0) ltac:(rewrite length_map; unfold CLOB; cbn [length]; lia))) end.
assert (XDv : DEC vb vbb = false).
{ apply (proj1 XVD). rewrite branch_ne_U in Hc1. rewrite Hv in E516.
lazymatch type of E516 with ew ?Ex 516 = _ => assert (E516' : ew Ex 516 = Z_to_bv 64 (bv_unsigned v)) by (rewrite E516; symmetry; apply Z_to_bv_bv_unsigned) end.
pose proof (bv_unsigned_in_range 64 v) as Rv. change (bv_modulus 64) with (2 ^ 64) in Rv.
rewrite (U_atom _ 516 (bv_unsigned v) E516' Rv), U_lit in Hc1 by (clear; lia).
apply negb_false_iff, Z.eqb_eq in Hc1. unfold w64. rewrite <- Hc1. symmetry. apply Z_to_bv_bv_unsigned. }
eapply (TAIL _ _ _ _ HS); [reflexivity | reflexivity | env_agree32 HAE | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact HJ2 | exact (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1234 K5) | ].
intros a Ha. destruct (Z.eqb_spec a p) as [-> | Hne].
+ lazymatch type of H37 with ew ?Ex 37 = _ => assert (F37u : bv_unsigned (ew Ex 37) = p) by (rewrite H37; apply unsigned_lit_small; lia) end.
lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ss (restrict ?H ?msx) =>
assert (F32 : ew Ex 32 = Z_to_bv 64 tidx) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32);
assert (F37u' : bv_unsigned (ew Ex 37) = p) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact F37u | rewrite E37; apply unsigned_lit_small; lia]);
pose proof (field_of_region_any Ex _ 37%nat p _ 0 1 0 1 0 1%N (SOff 32 0) (st_ok_pi_region_nthX Ex ss (restrict H msx) 0%nat _ HS eq_refl) F37u' ltac:(left; reflexivity) ltac:(lia)) as Vp end.
cbn [sv_denot ms_mem restrict] in Vp.
rewrite F32, !Z.add_0_r, Z_to_bv_bv_unsigned, (unsigned_lit_small tidx Rtidx) in Vp. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp. change (2 ^ (8 * Z.of_N 1)) with 256 in Vp.
rewrite (aview_of_val_mem1 _ _ _ _ Vp), (aview_of_val_mem1 _ _ _ _ Vvb), XVbb0.
unfold trfa. rewrite !(Z.mod_small vb), !(Z.mod_small vbb) by lia. rewrite XDv. rewrite Z.mod_mod by lia. reflexivity.
+ assert (Ra : 0 <= a < 2 ^ 64) by (clear - Ha Hq4096 Hqceil Hrnp C1; lia).
cbn [ms_mem]. rewrite (XK5 a Ra Hne), (XK4 a Ra Hne).
pose proof Kc0 as (_ & KC2 & _). replace a with (pt + (a - pt)) at 1 by (clear; lia).
rewrite (KC2 pt npt (a - pt) Hpt ltac:(clear - Ha Hrnp; lia) ltac:(tauto)). replace (pt + (a - pt)) with a by (clear; lia).
rewrite (XK3 a Ra Hne), (XK2 a Ra Hne). exact (XK1 a Ra Hne).
Qed.
Lemma fl_tinX : forall m, tin_stmtX m.
Proof.
induction m as [|m IH]; [|exact (fl_tin_stepX m IH)].
unfold tin_stmtX. intros. exfalso. lia.
Qed.
End f.
End e.
End d.
