(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88 YC89.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCi8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACik.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac tin_ctx_names H :=
destruct H as (HJ & Hpt & Hpawr & Hbi & HNb & HsepI & Hg & Hcf & Hbf & Hcb & HsepG & HsepC & HsepB
& Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx & Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp
& Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vtidx & Rtidx & Vsb & Vbfp & H26 & H27 & H21 & H22).
Ltac tin_prelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Ltac tctx_regs_of HK := let r := fresh "r" in let Hr := fresh "Hr" in
intros r Hr; apply HK; cbv [TCTX_REGS In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr.
Definition tout_XD (W : world SEGS) (memc : word -> option byte) (lyc : alayout) (Sc : astate) (sp1 pt npt : Z) (DEC : Z -> Z -> bool)
(gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) : Prop :=
forall mN, acall_kept SEGS B lyc Sc W memc W mN (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + npt) ->
forall x y, 0 <= x < 256 -> 0 <= y < 256 ->
(tcmp_zero (aview SEGS (w_H W) mN) gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx x y <-> DEC x y = false).
Lemma tout_XD_kept : forall W memc memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx,
tout_XD W memc lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
acall_kept SEGS B lyc Sc W memc W memN (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + npt) ->
tout_XD W memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W memc memN lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx XD K mN KN.
exact (XD mN (acall_kept_trans B _ _ _ _ _ _ _ _ _ K KN)).
Qed.
Lemma tin_XD_of_tout : forall W memc ms lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx,
tout_XD W memc lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
acall_kept SEGS B lyc Sc W memc W ms (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + npt) ->
alloc_ceiling <= sp1 -> sp1 + 232 <= 2 ^ 64 ->
tin_XD B W ms lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Proof.
intros W memc ms lyc Sc sp1 pt npt DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx XD K Hc1 Hc2 mN KN.
apply XD. eapply (acall_kept_trans B); [exact K|].
apply (acall_kept_band B _ _ _ _ _ _ _ (sp1 - TCMP_STK) (sp1 + 232) _ KN); [lia | lia |].
intros a Ha. destruct KN as (_ & _ & _ & _ & KN5 & KN6). destruct K as (_ & _ & _ & _ & _ & K6).
destruct (Z_lt_le_dec a sp1) as [Hlo | Hhi]; [apply KN6; lia|].
apply KN5; [lia | lia | apply K6; lia].
Qed.
Definition tout_postX (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model)
(lyc : alayout) (Sc : astate) (k : Z) (fpos pt npt : Z) (DEC : Z -> Z -> bool) (tidx w h top left Wd bimg y : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x22cc)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
(forall r : bv 5, reg_in r TOUT_CLOB = false -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\
acall_kept SEGS B lyc Sc W memc W mem' (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + npt) /\
(forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
toutV DEC tidx w h top left Wd (aview SEGS (w_H W) memc) (aview SEGS (w_H W) mem') pt bimg y.
Definition tout_stmtX (m : nat) : Prop :=
forall (y : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
(pt w h top left Wd bimg Nb g cfp bfp tidx : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z) (DEC : Z -> Z -> bool),
h - y <= Z.of_nat m -> 0 <= y < h ->
tin_ctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
tout_ctx W memc sp1 w h top left Wd Nb ->
tout_XD W memc lyc Sc sp1 pt (w * h) DEC gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx ->
getr regs 6 = Z_to_bv 64 SB -> getr regs 14 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 ((top + y) * Wd + left) ->
getr regs 19 = Z_to_bv 64 (pt + y * w) -> getr regs 18 = Z_to_bv 64 (pt + y * w) -> getr regs 20 = Z_to_bv 64 w ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x21f4)) memc (seg_rom SEGS)) mdc)
(tout_postX W regs memc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt (w * h) DEC tidx w h top left Wd bimg y).
Lemma fl_tout_stepX : forall m, tout_stmtX m -> tout_stmtX (S m).
Proof.
intros m IH. unfold tout_stmtX.
intros y W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1
pt w h top left Wd bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC
Hm Hy HCTX HOUT XD H6 H15 H18 H19 H24 H20.
pose proof HCTX as HCTX0. tin_ctx_names HCTX. pose proof HOUT as HOUT0.
destruct HOUT as (Rw & Rh & Htop0 & Hleft0 & Hlw & HWd & HthW & V176 & V184 & V192 & V200).
tin_prelude HJ. pose proof HJ as HJ0.
assert (HSpres2 : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memc a) by (intros a Ha; apply HSpres; lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt (w * h) HAR Hpt) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _ & Hnpt & _). pose proof (proj1 Hqh_ia) as Hqh.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hpt) as Hqh_img.
pose proof (req_size_pos' (w * h) ltac:(lia)) as [_ Hrnp].
pose proof (proj1 (proj2 HJ)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HywL : 0 <= y * w) by (apply Z.mul_nonneg_nonneg; lia).
assert (HywH : y * w + w <= w * h) by (rewrite (Z.mul_comm w h); rewrite <- Z.mul_succ_l; apply Z.mul_le_mono_nonneg_r; lia).
assert (HriL : 0 <= (top + y) * Wd + left) by (assert (0 <= (top + y) * Wd) by (apply Z.mul_nonneg_nonneg; lia); lia).
assert (HriH : (top + y) * Wd + left + w <= Nb).
{ apply (Z.le_trans _ ((top + y + 1) * Wd)); [rewrite Z.mul_add_distr_r; lia|]. apply (Z.le_trans _ ((top + h) * Wd)); [apply Z.mul_le_mono_nonneg_r; lia | exact HthW]. }
assert (Hw48 : 281474976710656 <= w * 2 ^ 48 <= 18446744073709551615) by (change (2 ^ 48) with 281474976710656; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 (w * 2 ^ 48); Z_to_bv 64 h; Z_to_bv 64 Wd; Z_to_bv 64 tidx; Z_to_bv 64 bfp])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (w * 2 ^ 48); Z_to_bv 64 h; Z_to_bv 64 Wd; Z_to_bv 64 tidx; Z_to_bv 64 bfp]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9. pose proof (EE 6%nat 6%bv eq_refl) as E6. rewrite H6 in E6.
pose proof (EE 14%nat 14%bv eq_refl) as E15. rewrite H15 in E15. pose proof (EE 24%nat 24%bv eq_refl) as E18. rewrite H18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite H19 in E19. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20.
assert (E32 : ew E 32 = Z_to_bv 64 (w * 2 ^ 48)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 tidx) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bfp FRAME_SIZE HAR Hbf) as (Hb16 & Hb4096 & Hbceil & Hbfh_ia & _ & _). pose proof (proj1 Hbfh_ia) as Hbfh. change (req_size FRAME_SIZE) with 40 in Hbceil.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hbfh_img.
assert (HS : st_ok_pi SEGS VAL E ss_tout (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x21f4)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_tout, tout_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x21f4) _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite H24; cbn [sv_denot]; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs [Z_to_bv 64 (w * 2 ^ 48); Z_to_bv 64 h; Z_to_bv 64 Wd; Z_to_bv 64 tidx; Z_to_bv 64 bfp] 19 19%bv eq_refl), H19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] | intros X; discriminate X |].
rewrite H27. cbn [sv_denot]. reflexivity.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tout_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HSpres; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ (w * 2 ^ 48)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 184 8 _ h); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ w); [cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V192]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 232 8 _ tidx); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact Vsb]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vbfp]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [tout_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E6, E32, E20, E19, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memc).
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK FLBspan 0x220c.
1: { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite E9; apply unsigned_lit_small; lia
| intros a Ha; unfold tout_loc in Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; rewrite FFS; lia | apply awr_ok_nil]. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (acall_kept_of_run B LAWS E _ lyc Sc W memc _ mdc (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + w * h) HAR HFr1 HG1
ltac:(unfold ss_tout, tout_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
rewrite E9, unsigned_lit_small in Hw by lia; right; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpres2) as K1.
assert (W1 : forall x, in_wrange E (ss_mem ss_tout) x -> sp1 + 208 <= x < sp1 + 232).
{ unfold ss_tout, tout_loc; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw.
rewrite E9, unsigned_lit_small in Hw by lia. lia. }
assert (X1 : forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply (aview_kept_out E _ _ _ _ HFr1 a ltac:(lia)). intros Hin. pose proof (W1 a Hin). lia. }
assert (XR1 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply (aview_kept_out E _ _ _ _ HFr1 a ltac:(lia)). intros Hin. pose proof (W1 a Hin). lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
pose proof (st_ok_pi_region_nth Ex ssx msx 0 ltac:(let rr := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in exact rr) HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 208 8%N (SOff 19 0) (pt + y * w) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V208;
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 216 8%N (SOff 24 0) ((top + y) * Wd + left) HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E18, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V216;
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 224 8%N (SOff 14 0) y HR9
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V224 end;
clear HR9 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V208, V216, V224.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 176) (w * 2 ^ 48) _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V176) as V176a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 184) h _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V184) as V184a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 192) w _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V192) as V192a.
pose proof (val_mem_frame8 E _ _ _ (sp1 + 200) Wd _ _ HFr1 W1 ltac:(lia) ltac:(lia) ltac:(lia) V200) as V200a.
cbn [ms_mem restrict mkst] in V176a, V184a, V192a, V200a.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (19%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
assert (HK1 : forall r : bv 5, In r TCTX_REGS -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbv [TCTX_REGS In] in Hr.
repeat (destruct Hr as [<- | Hr]; [first [apply HKr1; cbv; tauto | rewrite (st_ok_restrict_reg SEGS _ _ _ _ 27%bv HS); cbn [sv_denot]; rewrite H27; reflexivity] |]). destruct Hr. }
prreg HS (6%bv : bv 5) R6. prreg HS (23%bv : bv 5) R23. prreg HS (18%bv : bv 5) R24. prreg HS (20%bv : bv 5) R20. prreg HS (24%bv : bv 5) R18.
pose proof (tin_ctx_kept B LAWS W regs _ memc mdc _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJ K1 ltac:(lia) HK1) as HCTX1.
pmkst HS.
eapply SRr_bind.
{ pose proof (fl_tinX B LAWS TCMP (Z.to_nat w)) as TIN. unfold tin_stmtX in TIN.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (TIN w W (ms_regs msX) (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) (pt + y * w) bimg Nb ((top + y) * Wd + left) g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC) end;
[ rewrite Z2Nat.id by lia; lia | lia | exact HCTX1 | apply (tin_XD_of_tout _ memc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XD K1); lia | lia | lia | lia | lia
| rewrite R6, ?ew_ewset_other by lia; exact E6
| rewrite R23, ?ew_ewset_other by lia; exact E19
| rewrite R24, ?ew_ewset_other by lia; exact E19
| rewrite R20, ?ew_ewset_other by lia; exact E20
| rewrite R18, ?ew_ewset_other by lia; exact E18 ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & -> & HJI & HKI & H6I & KI & XVI).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bimg Nb HAR Hbi) as (_ & Hi4096 & Hiceil & _).
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
pose proof (tinV_pre DEC tidx (aview SEGS (w_H W) memc) _ _ pt (w * h) (pt + y * w) w bimg ((top + y) * Wd + left)
ltac:(intros a Ha; apply XR1; lia) ltac:(intros j Hj; apply XR1; lia) XVI) as XVIc.
clear R6 R23 R24 R20 R18.
pose proof HJI as HJI0.
assert (HSpresI : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memI a).
{ intros a Ha. pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K1 (acall_kept_band B _ _ _ _ _ _ _ (sp1 - TCMP_STK) (sp1 + 232) _ KI ltac:(lia) ltac:(lia) HSpresI)) as K2.
assert (X2 : forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) memI a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X1 a Ha). pose proof KI as (KI1 & _). apply KI1; lia. }
assert (HKI' : forall r : bv 5, reg_in r TOUT_CLOB = false -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r (tout_tin_clob r Hr)). destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']].
- rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS0). reflexivity.
- rewrite (st_ok_restrict_reg SEGS _ _ _ _ 27%bv HS). cbn [sv_denot]. rewrite H27. reflexivity.
- apply HKr1. cbv [TOUT_KEPT In] in Hr' |- *. tauto. }
assert (I19 : getr regsI 19 = Z_to_bv 64 (pt + y * w)) by (rewrite (HKI 19%bv eq_refl); rewrite (HKr1 19%bv ltac:(cbv; tauto)); exact H19).
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl); rewrite (HKr1 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 176) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V176a) as V176b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 184) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V184a) as V184b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 192) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V192a) as V192b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 200) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V200a) as V200b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 208) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V208) as V208b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 216) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V216) as V216b.
pose proof (val_mem_keptK B _ _ _ _ _ _ _ _ (sp1 + 224) 8 _ KI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(left; lia) V224) as V224b.
clear V176a V184a V192a V200a V208 V216 V224.
remember (Eimg (Ereg regsI [Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 Wd; Z_to_bv 64 ((top + y) * Wd + left); Z_to_bv 64 y])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 h; Z_to_bv 64 w; Z_to_bv 64 Wd; Z_to_bv 64 ((top + y) * Wd + left); Z_to_bv 64 y]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9. pose proof (EEt 19%nat 19%bv eq_refl) as T19. rewrite I19 in T19.
pose proof (EEt 6%nat 6%bv eq_refl) as T6. rewrite H6I in T6.
assert (T32 : ew Et 32 = Z_to_bv 64 h) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 w) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 ((top + y) * Wd + left)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (T36 : ew Et 36 = Z_to_bv 64 y) by (subst Et; exact (ew_Ereg_extra regsI _ 4)).
assert (HSt : st_ok_pi SEGS VAL Et ss_totl (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x22a0)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_totl. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x22a0) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, totl_loc; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite T9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 184 8 _ h); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 192 8 _ w); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V192b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 208 8 _ (pt + y * w)); [cbn [sv_denot]; rewrite T19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 216 8 _ ((top + y) * Wd + left)); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 224 8 _ y); [cbn [sv_denot]; rewrite T36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V224b]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [totl_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite T9, T19, T32, T33, T34, T35, T36, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HEt. pose proof HSt as HSt0. clear HS HS0. rename HSt into HS. try clear SHOK.
shok_auto SHOK (SOff 6 0) Et (mrestrict (w_H W) memI).
pose proof (proj1 HJI) as HARI.
hei_havoc HS; paj_run_tok RUN HS HJI SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + w * h) HARI HFr3 HG3
ltac:(unfold ss_totl, totl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) HSpresI) as K3.
assert (XK3 : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memI a).
{ intros a Ha. apply (aview_kept_out Et _ _ _ _ HFr3 a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
assert (X3 : forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X2 a Ha). apply (aview_kept_out Et _ _ _ _ HFr3 a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 36 y 1) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T36 | lia]).
rewrite (U_atom _ 32 h) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32 | lia]).
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x21f4.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + w * h) HARb HFrb HGb
ltac:(unfold ss_totl, totl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as Kb.
pose proof (acall_kept_trans B _ _ _ _ _ _ _ _ _ K2 (acall_kept_trans B _ _ _ _ _ _ _ _ _ K3 Kb)) as K4.
assert (XKb : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
assert (X4 : forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X3 a Ha). apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (27%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr4. cbn [ms_regs restrict] in HKr4.
assert (HK4 : forall r : bv 5, reg_in r TOUT_CLOB = false -> getr (ms_regs ms1) r = getr regs r).
{ intros r Hr. transitivity (getr regsI r); [|exact (HKI' r Hr)].
destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']]; [rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HSt0); reflexivity | apply HKr4; cbv; tauto | apply HKr4; cbv [TOUT_KEPT In] in Hr' |- *; tauto]. }
assert (Wt : forall x, in_wrange Et (ss_mem ss_totl) x -> sp1 + 208 <= x < sp1 + 232).
{ unfold ss_totl, totl_loc; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. lia. }
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 176) (w * 2 ^ 48) _ _ HFrb Wt ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 176) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V176b)) as V176c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 184) h _ _ HFrb Wt ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 184) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V184b)) as V184c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 192) w _ _ HFrb Wt ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 192) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V192b)) as V192c.
pose proof (val_mem_frame8 _ _ _ _ (sp1 + 200) Wd _ _ HFrb Wt ltac:(lia) ltac:(lia) ltac:(lia) (val_mem_frame8 _ _ _ _ (sp1 + 200) _ _ _ HFr3 Wt ltac:(lia) ltac:(lia) ltac:(lia) V200b)) as V200c.
cbn [ms_mem restrict mkst] in V176c, V184c, V192c, V200c.
prreg HS (6%bv : bv 5) R6. prreg HS (14%bv : bv 5) R15. prreg HS (20%bv : bv 5) R20.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F19 : ew Ev 19 = Z_to_bv 64 (pt + y * w)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T19);
assert (F33 : ew Ev 33 = Z_to_bv 64 w) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33);
assert (F34 : ew Ev 34 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T34);
assert (F35 : ew Ev 35 = Z_to_bv 64 ((top + y) * Wd + left)) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T35);
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (pt + y * w + w)) (denot_add_atoms Ev 19 33 (pt + y * w) w F19 F33 ltac:(lia) ltac:(lia) ltac:(lia)) R19;
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (pt + y * w + w)) (denot_add_atoms Ev 19 33 (pt + y * w) w F19 F33 ltac:(lia) ltac:(lia) ltac:(lia)) R24;
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (Wd + ((top + y) * Wd + left))) (denot_add_atoms Ev 34 35 Wd ((top + y) * Wd + left) F34 F35 ltac:(lia) ltac:(lia) ltac:(lia)) R18 end.
lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
pose proof (tin_ctx_kept B LAWS W regs (ms_regs msX) memc mdc (ms_mem msX) mdX sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt (w * h) bimg Nb g cfp bfp tidx
gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx _ _ HCTX0 HJI K4 ltac:(lia) ltac:(tctx_regs_of HK4)) as HCTX4 end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (y + 1) W _ _ _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 pt w h top left Wd bimg Nb g cfp bfp tidx gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx DEC);
[ lia | lia | exact HCTX4
| split; [exact Rw|]; split; [exact Rh|]; split; [exact Htop0|]; split; [exact Hleft0|]; split; [exact Hlw|]; split; [exact HWd|]; split; [exact HthW|];
split; [exact V176c|]; split; [exact V184c|]; split; [exact V192c | exact V200c]
| eapply tout_XD_kept; [exact XD | exact K4]
| rewrite R6, ?ew_ewset_other by lia; exact T6
| rewrite R15, ?ew_ewset_other by lia; rewrite T36; cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; reflexivity
| rewrite R18; f_equal; lia
| rewrite R19; f_equal; lia
| rewrite R24; f_equal; lia
| rewrite R20, ?ew_ewset_other by lia; exact T33 ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & H63 & K5 & X5 & XV5).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros r Hr; rewrite (HK3 r Hr); exact (HK4 r Hr)|]. split; [exact H63|].
split; [eapply (acall_kept_trans B); [exact K4 | exact K5]|].
split; [intros a Ha; rewrite (X5 a Ha); exact (X4 a Ha)|].
lazymatch type of XV5 with toutV _ _ _ _ _ _ _ (aview _ _ ?m3) _ _ _ _ =>
apply (toutV_step DEC tidx w h top left Wd ltac:(lia) _ (aview SEGS (w_H W) memI) (aview SEGS (w_H W) m3) _ pt bimg y Nb);
[ lia | lia | exact Htop0 | exact Hleft0 | exact Hlw | exact HthW | exact XVIc
| intros a Ha; cbn [ms_mem]; rewrite (XKb a ltac:(lia)); exact (XK3 a ltac:(lia))
| intros j Hj; pose proof K4 as (_ & KB2 & _); apply (KB2 bimg Nb j Hbi); [lia | cbn beta; lia]
| exact XV5 ] end.
-
rewrite branch_ne_U in Hc.
rewrite (U_atom_off _ 36 y 1) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T36 | lia]).
rewrite (U_atom _ 32 h) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32 | lia]).
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x22cc.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (acall_kept_of_run B LAWS _ _ lyc Sc W _ _ _ (sp1 - TCMP_STK) (sp1 + 232) (fun a => pt <= a < pt + w * h) HARb HFrb HGb
ltac:(unfold ss_totl, totl_loc; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(intros a Ha; cbn beta in Ha; split; [lia | pose proof (req_size_pos0 (w * h) ltac:(lia)) as [_ Hrqa]; clear - Ha Hqh_img Hrqa; unfold off_img in *; lia]) ltac:(lia) ltac:(pose proof K3 as (_ & _ & _ & _ & _ & K6); exact K6)) as Kb.
assert (XKb : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }

assert (X4 : forall a, sp1 <= a < sp1 + 208 -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) memc a).
{ intros a Ha. rewrite <- (X3 a Ha). apply (aview_kept_out _ _ _ _ _ HFrb a ltac:(lia)).
unfold ss_totl, totl_loc; cbn [ss_mem]; intros (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (27%bv :: TOUT_KEPT) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr4. cbn [ms_regs restrict] in HKr4.
prreg HS (6%bv : bv 5) R6.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJI|].
split.
{ intros r Hr. transitivity (getr regsI r); [|exact (HKI' r Hr)].
destruct (tout_clob_cases3 r Hr) as [-> | [-> | Hr']]; [cbn [ms_regs]; rewrite (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HS), (st_ok_restrict_reg SEGS _ _ _ _ 0%bv HSt0); reflexivity | apply HKr4; cbv; tauto | apply HKr4; cbv [TOUT_KEPT In] in Hr' |- *; tauto]. }
split; [rewrite R6, ?ew_ewset_other by lia; exact T6|].
split; [eapply (acall_kept_trans B); [exact K2 | eapply (acall_kept_trans B); [exact K3 | exact Kb]]|].
split; [exact X4|].
apply (toutV_last DEC tidx w h top left Wd ltac:(lia) _ _ pt bimg y ltac:(lia) ltac:(lia)).
apply (tinV_post DEC tidx _ (aview SEGS (w_H W) memI) _ pt (w * h) (pt + y * w) w bimg ((top + y) * Wd + left)); [|exact XVIc].
intros a Ha. cbn [ms_mem]. rewrite (XKb a ltac:(lia)). exact (XK3 a ltac:(lia)).
Qed.
Lemma fl_toutX : forall m, tout_stmtX m.
Proof.
induction m as [|m IH]; [|exact (fl_tout_stepX m IH)].
unfold tout_stmtX. intros. exfalso. lia.
Qed.
End d.
End c.
End b.
