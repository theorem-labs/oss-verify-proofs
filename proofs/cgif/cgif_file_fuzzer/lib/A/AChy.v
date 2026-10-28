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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a ACjr ACj1 ACjc.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACiz.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
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
Lemma aview_kept_ro : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, ~ in_wrange E rs a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hno a. rewrite (aview_wrap H m' a), (aview_wrap H m a).
apply (aview_kept_frame E rs H m m' 0 HF ltac:(lia)); [intros x Hx; apply Hno | apply Z.mod_pos_bound; lia].
Qed.
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac ro_no :=
let a := fresh "a" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hw := fresh "Hw" in
intros a (rg & Hin & Hw); lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rg l') in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hin.
Lemma fl_cpyX : forall (m : nat) (r : Z) W (regs : bvmap 5 word) memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos
(pt fimg N w h top left Wd Hd : Z),
h - r <= Z.of_nat m -> 0 <= r < h ->
1 <= w -> 0 <= left -> left + w <= Wd -> 1 <= h -> 0 <= top -> top + h <= Hd -> 1 <= Wd <= 65535 -> Hd <= 65535 -> Wd * Hd = N -> N <= 100000000 ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memc mdc k ->
In (pt, w * h) (ablocks B lyc Sc) -> In (fimg, N) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pt, w * h) blc -> pt <= a < pt + w * h ->
awr_byte TFLUSH_STK sp0 FP (ablocks B ly S) blc lyq ownq a) ->
(pt + req_size (w * h) <= fimg \/ fimg + req_size N <= pt) ->
spZ regs = sp1 -> sp0 - 400 <= sp1 <= sp0 - 384 -> sp1 mod 16 = 0 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 20 = Z_to_bv 64 (h - r) -> getr regs 18 = Z_to_bv 64 4294967295 -> getr regs 21 = Z_to_bv 64 (fimg + left) ->
getr regs 22 = Z_to_bv 64 ((top + r) * Wd) -> getr regs 23 = Z_to_bv 64 w -> getr regs 24 = Z_to_bv 64 Wd ->
getr regs 27 = Z_to_bv 64 (pt + r * w) -> getr regs 19 = Z_to_bv 64 w ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x2038)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x205c)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
(forall q : bv 5, reg_in q CPY_CLOB = false -> getr regs' q = getr regs q) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pt <= a < pt + w * h) -> ~ (sp1 - ESTACK <= a < sp1) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pt + r * w <= a < pt + h * w) -> ~ (sp1 - ESTACK <= a < sp1) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall j kk, r <= j < h -> 0 <= kk < w ->
aview SEGS (w_H W) mem' (pt + j * w + kk) = aview SEGS (w_H W) memc (fimg + left + (top + j) * Wd + kk))).
Proof.
induction m as [|m IH]; intros r W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt fimg N w h top left Wd Hd
Hm Hr Hw1 Hl0 Hlw Hh1 Ht0 Hth HWd HHd HN HNle HJ Hpt Himg Hpawr Hsep Hsp Hsp1 Hsp1al Hgp Htp H20 H18 H21 H22 H23 H24 H27 H19; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TFLUSH_STK = 17440) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hw65 : w <= 65535) by (clear - Hlw HWd Hl0; lia). assert (Hh65 : h <= 65535) by (clear - Hth Ht0 HHd; lia).
assert (Hwh1 : 1 <= w * h) by (clear - Hw1 Hh1; nia).
assert (HN1 : 1 <= N) by (clear - HN HWd Hth Hh1 Ht0; nia).
assert (Hrq : req_size (w * h) = w * h) by (unfold req_size; destruct (Z.eqb_spec (w * h) 0); [lia | reflexivity]).
assert (HrqN : req_size N = N) by (unfold req_size; destruct (Z.eqb_spec N 0); [lia | reflexivity]).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pt (w * h) HAR Hpt) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph. rewrite Hrq in Hpceil, Hppres.
pose proof (blk_off_imgP _ _ _ _ _ _ _ _ HAR Hpt) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc fimg N HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih. rewrite HrqN in Hiceil, Hipres.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg N HAR Himg) as Hih_img.
rewrite Hrq, HrqN in Hsep.
assert (Hrw : 0 <= r * w /\ r * w + w <= w * h) by (clear - Hr Hw1; nia).
assert (Hrow : 0 <= (top + r) * Wd /\ (top + r) * Wd + left + w <= N) by (clear - Hr Ht0 Hth HWd Hl0 Hlw HN; nia).
assert (Hrow32 : (top + r) * Wd < 2 ^ 32) by (clear - Hrow HNle Hl0 Hw1; lia).
assert (HwhM : w * h < 2 ^ 32) by (clear - Hw65 Hh65 Hw1 Hh1; nia).
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs q) by (intros n q Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20. pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite H22 in E22. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite H24 in E24. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite H19 in E19.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_cpy 0x2038) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x2038)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_cpy. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x2038) _ regs _ _ (mrestrict (w_H W) memc)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite H18; cbn [sv_denot]; reflexivity].
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; exact I]. cbn [cpy_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E21, E27, E22, E23, E24, E20, E19, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; lia. }
clear HE. pose proof HS as HS0.
paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (fimg + left + (top + r) * Wd))
(denot_add_and32 Ev 21 22 (fimg + left) ((top + r) * Wd) E21 E22 ltac:(lia) ltac:(lia) ltac:(lia)) Ra1 end.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc].
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ fimg N HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _). rewrite HrqN in Hipres1.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msX) TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k
(pt + r * w) (fimg + left + (top + r) * Wd) w (sp1 - sp0) _ HJ) end.
- rewrite Ra0, E27. reflexivity.
- exact Ra1.
- rewrite Ra2, E23. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp, Usp. lia.
- rewrite Zminus_mod, Hsp1al, Hal16. reflexivity.
- lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity].
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpt | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ pt (w * h) _ _ HAR1 Hpt); rewrite ?Hrq; lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp, Usp; intro; lia].
apply (aview_some_of_apresent SEGS). apply (proj1 (Hipres1 a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ fimg N _ _ HAR1 Himg); rewrite ?HrqN; lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
jafter_call_keep_hi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ 32 _) as Eb eqn:HEb in HS. assert (HEIEb : img_env VAL A_LIM Eb) by (rewrite HEb; lazymatch goal with |- img_env _ _ (havoc ?Eo _ _) => let Hq := rnHEI Eo in first [apply img_env_havoc_hi; [exact Hq | cbv; lia] | apply (img_env_havoc Eo); [exact Hq | cbv; lia]] end).
assert (OLD : forall n, (n < 32)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs []) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEb.
pose proof (OLD 20%nat ltac:(lia)) as F20. rewrite E20 in F20. pose proof (OLD 22%nat ltac:(lia)) as F22. rewrite E22 in F22.
pose proof (OLD 23%nat ltac:(lia)) as F23. rewrite E23 in F23. pose proof (OLD 24%nat ltac:(lia)) as F24. rewrite E24 in F24.
pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27. pose proof (OLD 19%nat ltac:(lia)) as F19. rewrite E19 in F19.
paj_run_shc RUNP RUNC HS HJ2; [apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
psrr_branch_pi RUNP BR HS.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ =>
rewrite branch_ne_U in Hb; rewrite (U_atom_off Eb 20 (h - r) (-1) F20) in Hb by lia; rewrite U_SLit in Hb; change (zcanon 0) with 0 in Hb;
apply (proj1 (negb_true_iff _)) in Hb; apply Z.eqb_neq in Hb; rename Hb into Hc end.
paj_run_to_shc RUNTOP HS HJ2 0x2038; [apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ CPY_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (22%bv : bv 5) (Z_to_bv 64 ((top + r) * Wd + Wd)) (denot_add_atoms Eb 22 24 ((top + r) * Wd) Wd F22 F24 ltac:(lia) ltac:(lia) ltac:(lia)) N22.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (w + (pt + r * w))) (denot_add_atoms Eb 19 27 w (pt + r * w) F19 F27 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (20%bv : bv 5) N20. rewrite F20 in N20. prreg HS (18%bv : bv 5) N18.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hrw1 : (r + 1) * w = r * w + w) by (clear; lia).
assert (Hrh : (r + 1) * w <= h * w) by (clear - Hr Hc Hw1; nia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ _ ?m5 _) _) _ =>
assert (XP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (pt + r * w <= a < pt + r * w + w) -> ~ (sp1 - ESTACK <= a < sp1) -> aview SEGS (w_H W) m5 a = aview SEGS (w_H W) memc a)
by (intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) a), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) a);
rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)); cbn [ms_mem]; exact (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) a));
assert (XE5 : forall kk, 0 <= kk < w -> aview SEGS (w_H W) m5 (pt + r * w + kk) = aview SEGS (w_H W) memc (fimg + left + (top + r) * Wd + kk))
by (intros kk Hkk; cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) _), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) _);
rewrite (Heff kk ltac:(clear - Hkk; lia)); cbn [ms_mem]; rewrite (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) _); first [reflexivity | f_equal; clear; lia])
end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (r + 1) W (ms_regs msX) (ms_mem msX) _ sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos pt fimg N w h top left Wd Hd);
[ lia | lia | exact Hw1 | exact Hl0 | exact Hlw | exact Hh1 | exact Ht0 | exact Hth | exact HWd | exact HHd | exact HN | exact HNle
| exact HJ2 | exact Hpt | exact Himg | exact Hpawr | rewrite Hrq, HrqN; exact Hsep
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact Hsp1 | exact Hsp1al
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite N20; cbn [sv_denot]; rewrite unsigned_lit_small by lia; f_equal; lia
| rewrite N18; reflexivity
| rewrite (HK 21%bv ltac:(cbv; tauto)); exact H21
| rewrite N22; f_equal; lia
| rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23 | rewrite (HK 24%bv ltac:(cbv; tauto)); exact H24
| rewrite N27; f_equal; lia
| rewrite (HK 19%bv ltac:(cbv; tauto)); exact H19 ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & Hout3 & Hpres3 & XO3 & XC3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [intros q Hq; rewrite (HK3 q Hq); destruct (cpy_clob_cases q Hq) as [-> | [-> | Hq']];
[ cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N18, H18; reflexivity
| exact (HK q Hq')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). cbn [ms_mem].
rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) a), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) a). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) a).
+ split; [intros a Ha; apply Hpres3; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
split.
* intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna Hrw1 Hw1; lia) Hnb).
exact (XP5 a Ha ltac:(clear - Hna Hrw Hrh Hrw1; lia) Hnb).
* intros j kk Hj Hkk.
assert (Hsrc : 0 <= (top + j) * Wd /\ (top + j) * Wd + left + w <= N) by (clear - Hj Hr Ht0 Hth HWd Hl0 Hlw HN; nia).
assert (Hdst : 0 <= j * w /\ j * w + w <= w * h) by (clear - Hj Hr Hw1; nia).
destruct (Z.eq_dec j r) as [-> | Hjr].
{ assert (Hav : 0 <= pt + r * w + kk < 2 ^ 64) by (clear - Hkk Hrw Hp4096 Hpceil C1; lia).
rewrite (XO3 _ Hav ltac:(clear - Hkk Hrw1; lia) ltac:(clear - Hkk Hrw Hpceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia)).
exact (XE5 kk Hkk). }
{ pose proof (XC3 j kk ltac:(clear - Hj Hjr; lia) Hkk) as Q. rewrite Q.
assert (Hiv : 0 <= fimg + left + (top + j) * Wd + kk < 2 ^ 64) by (clear - Hkk Hsrc Hl0 Hi4096 Hiceil C1; lia).
exact (XP5 _ Hiv ltac:(clear - Hkk Hsrc Hl0 Hrw Hsep; lia) ltac:(clear - Hkk Hsrc Hl0 Hiceil Hceil Hslo Hstk0 Hsp1 FFS C1; unfold ESTACK; lia)). }
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ =>
rewrite branch_ne_U in Hb; rewrite (U_atom_off Eb 20 (h - r) (-1) F20) in Hb by lia; rewrite U_SLit in Hb; change (zcanon 0) with 0 in Hb;
apply (proj1 (negb_false_iff _)) in Hb; apply Z.eqb_eq in Hb; rename Hb into Hc end.
paj_run_to_shc RUNTOP HS HJ2 0x205c; [apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ CPY_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (18%bv : bv 5) N18.
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ2|].
split; [intros q Hq; destruct (cpy_clob_cases q Hq) as [-> | [-> | Hq']];
[ cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N18, H18; reflexivity
| exact (HK q Hq')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) a), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) a). rewrite (Hout2 a Ha ltac:(lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) a).
+ split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
assert (Hrh : h * w = r * w + w) by (assert (Eh : h = r + 1) by (clear - Hc Hr; lia); rewrite Eh; clear; lia).
split.
* intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) a), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) a).
rewrite (Hout2 a Ha ltac:(clear - Hna Hrh; lia) ltac:(lia)).
cbn [ms_mem]. exact (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) a).
* intros j kk Hj Hkk. assert (j = r) as -> by (clear - Hj Hc; lia). cbn [ms_mem].
rewrite (aview_kept_ro _ _ _ _ _ HFr3 ltac:(ro_no) _), (aview_kept_ro _ _ _ _ _ HFr2 ltac:(ro_no) _).
rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem]. rewrite (aview_kept_ro _ _ _ _ _ HFr1 ltac:(ro_no) _).
first [reflexivity | f_equal; clear; lia].
Qed.
End d.
End c.
End b.
