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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACai ACam ACan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACac.
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
Section d.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Ltac iln_obl HJx Hx25 Hx32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 25 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 25 (cfp + 8) c Hx25) by lia | rewrite (U_atom Ex 25 (cfp + 8) Hx25) by lia ];
eapply (obl_of_range SEGS _ _ Ex (SOff 32 0) _ len cfp 40);
[ eapply (range_addressable_entry_frame SEGS _ LAWS); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; destruct Hrg as [<- | []]; cbn [fst snd] in Hxr; clear - Hxr Hrh C2 C3; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; change (req_size RAW_SIZE) with 48 in *; lia
| exact HAR0 | exact HRA ]
| rewrite (U_atom Ex 32 SB Hx32); [reflexivity | unfold SB; lia] | lia | lia ] end.
Lemma ra_iln1X : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 8 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 8 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR SEGS B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xb64)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0xbd0)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 8 * (mm - 1) < h /\ h <= i + 8 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 11 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * R <= a < pint + w * (R + mm)) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall j kk, 0 <= j < mm -> 0 <= kk < w ->
aview SEGS (w_H W) mem' (pint + w * (R + j) + kk) = aview SEGS (w_H W) memc (img + w * (i + 8 * j) + kk))).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_iln 27 0xb64) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xb64)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_iln. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xb64) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
paj_run_tok RUN HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 333276) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent SEGS). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS. assert (HEIEb : img_env VAL A_LIM Eb) by (rewrite HEb; lazymatch goal with |- img_env _ _ (havoc ?Eo _ _) => let Hq := rnHEI Eo in apply img_env_havoc_hi; [exact Hq | cbv; lia] end).
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
paj_run_tok RUN HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ec eqn:HEc | st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc  end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xb64; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 8) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; rewrite (Hout3 a Ha Hna Hnb); exact (HoutX a Ha Hna Hnb)|].
split; [intros a Ha; apply Hpres3; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
assert (Hwmm : 0 <= w * mm) by (clear - Hw Hm1; nia).
split.
+
intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) Hnb). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+
intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (i + 8 * j) /\ w * (i + 8 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hi Hj; lia|].
replace (w * (i + 8 * j) + w) with (w * (i + 8 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hj Hm2 Hi; lia. }
assert (Hwj : 0 <= w * j /\ w * j + w <= w * mm + w).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|]. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - Hw Hj; lia. }
destruct (Z.eq_dec j 0) as [-> | Hj0].
* assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (XO3 _ Hav ltac:(clear - Hkk Hw; lia) ltac:(clear - Hkk HwR Hw Hpceil Hnp Hrnp Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 8 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
* pose proof (XC3 (j - 1) kk ltac:(clear - Hj Hj0; lia) Hkk) as Q.
replace (R + 1 + (j - 1)) with (R + j) in Q by (clear; lia). replace (i + 8 + 8 * (j - 1)) with (i + 8 * j) in Q by (clear; lia).
rewrite Q. cbn [ms_mem].
assert (Hiv : 0 <= img + w * (i + 8 * j) + kk < 2 ^ 64) by (clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hiv), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hiv).
rewrite (Hout2 _ Hiv ltac:(clear - Hkk Hrow HwR Hw Hsep Hnp Hrnp HNi HrNi; lia) ltac:(clear - Hkk Hrow Hiceil HNi HrNi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xbd0; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (11%bv : bv 5) NXH. rewrite G35 in NXH.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. assert (j = 0) as -> by (clear - Hj; lia). cbn [ms_mem].
assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 8 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
Qed.
Lemma ra_iln2X : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 8 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 8 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR SEGS B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xbdc)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0xc68)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 8 * (mm - 1) < h /\ h <= i + 8 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * R <= a < pint + w * (R + mm)) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall j kk, 0 <= j < mm -> 0 <= kk < w ->
aview SEGS (w_H W) mem' (pint + w * (R + j) + kk) = aview SEGS (w_H W) memc (img + w * (i + 8 * j) + kk))).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_iln 27 0xbdc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xbdc)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_iln. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xbdc) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
paj_run_tok RUN HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 333276) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent SEGS). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS. assert (HEIEb : img_env VAL A_LIM Eb) by (rewrite HEb; lazymatch goal with |- img_env _ _ (havoc ?Eo _ _) => let Hq := rnHEI Eo in apply img_env_havoc_hi; [exact Hq | cbv; lia] end).
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
paj_run_tok RUN HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ec eqn:HEc | st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc  end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xbdc; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 8) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; rewrite (Hout3 a Ha Hna Hnb); exact (HoutX a Ha Hna Hnb)|].
split; [intros a Ha; apply Hpres3; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
assert (Hwmm : 0 <= w * mm) by (clear - Hw Hm1; nia).
split.
+
intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) Hnb). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+
intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (i + 8 * j) /\ w * (i + 8 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hi Hj; lia|].
replace (w * (i + 8 * j) + w) with (w * (i + 8 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hj Hm2 Hi; lia. }
assert (Hwj : 0 <= w * j /\ w * j + w <= w * mm + w).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|]. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - Hw Hj; lia. }
destruct (Z.eq_dec j 0) as [-> | Hj0].
* assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (XO3 _ Hav ltac:(clear - Hkk Hw; lia) ltac:(clear - Hkk HwR Hw Hpceil Hnp Hrnp Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 8 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
* pose proof (XC3 (j - 1) kk ltac:(clear - Hj Hj0; lia) Hkk) as Q.
replace (R + 1 + (j - 1)) with (R + j) in Q by (clear; lia). replace (i + 8 + 8 * (j - 1)) with (i + 8 * j) in Q by (clear; lia).
rewrite Q. cbn [ms_mem].
assert (Hiv : 0 <= img + w * (i + 8 * j) + kk < 2 ^ 64) by (clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hiv), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hiv).
rewrite (Hout2 _ Hiv ltac:(clear - Hkk Hrow HwR Hw Hsep Hnp Hrnp HNi HrNi; lia) ltac:(clear - Hkk Hrow Hiceil HNi HrNi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 8))) with (U Ec (SOff 18 8)) in Hc.
rewrite (U_atom_off Ec 18 i 8 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xc68; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. assert (j = 0) as -> by (clear - Hj; lia). cbn [ms_mem].
assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 8 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
Qed.
Lemma ra_iln3X : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 4 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 4 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR SEGS B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xc74)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0xcec)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 4 * (mm - 1) < h /\ h <= i + 4 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * R <= a < pint + w * (R + mm)) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall j kk, 0 <= j < mm -> 0 <= kk < w ->
aview SEGS (w_H W) mem' (pint + w * (R + j) + kk) = aview SEGS (w_H W) memc (img + w * (i + 4 * j) + kk))).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_iln 27 0xc74) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xc74)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_iln. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xc74) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
paj_run_tok RUN HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 333276) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent SEGS). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS. assert (HEIEb : img_env VAL A_LIM Eb) by (rewrite HEb; lazymatch goal with |- img_env _ _ (havoc ?Eo _ _) => let Hq := rnHEI Eo in apply img_env_havoc_hi; [exact Hq | cbv; lia] end).
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
paj_run_tok RUN HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ec eqn:HEc | st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc  end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 4))) with (U Ec (SOff 18 4)) in Hc.
rewrite (U_atom_off Ec 18 i 4 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xc74; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 4) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; rewrite (Hout3 a Ha Hna Hnb); exact (HoutX a Ha Hna Hnb)|].
split; [intros a Ha; apply Hpres3; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
assert (Hwmm : 0 <= w * mm) by (clear - Hw Hm1; nia).
split.
+
intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) Hnb). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+
intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (i + 4 * j) /\ w * (i + 4 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hi Hj; lia|].
replace (w * (i + 4 * j) + w) with (w * (i + 4 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hj Hm2 Hi; lia. }
assert (Hwj : 0 <= w * j /\ w * j + w <= w * mm + w).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|]. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - Hw Hj; lia. }
destruct (Z.eq_dec j 0) as [-> | Hj0].
* assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (XO3 _ Hav ltac:(clear - Hkk Hw; lia) ltac:(clear - Hkk HwR Hw Hpceil Hnp Hrnp Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 4 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
* pose proof (XC3 (j - 1) kk ltac:(clear - Hj Hj0; lia) Hkk) as Q.
replace (R + 1 + (j - 1)) with (R + j) in Q by (clear; lia). replace (i + 4 + 4 * (j - 1)) with (i + 4 * j) in Q by (clear; lia).
rewrite Q. cbn [ms_mem].
assert (Hiv : 0 <= img + w * (i + 4 * j) + kk < 2 ^ 64) by (clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hiv), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hiv).
rewrite (Hout2 _ Hiv ltac:(clear - Hkk Hrow HwR Hw Hsep Hnp Hrnp HNi HrNi; lia) ltac:(clear - Hkk Hrow Hiceil HNi HrNi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 4))) with (U Ec (SOff 18 4)) in Hc.
rewrite (U_atom_off Ec 18 i 4 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xcec; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. assert (j = 0) as -> by (clear - Hj; lia). cbn [ms_mem].
assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 4 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
Qed.
Lemma ra_iln4X : forall (m : nat) (i R : Z) W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
h - i <= 2 * Z.of_nat m -> 0 <= i < h -> 0 <= R ->
(forall j, 0 <= j -> i + 2 * j < h -> R + j + 1 <= h) ->
1 <= w <= 65535 -> 1 <= h <= 65535 -> w * h <= npint -> w * h <= Nimg ->
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memc mdc k ->
In (pint, npint) (ablocks B lyc Sc) -> In (img, Nimg) (ablocks B lyc Sc) ->
(forall blc lyq ownq a, In (pint, npint) blc -> pint <= a < pint + npint ->
awr_byte TRAWADD_STK sp0 [(raw + 40, raw + 44)] (ablocks B ly S) blc lyq ownq a) ->
(pint + req_size npint <= img \/ img + req_size Nimg <= pint) ->
(pint + req_size npint <= cfp \/ cfp + 40 <= pint) ->
(raw + req_size RAW_SIZE <= kLowShadowBeg \/ (kHighMemBeg <= raw /\ raw + req_size RAW_SIZE <= ASAN_CEIL)) ->
AR SEGS B ly S W0 mem0 md0 -> In (cid, pos) (frames S) -> 0 <= cid -> frame_addr ly cid pos mod 8 = 0 ->
frame_addr ly cid pos <= cfp -> cfp + 40 <= frame_addr ly cid pos + fs_frame_bytes cid -> cfp mod 8 = 0 ->
range_addressable (aview SEGS (w_H W0) mem0) SHADOW_OFF cfp 40 ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 8) 8 img ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 20) 2 w ->
val_mem SEGS (mrestrict (w_H W) memc) (cfp + 22) 2 h ->
spZ regs = sp0 - 320 -> 70368744177664 + 16 <= sp0 - 320 -> sp0 <= 2 ^ 47 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 25 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 19 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * R) -> getr regs 18 = Z_to_bv 64 i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xcf8)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' (mm : Z),
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0xd64)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
1 <= mm /\ i + 2 * (mm - 1) < h /\ h <= i + 2 * mm /\
getr regs' 27 = Z_to_bv 64 (pint + w * (R + mm)) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r ILN_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * R <= a < pint + w * (R + mm)) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall j kk, 0 <= j < mm -> 0 <= kk < w ->
aview SEGS (w_H W) mem' (pint + w * (R + j) + kk) = aview SEGS (w_H W) memc (img + w * (i + 2 * j) + kk))).
Proof.
induction m as [|m IH]; intros i R W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hm Hi HR Hrows Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _). pose proof (proj1 Hph_ia) as Hph.
pose proof (blk_off_imgP _ _ _ _ _ _ pint npint HAR Hpin) as Hph_img.
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _). pose proof (proj1 Hih_ia) as Hih.
pose proof (blk_off_imgP _ _ _ _ _ _ img Nimg HAR Himg) as Hih_img.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR0 Hfin) as Hfhigh_img.
pose proof (req_size_pos' npint ltac:(lia)) as [_ Hrnp]. pose proof (req_size_pos' Nimg ltac:(lia)) as [_ HrNi].
pose proof (Hrows 0 ltac:(lia) ltac:(lia)) as HR1.
assert (HwR : 0 <= w * R /\ w * (R + 1) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwi : 0 <= i * w /\ (i + 1) * w <= h * w) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
assert (Hhw : h * w = w * h) by (apply Z.mul_comm).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18. pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_iln 27 0xcf8) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xcf8)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_iln. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xcf8) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
- reflexivity.
- unfold iln_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- unfold iln_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E18, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 32 0) E (mrestrict (w_H W) memc).
paj_run_tok RUN HS HJ SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { unfold ss_iln, iln_regions; cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS lyc Sc W _ _ img Nimg HAR1 Himg) as (_ & _ & _ & _ & Hipres1 & _).
change (Z_to_bv 64 333276) with (Z_to_bv 64 (SIGMA AS_asan_memcpy)).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_intrin_at SEGS B LAWS Hsegs OCpy (SIGMA AS_asan_memcpy) AMEMCPY W (ms_regs msX) (ms_mem msX) TRAWADD_STK sp0 _ ly S W0 mem0 md0 [(1, fpos)] lyc Sc _ k
(pint + w * R) (img + i * w) w (-320) _ HJ) end.
- rewrite Ra0. rewrite E27. reflexivity.
- rewrite Ra1. rewrite E33, E18, E34. apply il_src_val; lia.
- rewrite Ra2. rewrite E34. reflexivity.
- lia. - lia. - lia.
- unfold spZ. rewrite Rsp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite Usp. lia.
- reflexivity. - lia. - rewrite FFS. unfold ESTACK. lia.
- rewrite Rgp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
- rewrite Rtp. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]. rewrite ?ew_ewset_other by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. split; [apply (Hpawr (ablocks B lyc Sc)); [exact Hpin | lia] | unfold ESTACK; intro; lia].
- apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ pint npint _ _ HAR1 Hpin); lia.
- split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [| unfold spZ, ESTACK; rewrite Rsp; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Usp; intro; lia].
apply (aview_some_of_apresent SEGS). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). apply (proj1 (Hipres a ltac:(lia))). }
split; [lia|]. split; [apply (amem_range_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia|]. split.
+ apply (range_addressable_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia.
+ intros _. apply (shadow_hull_vis_of_block SEGS B LAWS lyc Sc W _ _ img Nimg _ _ HAR1 Himg); lia. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout2 & Hpres2).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2;
lazymatch type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_nil];
eapply region_kept_aview;
[ cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E25; apply unsigned_lit_small; lia
| intros a Ha; cbn [ms_mem]; rewrite (Hout2 a ltac:(lia) ltac:(clear - Ha HsepC Hrnp Hnp HwR; lia) ltac:(clear - Ha Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia));
first [reflexivity | exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a ltac:(lia))]
| intros a Ha; apply Hpres2; exact Ha ]
| specialize (HS2 HQ); clear HQ ] end  end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc _ _ _) as Eb eqn:HEb in HS. assert (HEIEb : img_env VAL A_LIM Eb) by (rewrite HEb; lazymatch goal with |- img_env _ _ (havoc ?Eo _ _) => let Hq := rnHEI Eo in apply img_env_havoc_hi; [exact Hq | cbv; lia] end).
assert (OLD : forall n, (n < 36)%nat -> ew Eb n = ew E n) by (intros n Hn; rewrite HEb, ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (HAEb : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Eb) by (rewrite HEb; env_agree_chain HAE).
clear HEb.
pose proof (OLD 25%nat ltac:(lia)) as F25. rewrite E25 in F25. pose proof (OLD 27%nat ltac:(lia)) as F27. rewrite E27 in F27.
pose proof (OLD 18%nat ltac:(lia)) as F18. rewrite E18 in F18. pose proof (OLD 32%nat ltac:(lia)) as F32. rewrite E32 in F32.
pose proof (OLD 33%nat ltac:(lia)) as F33. rewrite E33 in F33. pose proof (OLD 34%nat ltac:(lia)) as F34. rewrite E34 in F34.
pose proof (OLD 35%nat ltac:(lia)) as F35. rewrite E35 in F35.
reshok HS.
paj_run_tok RUN HS HJ2 SHOK (SB, SB + 2 ^ 44 - 1).
all: try (iln_obl HJ2 F25 F32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as Ec eqn:HEc | st_ok _ ?Ex _ _ => remember Ex as Ec eqn:HEc  end.
assert (OLDc : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; rewrite ?ew_ewset_other by lia; apply OLD; exact Hn).
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ec) by (rewrite HEc; env_agree_chain HAEb).
clear HEc.
pose proof (OLDc 25%nat ltac:(lia)) as G25. rewrite E25 in G25. pose proof (OLDc 27%nat ltac:(lia)) as G27. rewrite E27 in G27.
pose proof (OLDc 18%nat ltac:(lia)) as G18. rewrite E18 in G18. pose proof (OLDc 32%nat ltac:(lia)) as G32. rewrite E32 in G32.
pose proof (OLDc 34%nat ltac:(lia)) as G34. rewrite E34 in G34. pose proof (OLDc 35%nat ltac:(lia)) as G35. rewrite E35 in G35.
assert (Mcell : forall mm : word -> option byte, (forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. split; [|split]; (eapply val_mem_kept; [| first [exact Mimg | exact Mw | exact Mh]]); intros q Hq; apply Hmm;
[ clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| clear - Hq Hf4096 Hflo Hfhi Hfceil C1; lia | clear - Hq HsepC Hrnp Hnp Hwh Hw Hh; lia | clear - Hq Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia ]. }
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 2))) with (U Ec (SOff 18 2)) in Hc.
rewrite (U_atom_off Ec 18 i 2 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_lt in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xcf8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (18%bv : bv 5) N18. rewrite G18 in N18.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
destruct (Mcell _ HoutX) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (IH (i + 2) (R + 1) W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; pose proof (Hrows (j + 1) ltac:(lia) ltac:(lia)); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ2 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| rewrite N27; f_equal; lia
| rewrite N18; rewrite unsigned_lit_small by lia; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
split; [reflexivity|]. exists regs3, mem3, md3, (mm + 1). split; [reflexivity|]. split; [exact HJ3|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite P27; f_equal; lia|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; rewrite (Hout3 a Ha Hna Hnb); exact (HoutX a Ha Hna Hnb)|].
split; [intros a Ha; apply Hpres3; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
assert (Hwmm : 0 <= w * mm) by (clear - Hw Hm1; nia).
split.
+
intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) Hnb). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna Hwmm HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+
intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (i + 2 * j) /\ w * (i + 2 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hi Hj; lia|].
replace (w * (i + 2 * j) + w) with (w * (i + 2 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hj Hm2 Hi; lia. }
assert (Hwj : 0 <= w * j /\ w * j + w <= w * mm + w).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|]. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; clear - Hw Hj; lia. }
destruct (Z.eq_dec j 0) as [-> | Hj0].
* assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (XO3 _ Hav ltac:(clear - Hkk Hw; lia) ltac:(clear - Hkk HwR Hw Hpceil Hnp Hrnp Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 2 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
* pose proof (XC3 (j - 1) kk ltac:(clear - Hj Hj0; lia) Hkk) as Q.
replace (R + 1 + (j - 1)) with (R + j) in Q by (clear; lia). replace (i + 2 + 2 * (j - 1)) with (i + 2 * j) in Q by (clear; lia).
rewrite Q. cbn [ms_mem].
assert (Hiv : 0 <= img + w * (i + 2 * j) + kk < 2 ^ 64) by (clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hiv), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hiv).
rewrite (Hout2 _ Hiv ltac:(clear - Hkk Hrow HwR Hw Hsep Hnp Hrnp HNi HrNi; lia) ltac:(clear - Hkk Hrow Hiceil HNi HrNi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia)). cbn [ms_mem].
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. change (bv_unsigned (sv_denot Ec (SOff 18 2))) with (U Ec (SOff 18 2)) in Hc.
rewrite (U_atom_off Ec 18 i 2 G18) in Hc by lia. cbn [sv_denot] in Hc. rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small in Hc by lia.
apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ2 0xd64; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (pint + w * R + w)) (denot_add_atoms Ec 27 34 (pint + w * R) w G27 G34 ltac:(lia) ltac:(lia) ltac:(lia)) N27.
prreg HS (21%bv : bv 5) N21. rewrite G25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite G25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow Ec 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
prreg HS (10%bv : bv 5) NXH. rewrite G35 in NXH.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 1 end.
split; [reflexivity|]. split; [exact HJ2|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite N27; f_equal; lia|]. split; [exact NXH|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split; [intros a Ha Hna Hnb; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); rewrite (Hout2 a Ha ltac:(lia) ltac:(lia));
cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha)|].
split; [intros a Ha; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG3); apply (apresent_grows _ _ _ _ HG2); apply Hpres2; cbn [ms_mem]; apply (apresent_grows _ _ _ _ HG1); exact Ha|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 a Ha), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha).
rewrite (Hout2 a Ha ltac:(clear - Hna HwR Hw; lia) ltac:(clear - Hnb; lia)). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. assert (j = 0) as -> by (clear - Hj; lia). cbn [ms_mem].
assert (Hav : 0 <= pint + w * (R + 0) + kk < 2 ^ 64) by (clear - Hkk HwR Hw Hp4096 Hpceil Hnp Hrnp C1; lia).
rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr3 _ Hav), (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 _ Hav).
replace (pint + w * (R + 0) + kk) with (pint + w * R + kk) by (clear; lia). rewrite (Heff kk ltac:(clear - Hkk; lia)). cbn [ms_mem].
assert (Hiv : 0 <= img + i * w + kk < 2 ^ 64) by (clear - Hkk Hwi Hhw Hw Hi4096 Hiceil HNi HrNi C1; lia).
replace (img + w * (i + 2 * 0) + kk) with (img + i * w + kk) by (clear; lia).
exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 _ Hiv).
Qed.
End e.
End d.
End b.
