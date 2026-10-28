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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACai ACam ACan ACac.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI0g.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACad.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACa0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ilx_in2 : forall h, 1 <= h -> 0 < (h + 3) / 8 -> 4 + 8 * ((h + 3) / 8 - 1) < h. Proof. intros. lia. Qed.
Lemma ilx_in3 : forall h, 1 <= h -> 0 < (h + 1) / 4 -> 2 + 4 * ((h + 1) / 4 - 1) < h. Proof. intros. lia. Qed.
Lemma ilx_in4 : forall h, 1 <= h -> 0 < h / 2 -> 1 + 2 * (h / 2 - 1) < h. Proof. intros. lia. Qed.
Lemma ilx_mrows : forall h, 1 <= h ->
mrows 0 8 h ((h + 7) / 8) /\ mrows 4 8 h ((h + 3) / 8) /\ mrows 2 4 h ((h + 1) / 4) /\ mrows 1 2 h (h / 2).
Proof. intros. unfold mrows. lia. Qed.
Lemma interlace_lengthZ : forall IMG w h, Z.of_nat (length IMG) = w * h -> 1 <= w -> 1 <= h ->
Z.of_nat (length (YO07.interlace w IMG)) = w * h.
Proof.
intros IMG w h HL Hw Hh. destruct (ilx_mrows h Hh) as (M1 & M2 & M3 & M4).
pose proof (interlace_length (Z.to_nat w) (Z.to_nat h) IMG (Z.to_nat ((h + 7) / 8)) (Z.to_nat ((h + 3) / 8)) (Z.to_nat ((h + 1) / 4)) (Z.to_nat (h / 2))
ltac:(lia) ltac:(apply Nat2Z.inj; rewrite Nat2Z.inj_mul, !Z2Nat.id by lia; exact HL)
(mrows_N 0 8 h ((h + 7) / 8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) M1) (mrows_N 4 8 h ((h + 3) / 8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) M2)
(mrows_N 2 4 h ((h + 1) / 4) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) M3) (mrows_N 1 2 h (h / 2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) M4)) as E.
rewrite Z2Nat.id in E by lia. rewrite E. exact HL.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma interlace_ipassZ : forall IMG w h m1 m2 m3 m4,
Z.of_nat (length IMG) = w * h -> 1 <= w -> 1 <= h ->
mrows 0 8 h m1 -> mrows 4 8 h m2 -> mrows 2 4 h m3 -> mrows 1 2 h m4 -> 0 <= m1 -> 0 <= m2 -> 0 <= m3 -> 0 <= m4 ->
YO07.interlace w IMG = ipassZ IMG w 0 8 m1 ++ ipassZ IMG w 4 8 m2 ++ ipassZ IMG w 2 4 m3 ++ ipassZ IMG w 1 2 m4.
Proof.
intros IMG w h m1 m2 m3 m4 HL Hw Hh M1 M2 M3 M4 P1 P2 P3 P4. unfold ipassZ.
pose proof (interlace_passes (Z.to_nat w) (Z.to_nat h) IMG (Z.to_nat m1) (Z.to_nat m2) (Z.to_nat m3) (Z.to_nat m4) ltac:(lia)
ltac:(apply Nat2Z.inj; rewrite Nat2Z.inj_mul, !Z2Nat.id by lia; exact HL)
(mrows_N 0 8 h m1 ltac:(lia) ltac:(lia) ltac:(lia) P1 M1) (mrows_N 4 8 h m2 ltac:(lia) ltac:(lia) ltac:(lia) P2 M2)
(mrows_N 2 4 h m3 ltac:(lia) ltac:(lia) ltac:(lia) P3 M3) (mrows_N 1 2 h m4 ltac:(lia) ltac:(lia) ltac:(lia) P4 M4)) as E.
rewrite Z2Nat.id in E by lia. exact E.
Qed.
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
Definition il_atX (pcX RB RX s t : Z) W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint img w h : Z)
: world SEGS -> config -> Prop :=
fun W' c' => il_at B pcX RX W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * RB <= a < pint + w * RX) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) (ms_mem (cfg_ms c')) a = aview SEGS (w_H W) memc a) /\
(forall j kk, 0 <= j < RX - RB -> 0 <= kk < w ->
aview SEGS (w_H W) (ms_mem (cfg_ms c')) (pint + w * (RB + j) + kk) = aview SEGS (w_H W) memc (img + w * (s + t * j) + kk)).
Definition il_doneX W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint w h : Z) (IMG : list Z)
: world SEGS -> config -> Prop :=
fun W' c' => il_done B W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c' /\
garr8 SEGS (mrestrict (w_H W) (ms_mem (cfg_ms c'))) pint (YO07.interlace w IMG).
Lemma ra_ilS2X : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8)) -> getr regs 11 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xbd0)) memc (seg_rom SEGS)) mdc)
(il_atX (BASE + 0xc68) ((h + 7) / 8) ((h + 7) / 8 + (h + 3) / 8) 4 8 W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint img w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 HH H9.
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
pose proof (il_rows_le h ltac:(lia)) as (HR1 & HR2 & HR3 & HRsum). pose proof (Z.div_pos h 2 ltac:(lia) ltac:(lia)) as HR4.
set (RB := (h + 7) / 8) in *.
assert (HRBh : 0 <= RB <= h) by (subst RB; lia).
assert (HwR : 0 <= w * RB /\ w * RB <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xbd0 11%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xbd0)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xbd0) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
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
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, iln_regions; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xc68.
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split.
{ split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite N27; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip2 h ltac:(lia)); lia|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. split.
+ intros a Ha Hna Hnb. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. exfalso. subst RB. rewrite ?(il_skip2 h ltac:(lia)) in Hj. clear - Hj Hc Hh. lia.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xbdc; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (18%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln2X B LAWS AMEMCPY (Z.to_nat h) 4 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound2 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| exact N27
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
pose proof (il_rows2 h mm ltac:(lia) Hm1 Hm2 Hm3) as Emm.
split.
{ split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite P27; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows2 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. subst RB. rewrite ?Emm in XO3, XC3. rewrite ?HRsum in XO3. split.
+ intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna; lia) Hnb). exact (HoutX a Ha).
+ intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (4 + 8 * j) /\ w * (4 + 8 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|].
replace (w * (4 + 8 * j) + w) with (w * (4 + 8 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hh Hj Hm1 Hm2 Hm3 Emm HRsum; lia. }
rewrite (XC3 j kk ltac:(clear - Hj Hh HRsum; lia) Hkk). apply HoutX. clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia.
Qed.
Lemma ra_ilS3X : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8)) -> getr regs 10 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xc68)) memc (seg_rom SEGS)) mdc)
(il_atX (BASE + 0xcec) ((h + 7) / 8 + (h + 3) / 8) ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4) 2 4 W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint img w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 HH H9.
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
pose proof (il_rows_le h ltac:(lia)) as (HR1 & HR2 & HR3 & HRsum). pose proof (Z.div_pos h 2 ltac:(lia) ltac:(lia)) as HR4.
set (RB := (h + 7) / 8 + (h + 3) / 8) in *.
assert (HRBh : 0 <= RB <= h) by (subst RB; lia).
assert (HwR : 0 <= w * RB /\ w * RB <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xc68 10%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xc68)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xc68) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
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
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, iln_regions; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xcec.
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split.
{ split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite N27; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip3 h ltac:(lia)); lia|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. split.
+ intros a Ha Hna Hnb. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. exfalso. subst RB. rewrite ?(il_skip3 h ltac:(lia)) in Hj. clear - Hj Hc Hh. lia.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xc74; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (18%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln3X B LAWS AMEMCPY (Z.to_nat h) 2 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound3 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| exact N27
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
pose proof (il_rows3 h mm ltac:(lia) Hm1 Hm2 Hm3) as Emm.
split.
{ split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite P27; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows3 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. subst RB. rewrite ?Emm in XO3, XC3. rewrite ?HRsum in XO3. split.
+ intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna; lia) Hnb). exact (HoutX a Ha).
+ intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (2 + 4 * j) /\ w * (2 + 4 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|].
replace (w * (2 + 4 * j) + w) with (w * (2 + 4 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hh Hj Hm1 Hm2 Hm3 Emm HRsum; lia. }
rewrite (XC3 j kk ltac:(clear - Hj Hh HRsum; lia) Hkk). apply HoutX. clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia.
Qed.
Lemma ra_ilS4X : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4)) -> getr regs 10 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xcec)) memc (seg_rom SEGS)) mdc)
(il_atX (BASE + 0xd64) ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4) (h) 1 2 W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint img w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 HH H9.
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
pose proof (il_rows_le h ltac:(lia)) as (HR1 & HR2 & HR3 & HRsum). pose proof (Z.div_pos h 2 ltac:(lia) ltac:(lia)) as HR4.
set (RB := (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4) in *.
assert (HRBh : 0 <= RB <= h) by (subst RB; lia).
assert (HwR : 0 <= w * RB /\ w * RB <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
assert (Hwh : w * h <= 65535 * 65535) by (apply Z.mul_le_mono_nonneg; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite H25 in E25. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xcec 10%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xcec)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xcec) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 12 E25) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 25 (cfp + 8) 14 E25) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32); lia.
+ rewrite H19. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
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
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E25, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, iln_regions; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xd64.
all: try (iln_obl HJ E25 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G25 : ew Ex 25 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E25);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 0 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 12 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 25 32 (cfp + 8) 14 G25 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split.
{ split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite N27; f_equal; f_equal; f_equal; subst RB; exact (il_skip4 h ltac:(lia))|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. split.
+ intros a Ha Hna Hnb. rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha).
+ intros j kk Hj Hkk. exfalso. subst RB. rewrite ?(il_skip4 h ltac:(lia)) in Hj. clear - Hj Hc Hh. lia.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xcf8; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (18%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E25 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E25 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 0 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 12 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N19. replace (cfp + 8 + 12) with (cfp + 20) in N19 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 25 32 (cfp + 8) 14 E25 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ iln_regions _ _ _ iln_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln4X B LAWS AMEMCPY (Z.to_nat h) 1 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound4 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 25%bv ltac:(cbv; tauto)); exact H25 | exact N26 | exact N21 | exact N19 | exact N22 | exact N24
| exact N27
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & PXH & HK3 & Hout3 & Hpres3 & XO3 & XC3).
pose proof (il_rows4 h mm ltac:(lia) Hm1 Hm2 Hm3) as Emm.
split.
{ split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite P27; f_equal; f_equal; f_equal; subst RB; rewrite (il_rows4 h mm ltac:(lia) Hm1 Hm2 Hm3); exact HRsum|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N19, H19; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha. }
cbn [cfg_ms ms_regs ms_mem mkst]. subst RB. rewrite ?Emm in XO3, XC3. rewrite ?HRsum in XO3. split.
+ intros a Ha Hna Hnb. rewrite (XO3 a Ha ltac:(clear - Hna; lia) Hnb). exact (HoutX a Ha).
+ intros j kk Hj Hkk.
assert (Hrow : 0 <= w * (1 + 2 * j) /\ w * (1 + 2 * j) + w <= w * h).
{ split; [apply Z.mul_nonneg_nonneg; clear - Hw Hj; lia|].
replace (w * (1 + 2 * j) + w) with (w * (1 + 2 * j + 1)) by (clear; lia). apply Z.mul_le_mono_nonneg_l; clear - Hw Hh Hj Hm1 Hm2 Hm3 Emm HRsum; lia. }
rewrite (XC3 j kk ltac:(clear - Hj Hh HRsum; lia) Hkk). apply HoutX. clear - Hkk Hrow Hi4096 Hiceil HNi HrNi C1; lia.
Qed.
Lemma ra_il_allX : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 27 = Z_to_bv 64 pint -> getr regs 18 = Z_to_bv 64 0 ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) ->
forall IMG : list Z, garr8 SEGS (mrestrict (w_H W) memc) img IMG -> Z.of_nat (length IMG) = w * h ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xb64)) memc (seg_rom SEGS)) mdc)
(il_doneX W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h IMG).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H25 H26 H21 H19 H22 H24 H27 H18 H9 IMG HIMG HIMGlen.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (req_size_pos' npint ltac:(nia)) as [_ Hrnp].
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & Hppres & _).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc img Nimg HAR Himg) as (Hi16 & Hi4096 & Hiceil & Hih_ia & Hipres & _).
pose proof (req_size_pos' Nimg ltac:(nia)) as [_ HrNi].
pose proof (il_rows_le h ltac:(lia)) as (HR1 & HR2 & HR3 & HRsum). pose proof (Z.div_pos h 2 ltac:(lia) ltac:(lia)) as HR4.
assert (HGIkept : forall (m1 m2 : word -> option byte) lo hi,
pint <= lo -> hi <= pint + w * h ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
garr8 SEGS (mrestrict (w_H W) m1) img IMG -> garr8 SEGS (mrestrict (w_H W) m2) img IMG).
{ intros m1 m2 lo hi Hlo Hhi Hout HG. apply (garr8_aview_kept SEGS (w_H W) (w_H W) m1 m2 img IMG); [|exact HG].
intros a Ha. rewrite HIMGlen in Ha. apply Hout; [clear - Ha Hi4096 Hiceil HNi HrNi C1; lia | clear - Ha Hlo Hhi Hsep Hnp Hrnp HNi HrNi; lia
| clear - Ha Hiceil HNi HrNi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia]. }
assert (HGPkept : forall (m1 m2 : word -> option byte) (PFX : list Z) RB hi,
Z.of_nat (length PFX) = w * RB -> 0 <= w * RB <= w * h -> hi <= pint + w * h ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint + w * RB <= a < hi) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) ->
garr8 SEGS (mrestrict (w_H W) m1) pint PFX -> garr8 SEGS (mrestrict (w_H W) m2) pint PFX).
{ intros m1 m2 PFX RB hi HL HRB Hhi Hout HG. apply (garr8_aview_kept SEGS (w_H W) (w_H W) m1 m2 pint PFX); [|exact HG].
intros a Ha. rewrite HL in Ha. apply Hout; [clear - Ha Hp4096 Hpceil Hnp Hrnp HRB Hhi C1; lia | clear - Ha; lia
| clear - Ha Hpceil Hnp Hrnp HRB Hhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia]. }
assert (HPASS : forall (m1 m2 : word -> option byte) (s t m R : Z),
garr8 SEGS (mrestrict (w_H W) m1) img IMG -> 0 <= s -> 1 <= t -> 0 <= m -> 0 <= R -> (0 < m -> s + t * (m - 1) < h) ->
(forall j kk, 0 <= j < m -> 0 <= kk < w -> aview SEGS (w_H W) m2 (pint + w * (R + j) + kk) = aview SEGS (w_H W) m1 (img + w * (s + t * j) + kk)) ->
garr8 SEGS (mrestrict (w_H W) m2) (pint + w * R) (ipassZ IMG w s t m)).
{ intros m1 m2 s t m R HG Hs Ht Hm HR Hin Hcp.
apply (garr8_ipass SEGS (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) img pint IMG w h s t m R HG HIMGlen ltac:(lia) Hs Ht Hm HR Hin).
intros j kk Hj Hkk. apply (mbyte_of_aview_eq SEGS). apply Hcp; [exact Hj | exact Hkk]. }
assert (Hkept : forall (mm : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. apply (il_cells_kept (w_H W) memc mm (sp0 - 320 - ESTACK) (sp0 - 320) pint (w * h) cfp img w h Hmm);
[ clear - Hf4096 Hflo; lia | clear - Hfhi Hfceil C1; lia | clear - HsepC Hrnp Hnp; lia | left; clear - Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| exact (conj Mimg (conj Mw Mh)) ]. }
eapply SRr_bind.
{ eapply (ra_iln1X B LAWS AMEMCPY (Z.to_nat h) 0 0 W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg | exact Mw | exact Mh
| exact Hsp | exact H46 | exact H47 | exact Hgp | exact Htp
| exact H25 | exact H26 | exact H21 | exact H19 | exact H22 | exact H24
| rewrite H27; f_equal; lia | exact H18 ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & P11 & HK3 & Hout3 & Hpres3 & XO3 & XC3).
pose proof (il_rows1 h mm ltac:(lia) Hm1 Hm2 Hm3) as Emm.
assert (HwR1 : 0 <= w * mm /\ w * mm <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (HPASS memc mem3 0 8 mm 0 HIMG ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) XC3) as HGP3. rewrite Z.mul_0_r, Z.add_0_r in HGP3.
pose proof (HGIkept memc mem3 (pint + w * 0) (pint + w * (0 + mm)) ltac:(lia) ltac:(lia) XO3 HIMG) as HGI3.
pose proof (ipassZ_length IMG w h 0 8 mm HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia)) as HL3.
destruct (Hkept mem3 Hout3) as (Mimg3 & Mw3 & Mh3).
eapply SRr_bind.
{ eapply (ra_ilS2X W regs3 mem3 md3 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK3 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK3 3%bv eq_refl); exact Hgp | rewrite (HK3 4%bv eq_refl); exact Htp
| rewrite (HK3 25%bv eq_refl); exact H25 | rewrite (HK3 26%bv eq_refl); exact H26 | rewrite (HK3 21%bv eq_refl); exact H21
| rewrite (HK3 19%bv eq_refl); exact H19 | rewrite (HK3 22%bv eq_refl); exact H22 | rewrite (HK3 24%bv eq_refl); exact H24
| rewrite P27; f_equal; rewrite <- Emm; lia | exact P11
| rewrite (HK3 9%bv eq_refl); exact H9 ]. }
cbv beta. intros W4 c4 Hwle4 ((-> & regs4 & mem4 & md4 & -> & HJ4 & Q27 & Q10 & HK4 & Hout4 & Hpres4) & XO4 & XC4). cbn [cfg_ms ms_regs ms_mem mkst] in XO4, XC4.
rewrite <- Emm in XO4, XC4. replace (mm + (h + 3) / 8 - mm) with ((h + 3) / 8) in XC4 by lia.
assert (HwR2 : 0 <= w * ((h + 3) / 8) /\ w * (mm + (h + 3) / 8) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (HPASS mem3 mem4 4 8 ((h + 3) / 8) mm HGI3 ltac:(lia) ltac:(lia) HR2 ltac:(lia) (ilx_in2 h ltac:(lia)) XC4) as HGQ4.
pose proof (HGPkept mem3 mem4 _ mm (pint + w * (mm + (h + 3) / 8)) HL3 HwR1 ltac:(lia) XO4 HGP3) as HGP3'.
assert (HGP4 : garr8 SEGS (mrestrict (w_H W) mem4) pint (ipassZ IMG w 0 8 mm ++ ipassZ IMG w 4 8 ((h + 3) / 8))).
{ apply (proj2 (garr8_app SEGS _ pint _ _)). split; [exact HGP3' | rewrite HL3; exact HGQ4]. }
clear HGQ4 HGP3'.
pose proof (HGIkept mem3 mem4 (pint + w * mm) (pint + w * (mm + (h + 3) / 8)) ltac:(lia) ltac:(lia) XO4 HGI3) as HGI4.
assert (HL4 : Z.of_nat (length (ipassZ IMG w 0 8 mm ++ ipassZ IMG w 4 8 ((h + 3) / 8))) = w * (mm + (h + 3) / 8)).
{ rewrite length_app, Nat2Z.inj_add, HL3, (ipassZ_length IMG w h 4 8 ((h + 3) / 8) HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) HR2 (ilx_in2 h ltac:(lia))). lia. }
assert (HK4' : forall r : bv 5, reg_in r IL_CLOB = false -> getr regs4 r = getr regs r) by (intros r Hr; rewrite (HK4 r Hr); exact (HK3 r Hr)).
assert (Hout4' : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) memc a) by (intros a Ha Hna Hnb; rewrite (Hout4 a Ha Hna Hnb); exact (Hout3 a Ha Hna Hnb)).
destruct (Hkept mem4 Hout4') as (Mimg4 & Mw4 & Mh4).
eapply SRr_bind.
{ eapply (ra_ilS3X W regs4 mem4 md4 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ4 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg4 | exact Mw4 | exact Mh4
| unfold spZ; rewrite (HK4' 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK4' 3%bv eq_refl); exact Hgp | rewrite (HK4' 4%bv eq_refl); exact Htp
| rewrite (HK4' 25%bv eq_refl); exact H25 | rewrite (HK4' 26%bv eq_refl); exact H26 | rewrite (HK4' 21%bv eq_refl); exact H21
| rewrite (HK4' 19%bv eq_refl); exact H19 | rewrite (HK4' 22%bv eq_refl); exact H22 | rewrite (HK4' 24%bv eq_refl); exact H24
| exact Q27 | exact Q10 | rewrite (HK4' 9%bv eq_refl); exact H9 ]. }
cbv beta. intros W5 c5 Hwle5 ((-> & regs5 & mem5 & md5 & -> & HJ5 & T27 & T10 & HK5 & Hout5 & Hpres5) & XO5 & XC5). cbn [cfg_ms ms_regs ms_mem mkst] in XO5, XC5.
rewrite <- Emm in XO5, XC5. replace (mm + (h + 3) / 8 + (h + 1) / 4 - (mm + (h + 3) / 8)) with ((h + 1) / 4) in XC5 by lia.
assert (HwR3 : 0 <= w * ((h + 1) / 4) /\ w * (mm + (h + 3) / 8 + (h + 1) / 4) <= w * h) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_l; lia]).
pose proof (HPASS mem4 mem5 2 4 ((h + 1) / 4) (mm + (h + 3) / 8) HGI4 ltac:(lia) ltac:(lia) HR3 ltac:(lia) (ilx_in3 h ltac:(lia)) XC5) as HGQ5.
pose proof (HGPkept mem4 mem5 _ (mm + (h + 3) / 8) (pint + w * (mm + (h + 3) / 8 + (h + 1) / 4)) HL4 ltac:(clear - HwR1 HwR2; lia) ltac:(lia) XO5 HGP4) as HGP4'.
assert (HGP5 : garr8 SEGS (mrestrict (w_H W) mem5) pint ((ipassZ IMG w 0 8 mm ++ ipassZ IMG w 4 8 ((h + 3) / 8)) ++ ipassZ IMG w 2 4 ((h + 1) / 4))).
{ apply (proj2 (garr8_app SEGS _ pint _ _)). split; [exact HGP4' | rewrite HL4; exact HGQ5]. }
clear HGQ5 HGP4'.
pose proof (HGIkept mem4 mem5 (pint + w * (mm + (h + 3) / 8)) (pint + w * (mm + (h + 3) / 8 + (h + 1) / 4)) ltac:(lia) ltac:(lia) XO5 HGI4) as HGI5.
assert (HL5 : Z.of_nat (length ((ipassZ IMG w 0 8 mm ++ ipassZ IMG w 4 8 ((h + 3) / 8)) ++ ipassZ IMG w 2 4 ((h + 1) / 4))) = w * (mm + (h + 3) / 8 + (h + 1) / 4)).
{ rewrite length_app, Nat2Z.inj_add, HL4, (ipassZ_length IMG w h 2 4 ((h + 1) / 4) HIMGlen ltac:(lia) ltac:(lia) ltac:(lia) HR3 (ilx_in3 h ltac:(lia))). lia. }
assert (HK5' : forall r : bv 5, reg_in r IL_CLOB = false -> getr regs5 r = getr regs r) by (intros r Hr; rewrite (HK5 r Hr); exact (HK4' r Hr)).
assert (Hout5' : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) memc a) by (intros a Ha Hna Hnb; rewrite (Hout5 a Ha Hna Hnb); exact (Hout4' a Ha Hna Hnb)).
destruct (Hkept mem5 Hout5') as (Mimg5 & Mw5 & Mh5).
eapply SRr_mono; [eapply (ra_ilS4X W regs5 mem5 md5 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos)|];
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ5 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg5 | exact Mw5 | exact Mh5
| unfold spZ; rewrite (HK5' 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK5' 3%bv eq_refl); exact Hgp | rewrite (HK5' 4%bv eq_refl); exact Htp
| rewrite (HK5' 25%bv eq_refl); exact H25 | rewrite (HK5' 26%bv eq_refl); exact H26 | rewrite (HK5' 21%bv eq_refl); exact H21
| rewrite (HK5' 19%bv eq_refl); exact H19 | rewrite (HK5' 22%bv eq_refl); exact H22 | rewrite (HK5' 24%bv eq_refl); exact H24
| exact T27 | exact T10 | rewrite (HK5' 9%bv eq_refl); exact H9 | ].
cbv beta. intros W6 c6 Hwle6 (HAT & XO6 & XC6). split.
{ revert HAT. apply (il_at_after B _ _ W regs regs5 memc mem5 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h).
- intros r Hr. rewrite (HK5 r Hr), (HK4 r Hr). exact (HK3 r Hr).
- intros a Ha Hna Hnb. rewrite (Hout5 a Ha Hna Hnb), (Hout4 a Ha Hna Hnb). exact (Hout3 a Ha Hna Hnb).
- intros a Ha. apply Hpres5, Hpres4, Hpres3. exact Ha. }
destruct HAT as (_ & regs6 & mem6 & md6 & -> & _). cbn [cfg_ms ms_regs ms_mem mkst] in XO6, XC6 |- *.
rewrite <- Emm in XO6, XC6.
replace (h - (mm + (h + 3) / 8 + (h + 1) / 4)) with (h / 2) in XC6 by lia.
pose proof (HPASS mem5 mem6 1 2 (h / 2) (mm + (h + 3) / 8 + (h + 1) / 4) HGI5 ltac:(lia) ltac:(lia) HR4 ltac:(lia) (ilx_in4 h ltac:(lia)) XC6) as HGQ6.
pose proof (HGPkept mem5 mem6 _ (mm + (h + 3) / 8 + (h + 1) / 4) (pint + w * h) HL5 ltac:(clear - HwR1 HwR2 HwR3; lia) ltac:(lia) XO6 HGP5) as HGP5'.
assert (HGP6 : garr8 SEGS (mrestrict (w_H W) mem6) pint (((ipassZ IMG w 0 8 mm ++ ipassZ IMG w 4 8 ((h + 3) / 8)) ++ ipassZ IMG w 2 4 ((h + 1) / 4)) ++ ipassZ IMG w 1 2 (h / 2))).
{ apply (proj2 (garr8_app SEGS _ pint _ _)). split; [exact HGP5' | rewrite HL5; exact HGQ6]. }
destruct (ilx_mrows h ltac:(lia)) as (M1 & M2 & M3 & M4). rewrite <- Emm in M1.
rewrite (interlace_ipassZ IMG w h mm ((h + 3) / 8) ((h + 1) / 4) (h / 2) HIMGlen ltac:(lia) ltac:(lia) M1 M2 M3 M4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
rewrite <- !app_assoc in HGP6. exact HGP6.
Qed.
End e.
End d.
End b.
