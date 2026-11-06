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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbk YC8a YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8h YC8j YCbc YCbf YCbd YCab YCai YCam YCan YCac.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma il_rows1 : forall h mm, 1 <= h -> 1 <= mm -> 0 + 8 * (mm - 1) < h -> h <= 0 + 8 * mm -> mm = (h + 7) / 8.
Proof. intros. lia. Qed.
Lemma il_rows2 : forall h mm, 1 <= h -> 1 <= mm -> 4 + 8 * (mm - 1) < h -> h <= 4 + 8 * mm -> mm = (h + 3) / 8.
Proof. intros. lia. Qed.
Lemma il_rows3 : forall h mm, 1 <= h -> 1 <= mm -> 2 + 4 * (mm - 1) < h -> h <= 2 + 4 * mm -> mm = (h + 1) / 4.
Proof. intros. lia. Qed.
Lemma il_bound2 : forall h j, 1 <= h -> 0 <= j -> 4 + 8 * j < h -> (h + 7) / 8 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_bound3 : forall h j, 1 <= h -> 0 <= j -> 2 + 4 * j < h -> (h + 7) / 8 + (h + 3) / 8 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_bound4 : forall h j, 1 <= h -> 0 <= j -> 1 + 2 * j < h -> (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_rows_le : forall h, 1 <= h -> 1 <= (h + 7) / 8 /\ 0 <= (h + 3) / 8 /\ 0 <= (h + 1) / 4 /\ (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 + h / 2 = h.
Proof. intros. lia. Qed.
Lemma il_skip2 : forall h, 1 <= h < 5 -> (h + 3) / 8 = 0. Proof. intros. lia. Qed.
Lemma il_skip3 : forall h, 1 <= h < 3 -> (h + 1) / 4 = 0. Proof. intros. lia. Qed.
Lemma il_rows4 : forall h mm, 1 <= h -> 1 <= mm -> 1 + 2 * (mm - 1) < h -> h <= 1 + 2 * mm -> mm = h / 2.
Proof. intros. lia. Qed.
Lemma il_skip4 : forall h, 1 <= h < 2 -> (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 = h. Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac iln_obl HJx Hx25 Hx32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 23 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 23 (cfp + 8) c Hx25) by lia | rewrite (U_atom Ex 23 (cfp + 8) Hx25) by lia ];
eapply (obl_of_range _ _ _ Ex (SOff 32 0) _ len cfp 40);
[ eapply (range_addressable_entry_frame _ _ LAWS); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; destruct Hrg as [<- | []]; cbn [fst snd] in Hxr; clear - Hxr Hrh C2 C3; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; change (req_size RAW_SIZE) with 48 in *; lia
| exact HAR0 | exact HRA ]
| rewrite (U_atom Ex 32 SB Hx32); [reflexivity | unfold SB; lia] | lia | lia ] end.
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_both3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Definition IL_CLOB : list (bv 5) := ILN_CLOB.
Definition ilg_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (27%nat, HPTR 0); (23%nat, HPTR 3); (33%nat, HPTR 0);
(34%nat, mkAF 1 65535 0); (35%nat, mkAF 1 65535 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ilg_regions : smem := iln_regions ++ [ YP09.mkRegion (Some 9%nat) 176 184 0 0 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))] ].
Lemma ilg_regions_ro : forall r, In r ilg_regions -> YP09.r_whi r <= YP09.r_wlo r.
Proof. intros r [<- | [<- | []]]; cbn; lia. Qed.
Definition ss_ilg (pc : Z) (rh : bv 5) : sstate := mkSS pc (sr_set iln_regs rh (SOff 35 0)) ilg_regions None ilg_facts.
Lemma iln_clob_sub4 : forall r : bv 5, reg_in r ILN_CLOB = false -> reg_in r ILN4_CLOB = false.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [reflexivity | vm_compute in Hr; discriminate] |]). destruct Hin.
Qed.
Definition il_at (pcX RX v27 : Z) W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint w h : Z)
: world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 pcX) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
getr regs' 27 = Z_to_bv 64 v27 /\ getr regs' 20 = Z_to_bv 64 (pint + w * RX) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r IL_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a).
Definition il_done W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint w h : Z)
: world SEGS -> config -> Prop := il_at (BASE + 0xfdc) h SB W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h.
Lemma il_at_after : forall pcX RX v27 W (regs regsX : bvmap 5 word) (memc memX : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h,
(forall r : bv 5, reg_in r IL_CLOB = false -> getr regsX r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memX a) ->
forall W' c', il_at pcX RX v27 W regsX memX sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c' ->
il_at pcX RX v27 W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c'.
Proof.
intros pcX RX v27 W regs regsX memc memX sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h HK Hout Hpres W' c'
(-> & regs' & mem' & md' & -> & HJ & P27 & P20 & P10 & HK' & Hout' & Hpres').
split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact P27|]. split; [exact P20|]. split; [exact P10|].
split; [intros r Hr; rewrite (HK' r Hr); exact (HK r Hr)|].
split; [intros a Ha Hna Hnb; rewrite (Hout' a Ha Hna Hnb); exact (Hout a Ha Hna Hnb)|].
intros a Ha. apply Hpres', Hpres, Ha.
Qed.
Lemma il_cells_kept : forall H (memc mm : word -> option byte) lo hi pint L cfp img w h,
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + L) -> ~ (lo <= a < hi) -> aview SEGS H mm a = aview SEGS H memc a) ->
0 <= cfp -> cfp + 40 <= 2 ^ 64 -> (pint + L <= cfp \/ cfp + 40 <= pint) -> (cfp + 40 <= lo \/ hi <= cfp) ->
val_mem SEGS (mrestrict H memc) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict H memc) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict H memc) (cfp + 22) 2 h ->
val_mem SEGS (mrestrict H mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict H mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict H mm) (cfp + 22) 2 h.
Proof.
intros H memc mm lo hi pint L cfp img w h Hout H0 H64 Hs1 Hs2 (V1 & V2 & V3).
split; [|split]; (eapply val_mem_kept; [| first [exact V1 | exact V2 | exact V3]]); intros q Hq; apply Hout; lia.
Qed.
Lemma il_slot_kept : forall H (memc mm : word -> option byte) lo hi pint L a v,
(forall x, 0 <= x < 2 ^ 64 -> ~ (pint <= x < pint + L) -> ~ (lo <= x < hi) -> aview SEGS H mm x = aview SEGS H memc x) ->
0 <= a -> a + 8 <= 2 ^ 64 -> (pint + L <= a \/ a + 8 <= pint) -> (a + 8 <= lo \/ hi <= a) ->
val_mem SEGS (mrestrict H memc) a 8 v -> val_mem SEGS (mrestrict H mm) a 8 v.
Proof.
intros H memc mm lo hi pint L a v Hout H0 H64 Hs1 Hs2 V. eapply val_mem_kept; [| exact V]. intros q Hq. apply Hout; lia.
Qed.
Lemma ra_ilS2 : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 23 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 25 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8)) -> getr regs 20 = Z_to_bv 64 (pint + w * ((h + 7) / 8)) -> getr regs 10 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 320 + 176) 8 SB ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xd84)) memc (seg_rom SEGS)) mdc)
(il_at (BASE + 0xe6c) ((h + 7) / 8 + (h + 3) / 8) (pint + w * ((h + 7) / 8 + (h + 3) / 8)) W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H23 H26 H21 H25 H22 H24 H27 H20 HH H9 MSB.
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
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20. pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xd84 10%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xd84)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xd84) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 12 E23) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 14 E23) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32); lia.
+ rewrite H25. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- reflexivity.
- unfold ilg_regions, iln_regions. cbn [app]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
[| rewrite E9, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E _ (sp0 - 320) 176 8 _ SB); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside | exact MSB] ].
rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- unfold ilg_regions, iln_regions. cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E23, E9, !unsigned_lit_small by lia. repeat split. clear - Hflo Hfhi Hfceil Hceil Hslo Hstk0 FFS C1. lia.
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E23, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, ilg_regions, iln_regions; cbn [ss_mem app]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xe6c.
all: try (iln_obl HJ E23 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 0 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 12 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 14 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite N27; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip2 h ltac:(lia)); lia|]. split; [rewrite N20; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip2 h ltac:(lia)); lia|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xd94; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E20 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (19%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln2 B LAWS AMEMCPY (Z.to_nat h) 4 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound2 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23 | exact N26 | exact N21 | exact N25 | exact N22 | exact N24
| exact N27
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & P20 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite P27; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows2 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [rewrite P20; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows2 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_ilS3 : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 23 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 25 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8)) -> getr regs 20 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8)) -> getr regs 10 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 320 + 176) 8 SB ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xe6c)) memc (seg_rom SEGS)) mdc)
(il_at (BASE + 0xf28) ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4) (pint + w * ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4)) W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H23 H26 H21 H25 H22 H24 H27 H20 HH H9 MSB.
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
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20. pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xe6c 10%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xe6c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xe6c) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 12 E23) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 14 E23) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32); lia.
+ rewrite H25. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- reflexivity.
- unfold ilg_regions, iln_regions. cbn [app]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
[| rewrite E9, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E _ (sp0 - 320) 176 8 _ SB); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside | exact MSB] ].
rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- unfold ilg_regions, iln_regions. cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E23, E9, !unsigned_lit_small by lia. repeat split. clear - Hflo Hfhi Hfceil Hceil Hslo Hstk0 FFS C1. lia.
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E23, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, ilg_regions, iln_regions; cbn [ss_mem app]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xf28.
all: try (iln_obl HJ E23 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E27 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 0 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 12 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 14 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite N27; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip3 h ltac:(lia)); lia|]. split; [rewrite N20; f_equal; f_equal; f_equal; subst RB; rewrite (il_skip3 h ltac:(lia)); lia|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xe7c; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E20 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (19%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln3 B LAWS AMEMCPY (Z.to_nat h) 2 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound3 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23 | exact N26 | exact N21 | exact N25 | exact N22 | exact N24
| exact N27
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & P20 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite P27; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows3 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [rewrite P20; f_equal; f_equal; f_equal; subst RB; rewrite <- (il_rows3 h mm ltac:(lia) Hm1 Hm2 Hm3); reflexivity|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r Hr); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_ilS4 : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 23 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 25 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4)) -> getr regs 20 = Z_to_bv 64 (pint + w * ((h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4)) -> getr regs 10 = Z_to_bv 64 h ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 320 + 176) 8 SB ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xf28)) memc (seg_rom SEGS)) mdc)
(il_at (BASE + 0xfdc) (h) (SB) W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H23 H26 H21 H25 H22 H24 H27 H20 HH H9 MSB.
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
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite H23 in E23. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite H27 in E27.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite H20 in E20. pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite H9 in E9.
pose proof (EE 2%nat 2%bv eq_refl) as E2.
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 img) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 w) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 h) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 320) by (rewrite E2; exact Hsp).
assert (HS : st_ok_pi SEGS VAL E (ss_ilg 0xf28 10%bv) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xf28)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_ilg. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0xf28) _ regs _ _ (mrestrict (w_H W) memc)).
- unfold iln_regs, sh_of.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin;
[subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |] | intros X; discriminate X |].
+ rewrite H21. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 12 E23) by lia. lia.
+ rewrite H22. symmetry. rewrite denot_lit_U. f_equal. rewrite (U_atom_off E 23 (cfp + 8) 14 E23) by lia. lia.
+ rewrite H26. symmetry. replace (cfp + 8) with (cfp + 8 + 0) at 1 by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32); lia.
+ rewrite H25. symmetry. replace (cfp + 20) with (cfp + 8 + 12) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32); lia.
+ rewrite H24. symmetry. replace (cfp + 22) with (cfp + 8 + 14) by lia. apply (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32); lia.
+ rewrite HH. symmetry. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- reflexivity.
- unfold ilg_regions, iln_regions. cbn [app]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
[| rewrite E9, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS E _ (sp0 - 320) 176 8 _ SB); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside | exact MSB] ].
rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 0 8 _ img);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Mimg].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 12 2 _ w);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 12) with (cfp + 20) by lia; exact Mw].
+ apply (chunk_ok_val SEGS E _ (cfp + 8) 14 2 _ h);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | replace (cfp + 8 + 14) with (cfp + 22) by lia; exact Mh].
- unfold ilg_regions, iln_regions. cbn [app pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E23, E9, !unsigned_lit_small by lia. repeat split. clear - Hflo Hfhi Hfceil Hceil Hslo Hstk0 FFS C1. lia.
- unfold ilg_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2. pose proof Hsp as Hsp'. unfold spZ in Hsp'. rewrite Hsp'. clear Hsp'.
rewrite E27, E23, E33, E34, E35, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try lia.
+ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (sp0 / 16) - 320) with ((sp0 / 16 - 20) * 16) by lia. apply Z_mod_mult.
+ rewrite <- Zplus_mod_idemp_l, Hcal. reflexivity. }
clear HE. pose proof HS as HS0.
paj_run_sh RUNP HS HJ; [unfold ss_ilg, ilg_regions, iln_regions; cbn [ss_mem app]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr1. rename HG into HG1. clear HF.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
reshok HS.
paj_run_to_tok RUNTO HS HJ SHOK (SB, SB + 2 ^ 44 - 1) 0xfdc.
all: try (iln_obl HJ E23 E32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA).
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr2. rename HG into HG2. clear HF.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32) | st_ok _ ?Ex _ _ =>
assert (OLDc : forall n, (n < 36)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity);
assert (HAEc : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 img; Z_to_bv 64 w; Z_to_bv 64 h]) Ex) by (env_agree_chain HAE);
assert (G23 : ew Ex 23 = Z_to_bv 64 (cfp + 8)) by (rewrite ?ew_ewset_other by lia; exact E23);
assert (G32 : ew Ex 32 = Z_to_bv 64 SB) by (rewrite ?ew_ewset_other by lia; exact E32)  end.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAEc ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E32 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (10%bv : bv 5) N10. rewrite E35 in N10.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 0 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 12 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow _ 23 32 (cfp + 8) 14 G23 G32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|].
split; [exact N27|]. split; [rewrite N20; f_equal; f_equal; f_equal; subst RB; exact (il_skip4 h ltac:(lia))|]. split; [exact N10|].
split; [intros r Hr; destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. cbn [ms_mem]. rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha). cbn [ms_mem]. exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha).
+ intros a Ha. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_ge in Hc.
paj_run_to_sh RUNTOP HS HJ 0xf3c; [apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_nil|]. rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ILN_KEPT' HS HAE ltac:(vm_compute; reflexivity)) as HK. cbn [ms_regs restrict] in HK.
prreg HS (27%bv : bv 5) N27. rewrite E32 in N27.
prreg HS (20%bv : bv 5) N20. rewrite E20 in N20.
prreg HS (19%bv : bv 5) N18.
prreg HS (21%bv : bv 5) N21. rewrite E23 in N21. rewrite unsigned_lit_small in N21 by lia. replace (cfp + 8 + 12) with (cfp + 20) in N21 by lia.
prreg HS (22%bv : bv 5) N22. rewrite E23 in N22. rewrite unsigned_lit_small in N22 by lia. replace (cfp + 8 + 14) with (cfp + 22) in N22 by lia.
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 0) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 0 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N26. replace (cfp + 8 + 0) with (cfp + 8) in N26 by lia.
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 12) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 12 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N25. replace (cfp + 8 + 12) with (cfp + 20) in N25 by lia.
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (SB + (cfp + 8 + 14) / 8)) (il_denot_shadow E 23 32 (cfp + 8) 14 E23 E32 ltac:(lia) ltac:(lia) ltac:(lia)) N24. replace (cfp + 8 + 14) with (cfp + 22) in N24 by lia.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
assert (HoutX : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha; cbn [ms_mem]; rewrite (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr2 a Ha); cbn [ms_mem]; exact (aview_kept_ro _ ilg_regions _ _ _ ilg_regions_ro HFr1 a Ha) | ] end.
lazymatch type of HoutX with forall a, _ -> aview _ _ ?mX a = _ =>
destruct (il_cells_kept (w_H W) memc mX 0 0 pint 0 cfp img w h ltac:(intros a Ha _ _; exact (HoutX a Ha)) ltac:(clear - Hf4096 Hflo; lia) ltac:(clear - Hfhi Hfceil C1; lia)
ltac:(clear - HsepC Hrnp Hnp HwR; lia) ltac:(right; clear - Hf4096 Hflo; lia) (conj Mimg (conj Mw Mh))) as (Mimg2 & Mw2 & Mh2) end.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (ra_iln4 B LAWS AMEMCPY (Z.to_nat h) 1 RB W (ms_regs msX) (ms_mem msX) _ sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; subst RB; apply (il_bound4 h j); lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg2 | exact Mw2 | exact Mh2
| unfold spZ; rewrite (HK 2%bv ltac:(cbv; tauto)); exact Hsp | exact H46 | exact H47
| rewrite (HK 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HK 4%bv ltac:(cbv; tauto)); exact Htp
| rewrite (HK 23%bv ltac:(cbv; tauto)); exact H23 | exact N26 | exact N21 | exact N25 | exact N22 | exact N24
| exact N20
| rewrite N18; reflexivity ] end. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & P20 & PXH & HK3 & Hout3 & Hpres3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split; [rewrite (HK3 27%bv eq_refl); exact N27|]. split; [rewrite P20; f_equal; f_equal; f_equal; subst RB; rewrite (il_rows4 h mm ltac:(lia) Hm1 Hm2 Hm3); exact HRsum|]. split; [exact PXH|].
split; [intros r Hr; rewrite (HK3 r (iln_clob_sub4 r Hr)); destruct (iln_clob_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]];
[cbn [ms_regs]; rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0); reflexivity
| cbn [ms_regs]; rewrite N25, H25; reflexivity | cbn [ms_regs]; rewrite N21, H21; reflexivity | cbn [ms_regs]; rewrite N22, H22; reflexivity
| cbn [ms_regs]; rewrite N24, H24; reflexivity | cbn [ms_regs]; rewrite N26, H26; reflexivity | exact (HK r Hr')]|].
split.
+ intros a Ha Hna Hnb. rewrite (Hout3 a Ha Hna Hnb). exact (HoutX a Ha).
+ intros a Ha. apply Hpres3. cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG2). cbn [ms_mem]. apply (apresent_grows _ _ _ _ HG1). exact Ha.
Qed.
Lemma ra_il_all : forall W (regs : bvmap 5 word) memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos,
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
getr regs 23 = Z_to_bv 64 (cfp + 8) -> getr regs 26 = Z_to_bv 64 (SB + (cfp + 8) / 8) ->
getr regs 21 = Z_to_bv 64 (cfp + 20) -> getr regs 25 = Z_to_bv 64 (SB + (cfp + 20) / 8) ->
getr regs 22 = Z_to_bv 64 (cfp + 22) -> getr regs 24 = Z_to_bv 64 (SB + (cfp + 22) / 8) ->
getr regs 27 = Z_to_bv 64 pint -> getr regs 19 = Z_to_bv 64 0 ->
getr regs 9 = Z_to_bv 64 (sp0 - 320) -> val_mem SEGS (mrestrict (w_H W) memc) (sp0 - 320 + 176) 8 SB ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0xce4)) memc (seg_rom SEGS)) mdc)
(il_done W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h).
Proof.
intros W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos
Hw Hh Hnp HNi HJ Hpin Himg Hpawr Hsep HsepC Hrh HAR0 Hfin Hcid0 Hfal Hflo Hfhi Hcal HRA Mimg Mw Mh Hsp H46 H47 Hgp Htp
H23 H26 H21 H25 H22 H24 H27 H19 H9 MSB.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _ & Hbot & Htop & Htop2).
assert (FFS : TRAWADD_STK = 17040) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W0 mem0 md0 cid pos HAR0 Hfin) as (Hf4096 & Hfceil & Hfhigh).
pose proof (req_size_pos' npint ltac:(nia)) as [_ Hrnp].
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc pint npint HAR Hpin) as (_ & Hp4096 & Hpceil & _).
assert (Hslot : forall (mm : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (sp0 - 320 + 176) 8 SB).
{ intros mm Hmm. apply (il_slot_kept (w_H W) memc mm (sp0 - 320 - ESTACK) (sp0 - 320) pint (w * h) (sp0 - 320 + 176) SB Hmm);
[ clear - H46; lia | clear - H47; lia | left; clear - Hpceil Hrnp Hnp Hceil Hslo Hstk0 FFS; lia | right; clear; lia | exact MSB ]. }
assert (Hkept : forall (mm : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mm a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict (w_H W) mm) (cfp + 22) 2 h).
{ intros mm Hmm. apply (il_cells_kept (w_H W) memc mm (sp0 - 320 - ESTACK) (sp0 - 320) pint (w * h) cfp img w h Hmm);
[ clear - Hf4096 Hflo; lia | clear - Hfhi Hfceil C1; lia | clear - HsepC Hrnp Hnp; lia | left; clear - Hfceil Hfhi Hceil Hslo Hstk0 FFS C1; unfold ESTACK; lia
| exact (conj Mimg (conj Mw Mh)) ]. }
eapply SRr_bind.
{ eapply (ra_iln1 B LAWS AMEMCPY (Z.to_nat h) 0 0 W regs memc mdc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ lia | lia | lia | intros j Hj Hij; lia
| exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg | exact Mw | exact Mh
| exact Hsp | exact H46 | exact H47 | exact Hgp | exact Htp
| exact H23 | exact H26 | exact H21 | exact H25 | exact H22 | exact H24
| rewrite H27; f_equal; lia | exact H19 ]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & mm & -> & HJ3 & Hm1 & Hm2 & Hm3 & P27 & P20 & P11 & HK3 & Hout3 & Hpres3).
pose proof (il_rows1 h mm ltac:(lia) Hm1 Hm2 Hm3) as Emm.
destruct (Hkept mem3 Hout3) as (Mimg3 & Mw3 & Mh3).
eapply SRr_mono; [| intros W' c' _; apply (il_at_after _ _ _ W regs regs3 memc mem3 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h HK3 Hout3 Hpres3)].
eapply SRr_bind.
{ eapply (ra_ilS2 W regs3 mem3 md3 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ3 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg3 | exact Mw3 | exact Mh3
| unfold spZ; rewrite (HK3 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK3 3%bv eq_refl); exact Hgp | rewrite (HK3 4%bv eq_refl); exact Htp
| rewrite (HK3 23%bv eq_refl); exact H23 | rewrite (HK3 26%bv eq_refl); exact H26 | rewrite (HK3 21%bv eq_refl); exact H21
| rewrite (HK3 25%bv eq_refl); exact H25 | rewrite (HK3 22%bv eq_refl); exact H22 | rewrite (HK3 24%bv eq_refl); exact H24
| rewrite P27; f_equal; rewrite <- Emm; lia | rewrite P20; f_equal; rewrite <- Emm; lia | exact P11
| rewrite (HK3 9%bv eq_refl); exact H9 | exact (Hslot mem3 Hout3) ]. }
cbv beta. intros W4 c4 Hwle4 (-> & regs4 & mem4 & md4 & -> & HJ4 & Q27 & Q20 & Q10 & HK4 & Hout4 & Hpres4).
assert (HK4' : forall r : bv 5, reg_in r IL_CLOB = false -> getr regs4 r = getr regs r) by (intros r Hr; rewrite (HK4 r Hr); exact (HK3 r Hr)).
assert (Hout4' : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) memc a) by (intros a Ha Hna Hnb; rewrite (Hout4 a Ha Hna Hnb); exact (Hout3 a Ha Hna Hnb)).
destruct (Hkept mem4 Hout4') as (Mimg4 & Mw4 & Mh4).
eapply SRr_mono; [| intros W' c' _; apply (il_at_after _ _ _ W regs3 regs4 mem3 mem4 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h HK4 Hout4 Hpres4)].
eapply SRr_bind.
{ eapply (ra_ilS3 W regs4 mem4 md4 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ4 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg4 | exact Mw4 | exact Mh4
| unfold spZ; rewrite (HK4' 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK4' 3%bv eq_refl); exact Hgp | rewrite (HK4' 4%bv eq_refl); exact Htp
| rewrite (HK4' 23%bv eq_refl); exact H23 | rewrite (HK4' 26%bv eq_refl); exact H26 | rewrite (HK4' 21%bv eq_refl); exact H21
| rewrite (HK4' 25%bv eq_refl); exact H25 | rewrite (HK4' 22%bv eq_refl); exact H22 | rewrite (HK4' 24%bv eq_refl); exact H24
| exact Q27 | exact Q20 | exact Q10 | rewrite (HK4' 9%bv eq_refl); exact H9 | exact (Hslot mem4 Hout4') ]. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & T27 & T20 & T10 & HK5 & Hout5 & Hpres5).
assert (HK5' : forall r : bv 5, reg_in r IL_CLOB = false -> getr regs5 r = getr regs r) by (intros r Hr; rewrite (HK5 r Hr); exact (HK4' r Hr)).
assert (Hout5' : forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem5 a = aview SEGS (w_H W) memc a) by (intros a Ha Hna Hnb; rewrite (Hout5 a Ha Hna Hnb); exact (Hout4' a Ha Hna Hnb)).
destruct (Hkept mem5 Hout5') as (Mimg5 & Mw5 & Mh5).
eapply SRr_mono; [| intros W' c' _; apply (il_at_after _ _ _ W regs4 regs5 mem4 mem5 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h HK5 Hout5 Hpres5)].
eapply (ra_ilS4 W regs5 mem5 md5 sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint npint img Nimg w h cfp cid pos);
[ exact Hw | exact Hh | exact Hnp | exact HNi | exact HJ5 | exact Hpin | exact Himg | exact Hpawr | exact Hsep | exact HsepC | exact Hrh
| exact HAR0 | exact Hfin | exact Hcid0 | exact Hfal | exact Hflo | exact Hfhi | exact Hcal | exact HRA | exact Mimg5 | exact Mw5 | exact Mh5
| unfold spZ; rewrite (HK5' 2%bv eq_refl); exact Hsp | exact H46 | exact H47
| rewrite (HK5' 3%bv eq_refl); exact Hgp | rewrite (HK5' 4%bv eq_refl); exact Htp
| rewrite (HK5' 23%bv eq_refl); exact H23 | rewrite (HK5' 26%bv eq_refl); exact H26 | rewrite (HK5' 21%bv eq_refl); exact H21
| rewrite (HK5' 25%bv eq_refl); exact H25 | rewrite (HK5' 22%bv eq_refl); exact H22 | rewrite (HK5' 24%bv eq_refl); exact H24
| exact T27 | exact T20 | exact T10 | rewrite (HK5' 9%bv eq_refl); exact H9 | exact (Hslot mem5 Hout5') ].
Qed.
End f.
End e.
End d.
