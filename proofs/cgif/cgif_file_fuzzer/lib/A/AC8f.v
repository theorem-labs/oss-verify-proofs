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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_asan3_1_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition A_cbl : Z := AF_asan3_create_byte_list.
Definition A_cbl_A : Z := 0x2668.
Definition A_cbl_B : Z := 0x2688.
Definition A_cbl_C : Z := 0x2788.
Definition A_cbl_X : Z := 0x2840.
Definition TCBL_STK : Z := 80.
Ltac tcnorm H HE31 HE9 :=
first [ rewrite branch_ltu_U in H | rewrite branch_geu_U in H | rewrite branch_eq_U in H | rewrite branch_ne_U in H ];
lazymatch type of H with context [U ?E' _] =>
lazymatch type of HE31 with ew _ 31 = ?v31 => lazymatch type of HE9 with ew _ 9 = ?v9 =>
let HE31' := fresh "HE31'" in let HE9' := fresh "HE9'" in
assert (HE31' : ew E' 31 = v31) by (cbn [ew ewset Nat.eqb]; exact HE31);
assert (HE9' : ew E' 9 = v9) by (cbn [ew ewset Nat.eqb]; exact HE9);
rewrite ?(U_t6 _ 31 _ _ 9 _ HE31' HE9') in H by lia;
rewrite ?(U_and255 _ 31 _ _ HE31') in H by lia;
clear HE31' HE9'
end end end;
rewrite ?U_lit in H by lia0;
first [ apply Z.ltb_lt in H | apply Z.ltb_ge in H | apply Z.eqb_eq in H | apply Z.eqb_neq in H
| apply (proj1 (Bool.negb_true_iff _)) in H; first [apply Z.ltb_ge in H | apply Z.eqb_neq in H]
| apply (proj1 (Bool.negb_false_iff _)) in H; first [apply Z.ltb_lt in H | apply Z.eqb_eq in H] ].
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Definition sr_tcbl : list sv := sr_set (sr_set (sr_set sr_atoms 7%bv (SLit 11)) 28%bv (SLit 8)) 30%bv (SLit 16).
Lemma regs_ok_tcbl : forall regs extra,
getr regs 7 = Z_to_bv 64 11 -> getr regs 28 = Z_to_bv 64 8 -> getr regs 30 = Z_to_bv 64 16 ->
regs_ok (Eimg (Ereg regs extra)) sr_tcbl regs.
Proof.
intros regs extra H7 H28 H30. unfold sr_tcbl.
repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]).
apply regs_ok_Eimg_Ereg.
Qed.
Definition BxC : sv := SOff 16 0.
Definition tcbl_core : list (nat * afact) :=
[ (10%nat, PTR 4); (11%nat, PTR 0); (12%nat, PTR 0); (13%nat, mkAF 0 65535 0); (14%nat, mkAF 0 12 0);
(5%nat, mkAF 0 131070 0); (17%nat, mkAF 0 (2^29) 0); (31%nat, mkAF 0 12 0); (16%nat, mkAF SB SB 0);
(29%nat, mkAF 1 (2^28) 0) ].
Definition tcbl_facts_AB : list (nat * afact) :=
tcbl_core ++ [ (9%nat, mkAF 0 7 0); (32%nat, PTR 0); (33%nat, mkAF 0 65535 0);
(34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0); (36%nat, mkAF 0 255 0) ].
Definition tcbl_facts_C : list (nat * afact) := tcbl_core ++ [ (19%nat, mkAF 0 31 0); (33%nat, mkAF 0 65535 0) ].
Definition TR12 : YP09.region := YP09.mkRegion (Some 12%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 2 (SOff 33%nat 0))].
Definition TR32 : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 3 0 3 [YP09.mkChunk 0 (CVal 1 (SOff 34%nat 0)); YP09.mkChunk 1 (CVal 1 (SOff 35%nat 0)); YP09.mkChunk 2 (CVal 1 (SOff 36%nat 0))].
Definition tcbl_alias : list (sv * sv) := [ (SAlu ALU_ADD (SOff 10%nat 0) (SOff 17%nat 0), SOff 32%nat 0) ].
Definition sv_s2 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 11%nat 0) (SLit 3)) (SOff 16%nat 0).
Definition ss_A : sstate := mkSS A_cbl_A sr_tcbl [] None (mkFacts tcbl_facts_AB [] []).
Definition ss_B : sstate := mkSS A_cbl_B sr_tcbl [TR12; TR32] None (mkFacts tcbl_facts_AB [] tcbl_alias).
Definition ss_C : sstate := mkSS A_cbl_C (sr_set sr_tcbl 18%bv sv_s2) [TR12] None (mkFacts tcbl_facts_C [] []).
Definition tcbl_regs_fix (regs : bvmap 5 word) (bl lz lzwPos D C0 : Z) : Prop :=
getr regs 10 = Z_to_bv 64 bl /\ getr regs 13 = Z_to_bv 64 D /\ getr regs 14 = Z_to_bv 64 C0 /\
getr regs 5 = Z_to_bv 64 (2 * D) /\ getr regs 16 = Z_to_bv 64 SB /\
getr regs 7 = Z_to_bv 64 11 /\ getr regs 28 = Z_to_bv 64 8 /\ getr regs 30 = Z_to_bv 64 16.
Definition tcbl_fix (Lby Llz lzwPos D C0 : Z) : Prop :=
0 < lzwPos < 2 ^ 28 /\ 2 * lzwPos <= Llz /\ 3 * lzwPos + 5 <= 2 * Lby /\ 0 <= D <= 65535 /\ 0 <= C0 <= 12.
Definition TREGS_FIX : list (bv 5) := [10; 13; 14; 5; 16; 7; 28; 30]%bv.
Definition TKEPT : list (bv 5) := [1; 2; 3; 4; 24; 25; 26; 27]%bv.
Lemma tcbl_regs_fix_kept : forall regs regs' bl lz lzwPos D C0,
tcbl_regs_fix regs bl lz lzwPos D C0 -> (forall r, In r TREGS_FIX -> getr regs' r = getr regs r) ->
tcbl_regs_fix regs' bl lz lzwPos D C0.
Proof.
intros regs regs' bl lz lzwPos D C0 (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30) HK.
unfold tcbl_regs_fix. rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.
Lemma tcbl_core_ok : forall regs extra ly S W mem md bl Lby lz Llz lzwPos D C0 i bp Lc,
AR SEGS B ly S W mem md -> In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 31 = Z_to_bv 64 Lc -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= Lc <= 12 ->
atoms_ok (Eimg (Ereg regs extra)) tcbl_core.
Proof.
intros regs extra ly S W mem md bl Lby lz Llz lzwPos D C0 i bp Lc HAR Hbl Hlz
(H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30) (F1 & F2 & F3 & F4 & F5) H11 H12 H17 H31 H29 Hi Hbp HLc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
cbn [atoms_ok tcbl_core]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
eimg_low; rewrite (ew_Ereg_nat regs _ 10 10%bv), (ew_Ereg_nat regs _ 11 11%bv), (ew_Ereg_nat regs _ 12 12%bv),
(ew_Ereg_nat regs _ 13 13%bv), (ew_Ereg_nat regs _ 14 14%bv), (ew_Ereg_nat regs _ 5 5%bv),
(ew_Ereg_nat regs _ 17 17%bv), (ew_Ereg_nat regs _ 31 31%bv), (ew_Ereg_nat regs _ 16 16%bv),
(ew_Ereg_nat regs _ 29 29%bv) by (vm_compute; reflexivity).
rewrite H10, H11, H12, H13, H14, H5, H17, H31, H16, H29, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3 in *.
repeat split; try lia.
all: match goal with |- ?g => idtac "COREFACT" g end; fail.
Qed.
Lemma tcbl_segA : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc,
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 9 = Z_to_bv 64 b -> getr regs 31 = Z_to_bv 64 Lc ->
getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbl_B)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
tcbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 11 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 12 = Z_to_bv 64 (lz + 2 * i) /\
getr regs' 17 = Z_to_bv 64 bp /\ getr regs' 9 = Z_to_bv 64 b /\ getr regs' 29 = Z_to_bv 64 (lzwPos - i) /\
getr regs' 31 = Z_to_bv 64 L' /\ 0 <= L' <= 12 /\
(forall r, In r TKEPT -> getr regs' r = getr regs r)).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc
HJ Hbl Hlz Hfix Hcf H11 H12 H17 H9 H31 H29 Hi Hbp HbpL Hb HLc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hfix as (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (_ & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB.
remember (Eimg (Ereg regs [Z_to_bv 64 (bl + bp)])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp)]) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HE31 : ew E 31 = Z_to_bv 64 Lc) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 31 31%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H31).
assert (HE9 : ew E 9 = Z_to_bv 64 b) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 9 9%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H9).
assert (HS : st_ok_pi SEGS VAL E ss_A (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_A. apply pa_entry_st_ok_full.
- apply regs_ok_tcbl; assumption.
- reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]]. unfold tcbl_facts_AB. cbn [f_atoms]. apply atoms_ok_app.
+ eapply (tcbl_core_ok regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
eimg_low; rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity).
eimg_low; rewrite (ew_Ereg_extra regs _ 0), (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
pose proof asan_consts as (C1 & _ & C3 & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3. idtac.
cbn [nth]. rewrite H9, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
clear HE.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
Local Ltac leafA HS HJ HA HE31 Hfix H11 H12 H17 H9 H29 :=
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ (TKEPT ++ [10; 13; 14; 5; 16; 11; 12; 17; 9; 29]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs restrict] in HK;
let Hq7 := fresh "Hq7" in let Hq28 := fresh "Hq28" in let Hq30 := fresh "Hq30" in let Hq31 := fresh "Hq31" in
prreg HS (7%bv : bv 5) Hq7; prreg HS (28%bv : bv 5) Hq28; prreg HS (30%bv : bv 5) Hq30; prreg HS (31%bv : bv 5) Hq31;
rewrite HE31 in Hq31; rewrite ?unsigned_lit_small in Hq31 by lia;
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SRr_ret; split; [reflexivity|];
lazymatch type of Hq31 with getr _ _ = Z_to_bv 64 ?L' =>
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
exists (ms_regs msx), (ms_mem msx), mdx, L' end end;
split; [reflexivity|]; split; [exact HJ|];
destruct Hfix as (?H10 & ?H13 & ?H14 & ?H5 & ?H16 & _ & _ & _);
split; [ unfold tcbl_regs_fix; repeat split; first [kreg HK | exact Hq7 | exact Hq28 | exact Hq30] |];
split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|]; split; [kreg HK|];
split; [exact Hq31|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK Bspan.
-
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafA HS HJ HA HE31 Hfix H11 H12 H17 H9 H29.
- tcnorm Hc HE31 HE9.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK Bspan.
+ paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafA HS HJ HA HE31 Hfix H11 H12 H17 H9 H29.
+ paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafA HS HJ HA HE31 Hfix H11 H12 H17 H9 H29.
Qed.
Lemma TR12_ok : forall regs ly S W mem md lz Llz i (w1 : word),
AR SEGS B ly S W mem md -> In (lz, Llz) (ablocks B ly S) ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> 0 <= i -> 2 * i + 2 <= Llz ->
exists X, 0 <= X < 2 ^ 16 /\
forall extra, region_ok SEGS (Eimg (Ereg regs (w1 :: Z_to_bv 64 X :: extra))) (mrestrict (w_H W) mem) TR12.
Proof.
intros regs ly S W mem md lz Llz i w1 HAR Hlz H12 Hi HiL.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (_ & _ & Hlzceil & Hlzh_ia & Hlzpres & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
assert (HP : forall j, 0 <= j < 2 -> YO0d.present (mrestrict (w_H W) mem) (lz + 2 * i + j)).
{ intros j Hj. destruct (Hlzpres (lz + 2 * i + j) ltac:(lia)) as [[Hh [bb0 Hb0]] _].
exists bb0. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem2 SEGS (mrestrict (w_H W) mem) (lz + 2 * i)) as (X & HX & HV);
[replace (lz + 2 * i) with (lz + 2 * i + 0) by lia; apply HP; lia | apply HP; lia |].
exists X. split; [exact HX|]. intros extra.
unfold region_ok, TR12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
eimg_low; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity). rewrite H12, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [| exact HX | cbn; lia | rewrite Z.add_0_r; exact HV].
cbn [sv_denot]. eimg_low; rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma TR32_ok : forall regs ly S W mem md bl Lby bp w2,
AR SEGS B ly S W mem md -> In (bl, Lby) (ablocks B ly S) ->
0 <= bp -> bp + 3 <= Lby ->
exists Y0 Y1 Y2, 0 <= Y0 < 256 /\ 0 <= Y1 < 256 /\ 0 <= Y2 < 256 /\
forall extra, region_ok SEGS (Eimg (Ereg regs (Z_to_bv 64 (bl + bp) :: w2 :: Z_to_bv 64 Y0 :: Z_to_bv 64 Y1 :: Z_to_bv 64 Y2 :: extra)))
(mrestrict (w_H W) mem) TR32.
Proof.
intros regs ly S W mem md bl Lby bp w2 HAR Hbl Hbp HbpL.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (_ & _ & Hblceil & Hblh_ia & Hblpres & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB.
assert (HP : forall j, 0 <= j < 3 -> YO0d.present (mrestrict (w_H W) mem) (bl + bp + j)).
{ intros j Hj. destruct (Hblpres (bl + bp + j) ltac:(lia)) as [[Hh [bb0 Hb0]] _].
exists bb0. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 SEGS (mrestrict (w_H W) mem) (bl + bp)) as (Y0 & HY0 & HV0); [replace (bl + bp) with (bl + bp + 0) by lia; apply HP; lia|].
destruct (val_mem1 SEGS (mrestrict (w_H W) mem) (bl + bp + 1)) as (Y1 & HY1 & HV1); [apply HP; lia|].
destruct (val_mem1 SEGS (mrestrict (w_H W) mem) (bl + bp + 2)) as (Y2 & HY2 & HV2); [apply HP; lia|].
exists Y0, Y1, Y2. split; [exact HY0|]. split; [exact HY1|]. split; [exact HY2|]. intros extra.
unfold region_ok, TR32. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
eimg_low; rewrite (ew_Ereg_extra regs _ 0). cbn [nth]. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hblpres (bl + bp + o) ltac:(lia))). }
constructor; [|constructor; [|constructor; [|constructor]]].
- eapply chunk_ok_val; [| exact HY0 | cbn; lia | rewrite Z.add_0_r; exact HV0].
cbn [sv_denot]. eimg_low; rewrite (ew_Ereg_extra regs _ 2). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY1 | cbn; lia | exact HV1].
cbn [sv_denot]. eimg_low; rewrite (ew_Ereg_extra regs _ 3). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
- eapply chunk_ok_val; [| exact HY2 | cbn; lia | exact HV2].
cbn [sv_denot]. eimg_low; rewrite (ew_Ereg_extra regs _ 4). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma tcbl_segB : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc,
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
(bl + req_size Lby <= lz \/ lz + req_size Llz <= bl) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 9 = Z_to_bv 64 b -> getr regs 31 = Z_to_bv 64 Lc ->
getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_B)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' sB corr,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbl_C)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
tcbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 11 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 12 = Z_to_bv 64 (lz + 2 * i) /\
getr regs' 17 = Z_to_bv 64 (bp + sB) /\ getr regs' 31 = Z_to_bv 64 Lc /\ getr regs' 29 = Z_to_bv 64 (lzwPos - i) /\
getr regs' 19 = Z_to_bv 64 (b + Lc) /\ getr regs' 20 = Z_to_bv 64 corr /\
getr regs' 18 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (lz + 2 * i)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) /\
(corr = 0 \/ (corr = -1 /\ 1 <= sB)) /\ 0 <= sB <= 2 /\ 8 * sB <= b + Lc < 8 * sB + 8 /\
(forall r, In r TKEPT -> getr regs' r = getr regs r)).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc
HJ Hbl Hlz Hdisj Hfix Hcf H11 H12 H17 H9 H31 H29 Hi Hbp HbpL Hb HLc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hfix as (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 HJ) as HAR. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
destruct (TR12_ok regs ly S W memc mdc lz Llz i (Z_to_bv 64 (bl + bp)) HAR Hlz H12 ltac:(lia) ltac:(lia)) as (X & HX & HR12).
destruct (TR32_ok regs ly S W memc mdc bl Lby bp (Z_to_bv 64 X) HAR Hbl ltac:(lia) HbpL) as (Y0 & Y1 & Y2 & HY0 & HY1 & HY2 & HR32).
specialize (HR12 [Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]). specialize (HR32 (@nil word)).
remember (Eimg (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) E)
by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HE31 : ew E 31 = Z_to_bv 64 Lc) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 31 31%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H31).
assert (HE9 : ew E 9 = Z_to_bv 64 b) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 9 9%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H9).
assert (HE17 : ew E 17 = Z_to_bv 64 bp) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 17 17%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H17).
assert (HE10 : ew E 10 = Z_to_bv 64 bl) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 10 10%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H10).
assert (HE11 : ew E 11 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 11 11%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H11).
assert (HE12 : ew E 12 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 12 12%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H12).
assert (HE16 : ew E 16 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 16 16%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H16).
assert (HE32 : ew E 32 = Z_to_bv 64 (bl + bp)) by (rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HBx : U E BxC = SHADOW_OFF) by (unfold BxC; rewrite (U_atom E 16 SB HE16) by (unfold SB; lia); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_B (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_B)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_B. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_tcbl; assumption.
- vm_compute. reflexivity.
- constructor; [exact HR12 | constructor; [exact HR32 | constructor]].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, TR12, TR32. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE12, HE32, !unsigned_lit_small by lia. repeat split. lia.
- split; [|split; [exact I|]].
+ unfold tcbl_facts_AB. cbn [f_atoms]. apply atoms_ok_app.
* rewrite HE. eapply (tcbl_core_ok regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
* cbn [atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3. idtac.
rewrite HE9, HE32. rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_alias tcbl_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 bl HE10), (U_atom E 17 bp HE17), (U_atom E 32 (bl + bp) HE32) by lia.
apply zcanon_id. unfold M64. lia. }
clear HE HR12 HR32.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
Local Ltac oblB HJ HE16 HE11 HE32 Hlz Hbl :=
lazymatch goal with
| |- range_addressable _ (U ?E' _) (U _ (SOff ?n ?c)) _ =>
let Hn := match n with 11%nat => HE11 | 32%nat => HE32 end in
let Hin := match n with 11%nat => Hlz | 32%nat => Hbl end in
rewrite (U_atom_off E' n _ c) by (first [cbn [ew ewset Nat.eqb]; exact Hn | lia]);
eapply (obl_of_block SEGS B LAWS _ _ _ _ _ E' BxC);
[ exact (proj1 HJ) | exact Hin
| unfold BxC; rewrite (U_atom E' 16 SB); [reflexivity | cbn [ew ewset Nat.eqb]; exact HE16 | unfold SB; lia]
| lia | lia ]
end.
Local Ltac awrB HE32 Hbl :=
lazymatch type of Hbl with In (?bl, ?Lby) _ =>
awr_ok_tac;
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32);
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE32; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
[ replace a with (bl + (a - bl)) by lia; apply (inFP_ablocks_fp _ bl Lby); [left; reflexivity | lia]
| exists bl, Lby; split; [exact Hbl | lia] ]
| apply awr_ok_nil ]
end.
Local Ltac runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl :=
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_C;
[ oblB HJ HE16 HE11 HE32 Hlz Hbl .. | awrB HE32 Hbl | ].
Local Ltac leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix :=
lazymatch type of HE17 with ew ?E 17 = Z_to_bv 64 ?bp =>
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
lazymatch type of HA with env_agree 32 ?E0 _ =>
let HA' := fresh "HA'" in
assert (HA' : env_agree 32 E0 E') by env_agree_chain HA;
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ (TKEPT ++ [10; 13; 14; 5; 16; 11; 12; 31; 29]%bv) HS HA' ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs restrict] in HK;
let Hq7 := fresh "Hq7" in let Hq28 := fresh "Hq28" in let Hq30 := fresh "Hq30" in
let Hq17 := fresh "Hq17" in let Hq20 := fresh "Hq20" in let Hq18 := fresh "Hq18" in let Hq19 := fresh "Hq19" in
let HE31' := fresh "HE31'" in let HE9' := fresh "HE9'" in
prreg HS (7%bv : bv 5) Hq7; prreg HS (28%bv : bv 5) Hq28; prreg HS (30%bv : bv 5) Hq30;
prreg HS (17%bv : bv 5) Hq17; prreg HS (20%bv : bv 5) Hq20; prreg HS (18%bv : bv 5) Hq18;
cbn [ew ewset Nat.eqb] in Hq17, Hq18;
rewrite HE17 in Hq17; rewrite ?unsigned_lit_small in Hq17 by lia;
lazymatch type of Hq17 with _ = Z_to_bv 64 bp => rewrite <- (Z.add_0_r bp) in Hq17 | _ => idtac end;
rewrite ?lit_m1 in Hq20;
rewrite HE11, HE16 in Hq18;
pose proof (st_ok_reg_U SEGS _ _ _ (19%bv : bv 5) HS) as Hq19; cbn [ms_regs restrict] in Hq19;
lazymatch type of Hq19 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Hq19 end;
assert (HE31' : ew E' 31 = ew E 31) by (cbn [ew ewset Nat.eqb]; reflexivity); rewrite HE31 in HE31';
assert (HE9' : ew E' 9 = ew E 9) by (cbn [ew ewset Nat.eqb]; reflexivity); rewrite HE9 in HE9';
rewrite (U_t6 _ 31 _ _ 9 _ HE31' HE9') in Hq19 by lia; rewrite ?Z.add_0_r in Hq19;
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SRr_ret; split; [reflexivity|];
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
eexists (ms_regs msx), (ms_mem msx), mdx, _, _ end;
split; [reflexivity|]; split; [exact HJ|];
destruct Hfix as (?H10 & ?H13 & ?H14 & ?H5 & ?H16 & _ & _ & _);
split; [ unfold tcbl_regs_fix; repeat split; first [kreg HK | exact Hq7 | exact Hq28 | exact Hq30] |];
split; [kreg HK|]; split; [kreg HK|]; split; [exact Hq17|]; split; [kreg HK|]; split; [kreg HK|];
split; [exact Hq19|]; split; [exact Hq20|]; split; [exact Hq18|];
split; [lia|]; split; [lia|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr
end end end.
runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9; runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
-   leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix.
- psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc0 HE31 HE9; runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
+   psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc1 HE31 HE9; runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
*   psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc2 HE31 HE9; runB HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
--   leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix.
--   leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix.
*   leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix.
+   leafB HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix.
Qed.
Lemma tcbl_segC : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp t Lc corr,
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 31 = Z_to_bv 64 Lc -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 19 = Z_to_bv 64 t -> getr regs 20 = Z_to_bv 64 corr ->
getr regs 18 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (lz + 2 * i)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= t <= 19 -> 0 <= Lc <= 12 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_C)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' b' m L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (if i + 1 =? lzwPos then A_cbl_X else A_cbl_A))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
tcbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 11 = Z_to_bv 64 (lz + 2 * (i + 1)) /\ getr regs' 12 = Z_to_bv 64 (lz + 2 * (i + 1)) /\
getr regs' 17 = Z_to_bv 64 bp /\ getr regs' 20 = Z_to_bv 64 corr /\ getr regs' 29 = Z_to_bv 64 (lzwPos - (i + 1)) /\
getr regs' 9 = Z_to_bv 64 b' /\ getr regs' 31 = Z_to_bv 64 L' /\
t = 8 * m + b' /\ 0 <= b' < 8 /\ 0 <= L' <= 12 /\
(forall r, In r TKEPT -> getr regs' r = getr regs r)).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp t Lc corr
HJ Hbl Hlz Hfix Hcf H11 H12 H17 H31 H29 H19 H20 H18 Hi Hbp Ht HLc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hfix as (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 HJ) as HAR. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
destruct (TR12_ok regs ly S W memc mdc lz Llz i (Z_to_bv 64 0) HAR Hlz H12 ltac:(lia) ltac:(lia)) as (X & HX & HR12).
specialize (HR12 (@nil word)).
remember (Eimg (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HA : env_agree 32 (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) E) by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HE31 : ew E 31 = Z_to_bv 64 Lc) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 31 31%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H31).
assert (HE19 : ew E 19 = Z_to_bv 64 t) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 19 19%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H19).
assert (HE14 : ew E 14 = Z_to_bv 64 C0) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 14 14%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H14).
assert (HE11 : ew E 11 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 11 11%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H11).
assert (HE12 : ew E 12 = Z_to_bv 64 (lz + 2 * i)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 12 12%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H12).
assert (HE16 : ew E 16 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 16 16%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H16).
assert (HE29 : ew E 29 = Z_to_bv 64 (lzwPos - i)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 29 29%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H29).
assert (HE32 : ew E 32 = Z_to_bv 64 0) by (rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_C (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_C)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_C. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [rewrite HE; apply regs_ok_tcbl; assumption | intros X'; discriminate X' |].
unfold sv_s2. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, HE11, HE16. exact H18.
- vm_compute. reflexivity.
- constructor; [exact HR12 | constructor].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
unfold tcbl_facts_C. cbn [f_atoms]. apply atoms_ok_app.
+ rewrite HE. eapply (tcbl_core_ok regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE19. rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
clear HE HR12.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
Local Ltac leafC HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht :=
lazymatch type of HE19 with ew ?E 19 = Z_to_bv 64 ?t =>
lazymatch type of HE11 with ew _ 11 = Z_to_bv 64 (?lz + 2 * ?i) =>
lazymatch type of HE29 with ew _ 29 = Z_to_bv 64 (?lzwPos - _) =>
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
lazymatch type of HA with env_agree 32 ?E0 _ =>
let HA' := fresh "HA'" in
assert (HA' : env_agree 32 E0 E') by env_agree_chain HA;
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ (TKEPT ++ [10; 13; 14; 5; 16; 17; 20]%bv) HS HA' ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs restrict] in HK;
let Hq7 := fresh "Hq7" in let Hq28 := fresh "Hq28" in let Hq30 := fresh "Hq30" in
let Hq11 := fresh "Hq11" in let Hq12 := fresh "Hq12" in let Hq29 := fresh "Hq29" in let Hq31 := fresh "Hq31" in let Hq9 := fresh "Hq9" in
let HE19' := fresh "HE19'" in
prreg HS (7%bv : bv 5) Hq7; prreg HS (28%bv : bv 5) Hq28; prreg HS (30%bv : bv 5) Hq30;
prreg HS (11%bv : bv 5) Hq11; prreg HS (12%bv : bv 5) Hq12; prreg HS (29%bv : bv 5) Hq29; prreg HS (31%bv : bv 5) Hq31;
cbn [ew ewset Nat.eqb] in Hq11, Hq12, Hq29, Hq31;
rewrite HE11, unsigned_lit_small in Hq11 by lia; rewrite HE12, unsigned_lit_small in Hq12 by lia;
rewrite HE29, unsigned_lit_small in Hq29 by lia;
first [rewrite HE31 in Hq31 | rewrite HE14 in Hq31];
pose proof (st_ok_reg_U SEGS _ _ _ (9%bv : bv 5) HS) as Hq9; cbn [ms_regs restrict] in Hq9;
lazymatch type of Hq9 with _ = Z_to_bv 64 (U _ (sr_get ?sr ?r)) =>
let e := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e in Hq9 end;
assert (HE19' : ew E' 19 = ew E 19) by (cbn [ew ewset Nat.eqb]; reflexivity); rewrite HE19 in HE19';
rewrite U_and_lit in Hq9 by lia0; rewrite (U_atom _ 19 t HE19') in Hq9 by lia;
let m := fresh "m" in let Hm := fresh "Hm" in
destruct (land7_split t ltac:(lia)) as (m & Hm);
repeat match goal with Hc : branch_taken _ (sv_denot _ (SOff 29 (-1))) (sv_denot _ (SLit 0)) = _ |- _ =>
let HE29' := fresh "HE29'" in
assert (HE29' : ew E' 29 = ew E 29) by (cbn [ew ewset Nat.eqb]; reflexivity); rewrite HE29 in HE29';
first [rewrite branch_ne_U in Hc | rewrite branch_eq_U in Hc];
rewrite (U_atom_off _ 29 (lzwPos - i) (-1) HE29'), U_lit in Hc by lia;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hc | apply (proj1 (Bool.negb_false_iff _)) in Hc | idtac ];
first [ apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc ]; clear HE29' end;
rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SRr_ret; split; [reflexivity|];
lazymatch type of Hq31 with _ = Z_to_bv 64 ?L' =>
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
exists (ms_regs msx), (ms_mem msx), mdx, (Z.land t 7), m, L' end end;
split; [ first [ replace (i + 1 =? lzwPos) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity
| replace (i + 1 =? lzwPos) with true by (symmetry; apply Z.eqb_eq; lia); reflexivity ] |];
split; [exact HJ|];
destruct Hfix as (?H10 & ?H13 & ?H14 & ?H5 & ?H16 & _ & _ & _);
split; [ unfold tcbl_regs_fix; repeat split; first [kreg HK | exact Hq7 | exact Hq28 | exact Hq30] |];
split; [rewrite Hq11; f_equal; lia|]; split; [rewrite Hq12; f_equal; lia|];
split; [kreg HK|]; split; [kreg HK|]; split; [rewrite Hq29; f_equal; lia|];
split; [exact Hq9|]; split; [exact Hq31|];
split; [lia|]; split; [lia|]; split; [lia|];
intros r Hr; apply HK; apply in_app_iff; left; exact Hr
end end end end end.
Local Ltac runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl tgt :=
paj_run_to_tok RUNTO HS HJ SHOK Bspan tgt;
[ oblB HJ HE16 HE11 HE32 Hlz Hbl .. | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] | ].
runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
psrr_branch_tok RUN BR HS SHOK Bspan; runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
-
psrr_branch_tok RUN BR HS SHOK Bspan.
+ runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A. leafC HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht.
+ runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X. leafC HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht.
-
psrr_branch_tok RUN BR HS SHOK Bspan.
+ runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A. leafC HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht.
+ runC HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X. leafC HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht.
Qed.
End h.
End f.
End d.
