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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4a YC80 YC1f YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC4b YI00 YO07 YI0i YI03 YI6c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC88.
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
Lemma U_byte0a : forall E ny nx no Y0 X off,
ew E ny = Z_to_bv 64 Y0 -> ew E nx = Z_to_bv 64 X -> ew E no = Z_to_bv 64 off ->
0 <= Y0 < 256 -> 0 <= X < 65536 -> 0 <= off <= 7 ->
U E (SAlu ALU_OR (SOff ny 0) (SAluw ALU_SLL (SOff nx 0) (SOff no 0))) mod 256 = Z.lor Y0 ((X * 2 ^ off) mod 256).
Proof.
intros E ny nx no Y0 X off Hy Hx Ho RY RX Ro.
rewrite U_SAlu. cbn [zalu_raw]. rewrite mod256_zcanon, mod256_lor.
rewrite (U_atom E ny Y0 Hy) by lia. rewrite (Z.mod_small Y0) by lia. f_equal.
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
rewrite mod256_mod_pow2, mod256_swrap by (cbn; lia).
rewrite (U_atom E no off Ho) by lia. rewrite (Z.mod_small off) by lia.
replace (Z.land off 31) with off by (symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
rewrite Z.shiftl_mul_pow2 by lia. rewrite Zmult_mod, mod256_mod_pow2 by lia.
rewrite (U_atom E nx X Hx) by lia. rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma addiw1_word : forall i, 0 <= i < 2 ^ 31 - 1 ->
sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 i)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (i + 1).
Proof.
intros i Hi. set (E0 := mkEnv (fun _ => Z_to_bv 64 i) (fun _ => @nil byte)).
pose proof (U_addw1 E0 0 i eq_refl Hi) as HU. unfold U in HU. cbn [sv_denot] in HU.
change (ew E0 0) with (Z_to_bv 64 i) in HU. rewrite unsigned_lit_small, Z.add_0_r in HU by lia.
apply bv_eq. rewrite HU, unsigned_lit_small by lia. reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Lemma TR12_okX : forall regs ly S W mem md lz Llz i (w1 : word) X,
AR SEGS B ly S W mem md -> In (lz, Llz) (ablocks B ly S) ->
getr regs 12 = Z_to_bv 64 (lz + 2 * i) -> 0 <= i -> 2 * i + 2 <= Llz ->
val_mem SEGS (mrestrict (w_H W) mem) (lz + 2 * i) 2 X -> 0 <= X < 2 ^ 16 ->
forall extra, region_ok SEGS (Eimg (Ereg regs (w1 :: Z_to_bv 64 X :: extra))) (mrestrict (w_H W) mem) TR12.
Proof.
intros regs ly S W mem md lz Llz i w1 X HAR Hlz H12 Hi HiL HV HX.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (_ & _ & Hlzceil & Hlzh_ia & Hlzpres & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
assert (HP : forall j, 0 <= j < 2 -> YO0d.present (mrestrict (w_H W) mem) (lz + 2 * i + j)).
{ intros j Hj. destruct (Hlzpres (lz + 2 * i + j) ltac:(lia)) as [[Hh [bb0 Hb0]] _].
exists bb0. unfold mrestrict. rewrite Hh. exact Hb0. }
intros extra. change (2 ^ 16) with 65536 in HX.
unfold region_ok, TR12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
eimg_low; rewrite (ew_Ereg_nat regs _ 12 12%bv) by (vm_compute; reflexivity). rewrite H12, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
eapply chunk_ok_val; [| exact HX | cbn; lia | rewrite Z.add_0_r; exact HV].
cbn [sv_denot]. eimg_low; rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma TR32_okX : forall regs ly S W mem md bl Lby bp w2 Y0,
AR SEGS B ly S W mem md -> In (bl, Lby) (ablocks B ly S) ->
0 <= bp -> bp + 3 <= Lby ->
val_mem SEGS (mrestrict (w_H W) mem) (bl + bp) 1 Y0 -> 0 <= Y0 < 256 ->
exists Y1 Y2, 0 <= Y1 < 256 /\ 0 <= Y2 < 256 /\
forall extra, region_ok SEGS (Eimg (Ereg regs (Z_to_bv 64 (bl + bp) :: w2 :: Z_to_bv 64 Y0 :: Z_to_bv 64 Y1 :: Z_to_bv 64 Y2 :: extra)))
(mrestrict (w_H W) mem) TR32.
Proof.
intros regs ly S W mem md bl Lby bp w2 Y0 HAR Hbl Hbp HbpL HV0 HY0.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (_ & _ & Hblceil & Hblh_ia & Hblpres & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB.
assert (HP : forall j, 0 <= j < 3 -> YO0d.present (mrestrict (w_H W) mem) (bl + bp + j)).
{ intros j Hj. destruct (Hblpres (bl + bp + j) ltac:(lia)) as [[Hh [bb0 Hb0]] _].
exists bb0. unfold mrestrict. rewrite Hh. exact Hb0. }
destruct (val_mem1 SEGS (mrestrict (w_H W) mem) (bl + bp + 1)) as (Y1 & HY1 & HV1); [apply HP; lia|].
destruct (val_mem1 SEGS (mrestrict (w_H W) mem) (bl + bp + 2)) as (Y2 & HY2 & HV2); [apply HP; lia|].
exists Y1, Y2. split; [exact HY1|]. split; [exact HY2|]. intros extra.
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
Lemma tcbl_segAX : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc (nreg dict : Z),
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 9 = Z_to_bv 64 b -> getr regs 31 = Z_to_bv 64 Lc ->
getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
getr regs 8 = Z_to_bv 64 nreg -> getr regs 6 = Z_to_bv 64 dict -> 0 <= nreg < 2 ^ 62 -> 0 <= dict < 2 ^ 31 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_cbl_B)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
tcbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 11 = Z_to_bv 64 (lz + 2 * i) /\ getr regs' 12 = Z_to_bv 64 (lz + 2 * i) /\
getr regs' 17 = Z_to_bv 64 bp /\ getr regs' 9 = Z_to_bv 64 b /\ getr regs' 29 = Z_to_bv 64 (lzwPos - i) /\
getr regs' 31 = Z_to_bv 64 L' /\ 0 <= L' <= 12 /\
(forall r, In r TKEPT -> getr regs' r = getr regs r) /\
(forall x, mem' x = memc x) /\
(let g := (Lc <? 12) && (nreg mod 65536 - D =? dict) in
L' = (if g then Lc + 1 else Lc) /\ getr regs' 8 = Z_to_bv 64 (if g then 2 * nreg else nreg) /\ getr regs' 6 = Z_to_bv 64 dict)).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc nreg dict
HJ Hbl Hlz Hfix Hcf H11 H12 H17 H9 H31 H29 Hi Hbp HbpL Hb HLc H8 H6 Hnreg Hdict.
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
assert (HE8 : ew E 8 = Z_to_bv 64 nreg) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 8 8%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H8).
assert (HE6 : ew E 6 = Z_to_bv 64 dict) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 6 6%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H6).
assert (HE13 : ew E 13 = Z_to_bv 64 D) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 13 13%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact (proj1 (proj2 Hfix))).
assert (HS : st_ok_pi SEGS VAL E ss_A (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx, HE. unfold ss_A. apply pa_entry_st_ok_full.
- apply regs_ok_tcbl; assumption.
- reflexivity.
- constructor.
- exact I.
- split; [|split; [exact I | exact I]]. unfold tcbl_facts_AB. cbn [f_atoms]. apply atoms_ok_app.
+ eapply (tcbl_core_ok B LAWS regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok, YC4b.PTR, YC1i.PTR. cbn [af_lo af_hi af_al2].
eimg_low; rewrite (ew_Ereg_nat regs _ 9 9%bv) by (vm_compute; reflexivity).
eimg_low; rewrite (ew_Ereg_extra regs _ 0), (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
pose proof asan_consts as (C1 & _ & C3 & _). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3. idtac.
cbn [nth]. rewrite H9, !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia. }
clear HE.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
Local Ltac xnoframe memc :=
let x := fresh "x_" in intros x;
repeat match goal with HF : frame_of _ _ _ ?m2 |- ?m2 x = _ => rewrite (HF x) by (cbn; intros (r0_ & Hr0_ & _); exact Hr0_) end; reflexivity.
Local Ltac leafAX HS HJ HA HE31 Hfix H11 H12 H17 H9 H29 gv HE8 HE6 :=
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ (TKEPT ++ [10; 13; 14; 5; 16; 11; 12; 17; 9; 29]%bv) HS HA ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs restrict] in HK;
let Hq7 := fresh "Hq7" in let Hq28 := fresh "Hq28" in let Hq30 := fresh "Hq30" in
let Hq31 := fresh "Hq31" in
prreg HS (7%bv : bv 5) Hq7; prreg HS (28%bv : bv 5) Hq28; prreg HS (30%bv : bv 5) Hq30;
prreg HS (31%bv : bv 5) Hq31;
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
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|];
split; [xnoframe idtac|];
cbv zeta; lazymatch goal with |- context [ (?lc <? 12) && ?tst ] => replace ((lc <? 12) && tst) with gv end;
[ let Hq8 := fresh "Hq8" in let Hq6 := fresh "Hq6" in
prreg HS (8%bv : bv 5) Hq8; prreg HS (6%bv : bv 5) Hq6;
split; [first [lia | reflexivity] |]; split; [rewrite Hq8; first [rewrite HE8; reflexivity | idtac] | rewrite Hq6, HE6; reflexivity] | ].
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
rename HF into HF0. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
-
tcnorm Hc HE31 HE9.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafAX HS HJ HA HE31 Hfix H11 H12 H17 H9 H29 false HE8 HE6.
symmetry. apply Bool.andb_false_iff. left. apply Z.ltb_ge. lia.
- tcnorm Hc HE31 HE9.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
psrr_branch_tok RUN BR HS SHOK Bspan.
+ paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafAX HS HJ HA HE31 Hfix H11 H12 H17 H9 H29 false HE8 HE6.
rewrite branch_ne_U, (U_growcmp E 8 13 6 nreg D dict HE8 HE13 HE6) in Hc0 by lia.
symmetry. apply Bool.andb_false_iff. right. apply Bool.negb_true_iff in Hc0. exact Hc0.
+ paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B. { apply awr_ok_nil. }
leafAX HS HJ HA HE31 Hfix H11 H12 H17 H9 H29 true HE8 HE6.
{ rewrite HE8, alu64_sll_lit by lia. unfold w64. f_equal. lia. }
rewrite branch_ne_U, (U_growcmp E 8 13 6 nreg D dict HE8 HE13 HE6) in Hc0 by lia.
symmetry. apply Bool.andb_true_iff. split; [apply Z.ltb_lt; lia|]. apply Bool.negb_false_iff in Hc0. exact Hc0.
Qed.
Ltac oblBX HJ HE16 HE11 HE32 Hlz Hbl :=
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
Ltac awrBX HE32 Hbl :=
lazymatch type of Hbl with In (?bl, ?Lby) _ =>
awr_ok_tac;
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 32);
[ reflexivity | cbn [ew ewset Nat.eqb]; rewrite HE32; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; left; split;
[ replace a with (bl + (a - bl)) by lia; apply (inFP_ablocks_fp _ bl Lby); [left; reflexivity | lia]
| exists bl, Lby; split; [exact Hbl | lia] ]
| apply awr_ok_nil ]
end.
Ltac runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl :=
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_C;
[ oblBX HJ HE16 HE11 HE32 Hlz Hbl .. | awrBX HE32 Hbl | ].
Ltac leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix :=
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
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|]
end end end.
Ltac xframeB HE32 lo hi :=
let x := fresh "x_" in let Hx := fresh "Hx_" in intros x Hx;
repeat match goal with HF : frame_of ?E' ?rs ?ma ?mb |- _ =>
rewrite (frame_of_outside E' rs ma mb lo hi x HF) by
(first [ exact Hx
| let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbv [In ss_mem ss_B add_cond TR12 TR32] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [r_base r_wlo r_whi base_val ew ewset Nat.eqb]; first [left; lia | right; rewrite HE32, unsigned_lit_small by lia; lia] |]); destruct Hr ]);
clear HF end;
reflexivity.
Ltac xchunkB HS HE32 HE33 HE34 HE9 k :=
lazymatch type of HE32 with ew _ 32 = Z_to_bv 64 (?bl + ?bp) =>
lazymatch type of HE33 with ew _ 33 = Z_to_bv 64 ?X =>
lazymatch type of HE34 with ew _ 34 = Z_to_bv 64 ?Y0 =>
lazymatch type of HE9 with ew _ 9 = Z_to_bv 64 ?b =>
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) =>
eapply (vval_mem_of_chunk_mod SEGS Ex _ _ 32%nat (bl + bp) k 1%N);
[ exact (st_ok_region_nth Ex (abs_ss VAL ss) (restrict H msx) 1 _ HS eq_refl) | reflexivity
| cbv [YP09.r_chunks In]; first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity]
| cbn [ew ewset Nat.eqb]; rewrite HE32; apply unsigned_lit_small; lia
| lazymatch goal with
| |- bv_unsigned (sv_denot _ (SAlu ALU_OR _ _)) mod _ = _ =>
apply (U_byte0a _ 34 33 9 Y0 X b); [cbn [ew ewset Nat.eqb]; exact HE34 | cbn [ew ewset Nat.eqb]; exact HE33 | cbn [ew ewset Nat.eqb]; exact HE9 | lia | lia | lia]
| |- bv_unsigned (sv_denot _ (SAluw ALU_SRL _ (SAlu ALU_SUB _ (SOff _ (-8))))) mod _ = _ =>
apply (U_spill _ 33 9 X b 8); [cbn [ew ewset Nat.eqb]; exact HE33 | cbn [ew ewset Nat.eqb]; exact HE9 | lia | lia | left; reflexivity]
| |- bv_unsigned (sv_denot _ (SAluw ALU_SRL _ (SAlu ALU_SUB _ (SOff _ (-16))))) mod _ = _ =>
apply (U_spill _ 33 9 X b 16); [cbn [ew ewset Nat.eqb]; exact HE33 | cbn [ew ewset Nat.eqb]; exact HE9 | lia | lia | right; reflexivity]
| |- bv_unsigned (sv_denot _ (SLit 0)) mod _ = _ => reflexivity
| |- ?g => fail 1 "xchunkB: unexpected chunk expression" g
end
| cbn; lia ] end end end end end.
Ltac xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP XL :=
lazymatch type of HE32 with ew ?E 32 = Z_to_bv 64 (?bl + ?bp) =>
lazymatch type of HE33 with ew _ 33 = Z_to_bv 64 ?X =>
lazymatch type of HE34 with ew _ 34 = Z_to_bv 64 ?Y0 =>
lazymatch type of HE9 with ew _ 9 = Z_to_bv 64 ?b =>
lazymatch type of HE31 with ew _ 31 = Z_to_bv 64 ?Lc =>
lazymatch type of GB with garr8 _ _ _ (?P ++ _) =>
lazymatch goal with |- (forall x : word, _ -> ?m2 x = ?m1 x) /\ _ =>
let FR := fresh "FR" in
assert (FR : forall x : word, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> m2 x = m1 x) by (xframeB HE32 (bl + bp) (bl + bp + 3));
split; [exact FR|];
let EPK := fresh "EPK" in let ECR := fresh "ECR" in
pose proof (pk_pack_shape P Y0 b Lc X) as (EPK & ECR); cbv zeta in EPK, ECR;
rewrite <- (length_rev (fst (pk_pack (Y0 :: rev P) b Lc X))), EPK, ECR, length_app;
repeat (first [ rewrite (proj2 (Z.ltb_lt (Lc + b) _)) by XL | rewrite (proj2 (Z.ltb_ge (Lc + b) _)) by XL
| rewrite (proj2 (Z.eqb_eq (Lc + b) _)) by XL | rewrite (proj2 (Z.eqb_neq (Lc + b) _)) by XL ]);
cbn [length orb app];
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ => lazymatch type of HA with env_agree 32 ?E0 _ =>
let HA' := fresh "HA'" in let HK := fresh "HKx" in
assert (HA' : env_agree 32 E0 E') by env_agree_chain HA;
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ [8; 6]%bv HS HA' ltac:(vm_compute; reflexivity)) as HK; cbn [ms_regs restrict] in HK;
split; [| split; [clear - LenP; lia | split; [reflexivity | split; kreg HK ]]] end end;
apply garr8_app; split;
[ eapply garr8_frame; [exact (proj1 (proj1 (garr8_app _ _ _ _ _) GB))|];
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold mbyte, mrestrict; rewrite (FR (Z_to_bv 64 a)); [reflexivity|]; rewrite unsigned_lit_small by lia; lia
| rewrite LenP; replace (bl + bp) with (bl + bp + 0) by lia;
let rng := first [apply lor_byte; [lia | apply Z.mod_pos_bound; lia] | apply Z.mod_pos_bound; lia | lia] in
apply garr8_cons_x; [xchunkB HS HE32 HE33 HE34 HE9 0 | rng | replace (bl + bp + 0 + 1) with (bl + bp + 1) by (clear; lia)];
first [ apply garr8_nil
| apply garr8_cons_x; [xchunkB HS HE32 HE33 HE34 HE9 1 | rng | replace (bl + bp + 1 + 1) with (bl + bp + 2) by (clear; lia)];
first [ apply garr8_nil
| apply garr8_cons_x; [xchunkB HS HE32 HE33 HE34 HE9 2 | rng | apply garr8_nil] ] ] ]
end end end end end end end.
Lemma tcbl_segBX : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc (P : list Z) (Y0 X : Z),
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
(bl + req_size Lby <= lz \/ lz + req_size Llz <= bl) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 9 = Z_to_bv 64 b -> getr regs 31 = Z_to_bv 64 Lc ->
getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> bp + 3 <= Lby -> 0 <= b <= 7 -> 0 <= Lc <= 12 ->
garr8 SEGS (mrestrict (w_H W) memc) bl (P ++ [Y0]) -> Z.of_nat (length P) = bp ->
val_mem SEGS (mrestrict (w_H W) memc) (lz + 2 * i) 2 X -> 0 <= X < 65536 ->
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
(forall r, In r TKEPT -> getr regs' r = getr regs r) /\
(forall x : word, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> mem' x = memc x) /\
garr8 SEGS (mrestrict (w_H W) mem') bl (rev (fst (pk_pack (Y0 :: rev P) b Lc X))) /\
Z.of_nat (length (fst (pk_pack (Y0 :: rev P) b Lc X))) = bp + sB + 1 /\
corr = (if snd (pk_pack (Y0 :: rev P) b Lc X) then -1 else 0) /\
getr regs' 8 = getr regs 8 /\ getr regs' 6 = getr regs 6).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp b Lc P Y0 X
HJ Hbl Hlz Hdisj Hfix Hcf H11 H12 H17 H9 H31 H29 Hi Hbp HbpL Hb HLc GB LenP HVX HX65.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hfix as (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 HJ) as HAR. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
assert (HGY : val_mem SEGS (mrestrict (w_H W) memc) (bl + bp) 1 Y0 /\ 0 <= Y0 < 256).
{ pose proof (GB (length P) ltac:(rewrite length_app; cbn [length]; lia)) as Q. rewrite app_nth2, Nat.sub_diag in Q by lia. cbn [nth] in Q. rewrite LenP in Q. exact Q. }
destruct HGY as [HVY0 HY0]. assert (HX : 0 <= X < 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
pose proof (TR12_okX regs ly S W memc mdc lz Llz i (Z_to_bv 64 (bl + bp)) X HAR Hlz H12 ltac:(lia) ltac:(lia) HVX HX) as HR12.
destruct (TR32_okX regs ly S W memc mdc bl Lby bp (Z_to_bv 64 X) Y0 HAR Hbl ltac:(lia) HbpL HVY0 HY0) as (Y1 & Y2 & HY1 & HY2 & HR32).
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
* rewrite HE. eapply (tcbl_core_ok B LAWS regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
* cbn [atoms_ok]. unfold afact_ok, YC4b.PTR, YC1i.PTR. cbn [af_lo af_hi af_al2]. ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg. rewrite ?C3. idtac.
rewrite HE9, HE32. rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; lia.
+ cbn [f_alias tcbl_alias alias_ok]. split; [|exact I].
apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 10 bl HE10), (U_atom E 17 bp HE17), (U_atom E 32 (bl + bp) HE32) by lia.
apply zcanon_id. unfold M64. lia. }
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 Y0) by (rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 2); reflexivity).
clear HE HR12 HR32.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9; runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
-   leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix. xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP ltac:(clear - Hc Hb HLc; lia).
- psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc0 HE31 HE9; runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
+   psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc1 HE31 HE9; runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
*   psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc2 HE31 HE9; runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
--   leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix. xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP ltac:(clear - Hc Hc0 Hc1 Hc2 Hb HLc; lia).
--   leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix. xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP ltac:(clear - Hc Hc0 Hc1 Hc2 Hb HLc; lia).
*   leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix. xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP ltac:(clear - Hc Hc0 Hc1 Hb HLc; lia).
+   leafBX HS HJ HA HE31 HE9 HE17 HE11 HE16 Hfix. xleafB HS HA HE32 HE33 HE34 HE9 HE31 GB LenP ltac:(clear - Hc Hc0 Hb HLc; lia).
Qed.
Ltac leafCX HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht :=
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
split; [intros r Hr; apply HK; apply in_app_iff; left; exact Hr|]
end end end end end.
Ltac runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl tgt :=
paj_run_to_tok RUNTO HS HJ SHOK Bspan tgt;
[ oblBX HJ HE16 HE11 HE32 Hlz Hbl .. | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] | ].
Ltac xleafC HS HE33 HE13 HE8 HE6 HE5 :=
lazymatch type of HE33 with ew ?E 33 = Z_to_bv 64 ?X =>
lazymatch type of HE13 with ew _ 13 = Z_to_bv 64 ?D =>
lazymatch type of HE8 with ew _ 8 = Z_to_bv 64 ?nreg =>
lazymatch type of HE6 with ew _ 6 = Z_to_bv 64 ?dict =>
repeat match goal with Hc : branch_taken _ (sv_denot ?E' (SOff 33 0)) (sv_denot _ (SOff 13 0)) = _ |- _ =>
let HE33' := fresh "HE33'" in let HE13' := fresh "HE13'" in
assert (HE33' : ew E' 33 = Z_to_bv 64 X) by (cbn [ew ewset Nat.eqb]; exact HE33);
assert (HE13' : ew E' 13 = Z_to_bv 64 D) by (cbn [ew ewset Nat.eqb]; exact HE13);
first [rewrite branch_ne_U in Hc | rewrite branch_eq_U in Hc];
rewrite (U_atom _ 33 X HE33'), (U_atom _ 13 D HE13') in Hc by lia;
first [ apply (proj1 (Bool.negb_true_iff _)) in Hc | apply (proj1 (Bool.negb_false_iff _)) in Hc | idtac ];
clear HE33' HE13' end;
split; [ let x := fresh "x_" in intros x;
repeat match goal with HF : frame_of _ _ _ ?m2 |- ?m2' _ = _ =>
first [ constr_eq m2 m2'; rewrite (HF x) by (cbn; intros (r0_ & Hr0_ & Hw_); cbv [In ss_mem ss_C add_cond TR12] in Hr0_;
repeat (destruct Hr0_ as [<- | Hr0_]; [cbn [r_wlo r_whi] in Hw_; lia|]); destruct Hr0_)
| fail ] end; reflexivity |];
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msx) =>
let Hq8 := fresh "Hq8" in let Hq6 := fresh "Hq6" in
prreg HS (8%bv : bv 5) Hq8; prreg HS (6%bv : bv 5) Hq6; cbn [ew ewset Nat.eqb] in Hq8, Hq6;
repeat match goal with Hc : (X =? D) = ?bb |- _ => rewrite Hc end;
split; [ first [reflexivity | lia] |];
split; [ rewrite Hq8, ?HE8, ?HE5; first [reflexivity | rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity]
| rewrite Hq6, ?HE6; first [reflexivity | apply addiw1_word; lia | rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity] ]
end end end end end.
Lemma tcbl_segCX : forall W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp t Lc corr (X nreg dict : Z),
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W memc mdc 0 ->
In (bl, Lby) (ablocks B ly S) -> In (lz, Llz) (ablocks B ly S) ->
tcbl_regs_fix regs bl lz lzwPos D C0 -> tcbl_fix Lby Llz lzwPos D C0 ->
getr regs 11 = Z_to_bv 64 (lz + 2 * i) -> getr regs 12 = Z_to_bv 64 (lz + 2 * i) ->
getr regs 17 = Z_to_bv 64 bp -> getr regs 31 = Z_to_bv 64 Lc -> getr regs 29 = Z_to_bv 64 (lzwPos - i) ->
getr regs 19 = Z_to_bv 64 t -> getr regs 20 = Z_to_bv 64 corr ->
getr regs 18 = alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 (lz + 2 * i)) (Z_to_bv 64 3)) (Z_to_bv 64 SB) ->
0 <= i < lzwPos -> 0 <= bp < 2 ^ 29 -> 0 <= t <= 19 -> 0 <= Lc <= 12 ->
val_mem SEGS (mrestrict (w_H W) memc) (lz + 2 * i) 2 X -> 0 <= X < 65536 ->
getr regs 8 = Z_to_bv 64 nreg -> getr regs 6 = Z_to_bv 64 dict -> 0 <= nreg < 2 ^ 62 -> 0 <= dict < 2 ^ 30 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_cbl_C)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md' b' m L',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (if i + 1 =? lzwPos then A_cbl_X else A_cbl_A))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B 0 sp1 (ablocks_fp [(bl, Lby)]) ly S W mem0 md0 [] ly S W mem' md' 0 /\
tcbl_regs_fix regs' bl lz lzwPos D C0 /\
getr regs' 11 = Z_to_bv 64 (lz + 2 * (i + 1)) /\ getr regs' 12 = Z_to_bv 64 (lz + 2 * (i + 1)) /\
getr regs' 17 = Z_to_bv 64 bp /\ getr regs' 20 = Z_to_bv 64 corr /\ getr regs' 29 = Z_to_bv 64 (lzwPos - (i + 1)) /\
getr regs' 9 = Z_to_bv 64 b' /\ getr regs' 31 = Z_to_bv 64 L' /\
t = 8 * m + b' /\ 0 <= b' < 8 /\ 0 <= L' <= 12 /\
(forall r, In r TKEPT -> getr regs' r = getr regs r) /\
(forall x, mem' x = memc x) /\
L' = (if X =? D then C0 else Lc) /\ getr regs' 8 = Z_to_bv 64 (if X =? D then 2 * D else nreg) /\
getr regs' 6 = Z_to_bv 64 (if X =? D then 1 else dict + 1)).
Proof.
intros W regs memc mdc sp1 mem0 md0 ly S bl Lby lz Llz lzwPos D C0 i bp t Lc corr X nreg dict
HJ Hbl Hlz Hfix Hcf H11 H12 H17 H31 H29 H19 H20 H18 Hi Hbp Ht HLc HVX HX65 H8 H6 Hnreg Hdict.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Hfix as (H10 & H13 & H14 & H5 & H16 & H7 & H28 & H30). pose proof Hcf as (F1 & F2 & F3 & F4 & F5).
pose proof (proj1 HJ) as HAR. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby HAR Hbl) as (Hbl16 & _ & Hblceil & Hblh_ia & _ & _). pose proof (proj1 Hblh_ia) as Hblh.
pose proof (blk_off_imgP _ _ _ _ _ _ bl Lby HAR Hbl) as Hblh_img.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz HAR Hlz) as (Hlz16 & _ & Hlzceil & Hlzh_ia & _ & _). pose proof (proj1 Hlzh_ia) as Hlzh.
pose proof (blk_off_imgP _ _ _ _ _ _ lz Llz HAR Hlz) as Hlzh_img.
pose proof (req_size_pos' Lby ltac:(lia)) as HrB. pose proof (req_size_pos' Llz ltac:(lia)) as HrL.
assert (HX : 0 <= X < 2 ^ 16) by (change (2 ^ 16) with 65536; lia).
pose proof (TR12_okX regs ly S W memc mdc lz Llz i (Z_to_bv 64 0) X HAR Hlz H12 ltac:(lia) ltac:(lia) HVX HX (@nil word)) as HR12.
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
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE8 : ew E 8 = Z_to_bv 64 nreg) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 8 8%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H8).
assert (HE6 : ew E 6 = Z_to_bv 64 dict) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 6 6%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact H6).
assert (HE13 : ew E 13 = Z_to_bv 64 D) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 13 13%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact (proj1 (proj2 Hfix))).
assert (HE5 : ew E 5 = Z_to_bv 64 (2 * D)) by (rewrite HE, Eimg_low, (ew_Ereg_nat regs _ 5 5%bv) by (first [vm_compute; reflexivity | unfold A_TEXT; lia]); exact (proj1 (proj2 (proj2 (proj2 Hfix))))).
assert (HS : st_ok_pi SEGS VAL E ss_C (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_C)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_C. apply pa_entry_st_ok_full.
- apply regs_ok_pin; [rewrite HE; apply regs_ok_tcbl; assumption | intros X'; discriminate X' |].
unfold sv_s2. cbn [sv_denot]. rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, HE11, HE16. exact H18.
- vm_compute. reflexivity.
- constructor; [exact HR12 | constructor].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
unfold tcbl_facts_C. cbn [f_atoms]. apply atoms_ok_app.
+ rewrite HE. eapply (tcbl_core_ok B LAWS regs _ ly S W memc _ bl Lby lz Llz lzwPos D C0 i bp Lc); try eassumption; lia.
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE19. rewrite HE; eimg_low; rewrite (ew_Ereg_extra regs _ 1). cbn [nth]. rewrite !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
clear HE HR12.
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
psrr_branch_tok RUN BR HS SHOK Bspan; runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
-
psrr_branch_tok RUN BR HS SHOK Bspan.
+ runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A. leafCX HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht. xleafC HS HE33 HE13 HE8 HE6 HE5.
+ runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X. leafCX HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht. xleafC HS HE33 HE13 HE8 HE6 HE5.
-
psrr_branch_tok RUN BR HS SHOK Bspan.
+ runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A. leafCX HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht. xleafC HS HE33 HE13 HE8 HE6 HE5.
+ runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X. leafCX HS HJ HA HE31 HE19 HE14 HE11 HE12 HE29 Hfix Ht. xleafC HS HE33 HE13 HE8 HE6 HE5.
Qed.
End h.
End f.
End d.
