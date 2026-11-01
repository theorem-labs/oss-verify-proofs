(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
intros regs ly S W mem md lz Llz i w1 X Hreach Hlzin H12 Hi0 Hroom Hval Hrng extra.
pose proof asan_consts as (Kceil & _).
pose proof (req_size_pos' Llz ltac:(lia)) as RqL.
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz Hreach Hlzin) as (_ & Hlo & Hhi & _).
assert (HB12 : bv_unsigned (ew (Eimg (Ereg regs (w1 :: Z_to_bv 64 X :: extra))) 12) = lz + 2 * i).
{ eimg_low. rewrite (ew_Ereg_nat regs _ 12 (12%bv : bv 5) eq_refl), H12. apply unsigned_lit_small. lia. }
assert (HX33 : sv_denot (Eimg (Ereg regs (w1 :: Z_to_bv 64 X :: extra))) (SOff 33 0) = Z_to_bv 64 X).
{ cbn [sv_denot]. eimg_low. rewrite (ew_Ereg_extra regs _ 1). cbn [nth].
rewrite unsigned_lit_small, Z.add_0_r by lia. reflexivity. }
unfold region_ok, TR12. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HB12. refine (conj _ (conj _ (conj _ _))); [lia | lia | intros o Ho; lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val _ _ _ _ 0 2 (SOff 33 0) X HX33); [exact Hrng | cbn; lia | rewrite Z.add_0_r; exact Hval].
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
HJ Hbl Hlz Pinned Sizes At11 At12 At17 At9 At31 At29 Irange Hbp HbpL Brange Lrange At8 At6 Hnr Hdi.
pose proof HJ as (Hreach & _). pose proof asan_consts as (Kceil & _).
pose proof Sizes as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof Pinned as (F10 & F13 & F14 & F5 & F16 & F7 & F28 & F30).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz Hreach Hlz) as (_ & Hlzlo & Hlzhi & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby Hreach Hbl) as (_ & Hbllo & Hblhi & _).
pose proof (req_size_pos' Llz ltac:(lia)) as RqL. pose proof (req_size_pos' Lby ltac:(lia)) as RqB.
remember (Eimg (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0])) as E eqn:HEdef.
assert (Himg : img_env VAL A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (HS : st_ok_pi SEGS VAL E ss_A (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_A)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. subst E. apply pa_entry_st_ok_full.
- apply regs_ok_tcbl; assumption.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; exact I]. cbn [f_atoms]. unfold tcbl_facts_AB. apply atoms_ok_app.
+ exact (tcbl_core_ok B LAWS regs _ ly S W memc mdc bl Lby lz Llz lzwPos D C0 i bp Lc Hreach Hbl Hlz Pinned Sizes At11 At12 At17 At31 At29 Irange Hbp Lrange).
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. eimg_low.
rewrite (ew_Ereg_nat regs _ 9 (9%bv : bv 5) eq_refl), At9.
rewrite (ew_Ereg_extra regs _ 0), (ew_Ereg_extra regs _ 1), (ew_Ereg_extra regs _ 2), (ew_Ereg_extra regs _ 3), (ew_Ereg_extra regs _ 4).
cbn [nth]. rewrite !unsigned_lit_small by lia. rewrite ?Z.pow_0_r, ?Z.mod_1_r. cbv [YC1i.PTR af_lo af_hi af_al2]. lia. }
assert (HEw : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (AG : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0]) E).
{ subst E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
pose proof (HEw 31%nat 31%bv ltac:(lia) eq_refl) as HE31. rewrite At31 in HE31.
pose proof (HEw 9%nat 9%bv ltac:(lia) eq_refl) as HE9. rewrite At9 in HE9.
pose proof (HEw 8%nat 8%bv ltac:(lia) eq_refl) as HE8. rewrite At8 in HE8.
pose proof (HEw 13%nat 13%bv ltac:(lia) eq_refl) as HE13. rewrite F13 in HE13.
pose proof (HEw 6%nat 6%bv ltac:(lia) eq_refl) as HE6. rewrite At6 in HE6.
assert (SHOK : sh_ok SEGS BxC [] E (mrestrict (w_H W) memc)) by apply Forall_nil.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B; [awr_ok_tac|].
assert (Hm0 : forall x, ms_mem ms x = memc x) by (intros x; apply HF; intros (rg & Hsel & _); vm_compute in Hsel; exact Hsel).
clear HF HFr HG. rename Hm0 into Hm.
psrr_branch_tok RUN BR HS SHOK Bspan.
- tcnorm Hc HE31 HE9.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B; [awr_ok_tac|].
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x. rewrite <- (Hm x). apply HF. intros (rg & Hsel & _). vm_compute in Hsel. exact Hsel. }
clear HF HFr HG Hm. clear ms. rename ms0 into ms. rename Hm0 into Hm.
rewrite ?wvb_collapse in HJ.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ (TKEPT ++ [10%bv; 13%bv; 14%bv; 5%bv; 16%bv; 11%bv; 12%bv; 17%bv; 9%bv; 29%bv; 6%bv; 8%bv; 31%bv])
HS AG ltac:(vm_compute; reflexivity)) as KP.
prreg HS (7%bv : bv 5) R7. prreg HS (28%bv : bv 5) R28. prreg HS (30%bv : bv 5) R30.
pmkst HS. apply SRr_ret. split; [reflexivity|]. do 3 eexists. exists Lc.
split; [reflexivity|]. split; [exact HJ|].
split; [unfold tcbl_regs_fix; rewrite R7, R28, R30, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
repeat split; assumption|].
rewrite !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right])).
split; [exact At11|]. split; [exact At12|]. split; [exact At17|]. split; [exact At9|]. split; [exact At29|]. split; [exact At31|].
split; [lia|].
split; [intros r Hr; apply KP; apply in_or_app; left; exact Hr|].
split; [exact Hm|].
cbv zeta. rewrite (proj2 (Z.ltb_ge Lc 12)) by lia. cbn [andb].
split; [reflexivity|]. split; [exact At8 | exact At6].
- tcnorm Hc HE31 HE9. rename Hc into HcL.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B; [awr_ok_tac|].
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x. rewrite <- (Hm x). apply HF. intros (rg & Hsel & _). vm_compute in Hsel. exact Hsel. }
clear HF HFr HG Hm. clear ms. rename ms0 into ms. rename Hm0 into Hm.
psrr_branch_tok RUN BR HS SHOK Bspan.
+ rewrite branch_ne_U, (U_growcmp E 8 13 6 nreg D dict HE8 HE13 HE6) in Hc by lia.
apply Bool.negb_true_iff in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B; [awr_ok_tac|].
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x. rewrite <- (Hm x). apply HF. intros (rg & Hsel & _). vm_compute in Hsel. exact Hsel. }
clear HF HFr HG Hm. clear ms. rename ms0 into ms. rename Hm0 into Hm.
rewrite ?wvb_collapse in HJ.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ (TKEPT ++ [10%bv; 13%bv; 14%bv; 5%bv; 16%bv; 11%bv; 12%bv; 17%bv; 9%bv; 29%bv; 6%bv; 8%bv; 31%bv])
HS AG ltac:(vm_compute; reflexivity)) as KP.
prreg HS (7%bv : bv 5) R7. prreg HS (28%bv : bv 5) R28. prreg HS (30%bv : bv 5) R30.
pmkst HS. apply SRr_ret. split; [reflexivity|]. do 3 eexists. exists Lc.
split; [reflexivity|]. split; [exact HJ|].
split; [unfold tcbl_regs_fix; rewrite R7, R28, R30, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
repeat split; assumption|].
rewrite !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right])).
split; [exact At11|]. split; [exact At12|]. split; [exact At17|]. split; [exact At9|]. split; [exact At29|]. split; [exact At31|].
split; [lia|].
split; [intros r Hr; apply KP; apply in_or_app; left; exact Hr|].
split; [exact Hm|].
cbv zeta. rewrite Hc, andb_false_r.
split; [reflexivity|]. split; [exact At8 | exact At6].
+ rewrite branch_ne_U, (U_growcmp E 8 13 6 nreg D dict HE8 HE13 HE6) in Hc by lia.
apply Bool.negb_false_iff in Hc.
paj_run_to_tok RUNTO HS HJ SHOK Bspan A_cbl_B; [awr_ok_tac|].
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x. rewrite <- (Hm x). apply HF. intros (rg & Hsel & _). vm_compute in Hsel. exact Hsel. }
clear HF HFr HG Hm. clear ms. rename ms0 into ms. rename Hm0 into Hm.
rewrite ?wvb_collapse in HJ.
pose proof (regs_kept_of_st_ok_pi E _ _ regs _ (TKEPT ++ [10%bv; 13%bv; 14%bv; 5%bv; 16%bv; 11%bv; 12%bv; 17%bv; 9%bv; 29%bv; 6%bv])
HS AG ltac:(vm_compute; reflexivity)) as KP.
prreg HS (7%bv : bv 5) R7. prreg HS (28%bv : bv 5) R28. prreg HS (30%bv : bv 5) R30.
prreg HS (31%bv : bv 5) R31. prreg HS (8%bv : bv 5) R8.
rewrite HE31, unsigned_lit_small in R31 by lia. rewrite HE8, alu64_sll1 in R8 by lia.
pmkst HS. apply SRr_ret. split; [reflexivity|]. do 3 eexists. exists (Lc + 1).
split; [reflexivity|]. split; [exact HJ|].
split; [unfold tcbl_regs_fix; rewrite R7, R28, R30, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
repeat split; assumption|].
rewrite R31, R8, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right])).
split; [exact At11|]. split; [exact At12|]. split; [exact At17|]. split; [exact At9|]. split; [exact At29|]. split; [reflexivity|].
split; [lia|].
split; [intros r Hr; apply KP; apply in_or_app; left; exact Hr|].
split; [exact Hm|].
cbv zeta. rewrite Hc, (proj2 (Z.ltb_lt Lc 12)) by lia. cbn [andb].
split; [reflexivity|]. split; [reflexivity | exact At6].
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
Ltac leafBX HS HJ AG HE31 HE9 HE17 sB corr KP :=
lazymatch type of HS with st_ok_pi _ _ ?E' ?ssf _ =>
lazymatch type of AG with env_agree 32 ?E0 ?E =>
lazymatch type of HE31 with ew _ 31 = Z_to_bv 64 ?Lv =>
lazymatch type of HE9 with ew _ 9 = Z_to_bv 64 ?bv0 =>
let AG' := fresh "AG'" in
assert (AG' : env_agree 32 E0 E') by
(destruct AG as [AG1 AG2]; split;
[ intros n Hn; rewrite <- (AG1 n Hn); repeat rewrite ew_ewset_other by lia; reflexivity
| cbn [ed ewset]; exact AG2 ]);
pose proof (regs_kept_of_st_ok_pi E' _ _ _ _
(TKEPT ++ [10%bv; 13%bv; 14%bv; 5%bv; 16%bv; 11%bv; 12%bv; 31%bv; 29%bv; 8%bv; 6%bv])
HS AG' ltac:(vm_compute; reflexivity)) as KP;
let R7 := fresh "R" in let R28 := fresh "R" in let R30 := fresh "R" in let R17 := fresh "R" in
let R20 := fresh "R" in let R18 := fresh "R" in let R19 := fresh "R" in
let r19 := constr:(19%bv : bv 5) in
prreg HS (7%bv : bv 5) R7; prreg HS (28%bv : bv 5) R28; prreg HS (30%bv : bv 5) R30;
prreg HS (17%bv : bv 5) R17; prreg HS (20%bv : bv 5) R20; prreg HS (18%bv : bv 5) R18;
pose proof (st_ok_pi_restrict_reg _ _ _ _ r19 HS) as R19;
let e19 := eval vm_compute in (sr_get (ss_regs ssf) r19) in
change (sr_get (ss_regs ssf) r19) with e19 in R19;
cbn [ms_regs restrict] in R19;
rewrite HE17, ?unsigned_lit_small in R17 by lia;
repeat match goal with
| Rr : getr (ms_regs _) _ = ?rhs, HEn : ew ?E1 ?n = Z_to_bv 64 _ |- _ =>
lazymatch rhs with context [ew E1 n] => rewrite HEn in Rr end
end;
rewrite ?wvb_collapse in HJ;
pmkst HS; apply SRr_ret; split; [reflexivity|]; do 3 eexists; exists sB, corr;
split; [reflexivity|]; split; [exact HJ|];
split; [unfold tcbl_regs_fix; rewrite R7, R28, R30, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
repeat split; assumption|];
rewrite R17, R20, R18, R19, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
split; [assumption|]; split; [assumption|];
split; [first [reflexivity | f_equal; lia]|];
split; [assumption|]; split; [assumption|];
split; [apply bv_eq; change (bv_unsigned (sv_denot E' e19)) with (U E' e19);
rewrite (U_t6 E' 31 0 Lv 9 bv0) by (first [cbn [ew ewset Nat.eqb]; assumption | lia]);
rewrite unsigned_lit_small by lia; lia|];
split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity]|]; split; [reflexivity|];
split; [lia|]; split; [lia|]; split; [lia|];
split; [intros r Hr; apply KP; apply in_or_app; left; exact Hr|]
end end end end.
Ltac xframeB HF Hm HE32 :=
let x := fresh "x" in let Hx := fresh "Hx" in
let rg := fresh "rg" in let Hsel := fresh "Hsel" in let Hwin := fresh "Hwin" in
intros x Hx; etransitivity; [| exact (Hm x Hx)]; apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel;
repeat (destruct Hsel as [<-|Hsel];
[ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hwin;
rewrite ?HE32, ?unsigned_lit_small in Hwin by lia; lia |]);
destruct Hsel.
Ltac xchunkB HS base HE32 HE33 HE34 HE9 :=
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
let HR := fresh "HR" in
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & (_ & HR & _) & _);
cbn [ss_mem abs_ss setpc ms_mem restrict] in HR;
apply Forall_inv_tail, Forall_inv in HR;
lazymatch goal with |- val_mem _ _ ?a _ _ =>
first [ replace a with (base + 0) by lia | replace a with (base + 1) by lia | replace a with (base + 2) by lia ] end;
eapply (vval_mem_of_chunk_mod SEGS E' _ _ 32 base _ 1 _ _ HR);
[ reflexivity
| cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])
| cbn [ew ewset Nat.eqb]; rewrite HE32; apply unsigned_lit_small; lia
| change (2 ^ (8 * Z.of_N 1)) with 256;
lazymatch goal with
| |- bv_unsigned (sv_denot ?E2 (SAlu ALU_OR (SOff ?ny 0) (SAluw ALU_SLL (SOff ?nx 0) (SOff ?no 0)))) mod 256 = _ =>
apply (U_byte0a E2 ny nx no)
| |- bv_unsigned (sv_denot ?E2 (SAluw ALU_SRL (SOff ?nx 0) (SAlu ALU_SUB (SLit 0) (SOff ?no (-8))))) mod 256 = _ =>
apply (U_spill E2 nx no _ _ 8)
| |- bv_unsigned (sv_denot ?E2 (SAluw ALU_SRL (SOff ?nx 0) (SAlu ALU_SUB (SLit 0) (SOff ?no (-16))))) mod 256 = _ =>
apply (U_spill E2 nx no _ _ 16)
| |- bv_unsigned (sv_denot _ (SLit _)) mod 256 = _ =>
cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity
end;
first [ cbn [ew ewset Nat.eqb]; first [exact HE34 | exact HE33 | exact HE9] | lia ]
| lia ];
clear HR
end.
Ltac xleafB HS Hm GP HlenP base KP HE32 HE33 HE34 HE9 :=
let SHl := fresh "SHl" in let SHc := fresh "SHc" in
split; [exact Hm|];
lazymatch goal with |- garr8 _ _ _ (rev (fst (pk_pack (?Y :: rev ?PP) ?o ?l ?c))) /\ _ =>
destruct (pk_pack_shape PP Y o l c) as [SHl SHc] end;
rewrite <- (length_rev (fst _)), SHl, SHc;
repeat match goal with
| |- context [?u <? ?w] => first [ rewrite (proj2 (Z.ltb_lt u w)) by lia | rewrite (proj2 (Z.ltb_ge u w)) by lia ]
| |- context [?u =? ?w] => first [ rewrite (proj2 (Z.eqb_eq u w)) by lia | rewrite (proj2 (Z.eqb_neq u w)) by lia ]
end;
cbn [orb];
split;
[ apply garr8_app; split;
[ eapply garr8_frame; [exact GP|]; intros a Ha; unfold mbyte, mrestrict; cbv beta;
rewrite Hm; [reflexivity|]; rewrite unsigned_lit_small; lia
| rewrite HlenP;
repeat (apply garr8_cons_x;
[ xchunkB HS base HE32 HE33 HE34 HE9
| first [ lia | apply Z.mod_pos_bound; lia | apply lor_byte; [lia | apply Z.mod_pos_bound; lia] ]
| ]);
apply garr8_nil ]
|];
split; [rewrite length_app; cbn [length]; lia|];
split; [reflexivity|];
split; first [reflexivity | apply KP; cbv [In TKEPT app]; repeat (first [left; reflexivity | right])].
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
HJ Hbl Hlz Apart Pinned Sizes At11 At12 At17 At9 At31 At29 Irange Hbp HbpL Brange Lrange Hgarr HlenP Xcode HX.
pose proof HJ as (Hreach & _). pose proof asan_consts as (Kceil & _).
pose proof Sizes as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof Pinned as (F10 & F13 & F14 & F5 & F16 & F7 & F28 & F30).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz Hreach Hlz) as (_ & Hlzlo & Hlzhi & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby Hreach Hbl) as (_ & Hbllo & Hblhi & _).
pose proof (req_size_pos' Llz ltac:(lia)) as RqL. pose proof (req_size_pos' Lby ltac:(lia)) as RqB.
apply garr8_app in Hgarr as [GP GY].
destruct (GY 0%nat ltac:(cbn [length]; lia)) as [VY0 RY0]. cbn [nth Z.of_nat] in VY0, RY0.
rewrite HlenP, Z.add_0_r in VY0. clear GY.
destruct (TR32_okX regs ly S W memc mdc bl Lby bp (Z_to_bv 64 X) Y0 Hreach Hbl ltac:(lia) HbpL VY0 RY0)
as (Y1 & Y2 & RY1 & RY2 & HT32).
remember (Eimg (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2])) as E eqn:HEdef.
assert (Himg : img_env VAL A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (HEw : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (AG : env_agree 32 (Ereg regs [Z_to_bv 64 (bl + bp); Z_to_bv 64 X; Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]) E).
{ subst E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (HE32 : ew E 32 = Z_to_bv 64 (bl + bp)) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HE34 : ew E 34 = Z_to_bv 64 Y0) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 2); reflexivity).
assert (HE35 : ew E 35 = Z_to_bv 64 Y1) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 3); reflexivity).
assert (HE36 : ew E 36 = Z_to_bv 64 Y2) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 4); reflexivity).
pose proof (HEw 16%nat 16%bv ltac:(lia) eq_refl) as HE16. rewrite F16 in HE16.
pose proof (HEw 11%nat 11%bv ltac:(lia) eq_refl) as HE11. rewrite At11 in HE11.
pose proof (HEw 12%nat 12%bv ltac:(lia) eq_refl) as HE12. rewrite At12 in HE12.
pose proof (HEw 10%nat 10%bv ltac:(lia) eq_refl) as HE10. rewrite F10 in HE10.
pose proof (HEw 17%nat 17%bv ltac:(lia) eq_refl) as HE17. rewrite At17 in HE17.
pose proof (HEw 9%nat 9%bv ltac:(lia) eq_refl) as HE9. rewrite At9 in HE9.
pose proof (HEw 31%nat 31%bv ltac:(lia) eq_refl) as HE31. rewrite At31 in HE31.
pose proof (HEw 29%nat 29%bv ltac:(lia) eq_refl) as HE29. rewrite At29 in HE29.
assert (HS : st_ok_pi SEGS VAL E ss_B (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_B)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_tcbl; assumption.
- reflexivity.
- subst E. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
+ exact (TR12_okX regs ly S W memc mdc lz Llz i (Z_to_bv 64 (bl + bp)) X Hreach Hlz At12 ltac:(lia) ltac:(lia) Xcode ltac:(lia)
[Z_to_bv 64 Y0; Z_to_bv 64 Y1; Z_to_bv 64 Y2]).
+ exact (HT32 []).
- split; [|split; exact I]. split; [|exact I].
unfold extent_disjoint, TR12, TR32. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE12, HE32, !unsigned_lit_small by lia. lia.
- split; [|split; [exact I|]].
+ cbn [f_atoms]. unfold tcbl_facts_AB. apply atoms_ok_app.
* subst E. exact (tcbl_core_ok B LAWS regs _ ly S W memc mdc bl Lby lz Llz lzwPos D C0 i bp Lc Hreach Hbl Hlz Pinned Sizes At11 At12 At17 At31 At29 Irange Hbp Lrange).
* cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HE9, HE32, HE33, HE34, HE35, HE36, !unsigned_lit_small by lia.
rewrite ?Z.pow_0_r, ?Z.mod_1_r. cbv [YC1i.PTR af_lo af_hi af_al2]. lia.
+ cbn [f_alias alias_ok tcbl_alias sv_denot]. split; [|exact I].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, HE10, HE17, HE32. apply alu64_add_lit. }
shok_auto SHOK BxC E (mrestrict (w_H W) memc).
assert (Hm : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> memc x = memc x)
by (intros; reflexivity).
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl.
assert (Hm1 : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem ms x = memc x)
by xframeB HF Hm HE32.
clear HF HFr HG Hm. rename Hm1 into Hm.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9;
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl;
(assert (Hm1 : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem ms0 x = memc x)
by xframeB HF Hm HE32);
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm1 into Hm.
- rename Hc into Hlt8.
leafBX HS HJ AG HE31 HE9 HE17 0 0 KP. xleafB HS Hm GP HlenP (bl + bp) KP HE32 HE33 HE34 HE9.
- rename Hc into Hge8.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9;
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl;
(assert (Hm1 : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem ms0 x = memc x)
by xframeB HF Hm HE32);
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm1 into Hm.
+ rename Hc into Hne8.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9;
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl;
(assert (Hm1 : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem ms0 x = memc x)
by xframeB HF Hm HE32);
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm1 into Hm.
* rename Hc into Hge16.
psrr_branch_tok RUN BR HS SHOK Bspan; tcnorm Hc HE31 HE9;
runBX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl;
(assert (Hm1 : forall x, bv_unsigned x < bl + bp \/ bl + bp + 3 <= bv_unsigned x -> ms_mem ms0 x = memc x)
by xframeB HF Hm HE32);
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm1 into Hm.
-- rename Hc into Hne16.
leafBX HS HJ AG HE31 HE9 HE17 2 0 KP. xleafB HS Hm GP HlenP (bl + bp) KP HE32 HE33 HE34 HE9.
-- rename Hc into Heq16.
leafBX HS HJ AG HE31 HE9 HE17 2 (-1) KP. xleafB HS Hm GP HlenP (bl + bp) KP HE32 HE33 HE34 HE9.
* rename Hc into Hlt16.
leafBX HS HJ AG HE31 HE9 HE17 1 0 KP. xleafB HS Hm GP HlenP (bl + bp) KP HE32 HE33 HE34 HE9.
+ rename Hc into Heq8.
leafBX HS HJ AG HE31 HE9 HE17 1 (-1) KP. xleafB HS Hm GP HlenP (bl + bp) KP HE32 HE33 HE34 HE9.
Qed.
Ltac leafCX HS HJ AG HPC t L HE11 HE12 HE29 HE19 HEL :=
lazymatch type of HS with st_ok_pi _ _ ?E' _ _ =>
lazymatch type of AG with env_agree 32 ?E0 ?E =>
let AG' := fresh "AG'" in
assert (AG' : env_agree 32 E0 E') by
(destruct AG as [AG1 AG2]; split;
[ intros n Hn; rewrite <- (AG1 n Hn); repeat rewrite ew_ewset_other by lia; reflexivity
| cbn [ed ewset]; exact AG2 ]);
let KP := fresh "KP" in
pose proof (regs_kept_of_st_ok_pi E' _ _ _ _ (TKEPT ++ [10%bv; 13%bv; 14%bv; 5%bv; 16%bv; 17%bv; 20%bv])
HS AG' ltac:(vm_compute; reflexivity)) as KP;
let R7 := fresh "R" in let R28 := fresh "R" in let R30 := fresh "R" in let R11 := fresh "R" in
let R12 := fresh "R" in let R29 := fresh "R" in let R9 := fresh "R" in let R31 := fresh "R" in
prreg HS (7%bv : bv 5) R7; prreg HS (28%bv : bv 5) R28; prreg HS (30%bv : bv 5) R30;
prreg HS (11%bv : bv 5) R11; prreg HS (12%bv : bv 5) R12; prreg HS (29%bv : bv 5) R29;
prreg HS (9%bv : bv 5) R9; prreg HS (31%bv : bv 5) R31;
rewrite HE11, unsigned_lit_small in R11 by lia; rewrite HE12, unsigned_lit_small in R12 by lia;
rewrite HE29, unsigned_lit_small in R29 by lia; rewrite HE19, alu_and7 in R9 by (unfold M64; lia);
rewrite HEL in R31;
rewrite ?wvb_collapse in HJ;
pmkst HS; apply SRr_ret; split; [reflexivity|]; do 3 eexists; exists (t mod 8), (t / 8), L;
split; [rewrite HPC; reflexivity|]; split; [exact HJ|];
split; [unfold tcbl_regs_fix; rewrite R7, R28, R30, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
repeat split; assumption|];
rewrite R11, R12, R29, R9, R31, !KP by (cbv [In TKEPT app]; repeat (first [left; reflexivity | right]));
split; [f_equal; lia|]; split; [f_equal; lia|]; split; [assumption|]; split; [assumption|];
split; [f_equal; lia|]; split; [reflexivity|]; split; [reflexivity|];
split; [apply Z.div_mod; lia|]; split; [apply Z.mod_pos_bound; lia|]; split; [lia|];
split; [intros r Hr; apply KP; apply in_or_app; left; exact Hr|]
end end.
Ltac runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl tgt :=
paj_run_to_tok RUNTO HS HJ SHOK Bspan tgt;
[ oblBX HJ HE16 HE11 HE32 Hlz Hbl .. | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] | ].
Ltac xleafC HS Hm HXD HEr8 HE6 Hdi :=
let R8 := fresh "R" in let R6 := fresh "R" in
prreg HS (8%bv : bv 5) R8; prreg HS (6%bv : bv 5) R6;
rewrite HEr8 in R8; try rewrite HE6 in R6;
split; [exact Hm|]; rewrite HXD; split; [reflexivity|];
rewrite R8, R6; split; [reflexivity | first [reflexivity | apply addiw1_word; clear - Hdi; lia]].
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
HJ Hbl Hlz Pinned Sizes At11 At12 At17 At31 At29 At19 At20 At18 Irange Hbp Trange Lrange Xcode HX At8 At6 Hnr Hdi.
pose proof HJ as (Hreach & _). pose proof asan_consts as (Kceil & _).
pose proof Sizes as (Q1 & Q2 & Q3 & Q4 & Q5). pose proof Pinned as (F10 & F13 & F14 & F5 & F16 & F7 & F28 & F30).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lz Llz Hreach Hlz) as (_ & Hlzlo & Hlzhi & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bl Lby Hreach Hbl) as (_ & Hbllo & Hblhi & _).
pose proof (req_size_pos' Llz ltac:(lia)) as RqL. pose proof (req_size_pos' Lby ltac:(lia)) as RqB.
remember (Eimg (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X])) as E eqn:HEdef.
assert (Himg : img_env VAL A_LIM E) by (rewrite HEdef; apply Eimg_env).
assert (HEw : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. }
assert (AG : env_agree 32 (Ereg regs [Z_to_bv 64 0; Z_to_bv 64 X]) E).
{ subst E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
pose proof (HEw 16%nat 16%bv ltac:(lia) eq_refl) as HE16. rewrite F16 in HE16.
pose proof (HEw 11%nat 11%bv ltac:(lia) eq_refl) as HE11. rewrite At11 in HE11.
assert (HE32 : ew E 32 = Z_to_bv 64 0) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (HE33 : ew E 33 = Z_to_bv 64 X) by (subst E; eimg_low; rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (HS : st_ok_pi SEGS VAL E ss_C (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_cbl_C)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- intros r. destruct (decide (r = 18%bv)) as [->|Hne].
+ rewrite sr_get_set_same by reflexivity. rewrite At18. unfold sv_s2. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, HE11, HE16. reflexivity.
+ rewrite sr_get_set_other by exact Hne. subst E. apply regs_ok_tcbl; assumption.
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]. subst E.
exact (TR12_okX regs ly S W memc mdc lz Llz i (Z_to_bv 64 0) X Hreach Hlz At12 ltac:(lia) ltac:(lia) Xcode ltac:(lia) []).
- split; exact I.
- split; [|split; exact I]. cbn [f_atoms]. unfold tcbl_facts_C. apply atoms_ok_app.
+ subst E. exact (tcbl_core_ok B LAWS regs _ ly S W memc mdc bl Lby lz Llz lzwPos D C0 i bp Lc Hreach Hbl Hlz Pinned Sizes At11 At12 At17 At31 At29 Irange Hbp Lrange).
+ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (HEw 19%nat 19%bv ltac:(lia) eq_refl), At19, HE33.
rewrite !unsigned_lit_small by lia. rewrite ?Z.pow_0_r, ?Z.mod_1_r. lia. }
assert (SHOK : sh_ok SEGS BxC [] E (mrestrict (w_H W) memc)) by apply Forall_nil.
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
assert (Hm : forall x, ms_mem ms x = memc x).
{ intros x. apply HF. intros (rg & Hsel & Hwin). vm_compute in Hsel. destruct Hsel as [<-|[]].
cbn [YP09.r_wlo YP09.r_whi] in Hwin. lia. }
clear HF HFr HG.
pose proof (HEw 13%nat 13%bv ltac:(lia) eq_refl) as HE13. rewrite F13 in HE13.
pose proof (HEw 12%nat 12%bv ltac:(lia) eq_refl) as HE12. rewrite At12 in HE12.
pose proof (HEw 29%nat 29%bv ltac:(lia) eq_refl) as HE29. rewrite At29 in HE29.
pose proof (HEw 19%nat 19%bv ltac:(lia) eq_refl) as HE19. rewrite At19 in HE19.
pose proof (HEw 31%nat 31%bv ltac:(lia) eq_refl) as HE31. rewrite At31 in HE31.
pose proof (HEw 14%nat 14%bv ltac:(lia) eq_refl) as HE14. rewrite F14 in HE14.
pose proof (HEw 8%nat 8%bv ltac:(lia) eq_refl) as HE8. rewrite At8 in HE8.
pose proof (HEw 6%nat 6%bv ltac:(lia) eq_refl) as HE6. rewrite At6 in HE6.
pose proof (HEw 5%nat 5%bv ltac:(lia) eq_refl) as HE5. rewrite F5 in HE5.
psrr_branch_tok RUN BR HS SHOK Bspan;
rewrite branch_ne_U, (U_atom _ 33 X), (U_atom _ 13 D) in Hc by (first [cbn [ew ewset Nat.eqb]; assumption | lia]);
lazymatch type of Hc with
| negb _ = true => apply Bool.negb_true_iff in Hc
| negb _ = false => apply Bool.negb_false_iff in Hc
end; rename Hc into HXD;
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A;
(assert (Hm0 : forall x, ms_mem ms0 x = memc x);
[ intros x; rewrite <- (Hm x); apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel; destruct Hsel as [<-|[]];
cbn [YP09.r_wlo YP09.r_whi] in Hwin; lia |]);
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm0 into Hm;
psrr_branch_tok RUN BR HS SHOK Bspan;
rewrite branch_ne_U, (U_atom_off _ 29 (lzwPos - i) (-1)), U_lit in Hc by (first [cbn [ew ewset Nat.eqb]; assumption | lia]).
- apply Bool.negb_true_iff, Z.eqb_neq in Hc.
assert (HPC : (i + 1 =? lzwPos) = false) by (apply Z.eqb_neq; lia).
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x; rewrite <- (Hm x); apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel; destruct Hsel as [<-|[]].
cbn [YP09.r_wlo YP09.r_whi] in Hwin; lia. }
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm0 into Hm.
leafCX HS HJ AG HPC t Lc HE11 HE12 HE29 HE19 HE31. xleafC HS Hm HXD HE8 HE6 Hdi.
- apply Bool.negb_false_iff, Z.eqb_eq in Hc.
assert (HPC : (i + 1 =? lzwPos) = true) by (apply Z.eqb_eq; lia).
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X.
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x; rewrite <- (Hm x); apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel; destruct Hsel as [<-|[]].
cbn [YP09.r_wlo YP09.r_whi] in Hwin; lia. }
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm0 into Hm.
leafCX HS HJ AG HPC t Lc HE11 HE12 HE29 HE19 HE31. xleafC HS Hm HXD HE8 HE6 Hdi.
- apply Bool.negb_true_iff, Z.eqb_neq in Hc.
assert (HPC : (i + 1 =? lzwPos) = false) by (apply Z.eqb_neq; lia).
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_A.
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x; rewrite <- (Hm x); apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel; destruct Hsel as [<-|[]].
cbn [YP09.r_wlo YP09.r_whi] in Hwin; lia. }
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm0 into Hm.
leafCX HS HJ AG HPC t C0 HE11 HE12 HE29 HE19 HE14. xleafC HS Hm HXD HE5 HE6 Hdi.
- apply Bool.negb_false_iff, Z.eqb_eq in Hc.
assert (HPC : (i + 1 =? lzwPos) = true) by (apply Z.eqb_eq; lia).
runCX HS HJ SHOK HE16 HE11 HE32 Hlz Hbl A_cbl_X.
assert (Hm0 : forall x, ms_mem ms0 x = memc x).
{ intros x; rewrite <- (Hm x); apply HF; intros (rg & Hsel & Hwin); vm_compute in Hsel; destruct Hsel as [<-|[]].
cbn [YP09.r_wlo YP09.r_whi] in Hwin; lia. }
clear HF HFr HG Hm; clear ms; rename ms0 into ms; rename Hm0 into Hm.
leafCX HS HJ AG HPC t C0 HE11 HE12 HE29 HE19 HE14. xleafC HS Hm HXD HE5 HE6 Hdi.
Qed.
End h.
End f.
End d.
