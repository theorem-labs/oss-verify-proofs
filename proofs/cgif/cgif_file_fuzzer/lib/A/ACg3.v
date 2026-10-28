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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z YI5x YI5v YI5s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 AChd AChe ACjr ACj3 ACgw ACh0 ACgy ACgv ACgu.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI3w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YI1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo ACg8 ACg9 ACgb.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Ltac af_E_names HEB sp0 g :=
lazymatch type of HEB with af_EB _ _ _ _ _ _ _ _ _ _ _ _ ?E =>
pose proof HEB as (HE & E67 & E70 & E71 & E72);
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI);
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity);
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia);
assert (HAE54 : env_agree 54 E E) by (split; [intros; reflexivity | reflexivity]) end.
Ltac evalE := cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia.
Ltac range_app_of Hia :=
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; cbn [Z.min Z.max] in Hx; generalize Hia; clear - Hx; unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Context {AP : af_params}.
#[local] Notation wfn := (@afp_wfn AP).
#[local] Notation hw := (@afp_hw AP).
#[local] Notation CTX := (@afp_ctx AP).
Context {AX : af_paramsX}.
#[local] Notation path := (@afx_path AX).
#[local] Notation pf := (@afx_pf AX).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Variable K : asink_syms.
Variable MT : ameter_ops.
Variable XN : xnums.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis MLAW : ameter_laws MT.
Hypothesis ML : model_laws (as_universe B).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
Ltac af_bf_fd HCF HSD HfIn b :=
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E (SAlu ALU_SRL _ _)) _ = b |- _ =>
lazymatch goal with E72 : ew E 72 = Z_to_bv 64 _, E51 : ew E 51 = Z_to_bv 64 _ |- _ =>
exact (af_bbr_fd E _ _ b E72 E51 (proj2 (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) _ (proj2 HSD _ HfIn) eq_refl eq_refl))
(proj2 (obj_at_nth SEGS _ _ _ _ 4 (24, 2%N) _ HCF eq_refl eq_refl)) H) end end.
Ltac af_bf_gen HT b :=
lazymatch goal with H : branch_taken BC_NE (sv_denot ?E (SAlu ALU_AND (SExt false 8 (SOff 41 0)) (SLit 1))) _ = b |- _ =>
lazymatch goal with E41 : ew E 41 = Z_to_bv 64 _ |- _ =>
let R := fresh "R" in
pose proof (proj2 (obj_at_nth SEGS _ _ _ _ 6 (44, 4%N) _ (proj1 HT) eq_refl eq_refl)) as R; cbn [snd] in R; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in R;
exact (af_bbr_and1 E 41 8 _ b E41 ltac:(clear - R; lia) ltac:(clear; cbn; lia) ltac:(clear; lia) H) end end.
Ltac af_bf_lct HCF b :=
match goal with H : branch_taken BC_NE (sv_denot ?E (SAlu ALU_AND ?a (SLit 1))) _ = b |- _ =>
lazymatch goal with E49 : ew E 49 = Z_to_bv 64 ?x |- _ =>
let R := fresh "R" in
pose proof (proj2 (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) _ HCF eq_refl eq_refl)) as R; cbn [snd] in R; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in R;
let Ua := fresh "Ua" in
assert (Ua : U E a = x) by first [exact (af_bU_zx32 E 49 x E49 R) | exact (U_zext32_atom E 49 x E49 R)];
exact (af_bbr_and1g E _ _ b Ua ltac:(clear - R; lia) H) end end.
Ltac af_bf_flags HCF HSD HfIn b :=
match goal with H : branch_taken BC_EQ (sv_denot ?E (SAlu ALU_OR _ (SAlu ALU_AND ?a _))) _ = b |- _ =>
lazymatch goal with E49 : ew E 49 = Z_to_bv 64 ?x, E71 : ew E 71 = Z_to_bv 64 _ |- _ =>
let R := fresh "R" in
pose proof (proj2 (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) _ HCF eq_refl eq_refl)) as R; cbn [snd] in R; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in R;
let Ua := fresh "Ua" in
assert (Ua : U E a = x) by first [exact (af_bU_zx32 E 49 x E49 R) | exact (U_zext32_atom E 49 x E49 R)];
exact (af_bbr_flagsg E _ _ _ b Ua E71 R
(proj2 (obj_at_nth SEGS _ _ _ _ 2 (16, 4%N) _ (proj2 HSD _ HfIn) eq_refl eq_refl)) H) end end.
Lemma af_B2X : AF_C_stmtX K MT XN B -> AF_L_stmtX K MT XN B -> AF_SM_stmtX K MT XN B -> AF_Bi_stmtX K MT XN B 2.
Proof.
intros PC PL PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f GPAL IMG LPAL gs gsF Hihv CX HE0 HPX Hn HS0 SHOK0 XC.
pose proof (af_xf_in _ XC) as XCm. clear XC.
destruct (af_B_extX B K MT XN LAWS ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E0 ms1 md1 f GPAL IMG LPAL gs CX HE0 HPX Hn HS0 SHOK0)
as (HEB & HPB & HS & SHOK).
set (E := havoc E0 70 [Z_to_bv 64 (fr_img f); Z_to_bv 64 (fr_attr f); Z_to_bv 64 (fr_delay f)]) in HEB, HS, SHOK.
clear HS0 SHOK0 HE0.
af_B_namesX LAWS CX HEB HPB Hn. clear Hih. rename Hihv into Hih.
destruct (af_xb_head K _ _ s N GPAL gs f XREL0 (proj1 (af_xf_out _ XCm)) (or_intror Hih) Hn) as (XHD & XqHD & XfHD).
assert (XREL0' : af_xrel K (mrestrict (w_H W) mem) md s N img lpa fattr nlp GPAL IMG LPAL gs) by (split; [exact XREL0 | split; [exact XIMG0 | split; [exact XIMGL | exact XLPAL0]]]).
rewrite Hih in HS, SHOK, Hn; change (Z.to_nat 2) with 2%nat in Hn; change (33 + Z.to_nat 2)%nat with 35%nat in HS, SHOK; cbn [Z.mul Pos.mul] in HS.
assert (B35 : bv_unsigned (ew E 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (Hfne : nth_error (cg_frames s) 2 = Some (Some f)).
{ clear - Hlen Hn. destruct (cg_frames s) as [|o0 [|o1 [|o2 [|x l]]]]; cbn in Hlen; try discriminate. cbn in Hn |- *. rewrite Hn. reflexivity. }
pose proof (proj2 HSD f HfIn) as HOBf.
assert (UH : U E (SExt false 16 (SOff 43 0)) = cg_H s) by (apply (U_zext_small E 16 _ _ (U_atom E 43 _ E43 ltac:(clear - RH; lia))); [clear - RH; lia | cbn; clear; lia]).
assert (UW : U E (SExt false 16 (SOff 42 0)) = cg_W s) by (apply (U_zext_small E 16 _ _ (U_atom E 42 _ E42 ltac:(clear - RW; lia))); [clear - RW; lia | cbn; clear; lia]).
assert (UHa : U E (SOff 43 0) = cg_H s) by (apply (U_atom E 43 _ E43); clear - RH; lia).
assert (UWa : U E (SOff 42 0) = cg_W s) by (apply (U_atom E 42 _ E42); clear - RW; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 42%nat (mkAF 1 65535 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E42, unsigned_lit_small by (clear - RW; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - RW HW1; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 42%nat (mkAF 1 65535 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E42, unsigned_lit_small by (clear - RW; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - RW HW1; lia)) as HS3; clear HS; rename HS3 into HS  end.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 43%nat (mkAF 1 65535 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E43, unsigned_lit_small by (clear - RH; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - RH HH1; lia)) as HS3; clear HS; rename HS3 into HS | st_ok _ ?Ex _ _ =>
pose proof (st_ok_pi_add_fact Ex _ _ 43%nat (mkAF 1 65535 0) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E43, unsigned_lit_small by (clear - RH; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - RH HH1; lia)) as HS3; clear HS; rename HS3 into HS  end.
norm_ss HS.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_C; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (xs_C 2 16 35) 644%nat;
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
apply (af_xb_c_fd K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm)); af_bf_fd HCF HSD HfIn true ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
apply (af_xb_c_fd K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm)); af_bf_fd HCF HSD HfIn true ]  end. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_C; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (xs_C 2 16 35) 644%nat;
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
apply (af_xb_c_keep s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (af_xf_out _ XCm)); af_bf_gen HT true ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
apply (af_xb_c_keep s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF (af_xf_out _ XCm)); af_bf_gen HT true ]  end. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
exfalso.
lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
rewrite branch_eq_U in H; rewrite U_lit in H by (clear; lia);
lazymatch type of H with context [U ?E9 (SMdw M_MUL ?a9 ?b9)] =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 (SMdw M_MUL a9 b9) HAG eq_refl) in H; clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) in H by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) in H by (clear - RW RH HNWH HN1; nia) ];
apply (proj1 (Z.eqb_eq _ _)) in H; clear - H HNWH HN1; nia end. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_LOOP; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R24. rregD HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24.
rewrite ?ew_ewset_other in R19 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in R24 by (clear - PBASE PBLO; lia).
af_rejoin HS (xs_L0 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (YI1d.U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia) ]; clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia
|
apply (af_xb_l0 K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm));
[ af_bf_fd HCF HSD HfIn false | af_bf_gen HT false | left; af_bf_lct HCF true ] ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (YI1d.U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia) ]; clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia
|
apply (af_xb_l0 K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm));
[ af_bf_fd HCF HSD HfIn false | af_bf_gen HT false | left; af_bf_lct HCF true ] ]  end. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
2: {
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
exfalso.
lazymatch goal with H : branch_taken _ _ _ = true |- _ =>
rewrite branch_eq_U in H; rewrite U_lit in H by (clear; lia);
lazymatch type of H with context [U ?E9 (SMdw M_MUL ?a9 ?b9)] =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 (SMdw M_MUL a9 b9) HAG eq_refl) in H; clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) in H by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) in H by (clear - RW RH HNWH HN1; nia) ];
apply (proj1 (Z.eqb_eq _ _)) in H; clear - H HNWH HN1; nia end. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_LOOP; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
prreg HS (19%bv : bv 5) R19. prreg HS (25%bv : bv 5) R24. rregD HS (20%bv : bv 5) R9.
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R19, R24.
rewrite ?ew_ewset_other in R19 by (clear - PBASE PBLO; lia). rewrite ?ew_ewset_other in R24 by (clear - PBASE PBLO; lia).
af_rejoin HS (xs_L0 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (YI1d.U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia) ]; clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia
|
apply (af_xb_l0 K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm));
[ af_bf_fd HCF HSD HfIn false | af_bf_gen HT false | right; af_bf_flags HCF HSD HfIn false ] ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PL (Z.to_nat N) ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f 0 GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
change 657%nat with (644 + 13)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 13 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R19; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 658%nat with (644 + 14)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 14 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R24; evalE; rewrite ?E48, ?E70; unfold w64; f_equal; clear; lia
|
change 648%nat with (644 + 4)%nat; rewrite (YN3v.ew_havoc_new _ 644 _ 4 (Z_to_bv 64 0)) by (cbn; clear; lia); cbn [nth];
rewrite R9; rewrite denot_lit_U; unfold w64; f_equal; rewrite Z2Nat.id by (clear - HN1; lia);
apply (YI1d.U_zext32_shifts _ _ N); [| clear - HN1; lia];
lazymatch goal with |- U ?E9 ?v9 = _ =>
tryif constr_eq E9 E then idtac else (
let HAG := fresh "HAG" in assert (HAG : env_agree 54 E E9) by (env_agree_chain HAE54);
rewrite (U_agree 54 E E9 v9 HAG eq_refl); clear HAG) end;
first [ rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UHa UWa) by (clear - RW RH HNWH HN1; nia)
| rewrite (U_mulw_small E _ _ (cg_H s) (cg_W s) UH UW) by (clear - RW RH HNWH HN1; nia) ]; clear - HNWH; lia
| clear; lia
| rewrite Z2Nat.id by (clear - HN1; lia); clear; lia
| clear - HN1; lia
|
apply (af_xb_l0 K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm));
[ af_bf_fd HCF HSD HfIn false | af_bf_gen HT false | right; af_bf_flags HCF HSD HfIn false ] ]  end. }
assert (XBF : af_xf (delay + fr_delay f <= 65535 /\ Z.land (cg_gen s) 1 = 0 /\ Z.land fattr 1 = 0 /\ (Z.land (fr_attr f) 1 = 0 /\ Z.land (fr_attr f) 4 = 0 /\ Z.land fattr 4 = 0))).
{ unfold af_xf. split; [af_bf_fd HCF HSD HfIn false|]. split; [af_bf_gen HT false|]. split; [af_bf_lct HCF false | af_bf_flags HCF HSD HfIn true]. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA  ; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
destruct (al_blocks _ _ LAWS _ _ _ _ _ img N (proj1 HJ) Himg) as (_ & _ & _ & _ & HiP & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (fr_img f) N (proj1 HJ) Hfimg) as (_ & _ & _ & _ & HfiP & _).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. rregD HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
lazymatch type of Qsp with getr ?rg _ = _ => assert (HspU : spZ rg = sp0 - 224) by (unfold spZ; rewrite Qsp; cbn [sv_denot]; evalE; rewrite Usp; apply unsigned_lit_small; clear - Hceil Hslo Hshi H47 HTS C1; lia) end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA AS_memcmp_2) ABCMP W (ms_regs msX) (ms_mem msX) TADDFRAME_STK sp0 (FPn g) ly S W mem md []
ly S mdX 0 img (fr_img f) N (-224) (Z_to_bv 64 (BASE + 0xb2c)) HJ);
[ rewrite Ra0; cbn [sv_denot]; evalE; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E48
| rewrite Ra1; cbn [sv_denot]; evalE; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; exact E70
| rewrite Ra2; rewrite denot_lit_U; unfold w64; f_equal; rewrite U_mul_smallD by (rewrite ?UH, ?UW, ?UHa, ?UWa; clear - RW RH; nia); rewrite ?UH, ?UW, ?UHa, ?UWa; clear - HNWH; lia
| clear - HN1; lia | clear - Hi4096; lia | clear - Hiceil HrN C1; lia | clear - Hfi4096; lia | clear - Hficeil HrN C1; lia
| rewrite HspU; clear; lia
| reflexivity | clear; lia | rewrite HTS, HES; clear; lia
| rewrite Qgp; cbn [sv_denot]; evalE; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp
| rewrite Qtp; cbn [sv_denot]; evalE; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp
| exact Rra
| apply ret_ok_codeptr_v; [clear; lia | reflexivity]
| intros a Ha; split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HiP a ltac:(clear - Ha HrN; lia))) | rewrite HspU, HES; intro; clear - Ha H Hi4096 Hiceil HrN Hceil Hslo HTS C1; lia]
| intros a Ha; split; [apply (aview_some_of_apresent SEGS); apply (proj1 (HfiP a ltac:(clear - Ha HrN; lia))) | rewrite HspU, HES; intro; clear - Ha H Hfi4096 Hficeil HrN Hceil Hslo HTS C1; lia]
| intros a Ha; rewrite HES; clear - Ha Hi4096 Hiceil HrN Hceil Hslo HTS C1; lia
| intros a Ha; rewrite HES; clear - Ha Hfi4096 Hficeil HrN Hceil Hslo HTS C1; lia
| apply (amem_range_of_block SEGS B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| apply (amem_range_of_block SEGS B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia
| apply (range_addressable_of_block SEGS B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| intros _; apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ img N _ _ (proj1 HJ) Himg); clear - HN1 HrN; lia
| apply (range_addressable_of_block SEGS B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia
| intros _; apply (shadow_hull_vis_of_block SEGS B LAWS ly S W _ _ (fr_img f) N _ _ (proj1 HJ) Hfimg); clear - HN1 HrN; lia ] end. }
cbv beta. clear Ra0 Ra1 Ra2 Qgp Qtp.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2).
assert (XCMP : af_xf (v = w64 0 <-> IMG = YO07.f_img XHD)).
{ pose proof (af_xrel_N B K LAWS AIL _ ly S W mem md _ W _ _ _ g s N img lpa fattr nlp rest GPAL IMG LPAL gs HJ HPerm Hpfr HWF XREL0') as (XRT & XIT & _).
destruct (af_xb_head K _ _ s N GPAL gs f XRT (proj1 (af_xf_out _ XCm)) (or_intror Hih) ltac:(rewrite Hih; exact Hn)) as (HD' & Hq' & XFT).
rewrite XqHD in Hq'. injection Hq' as <-.
pose proof XFT as (_ & _ & _ & _ & _ & _ & _ & GFI & LFI & _).
pose proof (af_bcmp_model _ (aview SEGS (w_H W) _) img (fr_img f) IMG (YO07.f_img XHD) N (fun a => eq_refl) XIT GFI XIMGL LFI) as XE.
unfold af_xf. split; [intros Hv0; apply (proj1 XE); apply (proj1 Hcmp); exact Hv0 | intros HE0; apply (proj2 Hcmp); apply (proj2 XE); exact HE0]. }
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcellb & _ & Kgotb & _). rewrite HBgot, HBcell in Kgotb. rewrite HBcell in Kcellb.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell2 & _ & Kgot2 & _). rewrite HBgot, HBcell in Kgot2. rewrite HBcell in Kcell2.
let K := lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa (af_SHB 35) ss) | st_ok _ _ ?ss _ => eval vm_compute in (run_K A_LIM Bxa (af_SHB 35) ss)  end in
jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
match type of HS2 with ?tt -> _ => assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil;
first
[ eapply region_kept_aview;
[ first [exact B35 | exact Usp | exact E32u | rewrite E46; apply unsigned_lit_small; clear - Hcfp C1; lia]
| intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply Hfr2;
[ clear - Ha Hh4096 Hhceil HZg Hgceil Hcfp Hceil Hslo Hshi H47 HTS C1; lia
| rewrite HES; clear - Ha Hh4096 Hhceil HZg Hgceil Hcfp Hceil Hslo Hshi H47 HTS C1; lia ]
| exact Hpres2 ]
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 241%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12)));
[exact (H (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgotb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2) | clear; lia] end
| lazymatch goal with |- region_kept _ ?Ex _ _ (YP09.mkRegion (Some 253%nat) _ _ _ _ _) => let H := rnHEI Ex in apply (region_kept_val_at Ex _ _ (A_OBJ 12) (VAL (A_OBJ 12)) 8 SHADOW_OFF);
[exact (H (A_OBJ 12) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcellb) | exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2) | clear; lia] end
| match goal with |- ?gg => idtac "KEPTFAIL" gg end ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS. try (let Hx := fresh "HEIo" in rename HEI2 into Hx). assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [first [exact HEI | assumption] | cbv; lia]).
assert (OLD2 : forall n, (n < 512)%nat -> ew E2 n = ew E n) by (intros n Hn0; rewrite HE2; apply YN3v.ew_havoc_old; clear - Hn0; lia).
assert (E516 : ew E2 516 = v) by (rewrite HE2; change 516%nat with (512 + 4)%nat; rewrite (YN3v.ew_havoc_new E 512 _ 4 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth map]; exact Hv).
assert (HAE2 : env_agree 512 E E2) by (rewrite HE2; apply env_agree_havoc_ge; [clear; lia | apply env_agree_refl]).
clear HE2.
pose proof (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E E2 HEB (fun n Hn0 => OLD2 n Hn0)) as HEB2.
pose proof (af_side_sep B LAWS ly S W mem md g s N _ ly sp0 (fun a => sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) HAR HPerm Hstk
ltac:(intros a Ha; cbv beta in Ha; left; rewrite HES in Ha; clear - Ha HTS; lia)) as [HZr2 HZf2].
replace (sp0 + -224) with (sp0 - 224) in Hfr2 by (clear - PBASE PBLO; lia).
pose proof (af_side_kept _ _ _ _ _ (fun a => sp0 - 224 - 2 * ESTACK <= a < sp0 - 224) HSD Hfr2 HZr2 HZf2) as HSD2. clear HSD HZr2 HZf2. rename HSD2 into HSD.
assert (HGK2 : forall i, 0 <= i < 96 -> ~ (88 <= i < 92) -> mbyte SEGS (mrestrict (w_H W) mem2) (g + i) = mbyte SEGS (mrestrict (w_H W) mem) (g + i)).
{ intros i Hi Hni. etransitivity; [| exact (HGK i Hi Hni)]. apply (mbyte_of_aview SEGS). apply Hfr2; [| rewrite HES]; clear - Hi HZg Hgceil Hceil Hslo HTS C1; lia. }
clear HGK. rename HGK2 into HGK.
clear HJ. rename HJ2 into HJ.
clear SHOK B35 HEB. try clear HE E67 E70 E71 E72 EEo E32 E33 E34 E35 E36 E37 E38 E39 E40 E41 E42 E43 E44 E45 E46 E47 E48 E49 E50 E51 E52 E53 Usp E32u HAE54 UH UW UHa UWa.
rename HEB2 into HEB. af_E_names HEB sp0 g.
assert (B35 : bv_unsigned (ew E2 35) = fr_ptr f) by (rewrite E35, Hn; cbn [frame_ptr]; apply unsigned_lit_small; clear - Hh4096 Hhceil C1; lia).
assert (SHOK : sh_ok SEGS Bxa (af_SHB 35) E2 (mrestrict (w_H W) mem2)).
{ pose proof (afobj_journalN B LAWS sp0 ly S W mem md [] ly S W _ _ _ g s N _ cfp 32 HJ HAR HPerm HFO) as (_ & _ & HRA2).
unfold sh_ok, af_SHB, af_SH. cbn [app]. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 E2 Bxa 32 g CGIF_SIZE 0 CGIF_SIZE (proj1 HJ) Hing).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32u.
+ lia.
+ change (req_size CGIF_SIZE) with 96. unfold CGIF_SIZE. lia.
- apply (shent_ok_of_range SEGS (w_H W) mem2 E2 Bxa 46 cfp 32 cfp 0 32 HRA2).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia. + range_app_of Hcfp_ia.
- apply (shent_ok_of_block SEGS B LAWS ly S W mem2 md2 E2 Bxa 35 (fr_ptr f) FRAME_SIZE 0 FRAME_SIZE (proj1 HJ) Hfb).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact B35.
+ lia.
+ rewrite HFS. change (req_size 40) with 40. lia. }
assert (HPB2 : af_preBX B ly S W regs mem md g cfp s N fattr (mkst regs2 (Z_to_bv 64 (BASE + 0xb2c)) mem2 (seg_rom SEGS)) md2).
{ split; [exact HJ|]. split; [exact HSD|]. split; [exact HGK|]. split; [exact Hcur|]. split; [exact HnoTab | rewrite Hih; clear; lia]. }
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
{
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_SAME; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (xs_SM 2 16 35) 644%nat.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
destruct (af_xf_out _ XBF) as (XF1 & XF2 & XF3 & XF4 & XF5 & XF6);
apply (af_xb_sm_fast K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm) XF1 XF2 XF3 XF4 XF6 XF5);
apply (proj1 (af_xf_out _ XCMP));
lazymatch goal with H : branch_taken BC_EQ (sv_denot ?E9 (SOff 516 0)) _ = true |- _ => exact (af_bbr_a0 E9 516 v true E516 H) end ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PSM ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f GPAL IMG LPAL gs gsF XHD CX);
[ apply (af_EB_agree _ _ _ _ _ _ _ _ _ _ _ _ E2); [exact HEB | agreeE_tac]
| split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | rewrite Hih; clear; lia]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| rewrite Hih; change (33 + Z.to_nat 2)%nat with 35%nat;
lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 512 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa (af_SHB 35) 512 E1 E' _ HAG1 eq_refl SHOK) end
|
destruct (af_xf_out _ XBF) as (XF1 & XF2 & XF3 & XF4 & XF5 & XF6);
apply (af_xb_sm_fast K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm) XF1 XF2 XF3 XF4 XF6 XF5);
apply (proj1 (af_xf_out _ XCMP));
lazymatch goal with H : branch_taken BC_EQ (sv_denot ?E9 (SOff 516 0)) _ = true |- _ => exact (af_bbr_a0 E9 516 v true E516 H) end ]  end. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA AF_C; [awr_bX Usp E32u Hing HTS 35%nat B35 Hfb Hfq |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_rejoin HS (xs_C 2 16 35) 644%nat;
lazymatch type of HS with st_ok_pi _ _ ?E2' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E2' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E2') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E2' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
destruct (af_xf_out _ XBF) as (XF1 & XF2 & XF3 & XF4 & XF5 & XF6);
apply (af_xb_c_fast K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm) XF1 XF2 XF3 XF4 XF6 XF5);
intros XE; apply (proj2 (af_xf_out _ XCMP)) in XE;
lazymatch goal with H : branch_taken BC_EQ (sv_denot ?E9 (SOff 516 0)) _ = false |- _ => exact (af_bbr_a0 E9 516 v false E516 H XE) end ] | st_ok _ ?E2' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E2' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E2); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E2); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E2') by (apply env_agree_havoc_ge; [clear; cbv; lia | (split; [intros; reflexivity | reflexivity]) || env_agree_chain HAE54]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E2' _ HAG1 eq_refl (proj1 (proj1 (Forall_app _ _ _) SHOK))) end
|
destruct (af_xf_out _ XBF) as (XF1 & XF2 & XF3 & XF4 & XF5 & XF6);
apply (af_xb_c_fast K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF f XHD XREL0 (or_intror Hih) XqHD XfHD (af_xf_out _ XCm) XF1 XF2 XF3 XF4 XF6 XF5);
intros XE; apply (proj2 (af_xf_out _ XCMP)) in XE;
lazymatch goal with H : branch_taken BC_EQ (sv_denot ?E9 (SOff 516 0)) _ = false |- _ => exact (af_bbr_a0 E9 516 v false E516 H XE) end ]  end.
Qed.
End e.
End d.
End c.
