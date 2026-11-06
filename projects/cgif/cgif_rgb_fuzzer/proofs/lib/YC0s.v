(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI03 YI04 YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC1b YC2q YC2u YC4r YC13 YC2o YC16 YC12 YC20 YC3q YC0u YC0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition regsA : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 10 (SOff 32 0)) 11 (SOff 46 0).
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma af_OK : AF_B_stmt B -> AF_C_stmt B -> AF_OK_stmt B.
Proof.
intros PB PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 CX HE HPX HS SHOK.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67 & Hih).
pose proof Hwx_tfa as Hwx. pose proof tra_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CX as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive & HPAL).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof (proj1 HWF) as Hlen.
assert (HAE54 : env_agree 54 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
destruct Hih as [Hih | Hih]; rewrite Hih in HS.
-
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 1%nat HAR HPerm) as Hslot.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear; lia).
rewrite (U_atom E 34 _ E34) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_eq _ _)) in Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x86100; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join HS (ss_C 1 8 34) 200%nat af_deads_C.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end ] end.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear; lia).
rewrite (U_atom E 34 _ E34) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_neq _ _)) in Hq.
destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exfalso; clear - Hq Hz; lia|].
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x85ee8; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join0 HS (ss_B 1 8 34).
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK ] end.
-
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 2%nat HAR HPerm) as Hslot.
aj_run_tok tratbl_lib_ok HS HJ SHOK RBspanA; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
srr_branch_tok tratbl_lib_ok HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear; lia).
rewrite (U_atom E 35 _ E35) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_eq _ _)) in Hq.
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x86100; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join HS (ss_C 2 16 35) 200%nat af_deads_C.
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree trasegs Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end ] end.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear; lia).
rewrite (U_atom E 35 _ E35) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_neq _ _)) in Hq.
destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exfalso; clear - Hq Hz; lia|].
aj_run_to_tok tratbl_lib_ok HS HJ SHOK RBspanA 0x85ee8; [awr_a Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join0 HS (ss_B 2 16 35).
lazymatch type of HS with st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_pre_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK ] end.
Qed.
End b.
End a.
