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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n YI5w YI5z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACjp ACh9 AChb ACj1 ACjr ACj3 ACgw ACh0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08 YI0f YI0b YC5d YC7z YC7y YC7x YC88 YC85 YC86.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACgt ACgq ACgr ACgs ACgk ACgf ACgm ACgo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
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
Definition regsA : list sv := Eval vm_compute in sr_set (sr_set sr_atoms 10 (SOff 32 0)) 11 (SOff 46 0).
Section c.
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
Lemma af_OKX : AF_B_stmtX K MT XN B -> AF_C_stmtX K MT XN B -> AF_OK_stmtX K MT XN B.
Proof.
intros PB PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E ms1 md1 GPAL IMG LPAL gs gsF CX HE HPX HS SHOK XC.
pose proof (af_xf_in _ XC) as XCm. clear XC.
pose proof HPX as (HJ & HSD & HGK & Hcur & HnoTab & E67 & Hih).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 CX) as (HPRE & Hctx & Hfr7 & HROD & H10 & H11 & HFO & HCF & HT & HWF & Hlpa & HPerm & Hev & Hlive).
pose proof (proj2 CX) as (Hpf0 & Hpfr & XREL0 & XSMAX & XIMG0 & XIMGL & XLPAL0 & XMOK).
assert (Hpfcb : In (pf, FILE_BLOCK) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ rest)) by (right; apply in_app_iff; right; exact Hpfr).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
clear Hpf0 XSMAX XIMGL XMOK.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HTS : TADDFRAME_STK = 17664) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hing : In (g, CGIF_SIZE) (ablocks B ly S)).
{ eapply Permutation_in; [apply Permutation_sym; exact HPerm|]. left. reflexivity. }
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & HgP & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgh, HgP, Hgh_img.
pose proof HE as (EEo & E32 & E33 & E34 & E35 & E36 & E37 & E38 & E39 & E40 & E41 & E42 & E43 & E44 & E45 & E46 & E47 & E48 & E49 & E50 & E51 & E52 & E53 & ?HEI).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
assert (E32u : bv_unsigned (ew E 32) = g) by (rewrite E32; apply unsigned_lit_small; lia).
pose proof (af_sideZ B LAWS ly S W mem md g s N _ ly sp0 HAR HPerm Hstk) as [HZr HZf].
assert (HZg : 0 <= g /\ g + 96 <= 2 ^ 64 /\ g + 96 + 224 <= sp0) by (clear - Hg4096 Hgceil C1 Hceil Hslo HTS; lia).
pose proof (proj1 HWF) as Hlen.
assert (HAE54 : env_agree 54 E E) by (split; [intros n Hn; reflexivity | reflexivity]).
destruct Hih as [Hih | Hih]; rewrite Hih in HS.
-
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 1%nat HAR HPerm) as Hslot.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear - PBASE PBLO; lia).
rewrite (U_atom E 34 _ E34) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (XCc : af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF).
{ apply (af_xok_c K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XREL0); [| rewrite Hih; clear; lia | exact (af_xf_out _ XCm)].
rewrite Hih. change (Z.to_nat 1) with 1%nat. clear - Hslot Hq. destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0xb30; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join HS (xs_C 1 8 34) 644%nat af_deads_C.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end
| exact XCc ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end
| exact XCc ]  end.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear - PBASE PBLO; lia).
rewrite (U_atom E 34 _ E34) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_neq _ _)) in Hq.
destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exfalso; clear - Hq Hz; lia|].
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0x918; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join0 HS (xs_B 1 8 34).
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK
| exact (af_xf_out _ XCm) ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK
| exact (af_xf_out _ XCm) ]  end.
-
pose proof (af_ptrs B LAWS ly S W mem md g s N _ 2%nat HAR HPerm) as Hslot.
hei_havoc HS; paj_run_tok RUN HS HJ SHOK RBspanA; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK RBspanA.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear - PBASE PBLO; lia).
rewrite (U_atom E 35 _ E35) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_eq _ _)) in Hq.
assert (XCc : af_xc s fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF).
{ apply (af_xok_c K _ _ s N fattr fgen delay nlp tidx GPAL IMG LPAL gs gsF XREL0); [| rewrite Hih; clear; lia | exact (af_xf_out _ XCm)].
rewrite Hih. change (Z.to_nat 2) with 2%nat. clear - Hslot Hq. destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exact Hn | rewrite Hn in Hq; cbn [frame_ptr] in Hq; lia]. }
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0xb30; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join HS (xs_C 2 16 35) 644%nat af_deads_C.
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end
| exact XCc ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PC ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact HS
| lazymatch type of SHOK with sh_ok _ _ _ ?E1 _ =>
let HAG1 := fresh "HAG1" in
assert (HAG1 : env_agree 54 E1 E') by (apply env_agree_havoc_ge; [clear; cbv; lia | split; [intros; reflexivity | reflexivity]]);
exact (sh_ok_agree SEGS Bxa af_SH 54 E1 E' _ HAG1 eq_refl SHOK) end
| exact XCc ]  end.
+
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hq end.
rewrite branch_eq_U in Hq; Unorm E HAE54 Hq; rewrite U_lit in Hq by (clear - PBASE PBLO; lia).
rewrite (U_atom E 35 _ E35) in Hq by (clear - Hslot C1; destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [rewrite Hz; lia | rewrite Hn; cbn [frame_ptr]; lia]).
apply (proj1 (Z.eqb_neq _ _)) in Hq.
destruct Hslot as [[Hn Hz] | (f0 & Hn & Hf0 & Hf1)]; [exfalso; clear - Hq Hz; lia|].
hei_havoc HS; paj_run_to_tok RUNTO HS HJ SHOK RBspanA 0x918; [awr_aX Usp E32u Hing HTS |].
side_step HSD HGK HZr HZf HZg Usp E32u; clear_frames.
af_join0 HS (xs_B 2 16 35).
lazymatch type of HS with st_ok_pi _ _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK
| exact (af_xf_out _ XCm) ] | st_ok _ ?E' _ (restrict _ ?msF) =>
eapply (PB ly S W regs mem md ch g cfp s N lpal lpa img fattr fgen delay nlp tidx rest E' msF _ f0 GPAL IMG LPAL gs gsF CX);
[ apply (af_E_agree _ _ _ _ _ _ _ _ _ _ _ E); [exact HE | agreeE_tac]
| apply (af_preX_agree B _ _ _ _ _ _ _ _ _ _ _ E); [| agreeE_tac];
split; [exact HJ | split; [exact HSD | split; [exact HGK | split; [exact Hcur | split; [exact HnoTab | split; [exact E67 | rewrite Hih; clear; lia]]]]]]
| rewrite Hih; exact Hn
| rewrite Hih; exact HS
| exact SHOK
| exact (af_xf_out _ XCm) ]  end.
Qed.
End c.
End b.
End a.
