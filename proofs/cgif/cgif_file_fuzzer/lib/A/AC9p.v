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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACan ACaf ACae.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7.
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
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
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
Variable KS : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B KS.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Variable XN : xnums.
Hypothesis HXM : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xm_lzw XN N idl + 2 * mo_free MT <= xm_rawadd XN N.
Hypothesis HXN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> mo_malloc MT N + xn_lzw XN N idl + 2 * mo_free MT <= xn_rawadd XN N.
Hypothesis HXMN : forall N idl, 1 <= N <= 100000000 -> 2 <= idl <= 256 -> 0 <= xn_lzw XN N idl <= xm_lzw XN N idl.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Local Ltac joinFX HS HJ3 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s vtac rtac netac :=
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x9e4; [awrRA AG fpos F EFA3|]; clear_frames;
let Qa0 := fresh "Qa0" in let HEv := fresh "HEv" in let En := fresh "En" in
prreg HS (10%bv : bv 5) Qa0; vtac Qa0;
rebaseE HS AG HEv; clear HEv;
ra_join HS ss_FX 759%nat ra_deads_F
ltac:(idtac; ra_join_val HS 759%nat 0%nat Qa0 En;
ra_join_fact HS 759%nat (mkAF 3 9 0) ltac:(rewrite En; rewrite ?unsigned_lit_small by rtac; rewrite Z.pow_0_r, Z.mod_1_r; split; [rtac | split; [reflexivity | clear; lia]]));
ra_handX RF' HS;
lazymatch goal with HXC : XC _, E661 : ew _ 661 = _, HK1v : xfacts (_ -> K1 = _), MLE0 : mo_le _ _ _ 0 |- _ =>
split; [| split; [exact HXC | split; [split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1v Hne'); reflexivity]
| rewrite En; netac] | exact MLE0]]] end;
split; [exact Hk3|]; split; [exact Eab3|]; exists K1;
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]].
Lemma ra_EX_aux : ra_fromX0 KS MT XN B CTX ss_FX (INV_FX MT B) -> ra_fromX0 KS MT XN B CTX ss_EX (INV_EX MT B).
Proof.
intros RF'. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3 & K1 & EK & HK1r & HK1s) & HXC & ((E661 & HXK) & E710) & MLE0).
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
fact_of HS 710%nat F251. xne E710 Hne Rne.
assert (Ene : bv_unsigned (ew E 710) = ne) by (rewrite E710; apply unsigned_lit_small; clear - Rne; lia).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x9c4; [awrRA AG fpos F EFA3|]. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (13%bv : bv 5) Ra3. prreg HS (12%bv : bv 5) Ra2.
rewrite <- (Z_to_bv_bv_unsigned 64 (ew E 710)) in Ra2.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (ra_pow2b B LAWS 9 0 (bv_unsigned (ew E 710)) W3 (ms_regs msX) (ms_mem msX) _ TRAWADD_STK (spZ regs) [(raw + 40, raw + 44)] ly S W mem md [(1, fpos)] ly3 S3 k eq_refl HJ3);
[ exact Ra0 | exact Ra3 | exact Ra2 | clear; lia | clear - F251; lia | right; reflexivity ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & K & -> & HJ5 & HK14 & HK10 & HK15 & HKlo & HKs1 & HKs2 & Hav5 & Hpr5 & Hrg5).
clear Ra0 Ra3 Ra2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msX) =>
let kk := eval vm_compute in (run_K A_LIM (SOff 32 0) [] ssx) in
jafter_stretch_hi HS kk regs5 (mrestrict (w_H W3) mem5) POW_CLOB_D 0x9d4 HS2;
specialize (HS2 Hrg5 (regions_kept_all Ev (w_H W3) (ms_mem msX) mem5 _ Hav5 Hpr5));
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS; rebaseE HS AG HEv;
let kk1 := eval vm_compute in (kk + 1)%nat in
lazymatch type of HS with st_ok_pi _ _ ?Ev2 _ _ =>
assert (EK0 : ew Ev2 kk = Z_to_bv 64 (K + 1)) by (rewrite HEv; unfold POW_CLOB_D; cbn [map]; rewrite (ew_havoc_new _ kk _ 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK10);
assert (EKK : ew Ev2 kk1 = Z_to_bv 64 K) by (rewrite HEv; unfold POW_CLOB_D; cbn [map]; change kk1 with (kk + 1)%nat; rewrite Nat.add_1_r;
rewrite (ew_havoc_new _ kk _ 1 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; exact HK14) end;
clear HEv end.
norm_ss HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ5 SHOK RABspan; [awrRA AG fpos F EFA3|]. clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
-
unfold branch_taken in Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => rewrite (denot_and255 Ev _ K EKK ltac:(clear - HKlo; lia)) in Hc end.
cbn [sv_denot] in Hc. rewrite bv_ltu_unsigned, !unsigned_lit_small in Hc by (clear - HKlo; lia).
apply Bool.negb_true_iff in Hc. apply Z.ltb_ge in Hc.
rewrite Ene in HKs1, HKs2.
joinFX HS HJ5 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => rewrite EK0 in Q) ltac:(clear - HKlo Hc; lia)
ltac:(f_equal; symmetry; unfold rx_iclen; rewrite <- Hne, (ra_icl_of_loop K ne HKlo HKs1 HKs2); clear - Hc HKlo; lia).
-
unfold branch_taken in Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => rewrite (denot_and255 Ev _ K EKK ltac:(clear - HKlo; lia)) in Hc end.
cbn [sv_denot] in Hc. rewrite bv_ltu_unsigned, !unsigned_lit_small in Hc by (clear - HKlo; lia).
apply Bool.negb_false_iff in Hc. apply Z.ltb_lt in Hc.
rewrite Ene in HKs1, HKs2.
joinFX HS HJ5 SHOK AG fpos F EFA3 RF' Hk3 Eab3 K1 EK HK1r HK1s ltac:(fun Q => idtac) ltac:(clear; lia)
ltac:(f_equal; symmetry; unfold rx_iclen; rewrite <- Hne, (ra_icl_of_loop K ne HKlo HKs1 HKs2); clear - Hc HKlo; lia).
Qed.
Lemma ra_EX : ra_fromX0 KS MT XN B CTX ss_FX (INV_FX MT B) -> ra_fromX0 KS MT XN B CTX ss_EX (INV_EX MT B).
Proof. exact ra_EX_aux. Qed.
End d.
End b.
End a.
