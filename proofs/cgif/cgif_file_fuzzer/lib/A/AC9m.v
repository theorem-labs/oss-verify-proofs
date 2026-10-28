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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACab ACam ACai ACan.
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
Lemma ra_B8X_aux : ra_fromX0 KS MT XN B CTX ss_CX (INV_CX MT B) -> ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX0 KS MT XN B CTX ss_B8X (INV_B8X MT B).
Proof.
intros RC RX. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3) & HXB & MLE0).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relow HS AG E10 E32 E10n E32n.
reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |].
clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
-
unfold branch_taken in Hc. rewrite bv_ltu_unsigned in Hc. cbn [sv_denot] in Hc.
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia. apply Z.ltb_lt in Hc.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 49 (mkAF 0 256 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E49, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS | st_ok _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 49 (mkAF 0 256 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E49, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3;
clear HS; rename HS3 into HS  end.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x8b8; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_CX 561%nat (@nil (bv 5)) ltac:(idtac).
ra_handX RC HS. split; [exact (conj Hk3 Eab3)|]. split; [| exact MLE0]. split; [exact HXB | clear - Hc Rslct; lia].
-
assert (Hc' : 256 < slct)
by (clear - Hc E49 Rslct; unfold branch_taken in Hc; rewrite bv_ltu_unsigned in Hc; cbn [sv_denot] in Hc;
rewrite E49, Z.add_0_r, Z_to_bv_bv_unsigned, !unsigned_lit_small in Hc by lia; apply Z.ltb_ge in Hc; lia).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x10c0.
all: try (obl_blk HJ3 E10n E40 Hraw3).
1: awrRA AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
xlift_exit HJ3 HSINK0 Hpf_in.
prreg HS (21%bv : bv 5) R21. replace (Z_to_bv 64 18446744073709551615) with (Z_to_bv 64 (-1)) in R21 by (apply bv_eq; reflexivity).
slot_val HS (Some 10%nat) 0 40 (Z_to_bv 64 18446744073709551615) ltac:(reflexivity) Qrc.
ra_join_slot HS ss_XX 1389%nat ra_deads_X (Some 10%nat) 0 40 ltac:(idtac; ra_join_val HS 1389%nat 13%nat R21 EnR; ra_join_val HS 1389%nat 23%nat Qrc EnC).
ra_handX RX HS. split; [split; [lia | rewrite Eab3; apply Permutation_refl]|].
exists (-1), []. split; [apply rx_model_badlct; [exact HXB | cbn [c_slct]; exact Hc']|]. split; [exact EnR|]. split; [change (1389 + 23)%nat with 1412%nat; rewrite EnC; reflexivity|].
split; [rewrite app_nil_r; exact HSINK|]. split; [cbn; unfold FRAME_OUT; clear - Hw Hh; nia|].
eapply (mle_weaken MT); [exact MLAW | exact MLE0 | apply (xnr_nonneg MT XN MLAW HXN HXMN (w * h)); clear - Hw Hh HnP; nia].
Qed.
Lemma ra_B8X : ra_fromX0 KS MT XN B CTX ss_CX (INV_CX MT B) -> ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX0 KS MT XN B CTX ss_B8X (INV_B8X MT B).
Proof. exact ra_B8X_aux. Qed.
Lemma ra_A2X_aux : ra_fromX0 KS MT XN B CTX ss_B8X (INV_B8X MT B) -> ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX0 KS MT XN B CTX ss_A2X (INV_0X MT B 1).
Proof.
intros RB RX. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3) & MLE0).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relow HS AG E10 E32 E10n E32n.
reshok_bx HS 40%nat.
psrr_branch_tok RUN BR HS SHOK RABspan.
-
assert (HcP : rcur = 6) by (clear - Hc E39 Rrcur; unfold branch_taken in Hc; rewrite (sext32_eqb_small E 39 rcur 6 E39) in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x89c; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_B8X 559%nat ([11; 21]%bv : list (bv 5)) ltac:(idtac).
ra_handX RB HS. split; [exact (conj Hk3 Eab3)|]. split; [right; exact HcP | exact MLE0].
- paj_run_tok RUN HS HJ3 SHOK RABspan; [awrRA AG fpos F EFA3 |]. clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
+
assert (HcN : rcur <> 0) by (clear - Hc0 E39 Rrcur; unfold branch_taken in Hc0; rewrite (sext32_eqb_small E 39 rcur 0 E39) in Hc0 by lia; destruct (Z.eqb_spec rcur 0); [discriminate | assumption]).
assert (Hc6 : rcur <> 6) by (clear - Hc E39 Rrcur; unfold branch_taken in Hc; rewrite (sext32_eqb_small E 39 rcur 6 E39) in Hc by lia; destruct (Z.eqb_spec rcur 6); [discriminate | assumption]).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x10c0; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
xlift_exit HJ3 HSINK0 Hpf_in.
prreg HS (21%bv : bv 5) R21. rewrite (denot_sext32_rc _ 39%nat rcur E39 Rrcur) in R21.
slot_val HS (Some 10%nat) 0 40 (Z_to_bv 64 rcur) ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) Qrc.
ra_join_slot HS ss_XX 1389%nat ra_deads_X (Some 10%nat) 0 40 ltac:(idtac; ra_join_val HS 1389%nat 13%nat R21 EnR; ra_join_val HS 1389%nat 23%nat Qrc EnC).
ra_handX RX HS. split; [split; [lia | rewrite Eab3; apply Permutation_refl]|].
exists (rc_int rcur), []. split; [apply rx_model_prev; cbn [c_rcur]; unfold rc_int; destruct (Z.ltb_spec rcur (2 ^ 31)); clear - Hc6 HcN Rrcur; lia|]. split; [exact EnR|].
split; [change (1389 + 23)%nat with 1412%nat; rewrite EnC; rewrite unsigned_lit_small by (clear - Rrcur; lia); unfold rc_int; destruct (Z.ltb_spec rcur (2 ^ 31)); [rewrite Z.mod_small by (clear - Rrcur; lia); reflexivity | replace (rcur - 2 ^ 32) with (rcur + (-1) * 2 ^ 32) by lia; rewrite Z_mod_plus_full, Z.mod_small by (clear - Rrcur; lia); reflexivity]|].
split; [rewrite app_nil_r; exact HSINK|]. split; [cbn; unfold FRAME_OUT; clear - Hw Hh; nia|].
eapply (mle_weaken MT); [exact MLAW | exact MLE0 | apply (xnr_nonneg MT XN MLAW HXN HXMN (w * h)); clear - Hw Hh HnP; nia].
+ assert (Hc0' : rcur = 0) by (clear - Hc0 E39 Rrcur; unfold branch_taken in Hc0; rewrite (sext32_eqb_small E 39 rcur 0 E39) in Hc0 by lia; destruct (Z.eqb_spec rcur 0); [assumption | discriminate]).
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x89c; [awrRA AG fpos F EFA3 |]. clear_frames.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_B8X 559%nat ([11; 21]%bv : list (bv 5)) ltac:(idtac).
ra_handX RB HS. split; [exact (conj Hk3 Eab3)|]. split; [left; exact Hc0' | exact MLE0].
Qed.
Lemma ra_A2X : ra_fromX0 KS MT XN B CTX ss_B8X (INV_B8X MT B) -> ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX0 KS MT XN B CTX ss_A2X (INV_0X MT B 1).
Proof. exact ra_A2X_aux. Qed.
End d.
End b.
End a.
