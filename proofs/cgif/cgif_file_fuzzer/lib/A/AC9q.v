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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACan ACah ACaf ACae.
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
Lemma ra_FX_aux : ra_fromX0 KS MT XN B CTX ss_PX (INV_PX MT B) -> ra_fromX0 KS MT XN B CTX ss_IX (INV_IX MT B) -> ra_fromX0 KS MT XN B CTX ss_FX (INV_FX MT B).
Proof.
intros RP RI. ra_preludeX.
pose proof HINV as ((Hk3 & Eab3 & K1 & EK & HK1r & HK1s) & HXC & ((E661 & HXK) & EICL) & MLE0).
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (rewrite Eab3; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
reshok_bx HS 40%nat.
fact_of HS 759%nat F300.
set (ics := bv_unsigned (ew E 759)) in F300.
assert (E759 : ew E 759 = Z_to_bv 64 ics) by (symmetry; apply Z_to_bv_bv_unsigned).
lazymatch goal with |- SRr _ _ _ (ra_postX _ _ _ _ ?cxv _) =>
assert (Hics : ics = rx_iclen cxv) by (subst ics; rewrite EICL; apply unsigned_lit_small; pose proof (rx_iclen_bounds cxv); lia) end.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x9fc; [awrRA AG fpos F EFA3|]. clear_frames.
frame_pres HJ3 Hfin3 EFA3 F HFpres4 HFSpres4.
fs_rwA HS E529 HFSpres4.
paj_run_to_sh RUNTOP HS HJ3 0xa38; [awrRA AG fpos F EFA3|]. clear_frames.
fs_roA HS. relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (oblFAX HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
assert (Hidl : 4 <= 2 ^ (ics - 1) <= 256).
{ clear - F300. split; [change 4 with (2 ^ 2); apply Z.pow_le_mono_r; lia | change 256 with (2 ^ 8); apply Z.pow_le_mono_r; lia]. }
Local Ltac joinFIX HS R tgt ics E759 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s :=
let En1 := fresh "En" in let En2 := fresh "En" in let Qt4 := fresh "Qt4" in let Qa6 := fresh "Qa6" in
slot_val HS (Some 2%nat) (-320) (-184) (Z_to_bv 64 ics) ltac:(exact (denot_ics _ 759 ics E759 ltac:(clear - F300; lia))) Qt4;
slot_val HS (Some 2%nat) (-320) (-192) (Z_to_bv 64 (2 ^ (ics - 1))) ltac:(exact (denot_idl _ 759 ics E759 ltac:(clear - F300; lia))) Qa6;
ra_join_slots HS tgt 809%nat ra_deads_FI [(Some 2%nat, -320, -192); (Some 2%nat, -320, -184)]
ltac:(idtac; ra_join_val HS 809%nat 5%nat Qa6 En1; ra_join_val HS 809%nat 6%nat Qt4 En2;
ra_join_fact HS 814%nat (mkAF 4 256 0) ltac:(rewrite En1; rewrite unsigned_lit_small by (clear - Hidl; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - Hidl; lia);
ra_join_fact HS 815%nat (mkAF 3 9 0) ltac:(rewrite En2; rewrite unsigned_lit_small by (clear - F300; lia); rewrite Z.pow_0_r, Z.mod_1_r; clear - F300; lia));
ra_handX R HS;
lazymatch goal with HXC : XC _, E661 : ew _ 661 = _, HK1v : xfacts (_ -> K1 = _), MLE0 : mo_le _ _ _ 0, EICL : ew _ 759 = _, Hics : ics = _, HIL : YO07.flag _ 2 = _ |- _ =>
split; [| split; [exact HXC | split; [split; [split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1v Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]
| split; [rewrite En1, Hics; reflexivity | rewrite En2, Hics; reflexivity]] | split; [exact HIL | exact MLE0]]]] end;
split; [exact Hk3|]; split; [exact Eab3|]; exists K1;
split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EK | split; [exact HK1r | exact HK1s]].
psrr_branch_tok RUN BR HS SHOK RABspan.
-
xbit2 Hc E43 Rfattr HIL.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0xb00; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
joinFIX HS RI ss_IX ics E759 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s.
-
xbit2 Hc E43 Rfattr HIL.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0xab8; [awrRA AG fpos F EFA3|]. clear_frames.
rebaseE HS AG HEv. clear HEv.
joinFIX HS RP ss_PX ics E759 F300 Hidl Hk3 Eab3 K1 EK HK1r HK1s.
Qed.
Lemma ra_FX : ra_fromX0 KS MT XN B CTX ss_PX (INV_PX MT B) -> ra_fromX0 KS MT XN B CTX ss_IX (INV_IX MT B) -> ra_fromX0 KS MT XN B CTX ss_FX (INV_FX MT B).
Proof. exact ra_FX_aux. Qed.
End d.
End b.
End a.
