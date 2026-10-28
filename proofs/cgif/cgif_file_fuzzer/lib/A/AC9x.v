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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACam ACai ACaj ACak ACan ACap.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACah.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC7y YC85 YC88.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba AC9z ACa3 ACa4 ACa5 ACa6 ACa7 ACa8 ACkb ACk9 ACka.
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
Lemma ra_TfX_aux : ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B).
Proof.
intros RX. ra_preludeX.
pose proof HINV as ((Hk3 & _ & HPerm3) & HXC & E1077 & HVNONE & HMET).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n. reshok_bx HS 40%nat.
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0x10b8.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
clear_frames.
rebaseE HS AG HEv. clear HEv.
xlift_exit HJ3 HSINK0 Hpf_in.
prreg HS (21%bv : bv 5) R21. rewrite E1077 in R21.
slot_val HS (Some 10%nat) 0 40 (Z_to_bv 64 5) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E1077, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) Qrc.
ra_join_slot HS ss_X1X 1359%nat ra_deads_X (Some 10%nat) 0 40 ltac:(idtac; ra_join_val HS 1359%nat 13%nat R21 EnR; ra_join_val HS 1359%nat 23%nat Qrc EnC).
ra_handX RX HS. split; [split; [rewrite HEV; clear - Hk3; lia | exact HPerm3]|].
exists 5, []. split.
{ lazymatch goal with |- rx_model ?cxv ?xxv = _ => rewrite (rx_model_lzw cxv xxv (proj1 HXC) (proj2 (proj2 HXC))) end.
cbn [x_IMG x_LCT]. unfold lzw_vnone in HVNONE. rewrite HVNONE. reflexivity. }
split; [exact EnR|]. split; [change (1359 + 23)%nat with 1382%nat; rewrite EnC; reflexivity|].
split; [rewrite app_nil_r; exact HSINK|]. split; [cbn; unfold FRAME_OUT; clear - Hw Hh; nia|].
destruct HMET as (acc & Hle & Hacc & HaM & HaN). cbn [c_S c_w c_h] in Hle, HaM, HaN.
eapply (mle_weaken MT); [exact MLAW | exact Hle | clear - HaN; lia].
Qed.
Lemma ra_TfX : ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359) -> ra_fromX0 KS MT XN B CTX ss_TfX (INV_TfX MT XN B).
Proof. exact ra_TfX_aux. Qed.
Lemma ra_T0X_aux : ra_fromX1 KS MT XN B CTX ss_G2X (INV_G2X KS MT XN B) -> ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B).
Proof.
intros RG.
assert (RT1 : ra_fromX0 KS MT XN B CTX ss_T1X (INV_T1X MT XN B)) by (eapply ra_T1X; eassumption).
assert (RT2 : ra_fromX0 KS MT XN B CTX ss_T2X (INV_T2X MT XN B)) by (eapply ra_T2X; eassumption).
ra_preludeX.
pose proof HINV as ((Hk3 & (K1 & EK & HK1r & HK1s) & (bb & Lbb & M & E1059 & E1060 & HPerm3 & Hbb4096 & HM & Abb & Tbb)) & HXC & ((E661 & HXK) & EICL) & HLZ & HMET).
xk1 HXK EK HK1r HK1v.
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; right; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
relowC HS AG E10 E11 E32 E10n E11n E32n.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
xbb_intro HPerm3 HLZ.
norm_ss HS. reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (obl_blk HJ3 E10n E40 Hraw3).
all: try (oblFAX HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xblk_stretch HFr HGout.
clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
-
assert (Hgce : YO07.flag fattr 1 || YO07.flag rattr 1 = true).
{ generalize Hc; intros HcX. unfold branch_taken in HcX.
erewrite (denot_or_and1_t _ 43%nat 34%nat fattr rattr) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact E43 | exact E34] | clear - Rfattr; lia | clear - Rrattr; lia]).
cbn [sv_denot] in HcX. rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (clear; destruct (_ || _); cbn; lia).
destruct (_ || _); [reflexivity | discriminate]. }
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0xe28.
all: try (oblFAX HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xblk_stretch HFr HGout.
clear_frames.
xsplit8 HS 80.
reshok_bx HS 40%nat.
paj_run_tok RUN HS HJ3 SHOK RABspan.
all: try (oblFAX HJ3 E11n E40 HRA HAR Hfin Hcid0 Hflo Hfhi Hfal).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRA AG fpos F EFA3.
xblk_stretch HFr HGout.
clear_frames.
psrr_branch_tok RUN BR HS SHOK RABspan.
+
assert (Hft : YO07.flag fattr 1 = false).
{ generalize Hc0; intros HcX. unfold branch_taken in HcX.
erewrite (denot_and1_sw _ 43%nat fattr) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E43 | clear - Rfattr; lia]).
cbn [sv_denot] in HcX. rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (first [clear - Rfattr; pose proof (Z_land_upper fattr 1 ltac:(lia)); pose proof (Z.land_nonneg fattr 1); lia | clear; lia]).
unfold YO07.flag. rewrite HcX. reflexivity. }
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_T1X 3000%nat ra_deads_Tc ltac:(idtac).
ra_handX RT1 HS.
split; [| split; [exact HXC | split; [| split; [| split]]]].
{ solve_INV_T0 Hk3 EK HK1r HK1s E1059 E1060 HPerm3 Hbb4096 HM Abb Tbb. }
{ pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{ exists out. split; [exact Hls|]. rewrite !ew_havoc_old by (clear - PBASE PBLO; lia).
rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
rewrite !unsigned_lit_small by (first [clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia | clear - XBB XF HML; unfold xbfacts in XBB; unfold xfacts in XF, HML; lia]).
split; [exact HGout | split; [exact HMo | exact HM16]]. }
{ exact HMET. }
{ split; [exact Hgce | exact Hft]. }
+
assert (Hft : YO07.flag fattr 1 = true).
{ generalize Hc0; intros HcX. unfold branch_taken in HcX.
erewrite (denot_and1_sw _ 43%nat fattr) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E43 | clear - Rfattr; lia]).
cbn [sv_denot] in HcX. rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (first [clear - Rfattr; pose proof (Z_land_upper fattr 1 ltac:(lia)); pose proof (Z.land_nonneg fattr 1); lia | clear; lia]).
unfold YO07.flag. rewrite HcX. reflexivity. }
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_T2X 3000%nat ra_deads_Tc ltac:(idtac).
ra_handX RT2 HS.
split; [| split; [exact HXC | split; [| split; [| split]]]].
{ solve_INV_T0 Hk3 EK HK1r HK1s E1059 E1060 HPerm3 Hbb4096 HM Abb Tbb. }
{ pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{ exists out. split; [exact Hls|]. rewrite !ew_havoc_old by (clear - PBASE PBLO; lia).
rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
rewrite !unsigned_lit_small by (first [clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia | clear - XBB XF HML; unfold xbfacts in XBB; unfold xfacts in XF, HML; lia]).
split; [exact HGout | split; [exact HMo | exact HM16]]. }
{ exact HMET. }
{ split; [exact Hgce | exact Hft]. }
-
assert (Hgce0 : YO07.flag fattr 1 || YO07.flag rattr 1 = false).
{ generalize Hc; intros HcX. unfold branch_taken in HcX.
erewrite (denot_or_and1_t _ 43%nat 34%nat fattr rattr) in HcX by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact E43 | exact E34] | clear - Rfattr; lia | clear - Rrattr; lia]).
cbn [sv_denot] in HcX. rewrite bv_eqb_unsigned, !unsigned_lit_small in HcX by (clear; destruct (_ || _); cbn; lia).
destruct (_ || _); [discriminate | reflexivity]. }
paj_run_to_tok RUNTO HS HJ3 SHOK RABspan 0xed4; [awrRA AG fpos F EFA3|].
xblk_stretch HFr HGout.
clear_frames.
xlift_exit HJ3 HSINK0 Hpf_in. clear Hpf3'.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_G2X 1159%nat ra_deads_G2 ltac:(idtac).
ra_handX RG HS.
split; [| split; [exact HXC | split; [| split; [| split]]]].
{ solve_INV_T0 Hk3 EK HK1r HK1s E1059 E1060 HPerm3 Hbb4096 HM Abb Tbb. }
{ pose proof HK1v as HK1w; unfold xfacts in HK1w.
split; [split; [rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact E661
| intros Hne'; rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); rewrite EK, (HK1w Hne'); reflexivity]
| rewrite !ew_havoc_old by (clear - PBASE PBLO; lia); exact EICL]. }
{ exists out. split; [exact Hls|]. rewrite !ew_havoc_old by (clear - PBASE PBLO; lia).
rewrite E1059, E1060. rewrite (Z.mod_small M) by (clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia).
rewrite !unsigned_lit_small by (first [clear - HM HLbbmax; unfold MALLOC_MAX in HLbbmax; lia | clear - XBB XF HML; unfold xbfacts in XBB; unfold xfacts in XF, HML; lia]).
split; [exact HGout | split; [exact HMo | exact HM16]]. }
{ exact HMET. }
{ unfold rx_gce, rx_ganim; cbn [c_rattr c_fattr c_disp c_delay c_tidx]. rewrite Bool.orb_comm, Hgce0. rewrite app_nil_r. exact HSINK. }
Qed.
Lemma ra_T0X : ra_fromX1 KS MT XN B CTX ss_G2X (INV_G2X KS MT XN B) -> ra_fromX0 KS MT XN B CTX ss_T0X (INV_T0X MT XN B).
Proof. exact ra_T0X_aux. Qed.
End d.
End b.
End a.
