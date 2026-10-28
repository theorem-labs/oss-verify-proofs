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
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
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
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Lemma ra_XX_aux : True -> ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389).
Proof.
intros _. ra_preludeX.
destruct HINV as ((Hk3 & HPerm3) & code & bytes & Hmodel & Ecode & Erc & HSINK & Hblen & MLE).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
reshok_bx HS 40%nat.
exitRAX RET RUNF HS HJ3 AG fpos F cfp g E528 E529 Hfin3 HfinS3 Hing3 EE Hra HEV EFA3 EFL3.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msX) =>
exists (bv_unsigned (ew Ex 1402)); exists (code mod 2 ^ 32);
assert (Hrc : 0 <= code mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia);
change (1389 + 13)%nat with 1402%nat in Ecode; change (1389 + 23)%nat with 1412%nat in Erc;
split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; cbn [sv_denot]; rewrite ?Z.add_0_r; unfold w64; rewrite ?Z_to_bv_bv_unsigned;
first [reflexivity | match goal with |- ?g => idtac "RES?" g end]|];
split; [pose proof (bv_unsigned_in_range 64 (ew Ex 1402)) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; clear - Hrg; lia|];
split; [| split; [ unfold ablocks; rewrite blocks_stack_free_state; exact HPerm3
| split; [ exists code, bytes; split; [exact Hmodel|];
split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Ecode, Z_to_bv_bv_unsigned; reflexivity|];
split; [reflexivity|]; split; [cbn [ms_mem]; exact HSINK | exact Hblen]
| first [exact MLE | (eapply (mo_le_set_fs_r MT MLAWF); exact MLE) | match goal with |- ?g => idtac "MLE?" g end] ] ] ];
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 10%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB10 : bv_unsigned (ew Ex 10) = raw) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia);
let fld od w e v Ev nm :=
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 raw cs lo hi wlo whi od w e v HRr HB10 ltac:(cbn; tauto)
ltac:(first [ reflexivity
| cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
first [rewrite (AG 32%nat) by lia; rewrite E32 | rewrite Ev]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ])
ltac:(cbn; clear - Rwfn Rg Rgct Rrattr RWd RHd Rsgct Rloops Hrc; lia) ltac:(cbn; lia)) as nm end in
fld 0 8%N (SOff 53 0) wfn E53 ident:(W0);
fld 8 8%N (SOff 32 0) g E32 ident:(W8); fld 16 8%N (SOff 33 0) gct E33 ident:(W16); fld 24 4%N (SOff 34 0) rattr E34 ident:(W24);
fld 28 2%N (SOff 35 0) Wd E35 ident:(W28); fld 30 2%N (SOff 36 0) Hd E36 ident:(W30); fld 32 2%N (SOff 37 0) sgct E37 ident:(W32);
fld 34 2%N (SOff 38 0) loops E38 ident:(W34);
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 10 raw cs lo hi wlo whi 40 4%N (SOff 1412 0) HRr HB10 ltac:(cbn; tauto) ltac:(cbn; lia)) as W40;
cbn [sv_denot] in W40; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in W40; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in W40; change (N.to_nat 4) with 4%nat in W40; rewrite Erc in W40 end | st_ok _ ?Ex ?ssx (restrict ?Hh ?msX) =>
exists (bv_unsigned (ew Ex 1402)); exists (code mod 2 ^ 32);
assert (Hrc : 0 <= code mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia);
change (1389 + 13)%nat with 1402%nat in Ecode; change (1389 + 23)%nat with 1412%nat in Erc;
split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; cbn [sv_denot]; rewrite ?Z.add_0_r; unfold w64; rewrite ?Z_to_bv_bv_unsigned;
first [reflexivity | match goal with |- ?g => idtac "RES?" g end]|];
split; [pose proof (bv_unsigned_in_range 64 (ew Ex 1402)) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; clear - Hrg; lia|];
split; [| split; [ unfold ablocks; rewrite blocks_stack_free_state; exact HPerm3
| split; [ exists code, bytes; split; [exact Hmodel|];
split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Ecode, Z_to_bv_bv_unsigned; reflexivity|];
split; [reflexivity|]; split; [cbn [ms_mem]; exact HSINK | exact Hblen]
| first [exact MLE | (eapply (mo_le_set_fs_r MT MLAWF); exact MLE) | match goal with |- ?g => idtac "MLE?" g end] ] ] ];
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 10%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict Hh msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB10 : bv_unsigned (ew Ex 10) = raw) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia);
let fld od w e v Ev nm :=
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 raw cs lo hi wlo whi od w e v HRr HB10 ltac:(cbn; tauto)
ltac:(first [ reflexivity
| cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
first [rewrite (AG 32%nat) by lia; rewrite E32 | rewrite Ev]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ])
ltac:(cbn; clear - Rwfn Rg Rgct Rrattr RWd RHd Rsgct Rloops Hrc; lia) ltac:(cbn; lia)) as nm end in
fld 0 8%N (SOff 53 0) wfn E53 ident:(W0);
fld 8 8%N (SOff 32 0) g E32 ident:(W8); fld 16 8%N (SOff 33 0) gct E33 ident:(W16); fld 24 4%N (SOff 34 0) rattr E34 ident:(W24);
fld 28 2%N (SOff 35 0) Wd E35 ident:(W28); fld 30 2%N (SOff 36 0) Hd E36 ident:(W30); fld 32 2%N (SOff 37 0) sgct E37 ident:(W32);
fld 34 2%N (SOff 38 0) loops E38 ident:(W34);
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region_any Ex _ 10 raw cs lo hi wlo whi 40 4%N (SOff 1412 0) HRr HB10 ltac:(cbn; tauto) ltac:(cbn; lia)) as W40;
cbn [sv_denot] in W40; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in W40; change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in W40; change (N.to_nat 4) with 4%nat in W40; rewrite Erc in W40 end  end.
cbn [obj_at LAY_Raw LAY_RawConfig app]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try exact I; first [assumption | clear - Rwfn Rg Rgct Rrattr RWd RHd Rsgct Rloops Hg4096 Hgceil C1 Hrc; lia | match goal with |- ?g => idtac "POST?" g end].
Qed.
Lemma ra_XX : ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389).
Proof. exact (ra_XX_aux I). Qed.
Lemma ra_X1X_aux : ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359).
Proof.
intros RX. ra_preludeX.
pose proof HINV as ((Hk3 & HPerm3) & code & bytes & Hmodel & Ecode & Erc & HSINK & Hblen & MLE).
change (1359 + 13)%nat with 1372%nat in Ecode. change (1359 + 23)%nat with 1382%nat in Erc.
remember (bv_unsigned (ew E 1382)) as rcw eqn:Hrcw in Erc.
assert (E1382 : ew E 1382 = Z_to_bv 64 rcw) by (rewrite Hrcw; symmetry; apply Z_to_bv_bv_unsigned).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
assert (Hpf3 : In (pf, FILE_BLOCK) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hpf_in).
ra_blocks3X Hraw3 Hing3 Hpf3. fold F in HdFR, HdFG.
fs_rwA HS E529 HFSpres3.
paj_run_to_sh RUNTOP HS HJ3 0x10c0. { awrRA AG fpos F EFA3. }
xsink_stretch HFr HSINK.
clear_frames. fs_roA HS.
rebaseE HS AG HEv. clear HEv.
prreg HS (21%bv : bv 5) R21. cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in R21. rewrite ?ew_ewset_other in R21 by lia. rewrite Ecode in R21.
slot_val HS (Some 10%nat) 0 40 (Z_to_bv 64 rcw) ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E1382, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) Qrc.
ra_join_slot HS ss_XX 1389%nat ra_deads_X (Some 10%nat) 0 40
ltac:(idtac; ra_join_val HS 1389%nat 13%nat R21 EnR; ra_join_val HS 1389%nat 23%nat Qrc EnC).
ra_handX RX HS.
split; [exact (conj Hk3 HPerm3)|]. exists code, bytes. split; [exact Hmodel|]. split; [exact EnR|].
split; [change (1389 + 23)%nat with 1412%nat; rewrite EnC, Hrcw, Z_to_bv_bv_unsigned; rewrite Hrcw in Erc; exact Erc|].
split; [exact HSINK | split; [exact Hblen | exact MLE]].
Qed.
Lemma ra_X1X : ra_fromX1 KS MT XN B CTX ss_XX (INV_XX KS MT XN B 1389) -> ra_fromX1 KS MT XN B CTX ss_X1X (INV_XX KS MT XN B 1359).
Proof. exact ra_X1X_aux. Qed.
End d.
End b.
End a.
