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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCbe.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00 YI0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba ACb7.
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
Section c.
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
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Variable MT : ameter_ops.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MLAWF : ameter_fs_laws MT.
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Hypothesis HGOT7 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 7)) 8 (BASE + AF_asan3_cgif_raw_newgif).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Lemma rn_XX_aux : True -> rn_fromX K MT B wfn hw ss_XX PRE_X.
Proof.
rn_preludeX.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as (_ & [_ R8] & [_ R16] & [_ R24] & [_ R28] & [_ R30] & [_ R32] & [_ R34] & _).
cbn [fst snd N.to_nat Z.of_N] in R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
reshok_bx HS 35%nat.
exitRX RET RUNF HS HJ3 AG fpos F cfgp g E528 E529 Hfin3 HfinS3 Hing3 EE Hra HEV EFA3 EFL3.
exists res. split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres; reflexivity|].
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MLAWF); exact MLE|].
right. split; [clear - Hres4096; lia|]. split; [exact Hsg|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); eapply Permutation_trans; [exact Eab3|]; apply Permutation_sym; apply Permutation_cons_append|].
split; [intros blc i Hbl Hi; apply Ares; [exact Hbl | exact Hi]|].
split; [exact Tres|].
split; [| lazymatch goal with H : asink_at _ _ _ _ _ _ |- _ => exact H end].
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 534%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB65 : bv_unsigned (ew Ex 534) = res) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres; apply unsigned_lit_small; lia);
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 0 8%N (SOff 41 0) wfn HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E41, Z.add_0_r, unsigned_lit_small by lia; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W0;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 8 8%N (SOff 32 0) g HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W8;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 16 8%N (SOff 33 0) pgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W16;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 24 4%N (SOff 34 0) rattr HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W24;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 28 2%N (SOff 36 0) Wd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W28;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 30 2%N (SOff 37 0) Hd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W30;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 32 2%N (SOff 38 0) sgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W32;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 34 2%N (SOff 39 0) loops HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W34;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 40 4%N (SLit R_PENDING) R_PENDING HRr HB65 ltac:(cbn; tauto) eq_refl ltac:(unfold R_PENDING; cbn; lia) ltac:(cbn; lia)) as W40
end | st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 534%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB65 : bv_unsigned (ew Ex 534) = res) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres; apply unsigned_lit_small; lia);
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion (Some 534%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 0 8%N (SOff 41 0) wfn HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E41, Z.add_0_r, unsigned_lit_small by lia; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W0;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 8 8%N (SOff 32 0) g HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W8;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 16 8%N (SOff 33 0) pgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W16;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 24 4%N (SOff 34 0) rattr HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W24;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 28 2%N (SOff 36 0) Wd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W28;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 30 2%N (SOff 37 0) Hd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W30;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 32 2%N (SOff 38 0) sgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W32;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 34 2%N (SOff 39 0) loops HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W34;
pose proof (field_of_region Ex _ 534 res cs lo hi wlo whi 40 4%N (SLit R_PENDING) R_PENDING HRr HB65 ltac:(cbn; tauto) eq_refl ltac:(unfold R_PENDING; cbn; lia) ltac:(cbn; lia)) as W40
end  end.
cbn [obj_at LAY_Raw LAY_RawConfig app]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try exact I; first [assumption | unfold R_PENDING; clear - R8 R16 R24 R28 R30 R32 R34 Hg4096 Hgceil C1 Rwfn; lia].
Qed.
Lemma rn_XX : rn_fromX K MT B wfn hw ss_XX PRE_X.
Proof. exact (rn_XX_aux I). Qed.
End c.
End b.
End a.
