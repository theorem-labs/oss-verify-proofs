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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YF9i YCeb YCe8 YCfq YCdy YCfr YCfu YCe9 YChv YChx YChw.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TrbLib B.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law trbsegs B.
Hypothesis FFL : frame_flag_lawP trbsegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Lemma rn_X_aux : True -> rn_from B ss_X.
Proof.
rn_prelude.
pose proof Hcfg as Hc'. cbn [obj_at LAY_RawConfig] in Hc'.
destruct Hc' as (_ & [_ R8] & [_ R16] & [_ R24] & [_ R28] & [_ R30] & [_ R32] & [_ R34] & _).
cbn [fst snd N.to_nat Z.of_N] in R8, R16, R24, R28, R30, R32, R34.
change (2 ^ (8 * 8)) with (2 ^ 64) in R8, R16. change (2 ^ (8 * 4)) with (2 ^ 32) in R24. change (2 ^ (8 * 2)) with 65536 in R28, R30, R32, R34.
reshok_bx HS 35%nat.
exitR HS HJ3 AG fpos F cfgp g E57 E58 Hfin3 HfinS3 Hing3 EE Hra HEV EFA3 EFL3.
exists res. split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres; reflexivity|].
right. split; [clear - Hres4096; lia|]. split; [exact Hsg|].
split; [unfold ablocks; rewrite blocks_stack_free_state; fold (ablocks B ly3 S3); rewrite Eab3; apply Permutation_sym; apply Permutation_cons_append|].
split; [intros blc i Hbl Hi; apply Ares; [exact Hbl | exact Hi]|].
split; [exact Tres|].
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 63%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB65 : bv_unsigned (ew Ex 63) = res) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite Rres; apply unsigned_lit_small; lia);
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion (Some 63%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 0 8%N (SLit A_cgif_writecb) A_cgif_writecb HRr HB65 ltac:(cbn; tauto) eq_refl ltac:(unfold A_cgif_writecb; cbn; lia) ltac:(cbn; lia)) as W0;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 8 8%N (SOff 32 0) g HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 32%nat) by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W8;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 16 8%N (SOff 33 0) pgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W16;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 24 4%N (SOff 34 0) rattr HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W24;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 28 2%N (SOff 36 0) Wd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W28;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 30 2%N (SOff 37 0) Hd HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W30;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 32 2%N (SOff 38 0) sgct HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W32;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 34 2%N (SOff 39 0) loops HRr HB65 ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn; lia) ltac:(cbn; lia)) as W34;
pose proof (field_of_region Ex _ 63 res cs lo hi wlo whi 40 4%N (SLit R_PENDING) R_PENDING HRr HB65 ltac:(cbn; tauto) eq_refl ltac:(unfold R_PENDING; cbn; lia) ltac:(cbn; lia)) as W40
end end.
cbn [obj_at LAY_Raw LAY_RawConfig app]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try exact I; first [assumption | unfold A_cgif_writecb, R_PENDING; clear - R8 R16 R24 R28 R30 R32 R34 Hg4096 Hgceil C1; lia].
Qed.
Lemma rn_X : rn_from B ss_X.
Proof. exact (rn_X_aux I). Qed.
End b.
End a.
