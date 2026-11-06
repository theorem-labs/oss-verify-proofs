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
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC46 YC4g YC4c YC4h.
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
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law trasegs B.
Hypothesis FFL : frame_flag_lawP trasegs B.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL.
Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL. Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL.
Lemma ra_X_aux : True -> ra_from B ss_X (INV_X B).
Proof.
intros _. ra_prelude.
destruct HINV as (Hk3 & HPerm3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
reshok_bx HS 40%nat.
exitRA HS HJ3 AG fpos F cfp g E69 E70 Hfin3 HfinS3 Hing3 EE Hra HEV EFA3 EFL3.
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hh ?msX) =>
exists (bv_unsigned (ew Ex 943));
lazymatch type of HJ3 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyF ?SF ?WF _ _ _ =>
assert (HrawF : In (raw, RAW_SIZE) (ablocks B lyF SF)) by (unfold ablocks; rewrite blocks_stack_free_state; exact Hraw3);
destruct (al_blocks _ _ LAWS _ _ _ _ _ raw RAW_SIZE (proj1 HJ3) HrawF) as (_ & _ & _ & _ & HrpresF & _); change (req_size RAW_SIZE) with 48 in HrpresF;
destruct (ra_val_mem_of_present4 (w_H WF) (ms_mem msX) (raw + 40) ltac:(intros i Hi; apply (fun Hq => proj1 (HrpresF (raw + 40 + i) Hq)); clear -Hi; lia)) as (rcz & Hrc & Vrc)
end;
exists rcz;
split; [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; cbn [sv_denot]; rewrite ?Z.add_0_r; unfold w64; rewrite ?Z_to_bv_bv_unsigned;
first [reflexivity | match goal with |- ?g => idtac "RES?" g end]|];
split; [pose proof (bv_unsigned_in_range 64 (ew Ex 943)) as Hrg; change (bv_modulus 64) with (2 ^ 64) in Hrg; clear - Hrg; lia|];
split; [| unfold ablocks; rewrite blocks_stack_free_state; exact HPerm3 ];
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 10%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_region) in
pose proof (st_ok_region_nth Ex ssx (restrict Hh msX) i r HS ltac:(vm_compute; reflexivity)) as HRr; cbn [ms_mem restrict] in HRr;
assert (HB10 : bv_unsigned (ew Ex 10) = raw) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 10%nat) by lia; rewrite E10; apply unsigned_lit_small; lia);
let fld od w e v Ev nm :=
lazymatch type of HRr with region_ok _ _ _ (YQ0b.mkRegion (Some 10%nat) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 10 raw cs lo hi wlo whi od w e v HRr HB10 ltac:(cbn; tauto)
ltac:(first [ reflexivity
| cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
first [rewrite (AG 32%nat) by lia; rewrite E32 | rewrite Ev]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ])
ltac:(unfold A_cgif_writecb; cbn; lia) ltac:(cbn; lia)) as nm end in
fld 0 8%N (SLit A_cgif_writecb) A_cgif_writecb E32 ident:(W0);
fld 8 8%N (SOff 32 0) g E32 ident:(W8); fld 16 8%N (SOff 33 0) gct E33 ident:(W16); fld 24 4%N (SOff 34 0) rattr E34 ident:(W24);
fld 28 2%N (SOff 35 0) Wd E35 ident:(W28); fld 30 2%N (SOff 36 0) Hd E36 ident:(W30); fld 32 2%N (SOff 37 0) sgct E37 ident:(W32);
fld 34 2%N (SOff 38 0) loops E38 ident:(W34)
end.
cbn [obj_at LAY_Raw LAY_RawConfig app]. unfold field_ok. cbn [fst snd N.to_nat Z.of_N].
change (2 ^ (8 * 8)) with (2 ^ 64). change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 2)) with 65536.
repeat split; try exact I; first [assumption | unfold A_cgif_writecb; clear - Rg Rgct Rrattr RWd RHd Rsgct Rloops Hg4096 Hgceil C1 Hrc; lia].
Qed.
Lemma ra_X : ra_from B ss_X (INV_X B).
Proof. exact (ra_X_aux I). Qed.
Lemma ra_X1_aux : ra_from B ss_X (INV_X B) -> ra_from B ss_X1 (INV_X B).
Proof.
intros RX. ra_prelude.
pose proof HINV as (Hk3 & HPerm3).
assert (Hraw3 : In (raw, RAW_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hraw_in).
assert (Hing3 : In (g, CGIF_SIZE) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm3|]; exact Hing).
ra_blocks3 Hraw3 Hing3. fold F in HdFR, HdFG.
fs_rwA HS E70 HFSpres3.
aj_run_to_sh tratbl_lib_ok HS HJ3 0x89434. { awrRA AG fpos F EFA3. }
clear_frames. fs_roA HS.
match type of HS with st_ok _ _ ?ssx _ => idtac "X1-END" ssx end.
rebaseE HS AG HEv. clear HEv.
ra_join HS ss_X 930%nat ra_deads_X ltac:(idtac).
ra_hand RX HS. exact HINV.
Qed.
Lemma ra_X1 : ra_from B ss_X (INV_X B) -> ra_from B ss_X1 (INV_X B).
Proof. exact ra_X1_aux. Qed.
End b.
End a.
