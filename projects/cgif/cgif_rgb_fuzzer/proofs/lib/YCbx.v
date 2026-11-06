(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI20.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC10 YC2p YC0x YC1b YC2u YC4o YC4q YC4c YC4h YC4a YC27 YC2r YC4u YC52 YCaq YCct YCce YCcd YCc6 YCcb YCc9 YCc5.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0o YG0t YG0r YG0q YC00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Set Printing Width 250.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.
Lemma rt_D_aux : rt_from B ss_X (INV_X B) -> rt_from B ss_E (INV_E B) -> rt_from B ss_D (INV_Bn B 14).
Proof.
intros RX RE. rt_prelude.
pose proof HINV as (Hk0 & Eab3 & HnC). cbn [c_n] in HnC.
relowRT HS AG E10 E11 E32 E10n E11n E32n. reshok HS.
srr_branch_tok tratbl_lib_ok HS SHOK RTBspan.
-
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RTBspan 0x81394.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
ra_join_win HS ss_X 600%nat rt_X_deads_bv ltac:(idtac).
rt_hand RX HS.
split; [cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_fpos c_sp1 c_E0]; lazymatch goal with |- rbv ?Sx ?S3x _ _ => match goal with HJx : ajournal _ _ _ _ _ _ Sx _ _ _ _ _ S3x _ _ _ _ |- _ => apply (rt_bv_j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJx) end end; [clear - Hk0; unfold RGB_COARSE; lia | clear; lia]|].
split; [assert (0 <= EV_RLIB) by (vm_compute; discriminate); clear - Hk0 H; lia | cbn [c_ly c_S]; rewrite Eab3; apply Permutation_refl].
- lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
hc_bool Hc ltac:(fun H => idtac). hc_prop Hc.
lazymatch type of Hc with U E (SMd M_MUL ?eH ?eW) <= _ =>
pose proof (st_ok_facts_ok trasegs _ _ _ HS) as HFO;
pose proof (sv_urange_sound E _ eW 0 65535 HFO ltac:(vm_compute; reflexivity)) as RW;
pose proof (sv_urange_sound E _ eH 0 65535 HFO ltac:(vm_compute; reflexivity)) as RH;
change (bv_unsigned (sv_denot E eW)) with (U E eW) in RW; change (bv_unsigned (sv_denot E eH)) with (U E eH) in RH;
assert (HN : U E (SMd M_MUL eH eW) = U E eW * U E eH)
by (rewrite U_SMd; cbn [zmd_raw]; rewrite zcanon_id by (unfold M64; clear - RW RH; nia); clear; lia);
assert (DN : sv_denot E (SMd M_MUL eH eW) = Z_to_bv 64 (U E eW * U E eH)) by (rewrite denot_lit_U, HN; reflexivity);
rewrite HN in Hc; clear HFO HN;
set (Wd := U E eW) in *; set (Hd := U E eH) in * end.
reshok HS.
aj_run_to_tok tratbl_lib_ok HS HJ3 SHOK RTBspan 0x81324.
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: awrRT AG fpos F EFA3.
clear_frames.
lazymatch goal with HS0 : st_ok _ _ _ _ |- _ => rename HS0 into HS end.
norm_ss HS.
fieldCraw HS 66 140%nat. lazymatch goal with Ef : ew _ 140 = _ |- _ => rename Ef into E140 end.
fieldCraw HS 68 141%nat. lazymatch goal with Ef : ew _ 141 = _ |- _ => rename Ef into E141 end.
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
assert (DN2 : sv_denot Ex e = Z_to_bv 64 (Wd * Hd)) by (rewrite !denot_havoc_below by (vm_compute; reflexivity); exact DN);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (Wd * Hd)) DN2 R20 end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) [20%bv : bv 5]) in
let vals' := eval cbn [map ms_regs restrict] in vals in
pose proof (st_ok_havoc_win trasegs 142 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
assert (E142 : ew (havoc Ex 142 vals') 142 = Z_to_bv 64 (Wd * Hd))
by (rewrite (ew_havoc_new _ 142 vals' 0 (Z_to_bv 64 0)) by (cbn; lia); cbn [nth]; cbn [ms_regs restrict] in R20; exact R20);
clear HS; rename HS3 into HS;
set_regs_rec HS 142%nat vals' 0%nat [20%bv : bv 5] end.
rebaseE HS AG HEv; clear HEv.
rt_hand RE HS.
split; [exact Hk0|]. split; [exact Eab3|]. split; [cbn [c_n]; exact HnC|].
exists Wd, Hd.
split; [rewrite ?ew_havoc_old by nat_side; exact E140|].
split; [rewrite ?ew_havoc_old by nat_side; rewrite E141; rewrite !denot_havoc_below by (vm_compute; reflexivity); reflexivity|].
split; [exact E142|].
split; [clear - RW; lia|]. split; [clear - RH; lia|]. exact Hc.
Qed.
Lemma rt_D : rt_from B ss_X (INV_X B) -> rt_from B ss_E (INV_E B) -> rt_from B ss_D (INV_Bn B 14).
Proof. exact rt_D_aux. Qed.
End b.
End a.
