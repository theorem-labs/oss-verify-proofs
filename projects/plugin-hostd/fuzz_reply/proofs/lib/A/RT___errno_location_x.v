(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract aerrno_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan's musl __errno_location at 0x8c9a8. *)
(* Modified by Theorem Labs, 2026-10-29: from lib/A/RT___errno_location.v, as the module RT___errno_location_x: cut to the proof of rt___errno_location (the helper lemmas are used by Import) and restated over a generic allocator invariant ARx under lib/Rt/RTx.v's rt_laws (rt___errno_location_x); the corollaries rt___errno_location_of_x (rt___errno_location's statement, unchanged) and rt___errno_location_cf added. *)
(* lib/A/RT___errno_location.v's runtime contract rt___errno_location restated
   over a generic allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of
   lib/Rt/RTx.v (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout,
   rtl_const_cells). RT___errno_location.v is not edited; its helper lemmas are used by Import. The statement is
   W_sites_x.v's aerrno_realizes_x; the proof of rt___errno_location_x is RT___errno_location.v's with AR -> ARx
   (am_layout of proj1 HAR -> rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas
   -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_frame (RT___errno_location.v:112) only; no ARm field; the three-law note (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not
   count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   At the end: rt___errno_location_of_x, whose statement is byte for byte RT___errno_location.v's
   rt___errno_location, from the twin at cgif's AR (ARx := FCiface.AR_nohp, laws RTx.rt_laws_AR); and
   rt___errno_location_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_journal W_contract W_sites.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT___errno_location.
Open Scope Z_scope.
(* the libraries Required above (FCiface -> YF0v; the cf files) set Zify's euclidean-division flag to false
   globally (e.g. Reusable/Q/YW06_cf.v:26); the original's lia steps need it on, as in the original's own build *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module FCI := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.FCiface.
Module CFN := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YGcfNames.
Module NCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0ncf.
Module DCF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YG0dcf.
Module RTX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt.RTx.
Module WSX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.W_sites_x.

Section core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- THE SITE CONTRACT over ARx ---- *)
Theorem rt___errno_location_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx ->
WSX.aerrno_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_errno_location).
Proof.
intros B ARx LAWS ly S hps W regs mem md HPRE.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
unfold cfg_at.
eapply (SRr_msteps frsegs fr_wx W).
{ rewrite restrict_mkst_fx.
  eapply mst_step; [reflexivity | exact (step_addi frsegs _ _ _ _ _ _ _ _ errno_F0 eq_refl errno_D0) |].
  eapply mst_step; [reflexivity | exact (step_addi frsegs _ _ _ _ _ _ _ _ errno_F1 eq_refl errno_D1) |].
  eapply mst_step; [reflexivity | exact (step_jalr_x0 frsegs _ _ _ _ _ _ _ _ errno_F2 eq_refl errno_D2 eq_refl) |].
  apply mst_refl. }
intros md' Hsame _.
rewrite unrestrict_mkst_mrestrict.
pose (r1 := regupd regs (10%bv : bv 5) (v_addi (getr regs (4%bv : bv 5)) (bv_signed (0%bv : bv 12)))).
pose (r2 := regupd r1 (10%bv : bv 5) (v_addi (getr r1 (10%bv : bv 5)) (bv_signed (3932%bv : bv 12)))).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r ?p ?m ?rom) ?d) _ =>
  change (mkst r p m rom) with (mkst r2 (v_jalr (getr r2 (1%bv : bv 5)) (bv_signed (0%bv : bv 12))) m rom) end.
assert (K : forall r : bv 5, r <> (10%bv : bv 5) -> getr r2 r = getr regs r).
{ intros r Hr. unfold r2, r1. rewrite !getr_other by exact Hr. reflexivity. }
assert (R10 : getr r2 (10%bv : bv 5) = w64 (as_tp B - 164)).
{ unfold r2. rewrite getr_same by discriminate. unfold r1. rewrite getr_same by discriminate.
  rewrite errno_value, Htp. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zminus_mod_idemp_l. reflexivity. }
assert (RA : v_jalr (getr r2 (1%bv : bv 5)) (bv_signed (0%bv : bv 12)) = w64 (raZ regs)).
{ rewrite (K (1%bv : bv 5)) by discriminate. change (bv_signed (0%bv : bv 12)) with 0. rewrite Hra.
  unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite RA.
apply SRr_ret. unfold WSX.aentry_post_x.
split; [reflexivity|]. exists r2, mem, md'.
split; [reflexivity|].
split.
{ pose proof (same_but_materialized_frame md md' Hsame) as MF.
  apply (RTX.rtl_frame _ _ _ LAWS ly S hps W mem md mem md' HAR).
  - intros a _ _. reflexivity.
  - intros a Ha. exact Ha.
  - apply MF.
  - apply MF.
  - apply MF.
  - intros a _ _. reflexivity. }
split.
{ intros r Hr. apply K. intros E. unfold acallee_saved in Hr.
  assert (U : bv_unsigned (Z_to_bv 5 r) = 10) by (rewrite E; reflexivity).
  rewrite Z_to_bv_unsigned in U. unfold bv_wrap in U. change (bv_modulus 5) with 32 in U.
  rewrite Z.mod_small in U by lia. lia. }
split; [exact Hsame|].
split; [exact R10|].
split; [intros a _ _ _; reflexivity|].
intros a Ha. exact Ha.
Qed.

(* ---- the instance at cgif's AR (Hp ignored): the statement is RT___errno_location.v's rt___errno_location, byte for byte ---- *)
Corollary rt___errno_location_of_x : forall B, AR_laws frsegs B ->
aerrno_realizes (PI := PB_fr) B (fr_sigma WS_errno_location).
Proof.
  intros B LAWS ly S W regs mem md.
  exact (rt___errno_location_x B (FCI.AR_nohp frsegs B) (RTX.rt_laws_AR frsegs B LAWS) ly S [] W regs mem md).
Qed.

(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt___errno_location_cf : forall B, DCF.AR_laws_cf frsegs B ->
  WSX.aerrno_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_errno_location).
Proof.
  intros B L.
  exact (rt___errno_location_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L)).
Qed.
End cf.

End core.
