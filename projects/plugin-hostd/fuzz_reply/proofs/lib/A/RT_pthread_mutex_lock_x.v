(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contract alock_realizes (lib/A/W_sites.v) proved for
   fuzz_reply.asan's musl pthread_mutex_lock at 0x9883c. *)
(* Modified by Theorem Labs, 2026-10-29: from lib/A/RT_pthread_mutex_lock.v, as the module RT_pthread_mutex_lock_x: cut to the proof of rt_pthread_mutex_lock (the helper lemmas are used by Import) and restated over a generic allocator invariant ARx under lib/Rt/RTx.v's rt_laws (rt_pthread_mutex_lock_x); the corollaries rt_pthread_mutex_lock_of_x (rt_pthread_mutex_lock's statement, unchanged) and rt_pthread_mutex_lock_cf added. *)
(* lib/A/RT_pthread_mutex_lock.v's runtime contract rt_pthread_mutex_lock restated
   over a generic allocator invariant ARx (ghost head set Hp threaded) under the five-law record rt_laws of
   lib/Rt/RTx.v (a Theorem Labs lane's, the one record for both images: rtl_frame, rtl_stack, rtl_const, rtl_layout,
   rtl_const_cells). RT_pthread_mutex_lock.v is not edited; its helper lemmas are used by Import. The statement is
   W_sites_x.v's alock_realizes_x; the proof of rt_pthread_mutex_lock_x is RT_pthread_mutex_lock.v's with AR -> ARx
   (am_layout of proj1 HAR -> rtl_layout, al_frame / al_stack -> rtl_frame / rtl_stack, RT_kit / RT_post's AR lemmas
   -> their _x forms there).
   Measured (lines at a working branch 9b1367c7fe1): the original reads AR through
   al_frame (RT_pthread_mutex_lock.v:424) only; no ARm field; the three-law note (RESUME.md:116-122 sha256 704eb9d3afa6; internal record) did not
   count the ARm fields, hence the record's rtl_layout and rtl_const_cells.
   At the end: rt_pthread_mutex_lock_cf, the twin at ARx := ARcf with the laws from AR_laws_cf (RTx.rt_laws_cf).
   QMm W1 (2026-10-31): alock_realizes_x now takes the not-kept premise on the lock word, which the cgif rule does
   not, so rt_pthread_mutex_lock_of_x (the cgif statement from this twin) no longer follows and had no user; it is
   gone. RT_pthread_mutex_lock.v still proves the cgif statement itself. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e YK1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_place W_kit W_img W_sites.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import RT_pthread_mutex_lock.
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
Theorem rt_pthread_mutex_lock_x : forall B
  (ARx : alayout -> astate -> list Z -> world frsegs -> (word -> option byte) -> Model -> Prop),
  RTX.rt_laws frsegs B ARx ->
WSX.alock_realizes_x (PI := PB_fr) B ARx (fr_sigma WS_pthread_mutex_lock).
Proof.
intros B ARx LAWS ly S hps W regs mem md A tb HPRE H10 HA0 HA4 HA12 Htb Htb16 HV0 HIN HDST _.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
set (HW := w_H W) in *.
change (option_map (fun b => bv_unsigned b) (mbyte frsegs (mrestrict HW mem) A) = Some tb) in Htb.
destruct (mbyte frsegs (mrestrict HW mem) A) as [b|] eqn:Hb; [|discriminate Htb].
cbn [option_map] in Htb. injection Htb as Htb.
assert (Hb16 : bv_unsigned b mod 16 = 0) by (rewrite Htb; exact Htb16).
assert (Hst : store_ok frsegs (mrestrict HW mem) (Z_to_bv 64 (A + 4)) 4 = true).
{ apply YN2e.store_ok_writable; [lia | lia |]. intros x Hx. exact (proj1 (HDST x Hx)). }
destruct (store_ok_restrict frsegs HW (w_Hoff W) 4 mem (Z_to_bv 64 (A + 4)) Hst) as [_ HRA].
assert (HVIS : forall x, A + 4 <= x < A + 8 -> HW (Z_to_bv 64 x) = false).
{ intros x Hx. pose proof (HRA (Z.to_nat (x - (A + 4))) ltac:(lia)) as E. unfold woff in E.
  rewrite unsigned_lit_small in E by lia. rewrite Z2Nat.id in E by lia.
  replace (A + 4 + (x - (A + 4))) with x in E by lia. exact E. }
destruct (lk_run regs (mrestrict HW mem) A b H10 HA0 HA4 HA12 Hb Hb16 HV0 Hst) as (RF & Hms & HRF).
unfold cfg_at. change (fr_sigma WS_pthread_mutex_lock) with 0x9883c.
eapply (SRr_msteps frsegs fr_wx W); [exact Hms|].
intros md' Hsame _.
set (bs16 := word_to_le_bytes 4 (w64 16)) in *.
set (mF := wbytes (mrestrict HW mem) (Z_to_bv 64 (A + 4)) bs16) in *.
set (mem' := munrestrict HW mem mF).
assert (L16 : length bs16 = 4%nat) by reflexivity.
(* the bytes of the new memory: the lock word at A + 4 is 16, every other byte is as before *)
assert (MB : forall x, 0 <= x < 2 ^ 64 -> mbyte frsegs (mrestrict HW mem') x =
  if (A + 4 <=? x) && (x <? A + 4 + 4) then nth_error bs16 (Z.to_nat (x - (A + 4)))
  else mbyte frsegs (mrestrict HW mem) x).
{ intros x Hx. destruct (HW (Z_to_bv 64 x)) eqn:Hh.
  - destruct ((A + 4 <=? x) && (x <? A + 4 + 4)) eqn:Hr.
    + exfalso. apply andb_prop in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
      rewrite (HVIS x ltac:(lia)) in Hh. discriminate Hh.
    + unfold mbyte, mrestrict, mem', munrestrict. rewrite Hh. reflexivity.
  - transitivity (mbyte frsegs mF x).
    { unfold mbyte, mrestrict, mem', munrestrict. rewrite Hh. reflexivity. }
    unfold mF. rewrite (wbytes_mbyte frsegs bs16 (mrestrict HW mem) (A + 4) x) by (rewrite ?L16; lia).
    rewrite L16. reflexivity. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (A + 4 <= a < A + 8) ->
  aview frsegs HW mem' a = aview frsegs HW mem a).
{ intros a Ha Hn. unfold aview. rewrite (MB a Ha).
  destruct ((A + 4 <=? a) && (a <? A + 4 + 4)) eqn:E; [|reflexivity].
  exfalso. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia. }
assert (AVW : forall k, (k < 4)%nat ->
  mbyte frsegs (mrestrict HW mem') (A + 4 + Z.of_nat k) = Some (Z_to_bv 8 (le_byte 16 4 k))).
{ intros k Hk. rewrite MB by lia.
  replace ((A + 4 <=? A + 4 + Z.of_nat k) && (A + 4 + Z.of_nat k <? A + 4 + 4)) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace (A + 4 + Z.of_nat k - (A + 4)) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  destruct k as [|[|[|[|k]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. }
assert (PRES : forall a, apresent HW mem a -> apresent HW mem' a).
{ intros a [Hh [b0 Hb0]]. split; [exact Hh|]. unfold mem', munrestrict. rewrite Hh.
  assert (G : mrestrict HW mem (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb0; discriminate).
  apply (wbytes_grows bs16 (mrestrict HW mem) (Z_to_bv 64 (A + 4))) in G. fold mF in G.
  destruct (mF (Z_to_bv 64 a)) as [b1|]; [exists b1; reflexivity | exfalso; exact (G eq_refl)]. }
assert (HAR' : ARx ly S hps W mem' md').
{ pose proof (same_but_materialized_frame md md' Hsame) as MF.
  apply (RTX.rtl_frame _ _ _ LAWS ly S hps W mem md mem' md' HAR).
  - intros a Ha Ho. apply AVQ; [exact Ha|]. intros Hin.
    destruct (HDST a ltac:(lia)) as (_ & Hno & _). exact (Hno Ho).
  - intros a Hv. change (w_H W) with HW in Hv |- *. rewrite aview_mod64 in Hv |- *.
    pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ra. set (a' := a mod 2 ^ 64) in *.
    destruct (Z_le_gt_dec (A + 4) a') as [L1|L1]; [destruct (Z_lt_ge_dec a' (A + 8)) as [L2|L2]|].
    + pose proof (AVW (Z.to_nat (a' - (A + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
      replace (A + 4 + (a' - (A + 4))) with a' in X by lia.
      unfold aview. rewrite X. discriminate.
    + rewrite (AVQ a' Ra ltac:(lia)). exact Hv.
    + rewrite (AVQ a' Ra ltac:(lia)). exact Hv.
  - apply MF.
  - apply MF.
  - apply MF.
  - intros a _ Hh. change (w_H W) with HW in Hh. unfold mem', munrestrict. rewrite Hh. reflexivity. }
assert (RA : v_jalr (getr regs (1%bv : bv 5)) 0 = w64 (raZ regs)).
{ rewrite Hra. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
rewrite RA.
apply SRr_ret. unfold WSX.aentry_post_x.
split; [reflexivity|]. exists RF, mem', md'.
split; [reflexivity|].
split; [exact HAR'|].
split.
{ intros r Hr. apply HRF. unfold acallee_saved in Hr.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  rewrite Z.mod_small by lia. lia. }
split; [exact Hsame|].
split; [exact AVW|].
split; [intros a Ha Hn _; exact (AVQ a Ha Hn)|].
exact PRES.
Qed.


(* ---- the instance at ARcf, the laws from AR_laws_cf ---- *)
Section cf. Context {ci : CFN.CfImg} {cp : CFN.CfParams}.
Corollary rt_pthread_mutex_lock_cf : forall B, DCF.AR_laws_cf frsegs B ->
  WSX.alock_realizes_x (PI := PB_fr) B (NCF.ARcf frsegs B) (fr_sigma WS_pthread_mutex_lock).
Proof.
  intros B L.
  exact (rt_pthread_mutex_lock_x B (NCF.ARcf frsegs B) (RTX.rt_laws_cf frsegs B L)).
Qed.
End cf.

End core.
