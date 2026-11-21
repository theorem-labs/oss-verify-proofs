(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC ZHarnessC ZInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC ZApiOk ZApiOkC ZLoopFactsC InflateCallsC RefZApi RefInflateSafeD.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zc_kit Zc_drc Zc_itout.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Transparent the_zapiC.
Notation zc := the_zapiC.

Definition u2_tin (x : u2L zc) : Z := ZIface.zs_total_in (ZApiInst.iz_z (u2_is zc x)).
Definition u2_tout (x : u2L zc) : Z := ZIface.zs_total_out (ZApiInst.iz_z (u2_is zc x)).

Definition u2_next (x : u2L zc) (src : list Z) (dlen : Z) (is' : ISC zc) (consumed : Z) (bs : list Z) : u2L zc :=
  mkU2L zc is' 0 0 (zdrop consumed (u2_rest zc x)) (zlength src - u2_tin x - consumed) (dlen - u2_tout x - zlength bs) (rev_append bs (u2_orev zc x)).

Definition U2I (dlen : Z) (src : list Z) (x : u2L zc) : Prop :=
  u2_reach zc dlen src x /\ ZApiOkC.UI dlen x /\ ZLoopFactsC.UT src dlen x /\ 0 <= u2_tout x < 2^64.

Lemma U2I_init : forall dlen src, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src ->
  U2I dlen src (u2_x0 zc dlen src).
Proof.
  intros dlen src HD HS HB. pose proof (u2_reach_x0 zc dlen src) as R.
  destruct (ZLoopFactsC.u2_reach_UT src dlen _ HD HS HB R) as [UI UT]. split; [exact R| split; [exact UI| split; [exact UT|]]].
  unfold u2_tout, u2_x0. cbv delta [the_zapiC]. cbn [u2_is ic_init ZApiInstC.zinstC]. unfold ZApiInst.zi_init. cbn [ZApiInst.iz_z]. rewrite (proj2 ZApiOk.iz0_totals). lia.
Qed.

Lemma U2I_shape : forall dlen src x, U2I dlen src x ->
  let rest := u2_rest zc x in
  0 <= u2_tin x /\ u2_tin x + zlength rest = zlength src /\ rest = zdrop (u2_tin x) src
  /\ u2_tout x = zlength (u2_orev zc x) /\ u2_aout zc x + u2_left zc x + zlength (u2_orev zc x) = dlen
  /\ (u2_len zc x = 0 \/ u2_ain zc x = 0) /\ (u2_left zc x = 0 \/ u2_aout zc x = 0)
  /\ 0 <= u2_ain zc x /\ 0 <= u2_len zc x /\ u2_len zc x + u2_ain zc x = zlength rest
  /\ 0 <= u2_aout zc x /\ 0 <= u2_left zc x
  /\ Forall (fun b => 0 <= b < 256) rest /\ 0 <= u2_tout x < 2^64.
Proof.
  intros dlen src x (R & UI & UT & TO). cbv zeta.
  destruct UI as (HJ & HB & Hain & Hlen & Hsum & Hrl & Haout & Hleft & Hle).
  destruct UT as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
  unfold u2_tout, u2_tin in *. change (@ZIface.zlength) with (@Prelim.zlength) in *. change (@ZIface.zskipn Z) with (@Prelim.zdrop) in *.
  repeat (split; [first [assumption | lia] |]). lia.
Qed.

Lemma u2_trip : forall dlen src x ok, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> U2I dlen src x ->
  let '(is', consumed, bs, rc) := ic_inflate zc (zdrop (u2_tin x) src) (u2_is zc x) (dlen - u2_tout x) ok in
  0 <= zlength bs <= dlen - u2_tout x
  /\ 0 <= u2_tout (u2_next x src dlen is' consumed bs) < 2^64
  /\ - 2^31 <= rc < 2^31
  /\ (forall x', u2_stepP zc ok x = inl x' ->
        x' = u2_next x src dlen is' consumed bs /\ rc = Z_OK /\ 0 <= consumed <= zlength src - u2_tin x
        /\ (ok = true -> U2I dlen src x'))
  /\ (forall x' err, u2_stepP zc ok x = inr (Some (x', err)) -> x' = u2_next x src dlen is' consumed bs /\ err = rc /\ rc <> Z_OK)
  /\ (u2_wants zc x = ZApiInstC.zic_wants_window (zdrop (u2_tin x) src) (u2_is zc x) (dlen - u2_tout x)).
Proof.
  intros dlen src x ok HD HS UX.
  pose proof (U2I_shape dlen src x UX) as SH. cbv zeta in SH. destruct SH as (TIN0 & TINS & EREST & TOUT & SUM & LA & LO & AIN0 & LEN0 & SUMI & AOUT0 & LEFT0 & RESTF & TO64).
  unfold U2I, u2_next, u2_tout, u2_tin in *. cbv delta [the_zapiC] in *.
  pose proof UX as (R & UI0 & UT0 & _).
  pose proof (ZLoopFactsC.u2_refill_shape src dlen x HD UI0 UT0) as RS.
  pose proof (ZApiOkC.u2_step dlen x ok HD UI0) as STEP.
  pose proof (ZLoopFactsC.u2_step_UT src dlen x ok) as STEPT.
  assert (RSTEP : forall x', ok = true -> u2_stepP _ ok x = inl x' -> u2_reach _ dlen src x') by (intros x' -> E; eapply u2_reach_step; [exact R| exact E]).
  unfold u2_wants, u2_inp, u2_ao. unfold u2_stepP in STEP, STEPT, RSTEP |- *.
  destruct (u2_refill _ x) as [[[ao lf] ai] ln]. cbv zeta in RS.
  destruct RS as (Eai & Eln & Eao & Elf & Einp & Htin & Htout).
  change (@ZIface.zlength) with (@Prelim.zlength) in *. change (@ZIface.zfirstn Z) with (@Prelim.ztake) in *. change (@ZIface.zskipn Z) with (@Prelim.zdrop) in *.
  set (tin := ZIface.zs_total_in (ZApiInst.iz_z (u2_is ZApiInstC.zinstC x))) in *.
  set (tout := ZIface.zs_total_out (ZApiInst.iz_z (u2_is ZApiInstC.zinstC x))) in *.
  rewrite Einp, Eao in STEP, STEPT, RSTEP |- *.
  cbn [ic_inflate ZApiInstC.zinstC] in *.
  pose proof UI0 as (HJ & HB & _).
  assert (HI : RefInflateSafeD.INV (ZApiInst.iz_s (u2_is _ x))) by (apply ZLoopFactsC.JC_INV; exact HJ).
  assert (HBi : RefZApi.bytes_ok (zdrop tin src)).
  { unfold RefZApi.bytes_ok. change (@Prelim.zdrop) with (@ZIface.zskipn Z) in *. rewrite EREST in RESTF. exact RESTF. }
  assert (LIN : zlength (zdrop tin src) = zlength src - tin) by (unfold zdrop, zlength in *; rewrite length_skipn; lia).
  unfold ZBC_MAX, ZC_MAX in HD, HS.
  pose proof (ZLoopFactsC.ic_inflate_factsC (zdrop tin src) (u2_is _ x) (dlen - tout) ok HI HBi ltac:(change (@ZIface.zlength) with (@Prelim.zlength); lia) ltac:(lia)) as CF.
  pose proof (zic_total_out_range (zdrop tin src) (u2_is _ x) (dlen - tout) ok HI HBi ltac:(change (@ZIface.zlength) with (@Prelim.zlength); lia) ltac:(lia) TO64) as TR.
  pose proof (zic_rc (zdrop tin src) (u2_is _ x) (dlen - tout) ok) as RCR. unfold cint in RCR.
  destruct (ZApiInstC.zic_inflate (zdrop tin src) (u2_is _ x) (dlen - tout) ok) as [[[is' consumed] bs] rc].
  cbn [snd] in RCR. change (@ZIface.zlength) with (@Prelim.zlength) in CF. destruct CF as (HI' & Hbs & HTO & HOK).
  rewrite Eai, Eln, Elf in STEP, STEPT, RSTEP |- *.
  split; [exact Hbs|]. split; [cbn [u2_is]; exact TR|]. split; [exact RCR|].
  split; [| split; [| reflexivity]].
  - intros x' E. destruct (u_step_ok (zlength src - tin) (dlen - tout) consumed bs rc) eqn:OK; [| discriminate E].
    destruct (Z.eqb_spec rc Z_OK) as [RC|RC]; [| discriminate E]. injection E as <-.
    unfold u_step_ok in OK. subst rc. cbn [Z.eqb Z_OK negb orb] in OK. rewrite !Bool.andb_true_iff in OK.
    destruct (HOK eq_refl) as [O2 _]. destruct OK as [O1 _]. apply Z.leb_le in O1.
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
    intros Hok. cbn [Z.eqb Z_OK] in STEP, STEPT, RSTEP.
    pose proof (RSTEP _ Hok eq_refl) as R'. pose proof (proj1 STEP) as UI'. pose proof (STEPT _ HD HS UI0 UT0 eq_refl) as UT'.
    split; [exact R'| split; [exact UI'| split; [exact UT'| cbn [u2_is]; exact TR]]].
  - intros x' err E. destruct (u_step_ok (zlength src - tin) (dlen - tout) consumed bs rc) eqn:OK; [| discriminate E].
    destruct (Z.eqb_spec rc Z_OK) as [RC|RC]; [discriminate E|]. injection E as <- <-. split; [reflexivity| split; [reflexivity| exact RC]].
Qed.

(* compress #16582 carry, k3 (cmpcarry-pu): on a Z_BUF_ERROR return the consumed count is in range (u2_end's B4) *)
Lemma u2_trip_buf : forall dlen src x ok, 0 < dlen <= ZBC_MAX -> zlength src <= ZBC_MAX -> U2I dlen src x ->
  let '(is', consumed, bs, rc) := ic_inflate zc (zdrop (u2_tin x) src) (u2_is zc x) (dlen - u2_tout x) ok in
  rc = Z_BUF_ERROR -> 0 <= consumed <= zlength src - u2_tin x.
Proof.
  intros dlen src x ok HD HS UX.
  pose proof (U2I_shape dlen src x UX) as SH. cbv zeta in SH. destruct SH as (TIN0 & TINS & EREST & TOUT & SUM & LA & LO & AIN0 & LEN0 & SUMI & AOUT0 & LEFT0 & RESTF & TO64).
  unfold U2I, u2_tout, u2_tin in *. cbv delta [the_zapiC] in *.
  pose proof UX as (R & UI0 & UT0 & _).
  change (@ZIface.zlength) with (@Prelim.zlength) in *. change (@ZIface.zfirstn Z) with (@Prelim.ztake) in *. change (@ZIface.zskipn Z) with (@Prelim.zdrop) in *.
  set (tin := ZIface.zs_total_in (ZApiInst.iz_z (u2_is ZApiInstC.zinstC x))) in *.
  set (tout := ZIface.zs_total_out (ZApiInst.iz_z (u2_is ZApiInstC.zinstC x))) in *.
  cbn [ic_inflate ZApiInstC.zinstC] in *.
  pose proof UI0 as (HJ & HB & _).
  assert (HI : RefInflateSafeD.INV (ZApiInst.iz_s (u2_is _ x))) by (apply ZLoopFactsC.JC_INV; exact HJ).
  assert (HBi : RefZApi.bytes_ok (zdrop tin src)).
  { unfold RefZApi.bytes_ok. change (@Prelim.zdrop) with (@ZIface.zskipn Z) in *. rewrite EREST in RESTF. exact RESTF. }
  assert (LIN : zlength (zdrop tin src) = zlength src - tin) by (unfold zdrop, zlength in *; rewrite length_skipn; lia).
  assert (LIN' : ZIface.zlength (zdrop tin src) = zlength src - tin) by exact LIN.
  unfold ZBC_MAX, ZC_MAX in HD, HS.
  pose proof (ZLoopFactsC.ic_inflate_bufC (zdrop tin src) (u2_is _ x) (dlen - tout) ok HI HBi ltac:(change (@ZIface.zlength) with (@Prelim.zlength); lia) ltac:(lia)) as CB.
  destruct (ZApiInstC.zic_inflate (zdrop tin src) (u2_is _ x) (dlen - tout) ok) as [[[is' consumed] bs] rc].
  intros EB. pose proof (CB EB) as CB2. try change (@ZIface.zlength) with (@Prelim.zlength) in CB2. lia.
Qed.
