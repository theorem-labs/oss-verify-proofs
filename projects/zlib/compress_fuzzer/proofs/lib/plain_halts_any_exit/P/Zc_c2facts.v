(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZApiL ZHarnessL ZApiC ZHarnessC ZInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZIface ZApiInst ZApiInstC ZApiOkC ZLoopFactsC DeflateSafe.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zc_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Transparent the_zapiC.
Notation zc := the_zapiC.

Definition c2_tin (x : c2L zc) : Z := ZIface.zs_total_in (ZApiInst.dz_z (c2_ds zc x)).
Definition c2_tout (x : c2L zc) : Z := ZIface.zs_total_out (ZApiInst.dz_z (c2_ds zc x)).

Definition c2_next (x : c2L zc) (N : Z) (ds' : DSC zc) (consumed : Z) (bs : list Z) : c2L zc :=
  mkC2L zc ds' 0 0 (zdrop consumed (c2_rest zc x)) (zlength (c2_rest zc x) - consumed) (N - c2_tout x - zlength bs) (rev_append bs (c2_orev zc x)).

Definition C2I (N : Z) (src : list Z) (level : Z) (x : c2L zc) : Prop :=
  c2_reach zc N src level x /\ ZApiOkC.CI N x /\ ZLoopFactsC.CT src x.

Lemma C2I_init : forall N src level, 0 <= N <= ZBC_MAX -> zlength src <= ZBC_MAX -> Forall (fun b => 0 <= b < 256) src -> 0 <= level <= 9 ->
  C2I N src level (c2_x0 zc N src level).
Proof.
  intros N src level HN HS HB HL. pose proof (c2_reach_x0 zc N src level) as R.
  destruct (ZLoopFactsC.c2_reach_CT src N level _ HN HS HB HL R) as [CI CT]. split; [exact R| split; [exact CI| exact CT]].
Qed.

Lemma C2I_shape : forall N src level x, 0 <= N <= ZBC_MAX -> C2I N src level x ->
  let rest := c2_rest zc x in
  c2_tout x = zlength (c2_orev zc x) /\ 0 <= c2_tout x /\ c2_tout x + c2_aout zc x + c2_left zc x = N
  /\ 0 <= c2_aout zc x /\ 0 <= c2_left zc x /\ 0 <= c2_ain zc x /\ 0 <= c2_slen zc x
  /\ c2_slen zc x + c2_ain zc x = zlength rest /\ zlength rest <= zlength src
  /\ (c2_slen zc x = 0 \/ c2_ain zc x = 0) /\ (c2_left zc x = 0 \/ c2_aout zc x = 0)
  /\ rest = zdrop (zlength src - zlength rest) src
  /\ 0 <= c2_tin x < 2^64 /\ Forall (fun b => 0 <= b < 256) rest.
Proof.
  intros N src level x HN (R & CI & CT). cbv zeta.
  destruct CI as (HDC & ZOK & HB & Hain & Hslen & Hsum & Hrl & Haout & Hleft & Htot & Hto & Hto0).
  destruct CT as (T1 & T2 & T3 & T4).
  unfold c2_tout, c2_tin. change (@ZIface.zlength) with (@Prelim.zlength) in *.
  destruct ZOK as (TI & _ & _ & _).
  repeat (split; [first [assumption | lia] |]). exact HB.
Qed.

Lemma c2_trip : forall N src level x n r, 0 <= N <= ZBC_MAX -> zlength src <= ZBC_MAX -> C2I N src level x ->
  c2_after zc (S n) x = Some r ->
  let rest := c2_rest zc x in
  let '(ds', consumed, bs, rc) := dc_deflate zc rest (c2_ds zc x) (N - c2_tout x) Z_FINISH in
  0 <= consumed <= zlength rest /\ zlength bs <= N - c2_tout x
  /\ c2_tout (c2_next x N ds' consumed bs) = c2_tout x + zlength bs
  /\ (rc = Z_OK -> C2I N src level (c2_next x N ds' consumed bs) /\ c2_after zc n (c2_next x N ds' consumed bs) = Some r)
  /\ (rc <> Z_OK -> r = (c2_next x N ds' consumed bs, rc)).
Proof.
  intros N src level x n r HN HS CX AF.
  unfold C2I, c2_next, c2_tout, c2_tin in *. cbv delta [the_zapiC] in *.
  pose proof CX as (R & CI & CT).
  pose proof (ZLoopFactsC.c2_refill_shape src N x HN CI CT) as RS.
  pose proof (ZApiOkC.c2_step N x HN CI) as STEP.
  pose proof (ZLoopFactsC.c2_step_CT src N x) as STEPT.
  rewrite c2_after_S in AF.
  assert (RSTEP : forall x', c2_stepP _ x = inl x' -> c2_reach _ N src level x') by (intros x' E; eapply c2_reach_step; [exact R| exact E]).
  unfold c2_stepP in AF, STEP, STEPT, RSTEP.
  destruct (c2_refill _ x) as [[[ao lf] ai] sl]. cbv zeta in RS.
  destruct RS as (Eai & Esl & Eao & Elf & Einp & Efl & Erest & Hoff & Hto & Hrl).
  change (@ZIface.zlength) with (@Prelim.zlength) in *. change (@ZIface.zfirstn Z) with (@Prelim.ztake) in *. change (@ZIface.zskipn Z) with (@Prelim.zdrop) in *.
  set (tout := ZIface.zs_total_out (ZApiInst.dz_z (c2_ds ZApiInstC.zinstC x))) in *.
  rewrite Einp, Efl, Eao in AF, STEP, STEPT, RSTEP. cbv zeta. change ZIface.Z_FINISH with Z_FINISH in *.
  cbn [dc_deflate dc_total_out ZApiInstC.zinstC] in *.
  destruct (ZApiInstC.zdc_deflate (c2_rest _ x) (c2_ds _ x) (N - tout) Z_FINISH) as [[[ds' consumed] bs] rc] eqn:ED.
  destruct (c_step_ok _ ai (N - tout) (c2_ds _ x) ds' consumed bs) eqn:OK.
  2:{ cbn in AF. discriminate AF. }
  unfold c_step_ok in OK. cbn [dc_total_out ZApiInstC.zinstC] in OK. rewrite !Bool.andb_true_iff in OK. destruct OK as (((O1 & O2) & O3) & O4).
  apply Z.leb_le in O1. apply Z.leb_le in O2. apply Z.leb_le in O3. apply Z.eqb_eq in O4.
  rewrite Elf, Esl, Eai in AF, STEP, STEPT, RSTEP.
  set (x' := mkC2L ZApiInstC.zinstC ds' 0 0 (zdrop consumed (c2_rest _ x)) (zlength (c2_rest _ x) - consumed) (N - tout - zlength bs) (rev_append bs (c2_orev _ x))) in *.
  split; [lia|]. split; [exact O3|].
  split. { subst x'. cbn [c2_ds]. fold tout in O4. change (@ZIface.zlength) with (@Prelim.zlength) in O4. exact O4. }
  split.
  - intros ->. cbn [Z.eqb Z_OK] in AF, STEP, STEPT, RSTEP. split; [| exact AF].
    split; [exact (RSTEP _ eq_refl)| split; [exact (proj1 STEP)| exact (STEPT _ HN CI CT eq_refl)]].
  - intros NZ. replace (rc =? Z_OK) with false in AF by (symmetry; apply Z.eqb_neq; exact NZ). cbn in AF. injection AF as <-. reflexivity.
Qed.
