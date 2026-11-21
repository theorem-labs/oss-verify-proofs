(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefZApi RefInflateRel RefUpdWin1 RefInflateInit1 RefInflateInit_run RefInflate_runA.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefInflateSafeD RefInflateSafeS2 RefInflateSafeS3 RefInflateEqD RefInflateEqA2 RefInflateEqF RefInflateEqS RefInflateEqU.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateFrameIn InflateCall HarnessSmall ZApiInst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition iinit_of (g : Z -> Z) : inflate_state := ireset_s (s_pre g 5%N MAX_WBITS).

Definition IREL (s_a : inflate_state) (x : istream) : Prop := ICALL s_a (iz_s x).

Definition wans_g (gw : Z -> Z) (ok : bool) : option (blk * (Z -> Z)) := if ok then Some (6%N, gw) else None.

Definition HK (gw : Z -> Z) : zhooks (bool * nat) :=
  mkHooks (fun _ _ => fun st : bool * nat => MRet (wans_g gw (fst st), (fst st, S (snd st))))
          (fun _ => fun st : bool * nat => MRet (tt, st)).

Lemma HK_zalloc_rel : forall g1 g2 a b,
  srel (fun r1 r2 : option (blk * (Z -> Z)) => option_map fst r1 = option_map fst r2) (zalloc (HK g1) a b) (zalloc (HK g2) a b).
Proof.
  intros g1 g2 a b st. cbn [zalloc HK mrel]. unfold st_rel. cbn [fst snd]. split; [| reflexivity].
  unfold wans_g. destruct (fst st); reflexivity.
Qed.

Lemma updatewindow_HK : forall gw s src end_ copy st,
  updatewindow (HK gw) s src end_ copy st
  = MRet (uw_pure s src end_ copy (wans_g gw (fst st)), match is_window_blk s with Some _ => st | None => (fst st, S (snd st)) end).
Proof.
  intros gw s src end_ copy st. rewrite updatewindow_unfold. unfold uw_pure.
  destruct (is_window_blk s) as [b|].
  - unfold sbind at 1. unfold sret at 1. cbn [mbind fst snd]. rewrite updw_body_eq. reflexivity.
  - unfold sbind. cbn [zalloc HK mbind fst snd sret].
    destruct (wans_g gw (fst st)) as [[b g]|]; cbn [mbind fst snd]; [rewrite updw_body_eq|]; reflexivity.
Qed.

Lemma inflate_p_HK : forall gw ok s zc flush, inflateStateCheck s = false ->
  exists n, inflate_m ivar_ref (HK gw) s zc flush (ok, O) = MRet (fst (inflate_p (wans_g gw ok) s zc flush), (ok, n))
            /\ snd (inflate_p (wans_g gw ok) s zc flush) = Nat.eqb n 1.
Proof.
  intros gw ok s zc flush Hc. unfold inflate_p.
  rewrite (inflate_m_W0 (HK gw)), (inflate_m_W0 HarnessSmall.dhooks) by exact Hc.
  destruct (inf_loop ivar_ref flush (W0 s zc)) as [stop [s' c' r']]. destruct stop as [|rc].
  - rewrite !inf_leave_eq. unfold sbind. destruct (lv_cond flush (s_rest s' r') (c_rest c' r') r').
    + rewrite updatewindow_HK, updatewindow_dh. cbn [mbind fst snd].
      destruct (is_window_blk (s_rest s' r')) as [b|];
        (destruct (uw_pure (s_rest s' r') _ _ _ (wans_g gw ok)) as [s2|]; unfold sret; cbn [fst snd]; eexists; split; reflexivity).
    + unfold sret. cbn [mbind fst snd]. exists O. split; reflexivity.
  - unfold sret. cbn [fst snd]. exists O. split; reflexivity.
Qed.


Theorem is0_of : is0 = iinit_of g0.
Proof. unfold is0, iinit_of. unfold iinit0, iinit_run, HarnessSmall.dpure. rewrite inflateInit2_m_eq. unfold sbind.
  cbn [zalloc HarnessSmall.dhooks mbind fst snd]. change (ir2_bad MAX_WBITS) with false. cbv iota. unfold sret. cbn [fst]. reflexivity.
Qed.

Theorem iinit_run_of : forall g,
  HarnessSmall.iinit_run [Some (5%N, g)] zstrm0
  = Some (Some (iinit_of g), zret0 (ireset_z (s_pre g 5%N MAX_WBITS) (z_pre (zc_none zstrm0))) Z_OK).
Proof.
  intros g. unfold HarnessSmall.iinit_run, HarnessSmall.dpure. rewrite inflateInit2_m_eq. unfold sbind.
  cbn [zalloc HarnessSmall.dhooks mbind fst snd]. change (ir2_bad MAX_WBITS) with false. cbv iota. unfold sret. cbn [fst]. reflexivity.
Qed.

Theorem IREL_init : forall g, IREL (iinit_of g) zi_init.
Proof.
  intros g. unfold IREL, zi_init, ICALL. cbn [iz_s]. rewrite is0_of. unfold iinit_of. change MAX_WBITS with DEF_WBITS.
  split; [apply IEQ_init|]. split; [apply UWS_init|]. split; apply INV_fresh; reflexivity.
Qed.

Theorem IREL_step : forall s_a x zc gw ok flush, IREL s_a x -> ZC zc ->
  let r_a := inflate_p (wans_g gw ok) s_a zc flush in
  let r_c := inflate_p (wans ok) (iz_s x) zc flush in
  snd (fst r_a) = snd (fst r_c) /\ snd r_a = snd r_c
  /\ IREL (fst (fst r_a)) (mkIZ (fst (fst r_c)) (zr_strm (snd (fst r_c)))).
Proof.
  intros s_a x zc gw ok flush (HQ & HU & I1 & I2) Hz. cbv zeta.
  change (wans ok) with (wans_g g0 ok).
  pose proof (INV_check _ I1) as C1. pose proof (INV_check _ I2) as C2.
  destruct (inflate_p_HK gw ok s_a zc flush C1) as (n1 & E1 & A1).
  destruct (inflate_p_HK g0 ok (iz_s x) zc flush C2) as (n2 & E2 & A2).
  pose proof (inflate_m_cong (HK gw) (HK g0) (HK_zalloc_rel gw g0) flush s_a (iz_s x) zc fastc_proof I1 Hz HQ HU (ok, O)) as R.
  rewrite E1, E2 in R. cbn [mrel] in R. destruct R as [(R1 & R2 & R3) R4]. cbn [fst snd] in R1, R2, R3, R4.
  assert (En : n1 = n2) by (injection R4; intros; assumption).
  split; [exact R1|]. split; [rewrite A1, A2, En; reflexivity|].
  unfold IREL, ICALL. cbn [iz_s]. split; [exact R2|]. split; [exact R3|].
  pose proof (inflate_p_pure (wans_g gw ok) s_a zc flush C1) as P1. pose proof (inflate_p_pure (wans_g g0 ok) (iz_s x) zc flush C2) as P2.
  destruct (fst (inflate_p (wans_g gw ok) s_a zc flush)) as [sa' zra]. destruct (fst (inflate_p (wans_g g0 ok) (iz_s x) zc flush)) as [sc' zrc].
  cbn [fst snd] in *. split; [exact (inflate_INV' s_a zc flush _ sa' zra I1 Hz P1) | exact (inflate_INV' (iz_s x) zc flush _ sc' zrc I2 Hz P2)].
Qed.
