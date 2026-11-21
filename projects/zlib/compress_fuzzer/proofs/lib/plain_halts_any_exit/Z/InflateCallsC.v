(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Prelim ZApi ZApiC ZHarnessC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate ModelRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefZApi RefInflateRel RefUpdWin1 RefInflate_runA.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK RefInflateSafeS1 RefInflateSafeS2 RefInflateSafeS3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateEqD RefInflateEqA2 RefInflateEqF RefInflateEqS RefInflateEqU RefInflateEqB InflateFrameIn InflateCall.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import HarnessSmall ZApiInst ZTaintI InflateStall InflateStallC InflateStallCS HarnessCompress ZApiInstC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ModelLevel.

  Definition JC (x : istream) : Prop := IREL (iz_s x) x.

  Lemma JC_init : JC zi_init.
  Proof. unfold JC. change (iz_s zi_init) with is0. rewrite is0_of. exact (IREL_init g0). Qed.

  Lemma JC_facts : forall x, JC x -> INV (iz_s x) /\ UWS (iz_s x) /\ IEQ (iz_s x) (iz_s x).
  Proof. intros x (HQ & HU & HI & _). split; [exact HI|]. split; [exact HU| exact HQ]. Qed.

  Lemma ic_call_facts : forall x inp aout ok, JC x -> ZC (mkZCall inp aout (iz_z x)) ->
    let '(x', consumed, bs, rc) := zic_inflate inp x aout ok in
    JC x'
    /\ (rc = Z_OK -> (zlength bs = aout /\ OSTALLED (iz_s x')) \/ (consumed = zlength inp /\ STALLED (iz_s x')))
    /\ (aout = 0 -> OSTALLED (iz_s x) -> rc <> Z_OK)
    /\ (inp = [] -> STALLED (iz_s x) -> rc <> Z_OK).
  Proof.
    intros x inp aout ok HJ Hz. unfold zic_inflate.
    set (zc := mkZCall inp aout (iz_z x)) in *.
    pose proof (JC_facts x HJ) as (HI & HUS & HQ).
    pose proof (sq_call2 (iz_s x) zc (wans ok) HI HUS HQ Hz) as SQC. cbv zeta in SQC.
    pose proof (ostalled_call (iz_s x) zc (wans ok) HI Hz) as OSC.
    pose proof (stalled_call (iz_s x) zc (wans ok) HI HUS Hz) as STC.
    pose proof (IREL_step (iz_s x) x zc g0 ok Z_NO_FLUSH HJ Hz) as RS'. cbv zeta in RS'. destruct RS' as (_ & _ & HR').
    change (wans_g g0 ok) with (wans ok) in HR'.
    destruct (inflate_p (wans ok) (iz_s x) zc Z_NO_FLUSH) as [[s' zr] asked]. cbn [fst snd] in SQC, OSC, STC, HR'.
    split; [exact HR'|]. split; [exact SQC|]. split.
    - intros A0 HO. apply OSC; [exact A0| exact HO].
    - intros N0 HS. apply STC; [exact N0| exact HS].
  Qed.

End ModelLevel.

Section SpecLevel.
  Import Prelim ZApiC ZHarnessC.

  Lemma ztake_all : forall l, ztake (Prelim.zlength l) l = l.
  Proof. intros l. unfold ztake, Prelim.zlength. rewrite Nat2Z.id. apply firstn_all. Qed.

  Lemma ztake_0 : forall l, ztake 0 l = [].
  Proof. intros l. reflexivity. Qed.

  Lemma Forall_skipn_ : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
  Proof. intros P n l H. revert n. induction H as [|a l Ha Hl IH]; intros [|n]; cbn; [constructor|constructor|constructor; assumption|apply IH]. Qed.

  Lemma length_ztake_zdrop_le : forall a b (l : list Z), (length (ztake a (zdrop b l)) <= length l)%nat.
  Proof. intros a b l. unfold ztake, zdrop. rewrite length_firstn, length_skipn. lia. Qed.

  Theorem u2_two_trips : forall dlen src x1 ok,
    0 < dlen <= ZC_UMAX -> Prelim.zlength src <= ZC_UMAX -> Forall (fun b => 0 <= b < 256) src ->
    u2_stepP zinstC true (u2_x0 zinstC dlen src) = inl x1 ->
    exists r, u2_stepP zinstC ok x1 = inr r.
  Proof.
    intros dlen src x1 ok Hd Hs Hby. unfold ZC_UMAX in Hd, Hs.
    pose proof (Zle_0_nat (length src)) as LN. change (Z.of_nat (length src)) with (Prelim.zlength src) in LN.
    unfold u2_stepP at 1. unfold u2_x0, u2_refill.
    cbn [u2_aout u2_left u2_ain u2_len u2_rest u2_is u2_orev ZApiC.ic_inflate ZApiC.ic_init ZApiC.ic_total_in ZApiC.ic_total_out zinstC].
    change (0 =? 0) with true. cbv iota.
    replace (ZC_UMAX <? dlen) with false by (symmetry; apply Z.ltb_ge; unfold ZC_UMAX; lia).
    replace (ZC_UMAX <? Prelim.zlength src) with false by (symmetry; apply Z.ltb_ge; unfold ZC_UMAX; lia).
    rewrite ztake_all.
    assert (HZ1 : ZC (mkZCall src dlen (iz_z zi_init))).
    { unfold ZC. cbn [zc_avail_out zc_input]. split; [lia|]. split; [change (ZIface.zlength src) with (Prelim.zlength src); lia| exact Hby]. }
    pose proof (ic_call_facts zi_init src dlen true JC_init HZ1) as F1.
    destruct (zic_inflate src zi_init dlen true) as [[[x1' consumed] bs] rc]. destruct F1 as (HJ1 & HOK1 & _ & _).
    destruct (u_step_ok (Prelim.zlength src) dlen consumed bs rc) eqn:SOK; [| intros H; discriminate H].
    destruct (Z.eqb_spec rc ZApi.Z_OK) as [E0|E0]; [| intros H; discriminate H].
    intros H. injection H as <-.
    unfold u_step_ok in SOK. rewrite E0 in SOK. change (ZApi.Z_OK =? Z_OK) with true in SOK. cbn [negb orb] in SOK.
    apply andb_true_iff in SOK as [S3 SOK]. apply andb_true_iff in SOK as [S1 S2].
    apply Z.leb_le in S1. apply Z.leb_le in S2. apply Z.leb_le in S3.
    pose proof (Zle_0_nat (length bs)) as LB. change (Z.of_nat (length bs)) with (Prelim.zlength bs) in LB.
    change ZApi.Z_OK with Z_OK in E0. specialize (HOK1 E0).

    unfold u2_stepP, u2_refill.
    cbn [u2_aout u2_left u2_ain u2_len u2_rest u2_is u2_orev ZApiC.ic_inflate ZApiC.ic_init ZApiC.ic_total_in ZApiC.ic_total_out zinstC].
    replace (dlen - dlen) with 0 by lia. replace (Prelim.zlength src - Prelim.zlength src) with 0 by lia.
    change (ZC_UMAX <? 0) with false. cbv iota.

    assert (BY2 : forall a, Forall (fun b => 0 <= b < 256) (ztake a (zdrop consumed src))).
    { intros a. unfold ztake, zdrop. apply Forall_firstn. apply Forall_skipn_. exact Hby. }
    assert (LEN2 : forall a, ZIface.zlength (ztake a (zdrop consumed src)) < 2 ^ 32).
    { intros a. unfold ZIface.zlength. pose proof (length_ztake_zdrop_le a consumed src). unfold Prelim.zlength in Hs. lia. }
    Ltac fin2 call F := let x2 := fresh "x2" in let c2 := fresh "c2" in let b2 := fresh "b2" in let r2 := fresh "r2" in let NE := fresh "NE" in
        destruct call as [[[x2 c2] b2] r2]; destruct F as (_ & _ & ?FO & ?FS);
        first [ pose proof (FO eq_refl ltac:(assumption)) as NE | pose proof (FS eq_refl ltac:(assumption)) as NE ];
        lazymatch goal with |- exists r, (if ?g then _ else _) = inr r => destruct g end;
        [ destruct (Z.eqb_spec r2 ZApi.Z_OK) as [EE|EE]; [exfalso; exact (NE EE)| eexists; reflexivity] | eexists; reflexivity ].
    destruct HOK1 as [[Hfull HO]|[Hall HS]].
    -
      change (ZIface.zlength bs) with (Prelim.zlength bs) in Hfull.
      replace (dlen - Prelim.zlength bs =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (Z.eqb_spec (Prelim.zlength src - consumed) 0) as [EA|EA]; cbv beta iota zeta.
      + pose proof (ic_call_facts x1' (ztake 0 (zdrop consumed src)) 0 ok HJ1
                      ltac:(unfold ZC; cbn [zc_avail_out zc_input]; split; [lia|]; split; [apply LEN2| apply BY2])) as F2.
        fin2 (zic_inflate (ztake 0 (zdrop consumed src)) x1' 0 ok) F2.
      + pose proof (ic_call_facts x1' (ztake (Prelim.zlength src - consumed) (zdrop consumed src)) 0 ok HJ1
                      ltac:(unfold ZC; cbn [zc_avail_out zc_input]; split; [lia|]; split; [apply LEN2| apply BY2])) as F2.
        fin2 (zic_inflate (ztake (Prelim.zlength src - consumed) (zdrop consumed src)) x1' 0 ok) F2.
    -
      change (ZIface.zlength src) with (Prelim.zlength src) in Hall.
      replace (Prelim.zlength src - consumed =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
      destruct (Z.eqb_spec (dlen - Prelim.zlength bs) 0) as [EA|EA]; cbv beta iota zeta; rewrite ztake_0.
      + pose proof (ic_call_facts x1' [] 0 ok HJ1
                      ltac:(unfold ZC; cbn [zc_avail_out zc_input]; split; [lia|]; split; [change (ZIface.zlength (@nil Z)) with 0; lia| constructor])) as F2.
        fin2 (zic_inflate [] x1' 0 ok) F2.
      + pose proof (ic_call_facts x1' [] (dlen - Prelim.zlength bs) ok HJ1
                      ltac:(unfold ZC; cbn [zc_avail_out zc_input]; split; [lia|]; split; [change (ZIface.zlength (@nil Z)) with 0; lia| constructor])) as F2.
        fin2 (zic_inflate [] x1' (dlen - Prelim.zlength bs) ok) F2.
  Qed.
End SpecLevel.
