(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItGen.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItMath.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItSort.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItShape.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition ty_ok (ty : codetype) (ll : list Z) (bits : Z) : Prop :=
  match ty with
  | CODES => NC ll <= 19 /\ 7 <= bits /\ Forall (fun l => l <= 7) ll
  | LENS => NC ll <= 288
  | DISTS => NC ll <= 32
  end.

Section AbsProps.
  Variable wl : list Z.
Variable ll : list Z.
Variable table : Z.
Variable bits : Z.
  Hypothesis Hll : Forall (fun l => 0 <= l <= 15) ll.
  Hypothesis Ewl : wl = wl_of ll.
  Hypothesis Hbits : 1 <= bits <= 15.
  #[local] Set Default Proof Using "Hll Ewl Hbits".

  Lemma HWa : forall l, 0 <= W wl l.
  Proof. rewrite Ewl. apply (W_of_nonneg ll Hll). Qed.
  Lemma HLa : length wl = 16%nat.
  Proof. rewrite Ewl. apply (wl_of_length ll Hll). Qed.
  Let HW := HWa.
  Let HL := HLa.

  Local Notation W := (W wl).
  Local Notation NZ := (NZ wl).
  Local Notation MAXL := (MAXL wl).
  Local Notation MINL := (MINL wl).
  Local Notation TM := (TM wl).
  Local Notation LEFT := (LEFT wl).

  Lemma nsyms_ok : forall ty, ty_ok ty ll bits -> NC ll <= nsyms ty.
  Proof. intros ty Hty. destruct ty; cbn [nsyms]; cbn [ty_ok] in Hty; lia. Qed.

  Lemma room_enough : forall ty u, it_not_enough ty u = false -> ty <> CODES -> u <= it_room ty.
  Proof.
    intros ty u H Hn. destruct ty; cbn [it_not_enough it_room] in *; [congruence| |]; apply Z.ltb_ge in H; exact H.
  Qed.

  Lemma countz_zero : forall x l, Forall (fun v => v <> x) l -> countz x l = 0.
  Proof.
    intros x l H. induction l as [|a l IH]; [reflexivity|].
    apply Forall_cons_iff in H as [Ha Hl]. rewrite countz_cons, (IH Hl).
    destruct (Z.eqb_spec x a); [congruence | reflexivity].
  Qed.

  Lemma codes_short : ty_ok CODES ll bits -> 1 <= MAXL -> ROOT wl bits = MAXL /\ MAXL <= 7.
  Proof.
    intros Hty HM. destruct Hty as [_ [Hb H7]].
    pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (MINL_spec wl HW HL HM) as [A _].
    assert (HM7 : MAXL <= 7).
    { destruct (Z.le_gt_cases MAXL 7) as [X|X]; [exact X|]. exfalso.
      specialize (M3 HM). replace (W MAXL) with (ItDefs.W (wl_of ll) MAXL) in M3 by (rewrite <- Ewl; reflexivity).
      rewrite (W_of ll Hll) in M3 by lia.
      rewrite countz_zero in M3; [lia|]. apply Forall_impl with (P := fun l => l <= 7); [intros v Hv; lia | exact H7]. }
    split; [|exact HM7]. unfold ROOT. lia.
  Qed.

  Lemma incomplete_facts : 0 < LEFT -> MAXL = 1 ->
    MINL = 1 /\ W 1 = 1 /\ NZ = 1 /\ ROOT wl bits = 1 /\ TM MAXL <= 2 ^ MAXL.
  Proof.
    intros HLp HM. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (MINL_spec wl HW HL ltac:(lia)) as [A [B C]].
    pose proof (LEFT_sign wl HW HL) as [_ [_ LS]]. apply (proj1 LS) in HLp.
    pose proof (TM_step' wl HW HL 1 ltac:(lia)) as T1. replace (1 - 1) with 0 in T1 by lia. rewrite (TM_0 wl HW HL) in T1.
    pose proof (OFF_MAXL wl HW HL ltac:(lia)) as OM.
    rewrite HM in HLp, T1, A, OM. rewrite (OFF_1 wl HW HL) in OM.
    replace (2 ^ (1 - 1)) with 1 in T1 by reflexivity. change (2 ^ 1) with 2 in HLp.
    assert (E1 : MINL = 1) by lia. rewrite E1 in B.
    assert (W1 : W 1 = 1) by lia.
    repeat split; try lia; unfold ROOT; rewrite ?HM, ?E1; try lia.
    all: match goal with |- ?g => idtac "REMAIN" g end.
  Qed.

  Local Notation len_at := (len_at wl).
  Local Notation hf := (hf wl).

  Lemma first_fail_eq : forall root ty,
    first_fail wl root ty = zsearch (fails_at wl root ty) 0 (Z.to_nat (NZ - 1)).
  Proof. intros root ty. exact (@eq_refl Z (zsearch (fails_at wl root ty) 0 (Z.to_nat (NZ - 1)))). Qed.

  Theorem it_abs_props : forall ty, ty_ok ty ll bits ->
    let '(ret, ws, toff, bits', ww) := it_abs wl ll ty table bits in
    ret = 0 ->
    1 <= bits' <= 15 /\ table + 2 ^ bits' <= toff <= table + it_room ty /\
    (forall i v, In (i, v) ws -> table <= i < toff) /\
    (forall i, table <= i < toff -> In i (map fst ws)) /\
    (forall i v, In (i, v) ws -> entry_shape ty bits' (toff - table) (i - table) v).
  Proof.
    intros ty Hty. pose proof (MAXL_spec wl HW HL) as [M1 [M2 M3]]. pose proof (nsyms_ok ty Hty) as NS.
    assert (HR : 2 <= it_room ty) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia).
    unfold it_abs.
    destruct (Z.eqb_spec MAXL 0) as [HM0|HM0].
    {
      intros _. change (2 ^ 1) with 2. split; [lia|]. split; [lia|]. split; [|split].
      - intros i v [H|[H|[]]]; injection H; intros; subst; lia.
      - intros i Hi. cbn [map fst]. assert (i = table \/ i = table + 1) as [->| ->] by lia; [left|right; left]; reflexivity.
      - intros i v Hin. right; right.
        assert (v = code_pack 64 1 0) as -> by (destruct Hin as [H|[H|[]]]; injection H; intros; subst; reflexivity).
        rewrite code_op_pack, code_bits_pack, code_val_pack. cbn. repeat split; reflexivity. }
    assert (HM1 : 1 <= MAXL) by lia.
    pose proof (MINL_spec wl HW HL HM1) as [MA [MB MC]].
    destruct (Z.ltb_spec LEFT 0) as [HL0|HL0]; [intros X; discriminate X|].
    pose proof (LEFT_sign wl HW HL) as [LS1 [LS2 LS3]].
    assert (HK : TM MAXL <= 2 ^ MAXL) by lia.
    destruct ((0 <? LEFT) && (codetype_eqb ty CODES || negb (MAXL =? 1))) eqn:Hinc; [intros X; discriminate X|].
    set (root := ROOT wl bits).
    assert (RR : MINL <= root <= MAXL) by (subst root; unfold ROOT; lia).
    pose proof (root_range wl HW HL root RR HM1) as RR2.
    destruct (it_not_enough ty (2 ^ root)) eqn:NE0; [intros X; discriminate X|].
    unfold loop_abs.
    destruct (Z.ltb_spec (first_fail wl root ty) (NZ - 1)) as [FF|FF]; [intros X; discriminate X|].
    intros _.
    pose proof (NZ_pos wl HW HL HM1) as NP.
    assert (Hnf : forall k, 0 <= k < NZ - 1 -> fails_at wl root ty k = false).
    { intros k Hk. rewrite first_fail_eq in FF. apply (zsearch_before (fails_at wl root ty) 0 (Z.to_nat (NZ - 1))). lia. }
    pose proof (used_lower wl HW HL root RR HM1 (NZ - 1) ltac:(lia)) as UL.
    pose proof (used_enough wl root ty HW HL RR HM1 HK NE0 Hnf (NZ - 1) ltac:(lia)) as UE.

    assert (HU : 2 ^ root <= used wl root (NZ - 1) <= it_room ty).
    { split; [exact UL|]. destruct (codetype_eqb ty CODES) eqn:TC.
      - assert (ty = CODES) as -> by (destruct ty; cbn in TC; congruence).
        destruct (codes_short Hty HM1) as [E7 M7]. fold root in E7.
        pose proof (lay_inv wl HW HL root RR HM1 (NZ - 1) ltac:(lia)) as [LI _].
        assert (HS : islong wl root (NZ - 1) = false).
        { unfold islong. apply Z.ltb_ge. rewrite (len_at_last wl HW HL HM1). lia. }
        destruct (LI HS) as [_ [_ ->]]. cbn [it_room]. rewrite E7.
        change 128 with (2 ^ 7). apply Z.pow_le_mono_r; lia.
      - apply room_enough; [exact UE|]. destruct ty; cbn in TC; congruence. }
    assert (HU2 : used wl root (NZ - 1) < 65536).
    { assert (it_room ty <= 852) by (destruct ty; cbn; unfold ENOUGH_LENS, ENOUGH_DISTS; lia). lia. }
    destruct (Z.eq_dec LEFT 0) as [HC0|HC0].
    -
      assert (HC : TM MAXL = 2 ^ MAXL) by (apply (proj1 LS2); exact HC0).
      unfold final_writes. rewrite (hf_NZ_complete wl root ty HW HL RR HM1 HK HC Hnf NE0). cbn [Z.eqb]. rewrite app_nil_r.
      replace (table + used wl root (NZ - 1) - table) with (used wl root (NZ - 1)) by lia.
      split; [lia|]. split; [lia|]. split; [|split].
      + intros i v Hin. eapply (trips_writes_range wl ll root ty table HW HL RR HM1 HK NZ); [lia | exact Hin].
      + intros i Hi. apply (coverage wl ll root ty table HW HL RR HM1 HK HC Hnf NE0). exact Hi.
      + intros i v Hin. apply (trips_shape wl ll root ty table Hll Ewl RR HM1 HK NS HU2). exact Hin.
    -
      assert (HLp : 0 < LEFT) by lia.
      destruct (Z.ltb_spec 0 LEFT); [|lia]. cbn [andb] in Hinc. apply Bool.orb_false_iff in Hinc as [TC HMx].
      apply Bool.negb_false_iff in HMx. apply Z.eqb_eq in HMx.
      destruct (incomplete_facts HLp HMx) as (Emin & W1 & NZ1 & R1 & _). fold root in R1.
      pose proof (here_shape wl ll root ty Hll Ewl RR HM1 HK NS HU2) as HS.
      unfold final_writes. rewrite NZ1 in *. change (1 - 1) with 0 in *.
      pose proof (lay_0 wl HW HL root RR HM1) as L0.
      assert (E0 : noff wl root 0 = 0 /\ curr wl root 0 = root /\ used wl root 0 = 2 ^ root).
      { unfold noff, curr, used. rewrite L0. repeat split; reflexivity. }
      destruct E0 as (En & Ec & Eu).
      pose proof (len_at_0 wl HW HL HM1) as EL. rewrite Emin in EL.
      assert (Ed : drop wl root 0 = 0).
      { unfold drop, islong. rewrite EL, R1. reflexivity. }
      assert (Ehf0 : hf 0 = 0) by reflexivity.
      assert (Ehf1 : hf 1 = 1).
      { unfold ItDefs.hf. cbn [Z.eqb]. change (1 - 1) with 0. rewrite (code_0 wl HW HL HM1), EL. reflexivity. }
      rewrite Ehf1. cbn [Z.eqb]. assert (P2 : 2 ^ root = 2) by (rewrite R1; reflexivity).
      rewrite ?Eu, ?En, ?EL, ?Ed, ?P2 in *.

      assert (ET : trips_writes wl ll root ty table 1 = fill_writes wl ll root ty table 0).
      { unfold trips_writes. change (Z.to_nat 1) with 1%nat. cbn [seq flat_map]. rewrite app_nil_r.
        change (Z.of_nat 0) with 0. unfold trip_writes, link_writes. rewrite NZ1. cbn [Z.add Z.ltb andb]. apply app_nil_r. }
      rewrite ET.
      assert (HF : forall i v, In (i, v) (fill_writes wl ll root ty table 0) <-> i = table /\ v = here wl ll root ty 0).
      { intros i v. rewrite (In_fill_writes wl ll root ty table HW HL RR HM1 HK 0 i v) by (rewrite EL, Ed, Ec, R1; lia).
        rewrite EL, Ed, Ec, En, Ehf0, R1. change (2 ^ (1 - (1 - 0))) with 1. change (2 ^ 0) with 1. change (0 / 1) with 0.
        split.
        - intros [-> [j [Hj ->]]]. split; [lia|reflexivity].
        - intros [-> ->]. split; [reflexivity|]. exists 0. lia. }
      replace (table + 2 - table) with 2 by lia.
      split; [lia|]. split; [lia|]. split; [|split].
      + intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]].
        * apply HF in Hin as [-> _]. lia.
        * injection Hin; intros; subst. lia.
      + intros i Hi. rewrite map_app. apply in_app_iff.
        assert (i = table \/ i = table + 1) as [->| ->] by lia.
        * left. eapply in_map_fst. apply (proj2 (HF table (here wl ll root ty 0))). split; reflexivity.
        * right. left. cbn. lia.
      + intros i v Hin. apply in_app_iff in Hin as [Hin|[Hin|[]]].
        * apply HF in Hin as [-> ->]. rewrite Z.sub_diag.
          apply HS; [lia| |]; unfold islong; rewrite ?EL, ?R1; cbn; intros; lia.
        * injection Hin; intros; subst. right; right.
          rewrite code_op_pack, code_bits_pack, code_val_pack. cbn. repeat split; try reflexivity. exact R1.
  Qed.
End AbsProps.
