(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm9RegionPoisoned.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJMB Require Import ShZero.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition shk (segs : list Segment) (m : word -> option byte) (p n : Z) : Prop :=
  0 < n ->
  (forall x : word, (Pm9RegionPoisoned.SB + p / 8 <= bv_unsigned x < Pm9RegionPoisoned.SB + (p + n - 1) / 8)%Z -> m x = Some (Z_to_bv 8 0))
  /\ (exists k, m (Z_to_bv 64 (Pm9RegionPoisoned.SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 k) /\ (k = 0 \/ ((p + n - 1) mod 8 < k <= 7)))
  /\ (n <= 64 -> exists w0 w1,
        rdn segs m (Z_to_bv 64 ((Pm9RegionPoisoned.SB + p / 8) - (Pm9RegionPoisoned.SB + p / 8) mod 8)) 8%nat = Some w0 /\
        rdn segs m (Z_to_bv 64 ((Pm9RegionPoisoned.SB + (p + n - 1) / 8) - (Pm9RegionPoisoned.SB + (p + n - 1) / 8) mod 8)) 8%nat = Some w1).

Lemma shk_of_shz : forall segs m p n, shz segs m p n -> shk segs m p n.
Proof.
  intros segs m p n S Hn. destruct (S Hn) as (A & B & C). split; [exact A|]. split; [exists 0; split; [exact B | left; reflexivity]|]. exact C.
Qed.

Lemma shk_of_zsh : forall segs m p n, zsh m p (p + n) -> app p n -> shk segs m p n.
Proof. intros segs m p n Z Ha. apply shk_of_shz, shz_of_zsh; assumption. Qed.

Lemma shk_k : forall segs m p n, shk segs m p n -> exists k,
  (0 < n -> m (Z_to_bv 64 (Pm9RegionPoisoned.SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 k)) /\ (k = 0 \/ ((p + n - 1) mod 8 < k <= 7)) /\
  (0 < n -> forall x : word, (Pm9RegionPoisoned.SB + p / 8 <= bv_unsigned x < Pm9RegionPoisoned.SB + (p + n - 1) / 8)%Z -> m x = Some (Z_to_bv 8 0)) /\
  (0 < n <= 64 -> exists w0 w1,
        rdn segs m (Z_to_bv 64 ((Pm9RegionPoisoned.SB + p / 8) - (Pm9RegionPoisoned.SB + p / 8) mod 8)) 8%nat = Some w0 /\
        rdn segs m (Z_to_bv 64 ((Pm9RegionPoisoned.SB + (p + n - 1) / 8) - (Pm9RegionPoisoned.SB + (p + n - 1) / 8) mod 8)) 8%nat = Some w1).
Proof.
  intros segs m p n S. destruct (Z.lt_ge_cases 0 n) as [Hn|Hn].
  - destruct (S Hn) as (A & (k & Hk & Hkr) & C). exists k. split; [intros _; exact Hk|]. split; [exact Hkr|].
    split; [intros _; exact A|]. intros [_ H64]. exact (C H64).
  - exists 0. split; [intros; lia|]. split; [left; reflexivity|]. split; [intros; lia|]. intros [H _]. lia.
Qed.

Lemma shk_transport : forall segs m m' W p n, shk segs m p n -> munch W m m' -> in_app_all W -> app p n -> shk segs m' p n.
Proof.
  intros segs m m' W p n S MU HW Ha Hn. destruct (S Hn) as (A & (k & Hk & Hkr) & C).

  assert (D1 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (R : forall y, Pm9RegionPoisoned.SB + p / 8 - 8 <= y < Pm9RegionPoisoned.SB + (p + n - 1) / 8 + 8 -> m' (wa y) = m (wa y)).
  { intros y Hy. pose proof (shw_range p (p + n) ltac:(replace (p + n - p) with n by lia; exact Ha) ltac:(lia)) as (R1 & R2).
    unfold shw_lo, shw_hi, SBZ, Pm9RegionPoisoned.SB in *.
    assert (D2 : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
    assert (Hy2 : 0 <= y < 2^64) by lia.
    apply MU. rewrite wa_unsigned by exact Hy2. apply outside_app; [exact HW|]. lia. }
  split; [|split].
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). rewrite R; [| lia].
    unfold wa. rewrite Z_to_bv_bv_unsigned. apply A. exact Hx.
  - exists k. split; [|exact Hkr]. fold (wa (Pm9RegionPoisoned.SB + (p + n - 1) / 8)). rewrite R; [exact Hk | lia].
  - intros H64. destruct (C H64) as (w0 & w1 & W0 & W1). exists w0, w1.
    assert (Hp0 : 0 <= p /\ p + n <= 0x7fffffffff00) by (destruct Ha as [[? ?]|[? ?]]; lia).
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n - 1) 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as HD8. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in HD8.
    pose proof (Z.mod_pos_bound (Pm9RegionPoisoned.SB + p / 8) 8 ltac:(lia)) as M0.
    pose proof (Z.mod_pos_bound (Pm9RegionPoisoned.SB + (p + n - 1) / 8) 8 ltac:(lia)) as M1.
    unfold Pm9RegionPoisoned.SB in *.
    set (a0 := (2147450880 + p / 8) - (2147450880 + p / 8) mod 8) in *.
    set (a1 := (2147450880 + (p + n - 1) / 8) - (2147450880 + (p + n - 1) / 8) mod 8) in *.
    assert (U0 : bv_unsigned (Z_to_bv 64 a0) = a0) by (apply unsigned_lit; unfold a0; lia).
    assert (U1 : bv_unsigned (Z_to_bv 64 a1) = a1) by (apply unsigned_lit; unfold a1; lia).
    split; [rewrite <- W0 | rewrite <- W1]; (apply rdn_ext; [rewrite ?U0, ?U1; cbn [Z.of_nat Pos.to_nat]; unfold a0, a1; lia|]);
      intros x Hx; rewrite ?U0, ?U1 in Hx; cbn [Z.of_nat Pos.to_nat] in Hx; rewrite <- (Z_to_bv_bv_unsigned x); fold (wa (bv_unsigned x)); apply R;
      unfold a0, a1 in Hx; unfold Pm9RegionPoisoned.SB; lia.
Qed.
