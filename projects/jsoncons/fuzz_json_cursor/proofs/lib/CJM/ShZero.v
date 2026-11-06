(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm8RegionPoisoned Pm8AsanMemcpy.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition SBZ : Z := 0x7fff8000.
Lemma SBZ_eq : SBZ = Pm8RegionPoisoned.SB. Proof. reflexivity. Qed.

Definition app (p n : Z) : Prop := (64 <= p /\ p + n + 8 <= 0x7fff7fff) \/ (0x10007fff8000 <= p /\ p + n <= 0x7fffffffff00).
Definition shw_lo (lo : Z) : Z := SBZ + lo / 8 - 8.
Definition shw_hi (hi : Z) : Z := SBZ + hi / 8 + 16.

Definition zsh (m : word -> option byte) (lo hi : Z) : Prop :=
  forall y, shw_lo lo <= y < shw_hi hi -> m (wa y) = Some (Z_to_bv 8 0).

Lemma zsh_sub : forall m lo hi lo' hi', zsh m lo hi -> lo <= lo' -> hi' <= hi -> zsh m lo' hi'.
Proof.
  intros m lo hi lo' hi' Z Hl Hh y Hy. apply Z. unfold shw_lo, shw_hi in *.
  pose proof (Z.div_le_mono lo lo' 8 ltac:(lia) Hl). pose proof (Z.div_le_mono hi' hi 8 ltac:(lia) Hh). lia.
Qed.

Lemma shw_range : forall lo hi, app lo (hi - lo) -> lo < hi ->
  SBZ <= shw_lo lo /\ shw_hi hi <= 0x10007fff8000.
Proof.
  intros lo hi Ha H.
  assert (A1 : 64 <= lo /\ hi <= 0x7fffffffff00) by (destruct Ha as [[A1 A2]|[A1 A2]]; lia).
  pose proof (Z.div_le_mono 64 lo 8 ltac:(lia) ltac:(lia)) as HL. change (64 / 8) with 8 in HL.
  pose proof (Z.div_le_mono hi 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as HD.
  change (0x7fffffffff00 / 8) with 17592186044384 in HD.
  unfold shw_lo, shw_hi, SBZ. lia.
Qed.

Fixpoint in_app_all (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (a, b) :: W' => (b <= a \/ app a (b - a)) /\ in_app_all W'
  end.

Lemma outside_app : forall W y, in_app_all W -> 0x7fff7fff < y < 0x10007fff8000 -> outside W y.
Proof.
  induction W as [|[a b] W IH]; intros y HW Hy; cbn [outside in_app_all] in *; [exact I|].
  destruct HW as [[Hba|[[A1 A2]|[A1 A2]]] HW']; (split; [lia|]); apply IH; assumption.
Qed.

Lemma zsh_transport : forall m m' W lo hi, zsh m lo hi -> munch W m m' -> in_app_all W -> app lo (hi - lo) -> lo < hi -> zsh m' lo hi.
Proof.
  intros m m' W lo hi Z MU HW Ha Hlh y Hy.
  pose proof (shw_range lo hi Ha Hlh) as (R1 & R2).
  assert (Hy2 : 0 <= y < 2^64) by (unfold shw_lo, shw_hi, SBZ in *; lia).
  rewrite (MU (wa y)). { apply Z, Hy. }
  rewrite wa_unsigned by exact Hy2. apply outside_app; [exact HW|]. unfold shw_lo, shw_hi, SBZ in *; lia.
Qed.

Lemma app_in_app8 : forall p n, app p n -> 0 <= n -> Pm8AsanMemcpy.in_app8 p n.
Proof. intros p n [[A1 A2]|[A1 A2]] Hn; unfold Pm8AsanMemcpy.in_app8, Pm8RegionPoisoned.LOWEND, Pm8RegionPoisoned.HIGHBEG, Pm8RegionPoisoned.HIGHEND; lia. Qed.

Section PORTA.
Variable segs : list Segment.
Variable m : word -> option byte.

Lemma rdn_zeros8 : forall a, (0 <= a)%Z -> (a + 8 <= 2^64)%Z -> (forall i, 0 <= i < 8 -> m (wa (a + i)) = Some (Z_to_bv 8 0)) ->
  exists w, rdn segs m (Z_to_bv 64 a) 8%nat = Some w.
Proof.
  intros a Ha Ha8 H. exists (repeat (Z_to_bv 8 0) 8).
  replace (Z_to_bv 64 a) with (wa (a + Z.of_nat 0)) by (unfold wa; f_equal; lia).
  rewrite (bytes_at_rdn segs m a (repeat (Z_to_bv 8 0) 8) 0 8); [reflexivity| |cbn; lia].
  split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [length repeat] in Hi.
  unfold mrd. rewrite H by lia. destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn; try reflexivity; lia.
Qed.

Lemma zsh_porta : forall p n, zsh m p (p + n) -> 0 < n -> app p n ->
  let f := (Pm8RegionPoisoned.SB + p / 8)%Z in
  let l := (Pm8RegionPoisoned.SB + (p + n - 1) / 8)%Z in
  (forall x : word, (f <= bv_unsigned x < l)%Z -> m x = Some (Z_to_bv 8 0))
  /\ m (Z_to_bv 64 l) = Some (Z_to_bv 8 0)
  /\ (exists w0 w1, rdn segs m (Z_to_bv 64 (f - f mod 8)) 8%nat = Some w0 /\ rdn segs m (Z_to_bv 64 (l - l mod 8)) 8%nat = Some w1).
Proof.
  intros p n Z Hn Ha f l.
  pose proof (shw_range p (p + n) ltac:(replace (p + n - p) with n by lia; exact Ha) ltac:(lia)) as (R1 & R2).
  unfold f, l. rewrite <- SBZ_eq. unfold shw_lo, shw_hi in *.
  assert (D1 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (D2 : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
  split; [| split].
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). apply Z. unfold shw_lo, shw_hi. lia.
  - fold (wa (SBZ + (p + n - 1) / 8)). apply Z. unfold shw_lo, shw_hi. lia.
  - pose proof (Z.mod_pos_bound (SBZ + p / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SBZ + (p + n - 1) / 8) 8 ltac:(lia)).
    destruct (rdn_zeros8 (SBZ + p / 8 - (SBZ + p / 8) mod 8)) as [w0 W0]; [unfold SBZ in *; lia | unfold SBZ in *; lia | |].
    { intros i Hi. apply Z. unfold shw_lo, shw_hi. lia. }
    destruct (rdn_zeros8 (SBZ + (p + n - 1) / 8 - (SBZ + (p + n - 1) / 8) mod 8)) as [w1 W1]; [unfold SBZ in *; lia | unfold SBZ in *; lia | |].
    { intros i Hi. apply Z. unfold shw_lo, shw_hi. lia. }
    exists w0, w1. split; assumption.
Qed.
End PORTA.

Definition shz (segs : list Segment) (m : word -> option byte) (p n : Z) : Prop :=
  0 < n ->
  (forall x : word, (Pm8RegionPoisoned.SB + p / 8 <= bv_unsigned x < Pm8RegionPoisoned.SB + (p + n - 1) / 8)%Z -> m x = Some (Z_to_bv 8 0))
  /\ m (Z_to_bv 64 (Pm8RegionPoisoned.SB + (p + n - 1) / 8)) = Some (Z_to_bv 8 0)
  /\ (n <= 64 -> exists w0 w1,
        rdn segs m (Z_to_bv 64 ((Pm8RegionPoisoned.SB + p / 8) - (Pm8RegionPoisoned.SB + p / 8) mod 8)) 8%nat = Some w0 /\
        rdn segs m (Z_to_bv 64 ((Pm8RegionPoisoned.SB + (p + n - 1) / 8) - (Pm8RegionPoisoned.SB + (p + n - 1) / 8) mod 8)) 8%nat = Some w1).

Lemma shz_of_zsh : forall segs m p n, zsh m p (p + n) -> app p n -> shz segs m p n.
Proof.
  intros segs m p n Z Ha Hn. destruct (zsh_porta segs m p n Z Hn Ha) as (A & B & C). split; [exact A|]. split; [exact B|]. intros _. exact C.
Qed.

Lemma shz_transport : forall segs m m' W p n, shz segs m p n -> munch W m m' -> in_app_all W -> app p n -> shz segs m' p n.
Proof.
  intros segs m m' W p n S MU HW Ha Hn. destruct (S Hn) as (A & B & C).
  assert (D1 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (R : forall y, Pm8RegionPoisoned.SB + p / 8 - 8 <= y < Pm8RegionPoisoned.SB + (p + n - 1) / 8 + 8 -> m' (wa y) = m (wa y)).
  { intros y Hy. pose proof (shw_range p (p + n) ltac:(replace (p + n - p) with n by lia; exact Ha) ltac:(lia)) as (R1 & R2).
    unfold shw_lo, shw_hi, SBZ, Pm8RegionPoisoned.SB in *.
    assert (D2 : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
    assert (Hy2 : 0 <= y < 2^64) by lia.
    apply MU. rewrite wa_unsigned by exact Hy2. apply outside_app; [exact HW|]. lia. }
  split; [|split].
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). rewrite R; [| lia].
    unfold wa. rewrite Z_to_bv_bv_unsigned. apply A. exact Hx.
  - fold (wa (Pm8RegionPoisoned.SB + (p + n - 1) / 8)). rewrite R; [exact B | lia].
  - intros H64. destruct (C H64) as (w0 & w1 & W0 & W1). exists w0, w1.
    assert (Hp0 : 0 <= p /\ p + n <= 0x7fffffffff00) by (destruct Ha as [[? ?]|[? ?]]; lia).
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (p + n - 1) 0x7fffffffff00 8 ltac:(lia) ltac:(lia)) as HD8. change (0x7fffffffff00 / 8)%Z with 17592186044384%Z in HD8.
    pose proof (Z.mod_pos_bound (Pm8RegionPoisoned.SB + p / 8) 8 ltac:(lia)) as M0.
    pose proof (Z.mod_pos_bound (Pm8RegionPoisoned.SB + (p + n - 1) / 8) 8 ltac:(lia)) as M1.
    unfold Pm8RegionPoisoned.SB in *.
    set (a0 := (2147450880 + p / 8) - (2147450880 + p / 8) mod 8) in *.
    set (a1 := (2147450880 + (p + n - 1) / 8) - (2147450880 + (p + n - 1) / 8) mod 8) in *.
    assert (U0 : bv_unsigned (Z_to_bv 64 a0) = a0) by (apply unsigned_lit; unfold a0; lia).
    assert (U1 : bv_unsigned (Z_to_bv 64 a1) = a1) by (apply unsigned_lit; unfold a1; lia).
    split; [rewrite <- W0 | rewrite <- W1]; (apply rdn_ext; [rewrite ?U0, ?U1; cbn [Z.of_nat Pos.to_nat]; unfold a0, a1; lia|]);
      intros x Hx; rewrite ?U0, ?U1 in Hx; cbn [Z.of_nat Pos.to_nat] in Hx; rewrite <- (Z_to_bv_bv_unsigned x); fold (wa (bv_unsigned x)); apply R;
      unfold a0, a1 in Hx; unfold Pm8RegionPoisoned.SB; lia.
Qed.
