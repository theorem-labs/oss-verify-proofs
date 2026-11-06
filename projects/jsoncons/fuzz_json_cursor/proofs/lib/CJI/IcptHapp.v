(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm8RegionPoisoned Pm8AsanMemcpy Pm8AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import Prelim.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.F8 Require Import F_memcpy F_printf_iface.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJM Require Import ShZero QcF IcptCells IcptCellsA FfpTac.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJI Require Import IcptPcomS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition happ (a b : Z) : Prop := b <= a \/ (0x160040 <= a /\ app a (b - a)) \/ (0x10007fff8000 <= a /\ b <= 2^47).
Fixpoint happ_all (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (a, b) :: W' => happ a b /\ happ_all W'
  end.

Lemma outside_happ : forall W y, happ_all W -> 0x7fff7fff < y < 0x10007fff8000 -> outside W y.
Proof.
  induction W as [|[a b] W IH]; intros y HW Hy; cbn [outside happ_all] in *; [exact I|].
  destruct HW as [[Hba|[[A0 [[A1 A2]|[A1 A2]]]|[A1 A2]]] HW']; (split; [lia|]); apply IH; assumption.
Qed.
Lemma outside_happ_low : forall W y, happ_all W -> 0 <= y < 0x160040 -> outside W y.
Proof.
  induction W as [|[a b] W IH]; intros y HW Hy; cbn [outside happ_all] in *; [exact I|].
  destruct HW as [[Hba|[[A0 _]|[A1 A2]]] HW']; (split; [lia|]); apply IH; assumption.
Qed.

Ltac happ_tac :=
  cbn [happ_all happ]; repeat split;
  first [ exact I | left; lia | right; right; lia | right; left; split; [lia | unfold app; right; lia]
        | right; left; split; [lia | match goal with H : app ?p ?n |- app ?p ?n' => eapply app_sub; [exact H | lia] end] ].

Section T.
Variable segs : list Segment.
Lemma rdn_munch_h : forall m m' W (a : word) k bs, happ_all W -> munch W m m' ->
  (bv_unsigned a + Z.of_nat k <= 0x160040)%Z ->
  rdn segs m a k = Some bs -> rdn segs m' a k = Some bs.
Proof.
  intros m m' W a k bs HW MU Ha H. rewrite <- H. apply rdn_ext; [lia|].
  intros x Hx. apply MU. apply outside_happ_low; [exact HW|]. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. lia.
Qed.
End T.

Lemma aenv_munch_h : forall m m' W, happ_all W -> munch W m m' -> aenv m -> aenv m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3 & H4 & H5). unfold aenv, ai_byte, fx_got in *.
  unfold Pm8RegionPoisoned.rt_layout_globs, Pm8AsanMemcpy.mc_icpt_globs, Pm8AsanMemset.ms_icpt_globs in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply rdn_munch_h; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.

Lemma icpt_cells_munch_h : forall W m m', happ_all W -> munch W m m' -> icpt_cells m -> icpt_cells m'.
Proof.
  intros W m m' HW MU (H1 & H2 & H3). unfold icpt_cells.
  split; [|split]; (eapply rdn_munch_h; [exact HW | exact MU | | eassumption]); rewrite unsigned_lit by lia; cbn; lia.
Qed.

Lemma zsh_transport_h : forall m m' W lo hi, zsh m lo hi -> munch W m m' -> happ_all W -> app lo (hi - lo) -> zsh m' lo hi.
Proof.
  intros m m' W lo hi Z MU HW Ha y Hy.
  pose proof (shw_range0 lo hi Ha) as (R1 & R2).
  assert (Hy2 : 0 <= y < 2^64) by (unfold shw_lo, shw_hi, SBZ in *; lia).
  rewrite (MU (wa y)). { apply Z, Hy. }
  rewrite wa_unsigned by exact Hy2. apply outside_happ; [exact HW|]. unfold shw_lo, shw_hi, SBZ in *; lia.
Qed.

Lemma shz_transport_h : forall segs m m' W p n, shz segs m p n -> munch W m m' -> happ_all W -> app p n -> shz segs m' p n.
Proof.
  intros segs m m' W p n S MU HW Ha Hn. destruct (S Hn) as (A & B & C).
  assert (D1 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (R : forall y, Pm8RegionPoisoned.SB + p / 8 - 8 <= y < Pm8RegionPoisoned.SB + (p + n - 1) / 8 + 8 -> m' (wa y) = m (wa y)).
  { intros y Hy. pose proof (shw_range p (p + n) ltac:(replace (p + n - p) with n by lia; exact Ha) ltac:(lia)) as (R1 & R2).
    unfold shw_lo, shw_hi, SBZ, Pm8RegionPoisoned.SB in *.
    assert (D2 : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
    assert (Hy2 : 0 <= y < 2^64) by lia.
    apply MU. rewrite wa_unsigned by exact Hy2. apply outside_happ; [exact HW|]. lia. }
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

Lemma shk_transport_h : forall segs m m' W p n, shk segs m p n -> munch W m m' -> happ_all W -> app p n -> shk segs m' p n.
Proof.
  intros segs m m' W p n S MU HW Ha Hn. destruct (S Hn) as (A & (k & Hk & Hkr) & C).
  assert (D1 : p / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (R : forall y, Pm8RegionPoisoned.SB + p / 8 - 8 <= y < Pm8RegionPoisoned.SB + (p + n - 1) / 8 + 8 -> m' (wa y) = m (wa y)).
  { intros y Hy. pose proof (shw_range p (p + n) ltac:(replace (p + n - p) with n by lia; exact Ha) ltac:(lia)) as (R1 & R2).
    unfold shw_lo, shw_hi, SBZ, Pm8RegionPoisoned.SB in *.
    assert (D2 : (p + n - 1) / 8 <= (p + n) / 8) by (apply Z.div_le_mono; lia).
    assert (Hy2 : 0 <= y < 2^64) by lia.
    apply MU. rewrite wa_unsigned by exact Hy2. apply outside_happ; [exact HW|]. lia. }
  split; [|split].
  - intros x Hx. rewrite <- (Z_to_bv_bv_unsigned x). fold (wa (bv_unsigned x)). rewrite R; [| lia].
    unfold wa. rewrite Z_to_bv_bv_unsigned. apply A. exact Hx.
  - exists k. split; [|exact Hkr]. fold (wa (Pm8RegionPoisoned.SB + (p + n - 1) / 8)). rewrite R; [exact Hk | lia].
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

Lemma fmtq_munch_h : forall m m' W A fmt, fmtq m A fmt -> munch W m m' -> happ_all W -> 64 <= A -> A + zlength fmt + 8 <= 0x7fff7fff ->
  fmtq m' A fmt.
Proof.
  intros m m' W A fmt FQ MU HW H1 H2 i n Hi Hn Hin.
  eapply shk_transport_h; [apply FQ; assumption | exact MU | exact HW | unfold ShZero.app; left; lia].
Qed.

Lemma happ_app : forall W1 W2, happ_all W1 -> happ_all W2 -> happ_all (W1 ++ W2).
Proof. induction W1 as [|[a b] W1 IH]; intros W2 H1 H2; cbn [app happ_all] in *; [exact H2|]. destruct H1 as [Ha H1]. split; [exact Ha | apply IH; assumption]. Qed.
