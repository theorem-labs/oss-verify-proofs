(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Pm9RegionPoisoned Pm9AsanMemcpy Pm9AsanMemset.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import MState Mem Frame.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CJMB Require Import ShZero IcptCells.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Fixpoint aapp_all (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (a, b) :: W' => (b <= a \/ (0x160040 <= a /\ app a (b - a))) /\ aapp_all W'
  end.
Lemma high_aapp_all : forall W, high_all W -> aapp_all W.
Proof.
  induction W as [|[a b] W IH]; cbn; [tauto|]. intros [[H|[H1 H2]] HW]; split; [left; exact H| |right; split; [lia | unfold app; right; lia]|]; apply IH, HW.
Qed.
Lemma aapp_in_app_all : forall W, aapp_all W -> in_app_all W.
Proof.
  induction W as [|[a b] W IH]; cbn; [tauto|]. intros [[H|[H1 H2]] HW]; split; [left; exact H| |right; exact H2|]; apply IH, HW.
Qed.
Lemma outside_aapp : forall W y, aapp_all W -> 0 <= y < 0x160040 -> outside W y.
Proof.
  induction W as [|[a b] W IH]; intros y HW Hy; cbn [outside aapp_all] in *; [exact I|].
  destruct HW as [[Hba|[A1 A2]] HW']; (split; [lia|]); apply IH; assumption.
Qed.
Lemma app_sub : forall p n n', app p n -> 0 <= n' <= n -> app p n'.
Proof. intros p n n' [[H1 H2]|[H1 H2]] Hn; [left | right]; lia. Qed.

Section T.
Variable segs : list Segment.
Lemma rdn_munch_a : forall m m' W (a : word) k bs, aapp_all W -> munch W m m' ->
  (bv_unsigned a + Z.of_nat k <= 0x160040)%Z ->
  rdn segs m a k = Some bs -> rdn segs m' a k = Some bs.
Proof.
  intros m m' W a k bs HW MU Ha H. rewrite <- H. apply rdn_ext; [lia|].
  intros x Hx. apply MU. apply outside_aapp; [exact HW|]. pose proof (bv_unsigned_in_range 64 x). unfold bv_modulus in *. lia.
Qed.
End T.
Lemma aenv_munch_a : forall m m' W, aapp_all W -> munch W m m' -> aenv m -> aenv m'.
Proof.
  intros m m' W HW MU (H1 & H2 & H3 & H4 & H5). unfold aenv, ai_byte, fx_got in *.
  unfold Pm9RegionPoisoned.rt_layout_globs, Pm9AsanMemcpy.mc_icpt_globs, Pm9AsanMemset.ms_icpt_globs in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply rdn_munch_a; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.

Ltac aapp_tac :=
  cbn [aapp_all]; repeat split;
  first [ exact I | left; lia | right; split; [lia | unfold app; right; lia]
        | right; split; [lia | match goal with H : app ?p ?n |- app ?p ?n' => eapply app_sub; [exact H | lia] end] ].
Lemma rt_layout_globs_munch_a : forall m m' W, aapp_all W -> munch W m m' -> Pm9RegionPoisoned.rt_layout_globs m -> Pm9RegionPoisoned.rt_layout_globs m'.
Proof.
  intros m m' W HW MU H. unfold Pm9RegionPoisoned.rt_layout_globs in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply rdn_munch_a; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.
Lemma mc_icpt_globs_munch_a : forall m m' W, aapp_all W -> munch W m m' -> Pm9AsanMemcpy.mc_icpt_globs m -> Pm9AsanMemcpy.mc_icpt_globs m'.
Proof.
  intros m m' W HW MU H. unfold Pm9AsanMemcpy.mc_icpt_globs in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; (eapply rdn_munch_a; [exact HW | exact MU | | eassumption ]); vm_compute; congruence.
Qed.
