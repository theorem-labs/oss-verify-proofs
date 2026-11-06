(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition app2r (lo hi : Z) : Prop := ((6537216 <= lo /\ hi <= 2147446784) \/ (KHI <= lo /\ hi <= KTOP))%Z.

Lemma app2r_lo : forall lo hi, app2r lo hi -> (6537216 <= lo)%Z.
Proof. unfold app2r. intros lo hi [[H _]|[H _]]; lia. Qed.
Lemma app2r_hi : forall lo hi, app2r lo hi -> (hi <= KTOP)%Z.
Proof. unfold app2r. intros lo hi [[_ H]|[_ H]]; lia. Qed.

Lemma app2r_sub : forall lo hi lo' hi', app2r lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> app2r lo' hi'.
Proof. unfold app2r. intros lo hi lo' hi' [[H1 H2]|[H1 H2]] H3 H4; [left|right]; lia. Qed.

Lemma app2r_intro_lo : forall lo hi, (6537216 <= lo)%Z -> (hi <= 2147446784)%Z -> app2r lo hi.
Proof. unfold app2r. intros; left; lia. Qed.
Lemma app2r_intro_hi : forall lo hi, (KHI <= lo)%Z -> (hi <= KTOP)%Z -> app2r lo hi.
Proof. unfold app2r. intros; right; lia. Qed.

(* [comment removed for export] *)
Lemma app2r_lin : forall lo hi, app2r lo hi ->
  exists c : Z, (0 <= c <= 1)%Z /\ (6537216 <= lo)%Z /\ (hi <= 2147446784 + c * 2^47)%Z /\ (KHI * c <= lo)%Z /\ (hi <= KTOP)%Z.
Proof. unfold app2r. intros lo hi [[H1 H2]|[H1 H2]]; [exists 0%Z | exists 1%Z]; lia. Qed.

(* [comment removed for export] *)
Definition rt_app (x n : Z) : Prop := ((4096 <= x /\ x + n <= 2147446784) \/ KHI <= x)%Z.
Lemma rt_app_lo : forall x n, rt_app x n -> (4096 <= x)%Z.
Proof. unfold rt_app. intros x n [[H _]|H]; lia. Qed.

(* [comment removed for export] *)
Ltac app2_has_lin lo := match goal with _ : (17594333495296 * _ <= lo)%Z |- _ => idtac end.
Ltac app2_flatten :=
  repeat match goal with
  | H : ?A /\ ?B |- _ =>
      lazymatch type of H with
      | context [app2r ?lo ?hi] =>
          tryif (match goal with _ : app2r lo hi |- _ => idtac end) then fail
          else (let H' := fresh "Hfl" in let Ha := fresh "Hfl" in let Hb := fresh "Hfl" in
                pose proof H as H'; destruct H' as [Ha Hb])
      | _ => fail
      end
  end.
Ltac app2_lin_all :=
  app2_flatten;
  repeat match goal with
  | H : app2r ?lo ?hi |- _ =>
      tryif app2_has_lin lo then fail
      else (let c := fresh "cls" in let H1 := fresh "Hcl" in let H2 := fresh "Hcl" in let H3 := fresh "Hcl" in
            let H4 := fresh "Hcl" in let H5 := fresh "Hcl" in
            destruct (app2r_lin lo hi H) as (c & H1 & H2 & H3 & H4 & H5))
  end;
  repeat match goal with
  | H : rt_app ?x ?n |- _ =>
      tryif (match goal with _ : (4096 <= x)%Z |- _ => idtac end) then fail
      else (let H1 := fresh "Hcl" in pose proof (rt_app_lo x n H) as H1)
  end.
(* [comment removed for export] *)
Ltac app2_pending :=
  match goal with
  | H : app2r ?lo _ |- _ => tryif app2_has_lin lo then fail else idtac
  | H : rt_app ?x _ |- _ => tryif (match goal with _ : (4096 <= x)%Z |- _ => idtac end) then fail else idtac
  | H : ?A /\ ?B |- _ =>
      lazymatch type of H with
      | context [app2r ?lo ?hi] => tryif (match goal with _ : app2r lo hi |- _ => idtac end) then fail else idtac
      end
  end.
Ltac lia_app2 :=
  lazymatch goal with
  | |- app2r _ _ =>
      solve [ app2_flatten; match goal with H : app2r _ _ |- _ => eapply app2r_sub; [exact H | lia_t12 | lia_t12] end
            | apply app2r_intro_hi; lia_t12
            | apply app2r_intro_lo; lia_t12 ]
  | |- ?A /\ ?B => split; lia_tc
  | _ => app2_pending; app2_lin_all; first [ lia_t12 | lia_t3 ]
  end
with lia_tc := first [ LiaCap.lia_cap_s ltac:(lia_t1) ltac:(fail) | lia_t2 | lia_app2 | lia_t3 ].
