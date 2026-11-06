(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Cells Frame Step.
Import ListNotations.
Open Scope Z_scope.

Section Agree.
Variable segs : list Segment.

Definition agree_on (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a ->
    m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma agree_on_refl : forall P m, agree_on P m m.
Proof. intros P m a _ _. auto. Qed.
#[using="Type"] Lemma agree_on_trans : forall P m1 m2 m3, agree_on P m1 m2 -> agree_on P m2 m3 -> agree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [congruence|auto]. Qed.
#[using="Type"] Lemma agree_on_mono : forall (P P' : Z -> Prop) m m', agree_on P m m' -> (forall a, P' a -> P a) -> agree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.

#[using="Type"] Lemma bytes_at_agree : forall P m m' A bs,
  agree_on P m m' -> bytes_at segs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) ->
  bytes_at segs m' A bs.
Proof.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma wr_at_agree : forall P m m' A n,
  agree_on P m m' -> wr_at segs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at segs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rw_cells_agree : forall P m m' A cs,
  agree_on P m m' -> rw_cells segs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  rw_cells segs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply wr_at_agree; eauto.
Qed.

#[using="Type"] Lemma stk_agree : forall P m m' lo hi,
  agree_on P m m' -> stk segs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk segs m' lo hi.
Proof.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HS i Hi) as [W [b Hb]]. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W'].
  split; [apply W', W|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

#[using="Type"] Lemma agree_on_of_munch : forall W m m', munch W m m' -> wmono segs m m' -> agree_on (fun a => outside W a) m m'.
Proof.
  intros W m m' MU WM a Ha Ho. split; [| apply WM]. apply MU. rewrite wa_unsigned by exact Ha. exact Ho.
Qed.

Fixpoint rin_ivs (ivs : list (Z * Z)) (a : Z) : Prop :=
  match ivs with
  | [] => False
  | iv :: rest => (fst iv <= a < snd iv) \/ rin_ivs rest a
  end.
End Agree.
