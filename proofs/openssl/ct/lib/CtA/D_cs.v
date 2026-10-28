(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma client_static_intro : forall x,
  (0x5aebc8 <= x < 0x66e9d8)
  \/ (0xb94690 <= x < 0xba4690)
  \/ (0xba4690 <= x < 0xba9398)
  \/ (0xba93a0 <= x < 0xba93e8)
  \/ (0xba9430 <= x < 0xbc96b0)
  \/ (0xbc96b8 <= x < 0xbca798)
  \/ (0xbca7a0 <= x < 0xbcacd0) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x66e9d8); [exists 0x5aebc8, 0x66e9d8; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0xba4690); [exists 0xb94690, 0xba4690; split; [right; left; reflexivity| lia]|]. exists 0xba4690, 0xbcacd0; split; [right; right; left; reflexivity| lia].
  - intros (lo & hi & Hin & Hlh). unfold RT_STATIC in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma client_static_range : forall x, client_static x -> 0x10000 <= x < SEGTOP_A.
Proof.
  intros x ((lo & hi & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. unfold SEGTOP_A.
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Lemma stage_static' : forall x, g_read_stage <= x < g_read_stage + 65536 -> client_static x.
Proof. intros x Hx. apply client_static_intro. unfold g_read_stage in *. lia. Qed.

Lemma stage_static : forall i, 0 <= i < 65536 -> client_static (g_read_stage + i).
Proof. intros i Hi. apply stage_static'. lia. Qed.

(* [comment removed for export] *)
Lemma errno_static : forall x, 0xba934c <= x < 0xba9350 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.
Lemma cancel_static : forall x, 0xba93f0 + -156 <= x < 0xba93f0 + -151 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.

Lemma stk_wr : forall m lo hi a n, stk ctasegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at ctasegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.
