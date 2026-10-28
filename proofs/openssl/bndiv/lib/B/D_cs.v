(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma client_static_intro : forall x,
  (0x5e6630 <= x < 0x6a0398)
  \/ (0xbc6050 <= x < 0xbd6050)
  \/ (0xbd6050 <= x < 0xbdadf8)
  \/ (0xbdae00 <= x < 0xbdae48)
  \/ (0xbdae90 <= x < 0xbfb110)
  \/ (0xbfb118 <= x < 0xbfc1f8)
  \/ (0xbfc200 <= x < 0xbfc730) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x6a0398); [exists 0x5e6630, 0x6a0398; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0xbd6050); [exists 0xbc6050, 0xbd6050; split; [right; left; reflexivity| lia]|]. exists 0xbd6050, 0xbfc730; split; [right; right; left; reflexivity| lia].
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
Lemma errno_static : forall x, 0xbdadac <= x < 0xbdadb0 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.
Lemma cancel_static : forall x, 0xbdae50 + -156 <= x < 0xbdae50 + -151 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.

Lemma stk_wr : forall m lo hi a n, stk bsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at bsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.
