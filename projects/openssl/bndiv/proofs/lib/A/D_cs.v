(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr ImageA.
From OSSVerify.Proofs.openssl.bndiv.lib.A Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma client_static_intro : forall x,
  (0x5ade30 <= x < 0x66d5d8)
  \/ (0xb93290 <= x < 0xba3290)
  \/ (0xba3290 <= x < 0xba8038)
  \/ (0xba8040 <= x < 0xba8088)
  \/ (0xba80d0 <= x < 0xbc8350)
  \/ (0xbc8358 <= x < 0xbc9438)
  \/ (0xbc9440 <= x < 0xbc9970) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x66d5d8); [exists 0x5ade30, 0x66d5d8; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0xba3290); [exists 0xb93290, 0xba3290; split; [right; left; reflexivity| lia]|]. exists 0xba3290, 0xbc9970; split; [right; right; left; reflexivity| lia].
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
Lemma errno_static : forall x, 0xba7fec <= x < 0xba7ff0 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.
Lemma cancel_static : forall x, 0xba8090 + -156 <= x < 0xba8090 + -151 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.

Lemma stk_wr : forall m lo hi a n, stk asegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at asegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.
