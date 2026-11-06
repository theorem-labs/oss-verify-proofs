(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma client_static_intro : forall x,
  (0x5e2868 <= x < 0x69c3d8)
  \/ (0xbc2090 <= x < 0xbd2090)
  \/ (0xbd2090 <= x < 0xbd6d98)
  \/ (0xbd6da0 <= x < 0xbd6de8)
  \/ (0xbd6e30 <= x < 0xbf70b0)
  \/ (0xbf70b8 <= x < 0xbf8198)
  \/ (0xbf81a0 <= x < 0xbf86d0) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x69c3d8); [exists 0x5e2868, 0x69c3d8; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0xbd2090); [exists 0xbc2090, 0xbd2090; split; [right; left; reflexivity| lia]|]. exists 0xbd2090, 0xbf86d0; split; [right; right; left; reflexivity| lia].
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

Lemma stk_wr : forall m lo hi a n, stk bgbsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at bgbsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.
