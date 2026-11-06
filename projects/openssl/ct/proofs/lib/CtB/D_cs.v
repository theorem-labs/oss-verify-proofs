(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr. 
From OSSVerify.Proofs.openssl.ct.lib.CtB Require Import Layout RT_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma client_static_intro : forall x,
  (0x5e74c8 <= x < 0x6a1818)
  \/ (0xbc74d0 <= x < 0xbd74d0)
  \/ (0xbd74d0 <= x < 0xbdc1d8)
  \/ (0xbdc1e0 <= x < 0xbdc228)
  \/ (0xbdc270 <= x < 0xbfc4f0)
  \/ (0xbfc4f8 <= x < 0xbfd5d8)
  \/ (0xbfd5e0 <= x < 0xbfdb10) -> client_static x.
Proof.
  intros x Hx. split.
  - destruct (Z.ltb_spec0 x 0x6a1818); [exists 0x5e74c8, 0x6a1818; split; [left; reflexivity| lia]|]. destruct (Z.ltb_spec0 x 0xbd74d0); [exists 0xbc74d0, 0xbd74d0; split; [right; left; reflexivity| lia]|]. exists 0xbd74d0, 0xbfdb10; split; [right; right; left; reflexivity| lia].
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
Lemma errno_static : forall x, 0xbdc18c <= x < 0xbdc190 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.
Lemma cancel_static : forall x, 0xbdc230 + -156 <= x < 0xbdc230 + -151 -> client_static x.
Proof. intros x Hx. apply client_static_intro. lia. Qed.

Lemma stk_wr : forall m lo hi a n, stk ctbsegs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at ctbsegs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|]. intros i Hi. apply H. lia.
Qed.
