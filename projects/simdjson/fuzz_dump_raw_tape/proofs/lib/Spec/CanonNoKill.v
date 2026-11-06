(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim Canon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma in_prefix {A} : forall (l1 l2 : list A) x, is_prefix l1 l2 -> In x l1 -> In x l2.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x Hp Hin; [destruct Hin|].
  destruct l2 as [|b l2]; cbn in Hp; [contradiction|]. destruct Hp as [-> Hp].
  destruct Hin as [->|Hin]; [left; reflexivity| right; exact (IH l2 x Hp Hin)].
Qed.

Lemma ct_events_nokill : forall fs ct sig fs', ~ In (KillEv sig fs') (ct_events fs ct).
Proof.
  intros fs ct sig fs' Hin. unfold ct_events in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - unfold evw in Hin. apply in_map_iff in Hin. destruct Hin as (b & Hb & _). discriminate Hb.
  - destruct Hin as [Hin|[]]. discriminate Hin.
Qed.

Theorem canonT_nokill : forall argv fs tr sig fs', canonT argv fs tr -> ~ In (KillEv sig fs') tr.
Proof.
  intros argv fs tr sig fs' (ct & _ & Hp) Hin.
  exact (ct_events_nokill fs ct sig fs' (in_prefix _ _ _ Hp Hin)).
Qed.
