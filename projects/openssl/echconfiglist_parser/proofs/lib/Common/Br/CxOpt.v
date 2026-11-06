(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
Import ListNotations. Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ledger_pos (k : list kentry) (ms : list amap) : bool := true.

Definition ledger_exact (E : env) (ms : list amap) : Prop := no_fog ms = true.

Lemma ledger_exact_nf : forall E ms, ledger_exact E ms -> no_fog ms = true.
Proof. intros E ms H. exact H. Qed.

Lemma maps_exact_D1 : forall E ms l, ledger_exact E ms -> maps_match E ms l -> l = map (amap_den E) ms.
Proof.
  intros E ms l H HM.
  exact (proj1 (maps_match_exact 0%nat (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) E ms l H) HM).
Qed.

Lemma ledger_exact_intro (segs : list Segment) (E : env) (M : word -> option byte) (k : list kentry)
  (HK : know_ok segs E M k) : forall ms, no_fog ms = true -> ledger_pos k ms = true -> ledger_exact E ms.
Proof. intros ms H _. exact H. Qed.
