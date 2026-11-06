(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ZBridge TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma nb_pos : forall b e, 0 < b -> 0 < e -> Z.lxor (Z.b2z (0 <? b)) (Z.b2z (e <? 1)) = 1.
Proof. intros b e Hb He. destruct (Z.ltb_spec 0 b); destruct (Z.ltb_spec e 1); cbn; first [reflexivity | exfalso; lia]. Qed.
Lemma nb_nil : Z.lxor (Z.b2z (0 <? 0)) (Z.b2z (0 <? 1)) = 1.
Proof. reflexivity. Qed.
Lemma b2z_pos : forall x, 0 < x -> Z.b2z (0 <? x) = 1.
Proof. intros x Hx. destruct (Z.ltb_spec 0 x); [reflexivity | exfalso; lia]. Qed.
Lemma b2z_lt1 : forall x, 0 < x -> Z.b2z (x <? 1) = 0.
Proof. intros x Hx. destruct (Z.ltb_spec x 1); [exfalso; lia | reflexivity]. Qed.

Ltac notrap_al F :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K; [exfalso; rewrite land7_mod8 in K; exact (K F) | clear K].

Ltac notrap_shr KR :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K;
  [ exfalso; rewrite Z.shiftr_div_pow2 in K by lia; rewrite Z.div_small in K by (clear - KR; lia); apply K; reflexivity | clear K ].
