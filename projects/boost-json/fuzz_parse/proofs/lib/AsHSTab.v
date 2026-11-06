(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import List.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AsanPlanCore AsanPlan.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~03acs37Corelib4Init9Datatypesk33natk34prodk34Somek34listk36optionk34pair37Corelib4Init5Logico62eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7AsHSTab~~~~~~pf9hs_lookup36Stdlib5Lists4Listu52Ink33fstk33sndo65Falseo63ando62oru5afold_right" s.
Import ListNotations. Import AP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint hs_lookup (h : nat) (l : list (nat * acs)) : option acs :=
  match l with
  | [] => None
  | (k, c) :: r => if Nat.eqb h k then Some c else hs_lookup h r
  end.

Lemma hs_lookup_In : ltac2:(zQ "a0!je!lb!m1!m8!mf!n6!nf!pa!t9!v8>1h$1>1l@1$4@2$2$1$0>1c$0>0@3$7@1$5$0@2$8^3^2@2$3$0^1@3$9@2$2$1$0@4$6$1$0^4^2^3").
Proof.
  intros h l c. induction l as [|[k c'] r IH]; cbn [hs_lookup]; intros H; [discriminate H|].
  destruct (Nat.eqb h k) eqn:E.
  - apply PeanoNat.Nat.eqb_eq in E. subst k. injection H as ->. left. reflexivity.
  - right. apply IH. exact H.
Qed.

(* [comment removed for export] *)
Lemma hs_lookup_cases : ltac2:(zQ "e0!je!lb!m1!pa!m8!vd!mf!n6!hg3!hg9!hh1!hh7!t9!hhc>1h$1>1l@1$6@2$2$1$0>1c$0>0@3$3@1$7$0@2$c^3^2@2$4$0^1@5$dP@2$2$1$0\2kc@2$2$1$0\1PP@2$b@2$a@3$3$1^6@3$5$1$0^2@3$3$0^4@3$8$1$0^2^1$9^3").
Proof.
  intros h l c H. apply hs_lookup_In in H. induction l as [|[k c'] r IH]; cbn [fold_right fst snd In] in *; [exact H|].
  destruct H as [H|H]; [left; injection H as -> ->; split; reflexivity | right; apply IH; exact H].
Qed.
