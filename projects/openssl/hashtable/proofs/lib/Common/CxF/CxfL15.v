(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfRt CxfL1 CxfL2 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFRTL.
Import CXFRT.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Definition is_kdisj (K : kentry) : bool := match K with KDisj _ _ _ _ => true | _ => false end.
Lemma L_CXFRTL_is_kdisj : @is_kdisj = @CXFRT.is_kdisj.
Proof. unfold is_kdisj. reflexivity. Qed.

Definition kd_eqb (x y : kentry) : bool :=
  match x, y with
  | KDisj a1 n1 a2 n2, KDisj b1 m1 b2 m2 =>
      if Z.eqb (a_off a1) (a_off b1) then if Z.eqb (a_off a2) (a_off b2) then
      if expr_eqb n1 m1 then if expr_eqb n2 m2 then
      if expr_eqb (a_base a1) (a_base b1) then expr_eqb (a_base a2) (a_base b2) else false else false else false else false else false
  | _, _ => false
  end.
Lemma L_CXFRTL_kd_eqb : @kd_eqb = @CXFRT.kd_eqb.
Proof. unfold kd_eqb. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Fixpoint kl_eqb (a b : list kentry) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => if kd_eqb x y then kl_eqb a' b' else false
  | _, _ => false
  end.
Lemma L_CXFRTL_kl_eqb : @kl_eqb = @CXFRT.kl_eqb.
Proof. unfold kl_eqb. rewrite ?L_CXFRTL_kd_eqb. reflexivity. Qed.

Definition rtc : Type := option (list kentry * rtab).
Lemma L_CXFRTL_rtc : @rtc = @CXFRT.rtc.
Proof. unfold rtc. reflexivity. Qed.

Definition rtc_ok (c : rtc) : Prop := match c with Some (kd, rt) => rt = mk_rt kd | None => True end.
Lemma L_CXFRTL_rtc_ok : @rtc_ok = @CXFRT.rtc_ok.
Proof. unfold rtc_ok. rewrite ?L_CXFRTL_rtc, ?AX2BL.L_AX2BL_mk_rt. reflexivity. Qed.

Definition get_rt (c : rtc) (fk : list kentry) : rtab * rtc :=
  let kd := List.filter is_kdisj fk in
  match c with
  | Some (kd', rt) => if kl_eqb kd kd' then (rt, c) else let rt' := mk_rt kd in (rt', Some (kd, rt'))
  | None => let rt' := mk_rt kd in (rt', Some (kd, rt'))
  end.
Lemma L_CXFRTL_get_rt : @get_rt = @CXFRT.get_rt.
Proof. unfold get_rt. rewrite ?L_CXFRTL_is_kdisj, ?L_CXFRTL_kl_eqb, ?L_CXFRTL_rtc, ?AX2BL.L_AX2BL_mk_rt. reflexivity. Qed.

Definition mkbc_c (c : rtc) (fk : list kentry) : bctx * rtc :=
  let ffk := facts_of fk in let ri := mk_ri ffk in
  let rc := get_rt c fk in
  (BC fk ffk (sum_factsB (BC fk ffk [] ri (fst rc)) fk) ri (fst rc), snd rc).
Lemma L_CXFRTL_mkbc_c : @mkbc_c = @CXFRT.mkbc_c.
Proof. unfold mkbc_c. rewrite ?L_CXFRTL_rtc, ?L_CXFRTL_get_rt, ?AX2L.L_AX2L_facts_of, ?AX2BL.L_AX2BL_mk_ri, ?AX2BL.L_AX2BL_sum_factsB. reflexivity. Qed.

End CXFRTL.
