(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition OC (s : inflate_state) : Prop :=
  let m := is_mode s in
  if (m =? LIT) || (m =? MATCH) then True
  else if (m =? COPY_) || (m =? COPY) then 0 < is_length s
  else False.

Definition OSTALLED (s : inflate_state) : Prop := OC s.

Ltac oc_red :=
  cbv beta iota zeta delta [OC OSTALLED Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac oc_red_in H :=
  cbv beta iota zeta delta [OC OSTALLED Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.

Lemma OC_keep : forall s s', is_mode s' = is_mode s -> is_length s' = is_length s -> OC s -> OC s'.
Proof. intros s s' E1 E2 H. unfold OC in *. rewrite E1, E2. exact H. Qed.

Lemma OC_not_TYPE : forall s, OC s -> is_mode s <> TYPE.
Proof. intros s H E. unfold OC in H. rewrite E in H. oc_red_in H. exact H. Qed.

Definition LV (w : iw) : Prop :=
  (ir_left (w_r w) = 0 /\ OC (w_s w)) \/ ir_ret (w_r w) <> Z_OK \/ (ir_have (w_r w) = 0 /\ SC (w_s w) (ir_hold (w_r w)) (ir_bits (w_r w))).

Definition SQ {A} (res : ares A) : Prop :=
  match res with
  | ARun _ _ => True
  | ALeave w' => LV w'
  | ARet rc _ => rc <> Z_OK
  end.

Definition arm_sq (M : Z) (arm : AM unit) : Prop :=
  forall s c r, WINV (mkW s c r) -> UWL s -> is_mode s = M -> SQ (arm (mkW s c r)).

Section Rules.
  Context {A B : Type}.

  Lemma SQ_bind : forall (m : AM A) (f : A -> AM B) w,
    match m w with
    | ARun a w' => SQ (f a w')
    | ALeave w' => LV w'
    | ARet rc _ => rc <> Z_OK
    end ->
    SQ (abind m f w).
  Proof. intros m f w H. unfold abind. destruct (m w); exact H. Qed.

  Lemma SQ_bind_run : forall (m : AM A) (f : A -> AM B) w a w',
    m w = ARun a w' -> SQ (f a w') -> SQ (abind m f w).
  Proof. intros m f w a w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma SQ_bind_leave : forall (m : AM A) (f : A -> AM B) w w',
    m w = ALeave w' -> LV w' -> SQ (abind m f w).
  Proof. intros m f w w' E H. unfold abind. rewrite E. exact H. Qed.
  Lemma SQ_bind_ret : forall (m : AM A) (f : A -> AM B) w rc w',
    m w = ARet rc w' -> rc <> Z_OK -> SQ (abind m f w).
  Proof. intros m f w rc w' E H. unfold abind. rewrite E. exact H. Qed.

  Lemma SQ_bind_any : forall (m : AM A) (f : A -> AM B) w,
    SQ (m w) -> (forall a w', SQ (f a w')) -> SQ (abind m f w).
  Proof. intros m f w Hm Hf. unfold abind. destruct (m w); [apply Hf|exact Hm|exact Hm]. Qed.

End Rules.

Ltac acase3 H :=
  lazymatch goal with
  | |- SQ (abind (if ?cnd then _ else _) _ _) => destruct cnd eqn:H
  | |- SQ ((if ?cnd then _ else _) _) => destruct cnd eqn:H
  | |- SQ (abind (abind _ _) _ _) => rewrite abind_assoc; acase3 H
  end.
Ltac arun3 lem := eapply SQ_bind_run; [apply lem|]; cbv beta iota.
Ltac aleave3 :=
  first [ rewrite aleave_eq; cbn [SQ]
        | rewrite areturn_eq; cbn [SQ]
        | eapply SQ_bind_leave; [reflexivity|]
        | eapply SQ_bind_ret; [reflexivity|] ].
Ltac arun03 := eapply SQ_bind_run; [reflexivity|]; cbv beta iota.
Ltac pstep3 lem := apply SQ_bind; rewrite lem.

Ltac lv_stall E :=
  right; right; cbn [w_r w_s]; sacc; split; [first [assumption | lia] |]; unfold SC; sacc; rewrite ?E; sc_red.

Ltac lv_left E := left; cbn [w_r w_s]; sacc; split; [first [assumption | lia | reflexivity] | unfold OC; sacc; rewrite ?E; oc_red; first [exact I | lia | assumption]].
Ltac lv_ret := right; left; cbn [w_r]; sacc; intros XX; discriminate XX.

Lemma LV_left : forall s c r, ir_left r = 0 -> OC s -> LV (mkW s c r).
Proof. intros s c r H1 H2. left. exact (conj H1 H2). Qed.

Lemma LV_stall : forall s c r, ir_have r = 0 -> SC s (ir_hold r) (ir_bits r) -> LV (mkW s c r).
Proof. intros s c r H1 H2. right; right. exact (conj H1 H2). Qed.
