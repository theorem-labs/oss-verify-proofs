(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition SC (s : inflate_state) (h b : Z) : Prop :=
  let m := is_mode s in
  if m =? HEAD then b < 16
  else if m =? DICTID then b < 32
  else if (m =? TYPE) || (m =? TYPEDO) then is_last s = 0 /\ b < 3
  else if m =? STORED then b mod 8 = 0 /\ b < 32
  else if (m =? COPY_) || (m =? COPY) then 0 < is_length s
  else if m =? TABLE then b < 14
  else if m =? LENLENS then is_have s < is_ncode s /\ b < 3
  else if m =? CODELENS then is_have s < is_nlen s + is_ndist s /\ b < cneed s h
  else if (m =? LEN_) || (m =? LEN) then b < lneed s (is_lencode s) (is_lenbits s) h
  else if (m =? LENEXT) || (m =? DISTEXT) then is_extra s <> 0 /\ b < is_extra s
  else if m =? DIST then b < lneed s (is_distcode s) (is_distbits s) h
  else if m =? CHECK then b < 32
  else False.

Definition STALLED (s : inflate_state) : Prop := SC s (is_hold s) (is_bits s).

Definition UWL (s : inflate_state) : Prop :=
  is_wrap s = 5 /\ (is_flags s = 0 \/ is_mode s = HEAD \/ is_mode s = BAD \/ is_mode s = MEM).

Definition LV (w : iw) : Prop :=
  ir_left (w_r w) = 0 \/ ir_ret (w_r w) <> Z_OK \/ (ir_have (w_r w) = 0 /\ SC (w_s w) (ir_hold (w_r w)) (ir_bits (w_r w))).

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

Ltac sc_red :=
  cbv beta iota delta [SC Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC].
Ltac sc_red_in H :=
  cbv beta iota delta [SC Z.eqb Pos.eqb orb
                       HEAD FLAGS TIME OS EXLEN EXTRA NAME COMMENT HCRC DICTID DICT TYPE TYPEDO STORED COPY_ COPY
                       TABLE LENLENS CODELENS LEN_ LEN LENEXT DIST DISTEXT MATCH LIT CHECK LENGTH DONE BAD MEM SYNC] in H.

Ltac lv_stall E :=
  right; right; cbn [w_r w_s]; sacc; split; [first [assumption | lia] |]; unfold SC; sacc; rewrite ?E; sc_red.

Ltac lv_left := left; cbn [w_r]; sacc; first [assumption | lia | reflexivity].
Ltac lv_ret := right; left; cbn [w_r]; sacc; intros XX; discriminate XX.

Lemma LV_left : forall s c r, ir_left r = 0 -> LV (mkW s c r).
Proof. intros s c r H. left. exact H. Qed.

Lemma LV_stall : forall s c r, ir_have r = 0 -> SC s (ir_hold r) (ir_bits r) -> LV (mkW s c r).
Proof. intros s c r H1 H2. right; right. exact (conj H1 H2). Qed.

Lemma SC_keep : forall s s' h b,
  is_mode s' = is_mode s -> is_last s' = is_last s -> is_length s' = is_length s -> is_extra s' = is_extra s ->
  is_have s' = is_have s -> is_ncode s' = is_ncode s -> is_nlen s' = is_nlen s -> is_ndist s' = is_ndist s ->
  is_lencode s' = is_lencode s -> is_distcode s' = is_distcode s -> is_lenbits s' = is_lenbits s -> is_distbits s' = is_distbits s ->
  is_lens s' = is_lens s -> is_codes s' = is_codes s ->
  SC s h b -> SC s' h b.
Proof.
  intros s s' h b E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 H.
  assert (EC : forall p x, code_at s' p x = code_at s p x) by (intros p x; unfold code_at; rewrite E14; reflexivity).
  assert (EL : forall p root hh, lneed s' p root hh = lneed s p root hh) by (intros; unfold lneed; rewrite !EC; reflexivity).
  assert (EN : forall hh, cneed s' hh = cneed s hh) by (intros; unfold cneed; rewrite E9, E11, !EC; reflexivity).
  unfold SC in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, EL, EL, EN. exact H.
Qed.

Lemma UWL_mode : forall s s', UWL s -> is_wrap s' = is_wrap s -> is_flags s' = is_flags s ->
  is_mode s <> HEAD -> is_mode s <> BAD -> is_mode s <> MEM -> UWL s'.
Proof.
  intros s s' [W F] Ew Ef N1 N2 N3. split; [rewrite Ew; exact W|]. left. rewrite Ef.
  destruct F as [F|[F|[F|F]]]; [exact F|exfalso; exact (N1 F)|exfalso; exact (N2 F)|exfalso; exact (N3 F)].
Qed.

Lemma pulled_have0 : forall r r', pulled r r' -> ir_have r = 0 ->
  ir_next r' = ir_next r /\ ir_have r' = 0 /\ ir_bits r' = ir_bits r /\ ir_hold r' = ir_hold r
  /\ ir_put r' = ir_put r /\ ir_left r' = ir_left r /\ ir_in r' = ir_in r /\ ir_out r' = ir_out r /\ ir_ret r' = ir_ret r.
Proof.
  intros r r' (k & Hk & N & Hv & Hv0 & B & M & R & P & L & I & O & T) H0.
  assert (K0 : k = 0) by lia. subst k.
  assert (EB : ir_bits r' = ir_bits r) by lia.
  assert (EH : ir_hold r' = ir_hold r).
  { rewrite <- M. symmetry. apply Z.mod_small. rewrite <- EB. exact R. }
  repeat split; try assumption; lia.
Qed.

Lemma land15_range : forall a, 0 <= a -> 0 <= Z.land a 15 <= 15.
Proof.
  intros a Ha. replace 15 with (Z.ones 4) by reflexivity. rewrite Z.land_ones by lia. rewrite Z.ones_equiv.
  pose proof (Z.mod_pos_bound a (2 ^ 4) ltac:(lia)). lia.
Qed.

Ltac uwl_keep HU E :=
  apply (UWL_mode _ _ HU); [sacc; reflexivity | sacc; reflexivity
                          | rewrite E; intros XX; discriminate XX | rewrite E; intros XX; discriminate XX | rewrite E; intros XX; discriminate XX].
