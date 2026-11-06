(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL (the items loop): the PURE facts its pieces take
   (ExvB_Loop_Stmt.v PURE_L_STEP / PURE_V_REST / PURE_NAME_REST / PURE_SUFFIX / PURE_PREF_CONS / PURE_PREF_LONG),
   proved closed. The grammar lemmas are the plain ex_value_m.v ones (run0_bind, run0_grow, run0_jr_string,
   run0_jr_name, ex_name_suf, the suf_* lemmas, suf_fuel, ex_V_len, ex_L_step, ex_V_rest) RESTATED here at
   ReaderRes.jr_strtod (plain ex_sm), with exv_run0 / exv_L / exv_name / exv_cap / PRH_FnEx.prhex_V for plain
   run0 / ex_L / ex_name / ex_cap / ex_V; no plain lemma is Required or cited. PjGrammar's own lemmas are used by name
   (agrees_*, fuel_mono, jr_value_fuel, jr_value_rest, decode_stop, skip_len, span_app).
   Rule 24: proves no function (kind: segment lemma).
   Numerals: 34, 44, 58, 91, 123, 116, 102, 110, 48 (WORD: ASCII bytes of the grammar: double quote, comma, colon,
   open bracket, open brace, the literals' first letters t / f / n, digit zero); 0, 1, 2 (LENGTH: skip counts and the
   grammar's fuel arithmetic 2 * length + 1 / + 2). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Arith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Abbreviation sm := ReaderRes.jr_strtod.

(* ---- exv_run0 over the grammar's monad (the plain run0 lemmas) ---- *)
Lemma exvp_run0_bind : forall A B (m : M A) (k : A -> M B), agrees m ->
  exv_run0 (jbind m k) = match exv_run0 m with Some a => exv_run0 (k a) | None => None end.
Proof.
  intros A B m k H. unfold exv_run0, jbind.
  destruct (m []) as [[r t] o] eqn:E.
  pose proof (agrees_nil A m H) as N. rewrite E in N. cbn [fst snd] in N.
  inversion N; subst; clear N.
  destruct r as [a|]; cbn [fst snd]; [|reflexivity].
  destruct (k a []) as [[r1 t1] o1]; reflexivity.
Qed.

Lemma exvp_run0_ret : forall A (a : A), exv_run0 (jret a) = Some a.
Proof. reflexivity. Qed.

Lemma exvp_run0_alloc : forall A n (k : unit -> M A), exv_run0 (jbind (jalloc n) k) = exv_run0 (k tt).
Proof.
  intros A n k. unfold exv_run0, jbind, jalloc, take. cbv beta iota zeta.
  destruct (k tt []) as [[r t] o]. reflexivity.
Qed.

Lemma exvp_run0_grow : forall o n cap, exv_run0 (grow o n cap) = Some (exv_cap n cap).
Proof.
  intros o n cap. unfold grow, exv_cap.
  destruct (Nat.ltb n cap); [reflexivity|]. destruct o; reflexivity.
Qed.

Lemma exvp_run0_jr_string : forall y, exv_run0 (jr_string y) = decode y.
Proof.
  intros y. unfold jr_string.
  destruct (scan y) as [q|] eqn:Es.
  - destruct (decode y) as [sr|]; reflexivity.
  - destruct (decode y) as [[s r]|] eqn:Ed; [|reflexivity].
    destruct (decode_stop y s r Ed) as (q & Hq & _). congruence.
Qed.

Lemma exvp_run0_jr_name : forall o y, exv_run0 (jr_name o y) = exv_name o y.
Proof.
  intros [|] y; [|reflexivity].
  unfold jr_name, exv_name. cbv beta iota.
  destruct (skip y) as [|b z]; cbv beta iota; [reflexivity|].
  destruct (b =? 34); cbv beta iota; [|reflexivity].
  rewrite exvp_run0_bind by apply agrees_jr_string.
  destruct (exv_run0 (jr_string z)) as [[nm r]|]; cbv beta iota; [|reflexivity].
  destruct (skip r) as [|c r1]; cbv beta iota; [reflexivity|].
  destruct (c =? 58); reflexivity.
Qed.

(* ---- suffixes (the plain suf lemmas) ---- *)
Definition exvp_suf (r x : list Z) : Prop := exists k, r = skipn k x.

Lemma exvp_skipn_skipn : forall (x : list Z) a b, skipn a (skipn b x) = skipn (b + a) x.
Proof.
  induction x as [|c x IH]; intros a b; [rewrite !skipn_nil; reflexivity|].
  destruct b as [|b]; [reflexivity|]. cbn [skipn Nat.add]. apply IH.
Qed.

Lemma exvp_suf_refl : forall x, exvp_suf x x.
Proof. intros x. exists 0%nat. reflexivity. Qed.

Lemma exvp_suf_trans : forall a b c, exvp_suf a b -> exvp_suf b c -> exvp_suf a c.
Proof. intros a b c [k1 ->] [k2 ->]. exists (k2 + k1)%nat. apply exvp_skipn_skipn. Qed.

Lemma exvp_suf_cons : forall r b y, exvp_suf r y -> exvp_suf r (b :: y).
Proof. intros r b y [k ->]. exists (S k). reflexivity. Qed.

Lemma exvp_suf_skipn : forall k x, exvp_suf (skipn k x) x.
Proof. intros k x. exists k. reflexivity. Qed.

Lemma exvp_suf_tail : forall c r x, exvp_suf (c :: r) x -> exvp_suf r x.
Proof.
  intros c r x H. apply (exvp_suf_trans r (c :: r) x); [|exact H]. exists 1%nat. reflexivity.
Qed.

Lemma exvp_suf_app : forall (a r : list Z), exvp_suf r (a ++ r).
Proof. intros a r. exists (length a). induction a as [|c a IH]; [reflexivity|exact IH]. Qed.

Lemma exvp_suf_skip : forall x, exvp_suf (skip x) x.
Proof.
  induction x as [|b x IH]; [apply exvp_suf_refl|]. cbn [skip].
  destruct (ws b); [apply exvp_suf_cons; exact IH|apply exvp_suf_refl].
Qed.

Lemma exvp_suf_len : forall r x, exvp_suf r x -> (length r <= length x)%nat.
Proof. intros r x [k ->]. rewrite length_skipn. lia. Qed.

(* the name read leaves a suffix (plain ex_name_suf) *)
Lemma exvp_name_suf : forall o y nm y1, exv_name o y = Some (nm, y1) -> exvp_suf y1 y.
Proof.
  intros [|] y nm y1; unfold exv_name; cbv beta iota.
  - destruct (skip y) as [|b z] eqn:Ey; cbv beta iota; [intro H; discriminate H|].
    destruct (b =? 34); cbv beta iota; [|intro H; discriminate H].
    rewrite exvp_run0_jr_string.
    destruct (decode z) as [[s r]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
    destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    destruct (c =? 58); cbv beta iota; [|intro H; discriminate H].
    intro H. injection H as _ <-.
    destruct (decode_stop z s r Ed) as (q & _ & Hr & _).
    apply (exvp_suf_trans _ r y).
    { apply (exvp_suf_tail c). rewrite <- Er. apply exvp_suf_skip. }
    apply (exvp_suf_trans r z y).
    { rewrite Hr. apply exvp_suf_skipn. }
    apply (exvp_suf_trans z (b :: z) y); [apply exvp_suf_cons, exvp_suf_refl|rewrite <- Ey; apply exvp_suf_skip].
  - intro H. injection H as _ <-. apply exvp_suf_refl.
Qed.

Lemma exvp_suf_cont : forall f d o b y v r,
  (forall d o n cap acc y v r, exv_run0 (jrl sm f d o n cap acc y) = Some (v, r) -> exvp_suf r y) ->
  exv_run0 (jr_cont (jrl sm f) d o (b :: y)) = Some (v, r) -> exvp_suf r (b :: y).
Proof.
  intros f d o b y v r IH. unfold jr_cont.
  destruct (Nat.ltb MAXD (S d)); cbv beta iota zeta; [intro H; discriminate H|].
  cbn [tl]. intro H. apply exvp_suf_cons. revert H.
  destruct (skip y) as [|c r0] eqn:Ey; cbv beta iota.
  - intro H. pose proof (exvp_suf_skip y) as Sy. rewrite Ey in Sy.
    exact (exvp_suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
  - pose proof (exvp_suf_skip y) as Sy. rewrite Ey in Sy.
    destruct (c =? closer o); cbv beta iota; intro H.
    + rewrite exvp_run0_ret in H. injection H as _ <-. exact (exvp_suf_tail c _ y Sy).
    + exact (exvp_suf_trans _ _ _ (IH _ _ _ _ _ _ _ _ H) Sy).
Qed.

Lemma exvp_suf_lit : forall w u x v r, exv_run0 (lit w u x) = Some (v, r) -> exvp_suf r x.
Proof.
  intros w u x v r. unfold lit.
  destruct (prefixb w x); intro H; [|discriminate H].
  rewrite exvp_run0_ret in H. injection H as _ <-. apply exvp_suf_skipn.
Qed.

Lemma exvp_suf_number : forall x v r, exv_run0 (jr_number sm x) = Some (v, r) -> exvp_suf r x.
Proof.
  intros x v r. unfold jr_number. cbv beta iota zeta.
  match goal with |- context [skipn ?j x] => set (J := j) end.
  destruct (skipn J x) as [|c z] eqn:Ez; cbv beta iota; [intro H; discriminate H|].
  pose proof (exvp_suf_skipn J x) as SJ. rewrite Ez in SJ.
  destruct (negb (digit c)); cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c =? 48) && ?m then _ else _] => destruct ((c =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  destruct (span numch z) as [a r0] eqn:Es; cbv beta iota zeta.
  rewrite exvp_run0_alloc.
  match goal with |- context [whole _ ?t] => destruct (whole sm t) end;
    cbv beta iota; intro H; [|discriminate H].
  rewrite exvp_run0_ret in H. injection H as _ <-.
  apply (exvp_suf_trans _ z x); [|exact (exvp_suf_tail c z x SJ)].
  rewrite (span_app _ _ _ _ Es). apply exvp_suf_app.
Qed.

(* plain suf_fuel *)
Lemma exvp_suf_fuel : forall f,
  (forall d x v r, exv_run0 (jrv sm f d x) = Some (v, r) -> exvp_suf r x) /\
  (forall d o n cap acc y v r, exv_run0 (jrl sm f d o n cap acc y) = Some (v, r) -> exvp_suf r y).
Proof.
  induction f as [|f [IHv IHl]]; [split; intros; discriminate|].
  split.
  - intros d x v r. cbn [jrv].
    destruct (skip x) as [|b y] eqn:Ex; cbv beta iota; [intro H; discriminate H|].
    pose proof (exvp_suf_skip x) as Sx. rewrite Ex in Sx.
    intro H. apply (exvp_suf_trans r (b :: y) x); [|exact Sx]. revert H.
    destruct (b =? 123); cbv beta iota; [exact (exvp_suf_cont f d true b y v r IHl)|].
    destruct (b =? 91); cbv beta iota; [exact (exvp_suf_cont f d false b y v r IHl)|].
    destruct (b =? 34); cbv beta iota.
    + rewrite exvp_run0_bind by apply agrees_jr_string. rewrite exvp_run0_jr_string.
      destruct (decode y) as [[s r0]|] eqn:Ed; cbv beta iota; [|intro H; discriminate H].
      intro H. rewrite exvp_run0_ret in H. injection H as _ <-.
      destruct (decode_stop y s r0 Ed) as (q & _ & Hr & _).
      apply exvp_suf_cons. rewrite Hr. apply exvp_suf_skipn.
    + destruct (b =? 116); cbv beta iota; [intro H; exact (exvp_suf_lit _ _ _ _ _ H)|].
      destruct (b =? 102); cbv beta iota; [intro H; exact (exvp_suf_lit _ _ _ _ _ H)|].
      destruct (b =? 110); cbv beta iota; [intro H; exact (exvp_suf_lit _ _ _ _ _ H)|].
      intro H. exact (exvp_suf_number _ _ _ H).
  - intros d o n cap acc y v r. cbn [jrl].
    rewrite exvp_run0_bind by apply agrees_grow. rewrite exvp_run0_grow. cbv beta iota.
    rewrite exvp_run0_bind by apply agrees_jr_name. rewrite exvp_run0_jr_name.
    destruct (exv_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|intro H; discriminate H].
    pose proof (exvp_name_suf o y nm y1 En) as S1.
    rewrite exvp_run0_bind by apply (proj1 (agrees_fuel sm f)).
    destruct (exv_run0 (jrv sm f d y1)) as [[u r0]|] eqn:Ev; cbv beta iota; [|intro H; discriminate H].
    pose proof (IHv d y1 u r0 Ev) as S2.
    destruct (skip r0) as [|c r1] eqn:Er; cbv beta iota; [intro H; discriminate H|].
    pose proof (exvp_suf_skip r0) as S3. rewrite Er in S3.
    assert (S4 : exvp_suf r1 y).
    { apply (exvp_suf_trans r1 r0 y); [exact (exvp_suf_tail c r1 r0 S3)|exact (exvp_suf_trans r0 y1 y S2 S1)]. }
    destruct (c =? 44); cbv beta iota.
    + intro H. exact (exvp_suf_trans _ _ _ (IHl _ _ _ _ _ _ _ _ H) S4).
    + destruct (c =? closer o); cbv beta iota; intro H; [|discriminate H].
      rewrite exvp_run0_ret in H. injection H as _ <-. exact S4.
Qed.

(* a value read is strictly shorter (plain ex_V_len, by PjGrammar.jr_value_rest) *)
Lemma exvp_V_len : forall d y u r, PRH_FnEx.prhex_V d y = Some (u, r) -> (length r < length y)%nat.
Proof.
  intros d y u r. unfold PRH_FnEx.prhex_V.
  destruct (jr_value sm (Z.to_nat d) y []) as [[res tr] ok'] eqn:E. cbn [fst]. intro H. subst res.
  exact (jr_value_rest sm _ _ _ _ _ _ _ E).
Qed.

(* ---- the six PURE_* facts ---- *)

(* plain ex_L_step *)
Lemma exvl_L_step : PURE_L_STEP.
Proof.
  unfold PURE_L_STEP. intros dn o n cap acc y.
  unfold exv_L at 1.
  replace (2 * length y + 2)%nat with (S (2 * length y + 1)) by lia.
  cbn [jrl].
  rewrite exvp_run0_bind by apply agrees_grow. rewrite exvp_run0_grow. cbv beta iota.
  rewrite exvp_run0_bind by apply agrees_jr_name. rewrite exvp_run0_jr_name.
  destruct (exv_name o y) as [[nm y1]|] eqn:En; cbv beta iota; [|reflexivity].
  pose proof (exvp_suf_len _ _ (exvp_name_suf o y nm y1 En)) as L1.
  rewrite exvp_run0_bind by apply (proj1 (agrees_fuel sm _)).
  assert (EV : exv_run0 (jrv sm (2 * length y + 1) dn y1) = PRH_FnEx.prhex_V (Z.of_nat dn) y1).
  { unfold PRH_FnEx.prhex_V. rewrite Nat2Z.id. unfold exv_run0.
    rewrite (jr_value_fuel sm (2 * length y + 1) dn y1 []) by lia. reflexivity. }
  rewrite EV.
  destruct (PRH_FnEx.prhex_V (Z.of_nat dn) y1) as [[u r]|] eqn:Ev; cbv beta iota; [|reflexivity].
  pose proof (exvp_V_len _ _ _ _ Ev) as L2.
  destruct (skip r) as [|c r1] eqn:Er; cbv beta iota; [reflexivity|].
  pose proof (skip_len r) as L3. rewrite Er in L3. cbn [length] in L3.
  destruct (c =? 44); cbv beta iota; [|destruct (c =? closer o); reflexivity].
  unfold exv_L, exv_run0.
  rewrite (proj2 (fuel_mono sm (2 * length r1 + 2)) dn o (S n) (exv_cap n cap) ((nm, u) :: acc) r1
    (2 * length y + 1)%nat []) by lia.
  reflexivity.
Qed.

(* plain ex_V_rest *)
Lemma exvl_V_rest : PURE_V_REST.
Proof.
  unfold PURE_V_REST. intros d y u r H. split; [exact (exvp_V_len d y u r H)|].
  change (exv_run0 (jrv sm (S (2 * length y)) (Z.to_nat d) y) = Some (u, r)) in H.
  exact (proj1 (exvp_suf_fuel _) _ _ _ _ H).
Qed.

Lemma exvl_name_rest : PURE_NAME_REST.
Proof.
  unfold PURE_NAME_REST. intros o y nm y1 H. split; [exact (exvp_name_suf o y nm y1 H)|].
  intros ->. unfold exv_name in H. cbv beta iota in H. injection H as <- <-. split; reflexivity.
Qed.

Lemma exvl_suffix : PURE_SUFFIX.
Proof.
  unfold PURE_SUFFIX. intros x r k ->. rewrite length_skipn.
  destruct (Nat.le_gt_cases k (length x)) as [Hk|Hk].
  - replace (length x - (length x - k))%nat with k by lia. reflexivity.
  - assert (E : skipn k x = []) by (apply skipn_all2; lia). rewrite E.
    apply skipn_all2. lia.
Qed.

(* ---- the prefix bookkeeping ---- *)
Lemma exvp_firstn_S : forall (A : Type) (l : list A) (n : nat) (d : A), (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  intros A l. induction l as [|a l IH]; intros [|n] d H; cbn [length] in H; try lia.
  - reflexivity.
  - cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma exvl_pref_cons : PURE_PREF_CONS.
Proof.
  unfold PURE_PREF_CONS. intros o t acc nm u Hlt _.
  destruct o; destruct t as [| | |txt bits|s|its|ms];
    cbv beta iota delta [exv_pref exv_same exv_count] in *; try tauto.
  - (* object *)
    cbn [length rev].
    rewrite (exvp_firstn_S _ ms (length acc) ([], JNull) Hlt).
    split.
    + intros [_ E]. apply app_inj_tail in E. destruct E as [E1 E2].
      split; [split; [lia|exact E1]|exact E2].
    + intros [[_ E1] E2]. split; [lia|]. rewrite E1, E2. reflexivity.
  - (* array *)
    cbn [length rev]. rewrite map_app. cbn [map snd].
    rewrite (exvp_firstn_S _ its (length acc) JNull Hlt).
    split.
    + intros [_ E]. apply app_inj_tail in E. destruct E as [E1 E2].
      split; [split; [lia|exact E1]|exact E2].
    + intros [[_ E1] E2]. split; [lia|]. rewrite E1, E2. reflexivity.
Qed.

Lemma exvl_pref_long : PURE_PREF_LONG.
Proof.
  unfold PURE_PREF_LONG. intros o t acc nm u Hle.
  destruct o; destruct t as [| | |txt bits|s|its|ms];
    cbv beta iota delta [exv_pref exv_count] in *; intros H; try contradiction;
    destruct H as [H _]; cbn [length] in H; lia.
Qed.

Print Assumptions exvl_L_step.
Print Assumptions exvl_V_rest.
Print Assumptions exvl_name_rest.
Print Assumptions exvl_suffix.
Print Assumptions exvl_pref_cons.
Print Assumptions exvl_pref_long.
