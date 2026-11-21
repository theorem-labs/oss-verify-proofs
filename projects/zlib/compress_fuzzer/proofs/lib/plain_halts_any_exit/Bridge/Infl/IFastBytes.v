(** * Bridge.Infl.IFastBytes — pair I16, an RT-only fact: [inflate_fast] writes bytes.

    Every byte RT's [inflate_fast] puts in the output is a literal ([u8]) or a copy out of
    the window or the output itself, so if both hold bytes on entry, the output still does
    on every exit ([fast_loop_bytes]).  [IInv.icore] carries "RT's output holds bytes" for
    CHECK's Adler-32 fold; [IFast] uses this file to keep it across the fast path. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module RIF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.InflateFast.

Definition bbody (r : RIF.IfBody) : Prop :=
  match r with
  | RIF.BodyOk s' | RIF.BodyEob s' | RIF.BodyBad s' _ => zbytes (RIF.f_buf s')
  | RIF.BodyFuel => True
  end.

Definition bstep (r : RIF.IfStep) : Prop :=
  match r with
  | RIF.IfCont s' | RIF.IfStop s' | RIF.IfEob s' | RIF.IfBad s' _ => zbytes (RIF.f_buf s')
  | RIF.IfFuel => True
  end.

Lemma u8_byte_f : forall v, 0 <= RBa.u8 v < 256.
Proof. intros v. unfold RBa.u8. apply Z.mod_pos_bound. lia. Qed.

Section Bytes.
  Variable c : RIF.IfCtx.
  Hypothesis Hw : zbytes (RIF.f_window c).

  Lemma b_put : forall v s, 0 <= v < 256 -> zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf (RIF.if_put v s)).
  Proof. intros v s Hv Hs. unfold RIF.if_put. cbn [RIF.f_buf]. apply zbytes_zset; assumption. Qed.

  Lemma b_read : forall s r, zbytes (RIF.f_buf s) -> 0 <= RIF.if_read c s r < 256.
  Proof. intros s [i|i] Hs; cbn [RIF.if_read]; [apply Hw | apply Hs]. Qed.

  Lemma b_copyn : forall n s r s1 r1, RIF.if_copyn n c s r = (s1, r1) ->
    zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf s1).
  Proof.
    induction n as [|n IH]; intros s r s1 r1 E Hs; cbn [RIF.if_copyn] in E.
    - injection E as <- _. exact Hs.
    - apply (IH _ _ _ _ E). apply b_put; [apply b_read; exact Hs | exact Hs].
  Qed.

  Lemma b_copy3w : forall f s r len s' r' l, RIF.if_copy3w f c s r len = Some (s', r', l) ->
    zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf s').
  Proof.
    induction f as [|f IH]; intros s r len s' r' l E Hs; cbn [RIF.if_copy3w] in E; [discriminate E|].
    destruct (2 <? len); [|injection E as <- _ _; exact Hs].
    destruct (RIF.if_copyn 3 c s r) as [s1 r1] eqn:E1.
    exact (IH _ _ _ _ _ _ E (b_copyn _ _ _ _ _ E1 Hs)).
  Qed.

  Lemma b_copytail : forall s r len, zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf (RIF.if_copytail c s r len)).
  Proof.
    intros s r len Hs. unfold RIF.if_copytail.
    destruct (len =? 0); [exact Hs|].
    destruct (RIF.if_copyn 1 c s r) as [s1 r1] eqn:E1.
    pose proof (b_copyn _ _ _ _ _ E1 Hs) as H1.
    destruct (1 <? len); [|exact H1].
    destruct (RIF.if_copyn 1 c s1 r1) as [s2 r2] eqn:E2. cbn [fst]. exact (b_copyn _ _ _ _ _ E2 H1).
  Qed.

  Lemma b_copydirect : forall s r len s', RIF.if_copydirect c s r len = Some s' ->
    zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf s').
  Proof.
    intros s r len s' E Hs. unfold RIF.if_copydirect in E.
    destruct (RIF.if_copyn 3 c s r) as [s1 r1] eqn:E1.
    destruct (RIF.if_copy3w RIF.copy_fuel c s1 r1 (RBa.u32 (len - 3))) as [[[s2 r2] l2]|] eqn:E2;
      [|discriminate E].
    injection E as <-. apply b_copytail. exact (b_copy3w _ _ _ _ _ _ _ E2 (b_copyn _ _ _ _ _ E1 Hs)).
  Qed.

  Ltac chain_copyn :=
    repeat match goal with
    | Ec : RIF.if_copyn _ c ?x _ = (?y, _), Hx : zbytes (RIF.f_buf ?x) |- _ =>
        pose proof (b_copyn _ _ _ _ _ Ec Hx); clear Ec
    end.

  Lemma b_winphase : forall s dist op len s' r' l, RIF.if_winphase c s dist op len = (s', r', l) ->
    zbytes (RIF.f_buf s) -> zbytes (RIF.f_buf s').
  Proof.
    intros s dist op len s' r' l E Hs. unfold RIF.if_winphase in E. cbv zeta in E.
    repeat first
      [ match type of E with context [match RIF.if_copyn ?n c ?x ?y with _ => _ end] =>
          let Ec := fresh "Ec" in destruct (RIF.if_copyn n c x y) as [? ?] eqn:Ec end
      | match type of E with context [if ?b then _ else _] => destruct b end ];
    injection E as <- _ _; chain_copyn; assumption.
  Qed.

  Lemma b_dodist : forall f len s h, zbytes (RIF.f_buf s) -> bbody (RIF.if_dodist f c len s h).
  Proof.
    induction f as [|f IH]; intros len s h Hs; cbn [RIF.if_dodist]; [exact I|]. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    repeat first
      [ match goal with |- context [match RIF.if_winphase ?c0 ?x ?d ?o ?l with _ => _ end] =>
          let E := fresh "Ew" in destruct (RIF.if_winphase c0 x d o l) as [[? ?] ?] eqn:E end
      | match goal with |- context [match RIF.if_copy3w ?f0 ?c0 ?x ?r ?l with _ => _ end] =>
          let E := fresh "E3" in destruct (RIF.if_copy3w f0 c0 x r l) as [[[? ?] ?]|] eqn:E end
      | match goal with |- context [match RIF.if_copydirect ?c0 ?x ?r ?l with _ => _ end] =>
          let E := fresh "Ed" in destruct (RIF.if_copydirect c0 x r l) as [?|] eqn:E end
      | match goal with |- context [if ?b then _ else _] => destruct b end ];
    cbn [bbody];
    first
      [ exact I
      | exact Hs
      | apply IH; exact Hs
      | (eapply b_copydirect; [eassumption | exact Hs])
      | (apply b_copytail; eapply b_copy3w; [eassumption|]; eapply b_winphase; [eassumption | exact Hs]) ].
  Qed.

  (** One exit of a [dolen] level.  The branches are tried by goal shape, so no unification
      ever reduces [if_dodist] at the literal fuel [tbl_fuel] (exponential). *)
  Ltac dl_close Hs IH :=
    match goal with
    | |- bbody (RIF.if_dodist _ _ _ _ _) =>
        apply b_dodist; unfold RIF.if_refill15;
        repeat match goal with |- context [if ?b then _ else _] => destruct b end; exact Hs
    | |- bbody (RIF.if_dolen _ _ _ _) => apply IH; exact Hs
    | |- bbody (RIF.BodyOk (RIF.if_put _ _)) => cbn [bbody]; apply b_put; [apply u8_byte_f | exact Hs]
    | |- bbody (RIF.BodyEob _) => cbn [bbody]; exact Hs
    | |- bbody (RIF.BodyBad _ _) => cbn [bbody]; exact Hs
    | |- bbody RIF.BodyFuel => exact I
    end.

  Lemma b_dolen : forall f s h, zbytes (RIF.f_buf s) -> bbody (RIF.if_dolen f c s h).
  Proof.
    induction f as [|f IH]; intros s h Hs; [exact I|].
    cbn [RIF.if_dolen]. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end.
    all: cbn beta iota.
    all: dl_close Hs IH.
  Qed.

  Lemma b_step : forall s, zbytes (RIF.f_buf s) -> bstep (RIF.if_step c s).
  Proof.
    intros s Hs. unfold RIF.if_step, RIF.if_body.
    generalize RIF.tbl_fuel as tf; intros tf.
    assert (H0 : zbytes (RIF.f_buf (RIF.if_refill15 c s))).
    { unfold RIF.if_refill15. destruct (_ <? _); exact Hs. }
    pose proof (b_dolen tf (RIF.if_refill15 c s)
                  (RIF.f_lcode c (Z.land (RIF.f_hold (RIF.if_refill15 c s)) (RIF.f_lmask c))) H0) as Hb.
    revert Hb.
    destruct (RIF.if_dolen tf c (RIF.if_refill15 c s)
                (RIF.f_lcode c (Z.land (RIF.f_hold (RIF.if_refill15 c s)) (RIF.f_lmask c))))
      as [s'|s'|s' m|]; cbn [bbody bstep]; intros Hb; try exact I; try exact Hb.
    destruct (RIF.if_guard c s'); exact Hb.
  Qed.

  Lemma b_loop : forall n s r, zbytes (RIF.f_buf s) -> RIF.if_loop n c s = Some r -> bstep r.
  Proof.
    (* step with [if_loop_S], never [cbn]: RT's own note, a [cbn] through the loop does not finish *)
    induction n as [|n IH]; intros s r Hs E; [discriminate E|].
    rewrite RIF.if_loop_S in E.
    pose proof (b_step s Hs) as Hb. revert Hb E.
    destruct (RIF.if_step c s) as [s'|s'|s'|s' m|]; cbn [bstep]; intros Hb E;
      try (injection E as <-; cbn [bstep]; exact Hb).
    exact (IH s' r Hb E).
  Qed.
End Bytes.

(** What [IFast] uses: the output after RT's fast loop holds bytes. *)
Lemma fast_loop_bytes : forall n c s r,
  zbytes (RIF.f_window c) -> zbytes (RIF.f_buf s) -> RIF.if_loop n c s = Some r -> bstep r.
Proof. intros n c s r Hw Hs E. exact (b_loop c Hw n s r Hs E). Qed.
