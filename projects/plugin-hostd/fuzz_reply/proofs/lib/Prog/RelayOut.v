From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
Open Scope Z_scope.

Record ctl := Ctl { c_client : Z; c_broken : bool; c_eintr : bool; c_dead : bool }.

Inductive mode := OFF | LIVE | DYING.

Definition mode_of (c : ctl) : mode :=
  if (c_client c <? 0) || c_broken c then OFF else if c_dead c then DYING else LIVE.

Definition send (c : ctl) (O : list Z) (B : list Z) : ctl * list Z :=
  match B with
  | [] => (c, O)
  | _ :: _ =>
      match mode_of c with
      | OFF => (c, O)
      | LIVE => (Ctl (c_client c) (c_broken c) false (c_dead c), O ++ B)
      | DYING => (Ctl (c_client c) true false (c_dead c), O)
      end
  end.

Fixpoint sends (c : ctl) (O : list Z) (Bs : list (list Z)) : ctl * list Z :=
  match Bs with
  | [] => (c, O)
  | B :: Bs' => let (c1, O1) := send c O B in sends c1 O1 Bs'
  end.

Lemma sends_app : forall Bs1 Bs2 c O,
  sends c O (Bs1 ++ Bs2) = let (c1, O1) := sends c O Bs1 in sends c1 O1 Bs2.
Proof.
  induction Bs1 as [|B Bs1 IH]; intros Bs2 c O; cbn [app sends]; [reflexivity|].
  destruct (send c O B) as [c1 O1]. apply IH.
Qed.

Lemma send_off : forall c O B, mode_of c = OFF -> send c O B = (c, O).
Proof. intros c O B H. unfold send. destruct B; [reflexivity|]. rewrite H. reflexivity. Qed.

Lemma sends_off : forall Bs c O, mode_of c = OFF -> sends c O Bs = (c, O).
Proof.
  induction Bs as [|B Bs IH]; intros c O H; cbn [sends]; [reflexivity|].
  rewrite (send_off c O B H). apply IH. exact H.
Qed.

Lemma mode_live_eintr : forall c e, mode_of c = LIVE ->
  mode_of (Ctl (c_client c) (c_broken c) e (c_dead c)) = LIVE.
Proof. intros [cl br ei de] e H. unfold mode_of in *. cbn in *. exact H. Qed.

Theorem sends_live : forall Bs c O, mode_of c = LIVE ->
  exists e, sends c O Bs = (Ctl (c_client c) (c_broken c) e (c_dead c), O ++ concat Bs)
            /\ (e = c_eintr c \/ e = false)
            /\ (Exists (fun B => B <> []) Bs -> e = false).
Proof.
  induction Bs as [|B Bs IH]; intros c O H.
  - exists (c_eintr c). cbn. rewrite app_nil_r. destruct c; cbn.
    split; [reflexivity|]. split; [left; reflexivity|]. intros Hx. inversion Hx.
  - cbn [sends concat]. unfold send at 1. destruct B as [|b B'].
    + destruct (IH c O H) as (e & He & He1 & He2). exists e.
      split; [exact He|]. split; [exact He1|].
      intros Hx. inversion Hx as [? ? Hn|? ? Hx']; subst; [congruence|exact (He2 Hx')].
    + rewrite H.
      pose proof (mode_live_eintr c false H) as H'.
      destruct (IH _ (O ++ b :: B') H') as (e & He & He1 & He2). cbn in He, He1, He2.
      exists e. rewrite He, app_assoc.
      split; [destruct c; reflexivity|]. split; [right; destruct He1; [exact H0|exact H0]|].
      intros _. destruct He1; assumption.
Qed.

Theorem sends_dying : forall Bs c O, mode_of c = DYING ->
  exists c', sends c O Bs = (c', O) /\ c_client c' = c_client c /\ c_dead c' = c_dead c
             /\ (c_broken c' = true <-> Exists (fun B => B <> []) Bs)
             /\ (Exists (fun B => B <> []) Bs \/ c' = c).
Proof.
  induction Bs as [|B Bs IH]; intros c O H.
  - exists c. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [|right; reflexivity].
    unfold mode_of in H. destruct ((c_client c <? 0) || c_broken c) eqn:E; [discriminate|].
    apply orb_false_iff in E. destruct E as [_ E]. rewrite E.
    split; [discriminate|intros Hx; inversion Hx].
  - cbn [sends]. unfold send at 1. destruct B as [|b B'].
    + destruct (IH c O H) as (c' & Hs & H1 & H2 & H3 & H4). exists c'.
      split; [exact Hs|]. split; [exact H1|]. split; [exact H2|]. split.
      * rewrite H3. split; intros Hx; [right; exact Hx|].
        inversion Hx as [? ? Hn|? ? Hx']; subst; [congruence|exact Hx'].
      * destruct H4 as [H4|H4]; [left; right; exact H4|right; exact H4].
    + rewrite H.
      set (c1 := Ctl (c_client c) true false (c_dead c)).
      assert (Hoff : mode_of c1 = OFF) by (unfold mode_of, c1; cbn; rewrite orb_true_r; reflexivity).
      rewrite (sends_off Bs c1 O Hoff). exists c1.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      * split; intros _; [left; discriminate|reflexivity].
      * left. left. discriminate.
Qed.

Definition with_nuls (ls : list (list Z)) : list (list Z) := map (fun l => l ++ [0]) ls.

Lemma with_nuls_nonempty : forall ls, ls <> [] -> Exists (fun B => B <> []) (with_nuls ls).
Proof.
  intros [|l ls] H; [congruence|]. cbn. left. destruct l; discriminate.
Qed.
