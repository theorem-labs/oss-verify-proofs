From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT TrNames RelayModel HarnessRep
  ListRep CheckRep ListTr relay_add_b_c.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint find_key (x : list Z) (ks : list (list Z)) : option nat :=
  match ks with
  | [] => None
  | k :: ks' => if list_eqb x k then Some O else option_map S (find_key x ks')
  end.

Definition gesture_model_tr (s : shl) (ln : list Z) : list tev :=
  match gesture ln with
  | Some (GBegin, x) => if existsb (list_eqb x) (sh_keys s) then [] else list_push_tr s x
  | Some (GEnd, x) => match find_key x (sh_keys s) with Some i => list_drop_tr s i | None => [] end
  | None => []
  end.

Definition gesture_model_sh (j : nat) (s : shl) (ln : list Z) : shl :=
  match gesture ln with
  | Some (GBegin, x) => if existsb (list_eqb x) (sh_keys s) then s else list_push_sh j s x
  | Some (GEnd, x) => match find_key x (sh_keys s) with Some i => list_drop_sh s i | None => s end
  | None => s
  end.

Fixpoint check_no_loss_tr (j : nat) (s : shl) (rs : list (tad * list Z)) : list tev :=
  match rs with
  | [] => []
  | r :: rs' =>
      gesture_model_tr s (snd r) ++ rec_drop_tr r ++
      check_no_loss_tr (j + nret sptr (gesture_model_tr s (snd r))) (gesture_model_sh j s (snd r)) rs'
  end.

Fixpoint check_no_loss_sh (j : nat) (s : shl) (rs : list (tad * list Z)) : shl :=
  match rs with
  | [] => s
  | r :: rs' => check_no_loss_sh (j + nret sptr (gesture_model_tr s (snd r))) (gesture_model_sh j s (snd r)) rs'
  end.

Definition hlist_free_tr (nm : Z -> tad) (l : hlist) : list tev := list_free_tr (sh_of nm l).

Definition check_shape_ends_tr (nm : Z -> tad) (gone : Z) (P : list byte) (rs : list (Z * list byte)) (d : list byte)
    : list tev :=
  if gone =? 0 then
    match ends_run P rs d (want_of P rs) with Some (_, ds, _) => recs_drop_tr (map (shr nm) ds) | None => [] end
  else recs_drop_tr (map (shr nm) (List.rev (filter (fun r => prefixb P (snd r)) rs))).

Definition source_reset_tr (nm : Z -> tad) (h : hsrc) : list tev :=
  hlist_free_tr nm (hs_pending h) ++ hlist_free_tr nm (hs_expected h) ++ hlist_free_tr nm (hs_held h) ++
  [RFree 6000 (nm (hs_partial h))].

Definition op_add_tr (i : option nat) (FD N C : Z) (g : tad) : list tev :=
  match i with Some _ => RMalloc 6000 :: relay_add_tr FD N C g | None => [] end.

Lemma find_key_lt : forall x ks i, find_key x ks = Some i -> (i < length ks)%nat.
Proof.
  intros x ks. induction ks as [|k ks IH]; intros i H; simpl in H; [discriminate|].
  destruct (list_eqb x k); [injection H as <-; simpl; lia|].
  destruct (find_key x ks) as [i'|] eqn:E; [|discriminate]. simpl in H. injection H as <-.
  specialize (IH i' eq_refl). simpl. lia.
Qed.

Lemma length_sh_keys : forall s, length (sh_keys s) = length (sh_recs s).
Proof. intros s. unfold sh_keys. apply length_map. Qed.

Lemma nret_gesture_model : forall s ln,
    nret sptr (gesture_model_tr s ln) =
    match gesture ln with
    | Some (GBegin, x) => if existsb (list_eqb x) (sh_keys s) then 0%nat else (if Z.eqb (sh_n s) (sh_cap s) then 2 else 1)%nat
    | _ => 0%nat
    end.
Proof.
  intros s ln. unfold gesture_model_tr. destruct (gesture ln) as [[[|] x]|]; [| |reflexivity].
  - destruct (existsb (list_eqb x) (sh_keys s)); [reflexivity | apply nret_list_push].
  - destruct (find_key x (sh_keys s)); reflexivity.
Qed.

Section Rel.
Variables (qs1 qs2 : list sptr).

Lemma gesture_model_rel : forall s1 s2 ln, sh_rel qs1 qs2 s1 s2 ->
    tr_rel sptr pdefT qs1 qs2 (gesture_model_tr s1 ln) (gesture_model_tr s2 ln).
Proof.
  intros s1 s2 ln H. pose proof (sh_rel_keys _ _ _ _ H) as Ek. unfold gesture_model_tr. rewrite Ek.
  destruct (gesture ln) as [[[|] x]|]; [| |constructor].
  - destruct (existsb (list_eqb x) (sh_keys s2)); [constructor | apply list_push_rel, H].
  - destruct (find_key x (sh_keys s2)) as [i|] eqn:Ei; [|constructor].
    apply list_drop_rel; [exact H|]. apply find_key_lt in Ei. rewrite <- Ek, length_sh_keys in Ei. exact Ei.
Qed.

End Rel.

Lemma gesture_model_sh_rel : forall qs1 qs2 s1 s2 ln j1 j2,
    sh_rel qs1 qs2 s1 s2 -> ret_agree sptr pdefT qs1 qs2 j1 j2 (nret sptr (gesture_model_tr s2 ln)) ->
    sh_rel qs1 qs2 (gesture_model_sh j1 s1 ln) (gesture_model_sh j2 s2 ln).
Proof.
  intros qs1 qs2 s1 s2 ln j1 j2 H Hr. rewrite nret_gesture_model in Hr.
  pose proof (sh_rel_keys _ _ _ _ H) as Ek. unfold gesture_model_sh. rewrite Ek.
  destruct (gesture ln) as [[[|] x]|]; [| |exact H].
  - destruct (existsb (list_eqb x) (sh_keys s2)); [exact H|]. apply list_push_sh_rel; assumption.
  - destruct (find_key x (sh_keys s2)); [apply list_drop_sh_rel, H | exact H].
Qed.
