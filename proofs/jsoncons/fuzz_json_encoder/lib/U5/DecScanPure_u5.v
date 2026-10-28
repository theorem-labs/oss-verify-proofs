(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PDS.
Definition expo (l : list Z) : Z :=
  match l with
  | c :: r' => if (c =? 101) || (c =? 69) then match PD.exp_scan r' with Some k => 1 + k | None => 0 end else 0
  | [] => 0
  end.
Fixpoint contD (g : bool) (l : list Z) : Z :=
  match l with
  | c :: r => if PD.is_dig c then 1 + contD g r
              else if (c =? 46) && negb g then 1 + contD true r
              else expo (c :: r)
  | [] => 0
  end.

(* [comment removed for export] *)
Lemma contD_dig : forall g c l, PD.is_dig c = true -> contD g (c :: l) = 1 + contD g l.
Proof. intros g c l H. cbn [contD]. rewrite H. reflexivity. Qed.
Lemma contD_dot : forall l, contD false (46 :: l) = 1 + contD true l.
Proof. intros l. reflexivity. Qed.
Lemma contD_stop_dot : forall l, contD true (46 :: l) = 0.
Proof. intros l. reflexivity. Qed.
Lemma contD_nodig : forall g c l, PD.is_dig c = false -> c <> 46 -> contD g (c :: l) = expo (c :: l).
Proof. intros g c l H1 H2. cbn [contD]. rewrite H1. apply Z.eqb_neq in H2. rewrite H2. reflexivity. Qed.
Lemma contD_stop : forall g c l, PD.is_dig c = false -> c <> 46 -> c <> 69 -> c <> 101 -> contD g (c :: l) = 0.
Proof.
  intros g c l H1 H2 H3 H4. rewrite contD_nodig by assumption. cbn [expo].
  apply Z.eqb_neq in H3, H4. rewrite H3, H4. reflexivity.
Qed.
Lemma contD_exp : forall g c l, c = 69 \/ c = 101 -> contD g (c :: l) = match PD.exp_scan l with Some k => 1 + k | None => 0 end.
Proof.
  intros g c l H. rewrite contD_nodig; [| destruct H as [-> | ->]; reflexivity | destruct H as [-> | ->]; discriminate].
  cbn [expo]. destruct H as [-> | ->]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma span_app0 : forall p l, p 0 = false -> PD.span p (l ++ [0]) = (fst (PD.span p l), snd (PD.span p l) ++ [0]).
Proof.
  intros p l Hp. induction l as [|c r IH]; cbn [app PD.span].
  - rewrite Hp. reflexivity.
  - destruct (p c); [|reflexivity]. rewrite IH. destruct (PD.span p r) as [n r']. reflexivity.
Qed.
Lemma exp_scan_app0 : forall l, PD.exp_scan (l ++ [0]) = PD.exp_scan l.
Proof.
  intros l. unfold PD.exp_scan.
  assert (G : forall r, (let '(n, _) := PD.span PD.is_dig (r ++ [0]) in if n =? 0 then None else Some n) = (let '(n, _) := PD.span PD.is_dig r in if n =? 0 then None else Some n) /\
                        forall sg, (let '(n, _) := PD.span PD.is_dig (r ++ [0]) in if n =? 0 then None else Some (sg + n)) = (let '(n, _) := PD.span PD.is_dig r in if n =? 0 then None else Some (sg + n))).
  { intros r. rewrite (span_app0 PD.is_dig r eq_refl). destruct (PD.span PD.is_dig r) as [n r']. cbn [fst snd]. split; [reflexivity | intros; reflexivity]. }
  destruct l as [|c r]; cbn [app].
  - reflexivity.
  - destruct ((c =? 43) || (c =? 45)).
    + exact (proj2 (G r) 1).
    + change (c :: r ++ [0]) with ((c :: r) ++ [0]). exact (proj2 (G (c :: r)) 0).
Qed.
Lemma expo_app0 : forall l, expo (l ++ [0]) = expo l.
Proof.
  intros [|c r]; cbn [app expo]; [reflexivity|]. rewrite exp_scan_app0. reflexivity.
Qed.
Lemma contD_app0 : forall l g, contD g (l ++ [0]) = contD g l.
Proof.
  induction l as [|c r IH]; intros g; [reflexivity|].
  change ((c :: r) ++ [0]) with (c :: (r ++ [0])). cbn [contD].
  rewrite !IH. change (c :: r ++ [0]) with ((c :: r) ++ [0]). rewrite expo_app0. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma contD_dig_loop : forall l g, contD g l = (let '(n, _, r) := PD.dig_loop g l in n + expo r).
Proof.
  induction l as [|c r IH]; intros g; [reflexivity|].
  cbn [contD PD.dig_loop]. destruct (PD.is_dig c) eqn:Hd.
  - rewrite IH. destruct (PD.dig_loop g r) as [[n d] r']. lia.
  - destruct ((c =? 46) && negb g) eqn:Hp.
    + rewrite IH. destruct (PD.dig_loop true r) as [[n d] r']. lia.
    + reflexivity.
Qed.
Lemma contD_zeros : forall l g, contD g l = (let '(n, r) := PD.span (fun c => c =? 48) l in n + contD g r).
Proof.
  induction l as [|c r IH]; intros g; [reflexivity|].
  cbn [PD.span]. destruct (c =? 48) eqn:Hc.
  - apply Z.eqb_eq in Hc. subst c. rewrite contD_dig by reflexivity. rewrite IH. destruct (PD.span (fun c => c =? 48) r) as [n r']. lia.
  - lia.
Qed.
Lemma dig_loop_dig : forall g c r, PD.is_dig c = true -> snd (fst (PD.dig_loop g (c :: r))) = true.
Proof. intros g c r H. cbn [PD.dig_loop]. rewrite H. destruct (PD.dig_loop g r) as [[n d] r']. reflexivity. Qed.
Lemma span_pos : forall p l, 0 <= fst (PD.span p l).
Proof. intros p l. induction l as [|c r IH]; cbn [PD.span]; [cbn; lia|]. destruct (p c); [|cbn; lia]. destruct (PD.span p r) as [n r']. cbn [fst] in *. lia. Qed.

Ltac fin r3 := unfold expo; destruct r3 as [|? ?]; cbn [andb]; [lia|]; match goal with |- context [(?c =? 101) || (?c =? 69)] => destruct ((c =? 101) || (c =? 69)) end; [match goal with |- context [PD.exp_scan ?r] => destruct (PD.exp_scan r) end|]; lia.
(* [comment removed for export] *)
Theorem dec_len_contD : forall c r, PD.is_dig c = true -> PD.dec_len (c :: r) = contD false (c :: r).
Proof.
  intros c r Hd. destruct (Z.eq_dec c 48) as [-> | Hne].
  - (* [comment removed for export] *)
    rewrite (contD_zeros (48 :: r) false). unfold PD.dec_len.
    pose proof (span_pos (fun c => c =? 48) r) as Hpos.
    cbn [PD.span]. change (48 =? 48) with true. cbv iota.
    destruct (PD.span (fun c => c =? 48) r) as [n1 r1]. cbn [fst] in Hpos.
    assert (Hn1 : (0 <? n1 + 1) = true) by (apply Z.ltb_lt; lia). rewrite Hn1. cbn [orb].
    destruct r1 as [|c1 r1'].
    + cbn. lia.
    + destruct (Z.eq_dec c1 46) as [-> | Hc1].
      * rewrite contD_dot. rewrite (contD_zeros r1' true).
        destruct (PD.span (fun c => c =? 48) r1') as [n2 r2]. rewrite (contD_dig_loop r2 true).
        destruct (PD.dig_loop true r2) as [[n3 d3] r3]. fin r3.
      * assert (E : match c1 with 46 => false | _ => true end = true -> True) by trivial.
        rewrite (contD_dig_loop (c1 :: r1') false).
        replace (match c1 :: r1' with
                 | 46 :: r' => let '(n2, r2) := PD.span (fun c : Z => c =? 48) r' in (1, true, n2, r2)
                 | _ => (0, false, 0, c1 :: r1')
                 end) with (0, false, 0, c1 :: r1').
        2:{ destruct c1 as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). exfalso; apply Hc1; reflexivity. }
        destruct (PD.dig_loop false (c1 :: r1')) as [[n3 d3] r3]. fin r3.
  - (* [comment removed for export] *)
    unfold PD.dec_len. cbn [PD.span]. apply Z.eqb_neq in Hne. rewrite Hne.
    assert (H46 : c <> 46) by (intros ->; discriminate).
    replace (match c :: r with
             | 46 :: r' => let '(n2, r2) := PD.span (fun c : Z => c =? 48) r' in (1, true, n2, r2)
             | _ => (0, false, 0, c :: r)
             end) with (0, false, 0, c :: r).
    2:{ destruct c as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). exfalso; apply H46; reflexivity. }
    rewrite (contD_dig_loop (c :: r) false). pose proof (dig_loop_dig false c r Hd) as Hd3.
    destruct (PD.dig_loop false (c :: r)) as [[n3 d3] r3]. cbn [fst snd] in Hd3. subst d3.
    change (0 <? 0) with false. cbn [orb]. fin r3.
Qed.

(* [comment removed for export] *)
Corollary dec_len_contD0 : forall c r, PD.is_dig c = true -> PD.dec_len (c :: r) = contD false ((c :: r) ++ [0]).
Proof. intros c r H. rewrite contD_app0. apply dec_len_contD. exact H. Qed.

(* [comment removed for export] *)
Lemma skipn_nth : forall (l : list Z) (n : nat) d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
  induction l as [|c r IH]; intros n d H; [cbn in H; lia|].
  destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.
End PDS.
