(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PDJ.
Definition is_dig (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition nl_step (k c : Z) : option Z :=
  if Z.eqb k (-1) then (if Z.eqb c 45 then Some 0 else if Z.eqb c 48 then Some 1 else if is_dig c then Some 2 else None)
  else if Z.eqb k 0 then (if Z.eqb c 48 then Some 1 else if is_dig c then Some 2 else None)
  else if Z.eqb k 1 then (if Z.eqb c 46 then Some 3 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else if is_dig c then Some 2 (* [comment removed for export] *) else None)
  else if Z.eqb k 2 then (if is_dig c then Some 2 else if Z.eqb c 46 then Some 3 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else None)
  else if Z.eqb k 3 then (if is_dig c then Some 4 else None)
  else if Z.eqb k 4 then (if is_dig c then Some 4 else if Z.eqb c 101 || Z.eqb c 69 then Some 5 else None)
  else if Z.eqb k 5 then (if Z.eqb c 45 || Z.eqb c 43 then Some 6 else if is_dig c then Some 7 else None)
  else if Z.eqb k 6 then (if is_dig c then Some 7 else None)
  else if Z.eqb k 7 then (if is_dig c then Some 7 else None)
  else None.
Fixpoint nl_run (k : Z) (s : list Z) : option Z :=
  match s with [] => Some k | c :: r => match nl_step k c with Some k' => nl_run k' r | None => None end end.
Definition num_final (s : list Z) : Prop := exists k, nl_run (-1) s = Some k /\ In k [1; 2; 4; 7].

Definition fin (k : Z) : Prop := In k [1; 2; 4; 7].
Definition len (l : list Z) : Z := Z.of_nat (length l).
Lemma len_cons : forall c l, len (c :: l) = 1 + len l. Proof. intros. unfold len. cbn [length]. lia. Qed.
Lemma is_dig_eq : forall c, PD.is_dig c = is_dig c. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition ne (r3 : list Z) : Z :=
  match r3 with
  | c :: r' => if (c =? 101) || (c =? 69) then match PD.exp_scan r' with Some k => 1 + k | None => 0 end else 0
  | [] => 0
  end.
Definition tail_ok (g : bool) (l : list Z) : Prop := let '(n, _, r3) := PD.dig_loop g l in n + ne r3 = len l.

Lemma span_digs : forall l, nl_run 7 l <> None -> PD.span PD.is_dig l = (len l, []).
Proof.
  induction l as [|c r IH]; intros H; [reflexivity|]. cbn [nl_run] in H. unfold nl_step in H. cbn in H. cbn [PD.span]. rewrite is_dig_eq.
  destruct (is_dig c) eqn:D; [|congruence]. rewrite (IH H). rewrite len_cons. f_equal. lia.
Qed.
Lemma run7 : forall l k, nl_run 7 l = Some k -> k = 7.
Proof. induction l as [|c r IH]; intros k H; cbn [nl_run] in H; [congruence|]. unfold nl_step in H. cbn in H. destruct (is_dig c); [exact (IH _ H) | discriminate]. Qed.
Lemma exp5 : forall l k, nl_run 5 l = Some k -> fin k -> PD.exp_scan l = Some (len l).
Proof.
  intros l k H F. destruct l as [|c r]; [cbn in H; injection H as <-; unfold fin in F; cbn in F; lia|].
  cbn [nl_run] in H. unfold nl_step in H. cbn in H. unfold PD.exp_scan.
  destruct ((c =? 45) || (c =? 43)) eqn:S.
  - (* [comment removed for export] *)
    assert (S' : (c =? 43) || (c =? 45) = true) by (rewrite orb_comm; exact S). rewrite S'.
    destruct r as [|d r']; [cbn in H; injection H as <-; unfold fin in F; cbn in F; lia|].
    cbn [nl_run] in H. unfold nl_step in H. cbn in H. destruct (is_dig d) eqn:D; [|discriminate].
    assert (N7 : nl_run 7 (d :: r') <> None) by (cbn [nl_run]; unfold nl_step; cbn; rewrite D; congruence).
    rewrite (span_digs _ N7). rewrite !len_cons. pose proof (Zle_0_nat (length r')). unfold len.
    destruct (Z.eqb_spec (1 + Z.of_nat (length r')) 0); [lia|]. f_equal; lia.
  - assert (S' : (c =? 43) || (c =? 45) = false) by (rewrite orb_comm; exact S). rewrite S'.
    destruct (is_dig c) eqn:D; [|discriminate].
    assert (N7 : nl_run 7 (c :: r) <> None) by (cbn [nl_run]; unfold nl_step; cbn; rewrite D; congruence).
    rewrite (span_digs _ N7). rewrite len_cons. pose proof (Zle_0_nat (length r)). unfold len.
    destruct (Z.eqb_spec (1 + Z.of_nat (length r)) 0); [lia|]. f_equal; lia.
Qed.
Lemma e_not_dig : forall c, (c =? 101) || (c =? 69) = true -> is_dig c = false /\ (c =? 46) = false.
Proof. intros c H. apply orb_prop in H as [H|H]; apply Z.eqb_eq in H; subst c; split; reflexivity. Qed.
(* [comment removed for export] *)
Lemma tail_e : forall g c r k, (c =? 101) || (c =? 69) = true -> nl_run 5 r = Some k -> fin k -> tail_ok g (c :: r).
Proof.
  intros g c r k E H F. destruct (e_not_dig c E) as [D P]. unfold tail_ok. cbn [PD.dig_loop]. rewrite is_dig_eq, D, P. cbn [andb].
  unfold ne. rewrite E, (exp5 r k H F). rewrite len_cons. lia.
Qed.
Lemma tail4 : forall l k, nl_run 4 l = Some k -> fin k -> tail_ok true l.
Proof.
  induction l as [|c r IH]; intros k H F; [reflexivity|]. cbn [nl_run] in H. unfold nl_step in H. cbn in H.
  destruct (is_dig c) eqn:D.
  - specialize (IH k H F). unfold tail_ok in *. cbn [PD.dig_loop]. rewrite is_dig_eq, D. destruct (PD.dig_loop true r) as [[n d] r3]. rewrite len_cons. lia.
  - destruct ((c =? 101) || (c =? 69)) eqn:E; [|discriminate]. exact (tail_e true c r k E H F).
Qed.
Lemma tail3 : forall l k, nl_run 3 l = Some k -> fin k -> tail_ok true l.
Proof.
  intros l k H F. destruct l as [|c r]; [cbn in H; injection H as <-; unfold fin in F; cbn in F; lia|].
  cbn [nl_run] in H. unfold nl_step in H. cbn in H. destruct (is_dig c) eqn:D; [|discriminate].
  pose proof (tail4 r k H F) as T. unfold tail_ok in *. cbn [PD.dig_loop]. rewrite is_dig_eq, D. destruct (PD.dig_loop true r) as [[n d] r3]. rewrite len_cons. lia.
Qed.
Lemma tail_dot : forall r k, nl_run 3 r = Some k -> fin k -> tail_ok false (46 :: r).
Proof.
  intros r k H F. pose proof (tail3 r k H F) as T. unfold tail_ok in *. cbn [PD.dig_loop]. change (PD.is_dig 46) with false. cbn [andb negb Z.eqb Pos.eqb].
  destruct (PD.dig_loop true r) as [[n d] r3]. rewrite len_cons. lia.
Qed.
Lemma tail2 : forall l k, nl_run 2 l = Some k -> fin k -> tail_ok false l.
Proof.
  induction l as [|c r IH]; intros k H F; [reflexivity|]. cbn [nl_run] in H. unfold nl_step in H. cbn in H.
  destruct (is_dig c) eqn:D.
  - specialize (IH k H F). unfold tail_ok in *. cbn [PD.dig_loop]. rewrite is_dig_eq, D. destruct (PD.dig_loop false r) as [[n d] r3]. rewrite len_cons. lia.
  - destruct (c =? 46) eqn:P; [apply Z.eqb_eq in P; subst c; exact (tail_dot r k H F)|].
    destruct ((c =? 101) || (c =? 69)) eqn:E; [|discriminate]. exact (tail_e false c r k E H F).
Qed.
Lemma tail1 : forall l k, nl_run 1 l = Some k -> fin k -> tail_ok false l.
Proof.
  intros l k H F. destruct l as [|c r]; [reflexivity|]. cbn [nl_run] in H. unfold nl_step in H. cbn in H.
  destruct (c =? 46) eqn:P; [apply Z.eqb_eq in P; subst c; exact (tail_dot r k H F)|].
  destruct ((c =? 101) || (c =? 69)) eqn:E; [exact (tail_e false c r k E H F)|].
  destruct (is_dig c) eqn:D; [|discriminate].
  pose proof (tail2 r k H F) as T. unfold tail_ok in *. cbn [PD.dig_loop]. rewrite is_dig_eq, D. destruct (PD.dig_loop false r) as [[n d] r3]. rewrite len_cons. lia.
Qed.

(* [comment removed for export] *)
Lemma dl_zeros : forall g s, let '(n1, r1) := PD.span (fun c => c =? 48) s in let '(n', d', r') := PD.dig_loop g r1 in
  PD.dig_loop g s = (n1 + n', (0 <? n1) || d', r') /\ 0 <= n1.
Proof.
  intros g. induction s as [|c r IH]; cbn [PD.span].
  - destruct (PD.dig_loop g []) as [[n' d'] r'] eqn:E. cbn in E. injection E as <- <- <-. split; [reflexivity | lia].
  - destruct (c =? 48) eqn:Z.
    + apply Z.eqb_eq in Z. subst c. destruct (PD.span (fun c => c =? 48) r) as [n1 r1]. destruct (PD.dig_loop g r1) as [[n' d'] r'] eqn:E.
      destruct IH as [IH P]. split; [|lia]. cbn [PD.dig_loop]. change (PD.is_dig 48) with true. cbv iota. rewrite IH.
      replace (0 <? n1 + 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [orb]. f_equal. f_equal. lia.
    + destruct (PD.dig_loop g (c :: r)) as [[n' d'] r'] eqn:E. split; [|lia]. rewrite Z.add_0_l. reflexivity.
Qed.
Lemma dec_len_dl : forall s, let '(n, d, r3) := PD.dig_loop false s in PD.dec_len s = n + (if d then ne r3 else 0).
Proof.
  intros s. unfold PD.dec_len. pose proof (dl_zeros false s) as A. destruct (PD.span (fun c => c =? 48) s) as [n1 r1].
  destruct r1 as [|c1 r'].
  - cbn [PD.dig_loop] in *. destruct A as [A P]. rewrite A. cbv beta iota zeta. change (0 <? 0) with false. rewrite !orb_false_r. destruct (0 <? n1); cbv beta iota; unfold ne; lia.
  - destruct (Z.eq_dec c1 46) as [->|NE].
    + (* [comment removed for export] *)
      cbn [PD.dig_loop] in A. change (PD.is_dig 46) with false in A. cbn [andb negb Z.eqb Pos.eqb] in A.
      pose proof (dl_zeros true r') as B. destruct (PD.span (fun c => c =? 48) r') as [n2 r2]. destruct (PD.dig_loop true r2) as [[n3 d3] r3] eqn:E3.
      destruct B as [B P2]. rewrite B in A. destruct A as [A P1]. rewrite A.
      replace (n1 + (n2 + n3 + 1)) with (n1 + 1 + n2 + n3) by lia. rewrite <- orb_assoc.
      destruct ((0 <? n1) || ((0 <? n2) || d3)) eqn:G; unfold ne; destruct r3 as [|c r4]; cbn [andb]; lia.
    + assert (M : match c1 :: r' with 46 :: r0 => let '(n2, r2) := PD.span (fun c => c =? 48) r0 in (1, true, n2, r2) | _ => (0, false, 0, c1 :: r') end = (0, false, 0, c1 :: r')).
      { destruct c1 as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). exfalso. apply NE. reflexivity. }
      rewrite M. destruct (PD.dig_loop false (c1 :: r')) as [[n3 d3] r3] eqn:E3. destruct A as [A P1]. rewrite A.
      rewrite orb_false_r. destruct ((0 <? n1) || d3) eqn:G; unfold ne; destruct r3 as [|c r4]; cbn [andb]; lia.
Qed.

Lemma dec_full : forall c l, is_dig c = true -> tail_ok false l -> PD.dec_len (c :: l) = 1 + len l.
Proof.
  intros c l D T. pose proof (dec_len_dl (c :: l)) as A. unfold tail_ok in T. cbn [PD.dig_loop] in A. rewrite is_dig_eq, D in A.
  destruct (PD.dig_loop false l) as [[n d] r3]. rewrite A. lia.
Qed.

Theorem json_full : forall txt, num_final txt ->
  let q := match txt with 45 :: _ => 1 | _ => 0 end in q + PD.dec_len (skipn (Z.to_nat q) txt) = len txt.
Proof.
  intros txt (k & H & F). fold (fin k) in F. destruct txt as [|c l]; [cbn in H; injection H as <-; unfold fin in F; cbn in F; lia|].
  cbn [nl_run] in H. unfold nl_step in H. cbn in H.
  destruct (c =? 45) eqn:M.
  - apply Z.eqb_eq in M. subst c. cbv beta iota zeta. change (Z.to_nat 1) with 1%nat. simpl skipn. rewrite len_cons.
    destruct l as [|d l']; [cbn in H; injection H as <-; unfold fin in F; cbn in F; lia|].
    cbn [nl_run] in H. unfold nl_step in H. cbn in H. rewrite len_cons. simpl skipn.
    destruct (d =? 48) eqn:Z0.
    + apply Z.eqb_eq in Z0. subst d. rewrite (dec_full 48 l' eq_refl (tail1 l' k H F)). lia.
    + destruct (is_dig d) eqn:D; [|discriminate]. rewrite (dec_full d l' D (tail2 l' k H F)). lia.
  - assert (Q : match c :: l with 45 :: _ => 1 | _ => 0 end = 0).
    { destruct c as [|p|p]; try reflexivity. do 6 (destruct p as [p|p|]; try reflexivity). discriminate M. }
    cbv zeta. rewrite Q. change (Z.to_nat 0) with 0%nat. simpl skipn. rewrite len_cons.
    destruct (c =? 48) eqn:Z0.
    + apply Z.eqb_eq in Z0. subst c. rewrite (dec_full 48 l eq_refl (tail1 l k H F)). lia.
    + destruct (is_dig c) eqn:D; [|discriminate]. rewrite (dec_full c l D (tail2 l k H F)). lia.
Qed.
End PDJ.
