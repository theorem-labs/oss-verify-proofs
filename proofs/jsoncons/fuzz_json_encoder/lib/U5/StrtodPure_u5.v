(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import DecIface_u5 DecJson_u5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PSP.
Import PDJ.
Lemma step_byte : forall k c k', nl_step k c = Some k' -> 0 <= c < 256 /\ 0 <= k' <= 7.
Proof.
  intros k c k' H. unfold nl_step, is_dig in H.
  repeat match type of H with
         | (if ?b then _ else _) = _ => let E := fresh "E" in destruct b eqn:E
         end; try discriminate; injection H as <-;
  repeat match goal with
         | X : (_ =? _) = true |- _ => apply Z.eqb_eq in X
         | X : (_ || _) = true |- _ => apply orb_prop in X as [X|X]
         | X : (_ && _) = true |- _ => apply andb_prop in X as [? ?]
         | X : (_ <=? _) = true |- _ => apply Z.leb_le in X
         end; lia.
Qed.
Lemma run_bytes : forall l k k', nl_run k l = Some k' -> Forall (fun c => 0 <= c < 256) l.
Proof.
  induction l as [|c r IH]; intros k k' H; [constructor|]. cbn [nl_run] in H. destruct (nl_step k c) as [k1|] eqn:E; [|discriminate].
  constructor; [exact (proj1 (step_byte _ _ _ E)) | exact (IH _ _ H)].
Qed.
Lemma final_bytes : forall txt, num_final txt -> Forall (fun c => 0 <= c < 256) txt.
Proof. intros txt (k & H & _). exact (run_bytes _ _ _ H). Qed.

(* [comment removed for export] *)
Lemma final_shape : forall txt, num_final txt ->
  (exists c0 r, txt = c0 :: r /\ PD.is_dig c0 = true) \/ (exists c1 r, txt = 45 :: c1 :: r /\ PD.is_dig c1 = true).
Proof.
  intros txt (k & H & F). destruct txt as [|c l]; [cbn in H; injection H as <-; cbn in F; lia|].
  cbn [nl_run] in H. unfold nl_step in H. cbn [Z.eqb] in H. change (-1 =? -1) with true in H. cbv iota in H.
  destruct (c =? 45) eqn:M.
  - apply Z.eqb_eq in M. subst c. right. destruct l as [|c1 r]; [cbn in H; injection H as <-; cbn in F; lia|].
    exists c1, r. split; [reflexivity|]. cbn [nl_run] in H. unfold nl_step in H. change (0 =? -1) with false in H. change (0 =? 0) with true in H. cbv iota in H.
    destruct (c1 =? 48) eqn:M1; [apply Z.eqb_eq in M1; subst c1; reflexivity|]. fold (PD.is_dig c1) in H. unfold is_dig in H. fold (PD.is_dig c1) in H.
    destruct (PD.is_dig c1); [reflexivity | discriminate].
  - left. exists c, l. split; [reflexivity|]. destruct (c =? 48) eqn:M1; [apply Z.eqb_eq in M1; subst c; reflexivity|]. unfold is_dig in H. fold (PD.is_dig c) in H.
    destruct (PD.is_dig c); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition after0_ok (c : Z) : Prop := c = 0 \/ c = 46 \/ c = 101 \/ c = 69 \/ PD.is_dig c = true.
Lemma after0_run : forall l k, nl_run 1 l = Some k -> after0_ok (nth 0 (l ++ [0]) 0).
Proof.
  intros [|c r] k H; [left; reflexivity|]. cbn [app nth]. cbn [nl_run] in H. unfold nl_step in H.
  change (1 =? -1) with false in H. change (1 =? 0) with false in H. change (1 =? 1) with true in H. cbv iota in H.
  destruct (c =? 46) eqn:M1; [apply Z.eqb_eq in M1; right; left; exact M1|].
  destruct ((c =? 101) || (c =? 69)) eqn:M2; [apply orb_prop in M2 as [M2|M2]; apply Z.eqb_eq in M2; unfold after0_ok; tauto|].
  unfold is_dig in H. fold (PD.is_dig c) in H. destruct (PD.is_dig c) eqn:M3; [unfold after0_ok; tauto | discriminate].
Qed.
Lemma final_after0 : forall txt, num_final txt ->
  (forall r, txt = 48 :: r -> after0_ok (nth 1 (txt ++ [0]) 0)) /\ (forall r, txt = 45 :: 48 :: r -> after0_ok (nth 2 (txt ++ [0]) 0)).
Proof.
  intros txt (k & H & F). split; intros r ->.
  - cbn [nl_run] in H. change (nl_step (-1) 48) with (Some 1) in H. cbv iota in H. exact (after0_run r k H).
  - cbn [nl_run] in H. change (nl_step (-1) 45) with (Some 0) in H. cbv iota in H. change (nl_step 0 48) with (Some 1) in H. cbv iota in H. exact (after0_run r k H).
Qed.
Lemma after0_not_x : forall c, after0_ok c -> Z.land c (2 ^ 64 - 33) <> 88.
Proof.
  intros c [-> | [-> | [-> | [-> | H]]]]; [vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate | vm_compute; discriminate |].
  unfold PD.is_dig in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  assert (X : forallb (fun c => negb (Z.land c (2 ^ 64 - 33) =? 88)) (map Z.of_nat (seq 48 10)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in X. specialize (X c). rewrite negb_true_iff in X. apply Z.eqb_neq. apply X.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
End PSP.
