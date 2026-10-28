(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import ShapeAlg.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode NodesA_wv.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import X_bridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma concat_map_to_bytes : forall (l : list (list Z)), concat (map to_bytes l) = to_bytes (concat l).
Proof. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite IH. unfold to_bytes. rewrite map_app. reflexivity. Qed.

Lemma length_to_bytes_x : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.

Lemma dec_writev_eff0 : forall total (i : nat), (1 <= Z.of_nat i <= total) -> total < 2^64 ->
  dec_writev total (eff0 (Z_to_bv 64 (Z.of_nat i))) = Some (Z.of_nat i).
Proof.
  intros total i Hi Ht. unfold dec_writev, eff0. rewrite unsigned_lit by lia.
  replace ((1 <=? Z.of_nat i) && (Z.of_nat i <=? total)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  rewrite orb_true_r. reflexivity.
Qed.

Lemma dec_writev_eff00 : dec_writev 0 (eff0 (Z_to_bv 64 0)) = Some 0.
Proof. reflexivity. Qed.

Lemma iov_advance_concat : forall iovs k, (1 <= length iovs <= 2)%nat -> 1 <= k < iov_total iovs ->
  concat (iov_advance iovs k) = skipn (Z.to_nat k) (concat iovs) /\ (1 <= length (iov_advance iovs k) <= 2)%nat.
Proof.
  intros iovs k Hl Hk. unfold iov_total, zlength in Hk.
  destruct iovs as [|a [|b [|c rest]]]; cbn [length] in Hl; try lia.
  - cbn [concat] in *. rewrite app_nil_r in *. cbn [iov_advance].
    replace (zlength a <? k) with false by (symmetry; apply Z.ltb_ge; unfold zlength; lia).
    cbn. rewrite app_nil_r. split; [reflexivity| cbn [length]; lia].
  - cbn [concat] in *. rewrite app_nil_r in *. rewrite length_app in Hk. cbn [iov_advance].
    destruct (Z.ltb_spec (zlength a) k) as [L|L]; unfold zlength in L.
    + cbn. rewrite app_nil_r. unfold zdrop. rewrite skipn_app.
      replace (Z.to_nat k - length a)%nat with (Z.to_nat (k - Z.of_nat (length a))) by lia.
      rewrite (skipn_all2 a) by lia. split; [reflexivity| cbn [length]; lia].
    + cbn [concat]. rewrite app_nil_r. unfold zdrop. rewrite skipn_app.
      replace (Z.to_nat k - length a)%nat with 0%nat by lia. cbn [skipn]. split; [reflexivity| cbn; lia].
Qed.

Lemma t_alt_eq : forall {I : Type} (f g : I -> TSet), (forall i, t_eq (f i) (g i)) -> t_eq (t_alt f) (t_alt g).
Proof. intros I f g H tr. split; intros [i Hi]; exists i; apply H; exact Hi. Qed.

Lemma t_emit_eq : forall e T T', t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. split; intros [Hp|(tr' & -> & Ht)]; [left; exact Hp| right; exists tr'; split; [reflexivity| apply H; exact Ht]
                                                          | left; exact Hp| right; exists tr'; split; [reflexivity| apply H; exact Ht]].
Qed.

Section StdioTT.
Context {St : Type}.

Lemma mloop_S_eq : forall {X R} n (body : X -> @M St (X + R)) x (st : St),
  mloop (S n) body x st = ebind (body x st) (fun p => (match fst p with inl x' => mloop n body x' | inr r => mret r end) (snd p)).
Proof. reflexivity. Qed.

Lemma wv_body_eq : forall fd iovs (st : St),
  wv_body fd iovs st = ebind (enode (NWritev fd (map to_bytes iovs))
                                    (fun r => match dec_writev (iov_total iovs) r with Some a => Some (a, st) | None => None end))
                             (fun p => (if fst p =? iov_total iovs then mret (inr tt) else mret (inl (iov_advance iovs (fst p)))) (snd p)).
Proof. reflexivity. Qed.

Theorem TT_wv_loop : forall n fd iovs (st : St) (T : unit * St -> TSet),
  (1 <= length iovs <= 2)%nat -> iov_total iovs < Z.of_nat n -> iov_total iovs <= 2^26 -> T (tt, st) [] ->
  t_eq (TT (mloop n (wv_body fd) iovs st) T) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iovs))) (T (tt, st))).
Proof.
  induction n as [|n IH]; intros fd iovs st T Hl Hn Htot HT0.
  - exfalso. unfold iov_total, zlength in Hn. lia.
  - rewrite mloop_S_eq, TT_ebind, wv_body_eq, TT_ebind. unfold enode. cbn [TT].
    rewrite concat_map_to_bytes.
    assert (LT : Z.of_nat (length (to_bytes (concat iovs))) = iov_total iovs) by (rewrite length_to_bytes_x; reflexivity).
    destruct (to_bytes (concat iovs)) as [|b bs] eqn:E.
    + assert (H0 : iov_total iovs = 0) by (rewrite <- LT; reflexivity). rewrite H0, dec_writev_eff00. cbn [TT fst snd]. cbn [Z.eqb]. unfold mret. cbn [TT fst snd].
      apply t_eq_sym. apply t_emit_nil_eq. exact HT0.
    + eapply t_eq_trans; [| apply (t_alt_wall' (Z_to_bv 64 fd) (b :: bs) (T (tt, st)) ltac:(cbn; lia))].
      apply t_alt_eq. intros [i Hi]. cbn [proj1_sig]. apply t_emit_eq.
      rewrite (dec_writev_eff0 (iov_total iovs) i) by lia. cbn [TT fst snd].
      destruct (Z.eqb_spec (Z.of_nat i) (iov_total iovs)) as [EQ|NE].
      * unfold mret. cbn [TT fst snd].
        replace i with (length (b :: bs)) by lia. rewrite skipn_all. cbn [map]. apply t_eq_sym. apply t_emit_nil_eq. exact HT0.
      * unfold mret. cbn [TT fst snd].
        destruct (iov_advance_concat iovs (Z.of_nat i) Hl ltac:(lia)) as [EC HL'].
        eapply t_eq_trans.
        -- apply IH; [exact HL'| | | exact HT0].
           ++ assert (Z.of_nat (length (concat (iov_advance iovs (Z.of_nat i)))) = iov_total iovs - Z.of_nat i).
              { rewrite EC, length_skipn. unfold iov_total, zlength in *. lia. }
              unfold iov_total, zlength in *. lia.
           ++ assert (Z.of_nat (length (concat (iov_advance iovs (Z.of_nat i)))) = iov_total iovs - Z.of_nat i).
              { rewrite EC, length_skipn. unfold iov_total, zlength in *. lia. }
              unfold iov_total, zlength in *. lia.
        -- rewrite EC. unfold to_bytes. rewrite <- skipn_map. fold (to_bytes (concat iovs)). rewrite E. rewrite Nat2Z.id.
           apply t_eq_refl.
Qed.

Theorem tok_wv_loop : forall chans n fd iovs (st : St),
  In fd chans -> (1 <= length iovs <= 2)%nat -> iov_total iovs < Z.of_nat n -> iov_total iovs <= 2^26 ->
  tok chans (mloop n (wv_body fd) iovs st).
Proof.
  intros chans. induction n as [|n IH]; intros fd iovs st Hfd Hl Hn Htot.
  - exfalso. unfold iov_total, zlength in Hn. lia.
  - rewrite mloop_S_eq, wv_body_eq. unfold enode. cbn [ebind bind tok]. split; [exact Hfd|].
    rewrite concat_map_to_bytes.
    assert (LT : Z.of_nat (length (to_bytes (concat iovs))) = iov_total iovs) by (rewrite length_to_bytes_x; reflexivity).
    split.
    + intros E. rewrite E in LT. assert (H0 : iov_total iovs = 0) by (rewrite <- LT; reflexivity). rewrite H0, dec_writev_eff00. cbn. exact I.
    + intros i Hi. rewrite (dec_writev_eff0 (iov_total iovs) i) by lia. cbn [bind tok fst snd].
      destruct (Z.eqb_spec (Z.of_nat i) (iov_total iovs)) as [EQ|NE]; [cbn; exact I|].
      destruct (iov_advance_concat iovs (Z.of_nat i) Hl ltac:(lia)) as [EC HL'].
      assert (Z.of_nat (length (concat (iov_advance iovs (Z.of_nat i)))) = iov_total iovs - Z.of_nat i).
      { rewrite EC, length_skipn. unfold iov_total, zlength in *. lia. }
      change (tok chans (mloop n (wv_body fd) (iov_advance iovs (Z.of_nat i)) st)).
      apply IH; [exact Hfd| exact HL'| unfold iov_total, zlength in *; lia| unfold iov_total, zlength in *; lia].
Qed.

End StdioTT.
