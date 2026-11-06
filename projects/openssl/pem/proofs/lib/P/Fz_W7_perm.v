(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks ClientOwn.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Harness Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Perm.
  Context {ptr : Type}.
  Implicit Types (L R S : @clist ptr).

  (* [comment removed for export] *)
  Lemma cntA_app : forall L R, cntA (L ++ R) = cntA L + cntA R.
  Proof. intros L R. unfold cntA. rewrite List.filter_app, List.length_app, Nat2Z.inj_add. reflexivity. Qed.
  Lemma cntB_app : forall L R, cntB (L ++ R) = cntB L + cntB R.
  Proof. intros L R. unfold cntB. rewrite List.filter_app, List.length_app, Nat2Z.inj_add. reflexivity. Qed.
  Lemma bigsum_app : forall L R, bigsum (L ++ R) = bigsum L + bigsum R.
  Proof. intros L R. unfold bigsum. induction L as [|x L IH]; cbn [fold_right app]; [lia|]. rewrite IH. lia. Qed.
  Lemma cntA_cons : forall (e : ptr * Z) L, cntA (e :: L) = (if snd e <=? TIER_A_MAX then 1 else 0) + cntA L.
  Proof. intros e L. change (e :: L) with ([e] ++ L). rewrite cntA_app. f_equal. unfold cntA. cbn [List.filter]. destruct (snd e <=? TIER_A_MAX); reflexivity. Qed.
  Lemma cntB_cons : forall (e : ptr * Z) L, cntB (e :: L) = (if TIER_A_MAX <? snd e then 1 else 0) + cntB L.
  Proof. intros e L. change (e :: L) with ([e] ++ L). rewrite cntB_app. f_equal. unfold cntB. cbn [List.filter]. destruct (TIER_A_MAX <? snd e); reflexivity. Qed.
  Lemma bigsum_cons : forall (e : ptr * Z) L, bigsum (e :: L) = (if TIER_A_MAX <? snd e then snd e + 8192 else 0) + bigsum L.
  Proof. intros e L. reflexivity. Qed.
  Lemma cntA_nil : cntA ([] : @clist ptr) = 0. Proof. reflexivity. Qed.
  Lemma cntB_nil : cntB ([] : @clist ptr) = 0. Proof. reflexivity. Qed.
  Lemma bigsum_nil : bigsum ([] : @clist ptr) = 0. Proof. reflexivity. Qed.
  Lemma cntA_nonneg : forall L, 0 <= cntA L. Proof. intros L. unfold cntA. lia. Qed.
  Lemma cntB_nonneg : forall L, 0 <= cntB L. Proof. intros L. unfold cntB. lia. Qed.

  (* [comment removed for export] *)
  Lemma cntA_perm : forall L R, Permutation L R -> cntA L = cntA R.
  Proof. intros L R P. induction P; [reflexivity| rewrite !cntA_cons; lia| rewrite !cntA_cons; lia| lia]. Qed.
  Lemma cntB_perm : forall L R, Permutation L R -> cntB L = cntB R.
  Proof. intros L R P. induction P; [reflexivity| rewrite !cntB_cons; lia| rewrite !cntB_cons; lia| lia]. Qed.
  Lemma bigsum_perm : forall L R, Permutation L R -> bigsum L = bigsum R.
  Proof. intros L R P. induction P; [reflexivity| rewrite !bigsum_cons; lia| rewrite !bigsum_cons; lia| lia]. Qed.

  (* [comment removed for export] *)
  Lemma perm_cremove : forall L (i : nat) e, nth_error L i = Some e -> Permutation L (e :: cremove i L).
  Proof.
    induction L as [|x L IH]; intros i e H; [destruct i; discriminate|].
    destruct i as [|i]; cbn in H |- *; [inversion H; subst; apply Permutation_refl|].
    eapply perm_trans; [apply perm_skip; exact (IH _ _ H)| apply perm_swap].
  Qed.

  (* [comment removed for export] *)
  Lemma nodup_fst : forall L, List.NoDup (map fst L) -> List.NoDup L.
  Proof. intros L H. exact (NoDup_map_inv fst L H). Qed.

  Lemma in_fst : forall L (e : ptr * Z), In e L -> In (fst e) (map fst L).
  Proof. intros L e H. apply in_map. exact H. Qed.

  (* [comment removed for export] *)
  Lemma nodup_fst_eq : forall L (p : ptr) (a b : Z), List.NoDup (map fst L) -> In (p, a) L -> In (p, b) L -> a = b.
  Proof.
    induction L as [|x L IH]; intros p a b ND Ha Hb; [destruct Ha|]. cbn [map] in ND. inversion ND as [|y l NI ND']; subst.
    destruct Ha as [->|Ha]; destruct Hb as [E|Hb].
    - inversion E. reflexivity.
    - exfalso. apply NI. cbn [fst]. apply in_map_iff. exists (p, b). split; [reflexivity| exact Hb].
    - exfalso. apply NI. rewrite E. cbn [fst]. apply in_map_iff. exists (p, a). split; [reflexivity| exact Ha].
    - exact (IH p a b ND' Ha Hb).
  Qed.

  (* [comment removed for export] *)
  Lemma pigeonhole : forall L S, List.NoDup (map fst L) -> List.NoDup (map fst S) -> (forall e, In e S -> In e L) -> length L = length S -> Permutation L S.
  Proof.
    intros L S NDL NDS INCL LEN. apply Permutation_sym. apply NoDup_Permutation_bis; [exact (nodup_fst _ NDS)| lia| intros e He; exact (INCL e He)].
  Qed.

  (* [comment removed for export] *)
  Lemma perm_remove_ids : forall Lc L' AK R (ids : list ptr),
    Permutation Lc (AK ++ R) -> List.NoDup (map fst Lc) -> List.NoDup (map fst L') ->
    (forall q, In q ids <-> In q (map fst AK)) ->
    (forall e, In e L' <-> (In e Lc /\ ~ In (fst e) ids)) ->
    Permutation L' R.
  Proof.
    intros Lc L' AK R ids P NDC NDL IDS IFF.
    assert (NDAR : List.NoDup (map fst (AK ++ R))) by (eapply Permutation_NoDup; [apply Permutation_map; exact P| exact NDC]).
    apply Permutation.NoDup_Permutation; [exact (nodup_fst _ NDL)| |].
    { apply (nodup_fst R). rewrite map_app in NDAR. exact (NoDup_app_remove_l _ _ NDAR). }
    intros e. rewrite IFF. split.
    - intros [He NI]. assert (He' : In e (AK ++ R)) by (eapply Permutation_in; [exact P| exact He]).
      apply in_app_iff in He'. destruct He' as [He'|He']; [| exact He']. exfalso. apply NI. apply IDS. apply in_fst. exact He'.
    - intros He. split; [eapply Permutation_in; [apply Permutation_sym; exact P| apply in_app_iff; right; exact He]|].
      intros X. apply IDS in X. rewrite map_app in NDAR. apply in_map_iff in X. destruct X as (e' & E & He').
      clear - NDAR He He' E. induction AK as [|a AK IH]; [destruct He'|]. cbn [map app] in NDAR. inversion NDAR as [|y l NI ND']; subst.
      destruct He' as [->|He']; [| exact (IH ND' He')]. apply NI. rewrite E. apply in_app_iff. right. apply in_map. exact He.
  Qed.

  (* [comment removed for export] *)
  Lemma perm_remove_one : forall Lc (i : nat) (e : ptr * Z) AK1 AK2 R,
    Permutation Lc (AK1 ++ e :: AK2 ++ R) -> nth_error Lc i = Some e -> Permutation (cremove i Lc) (AK1 ++ AK2 ++ R).
  Proof.
    intros Lc i e AK1 AK2 R P HN. apply (Permutation_cons_inv (a := e)).
    eapply perm_trans; [apply Permutation_sym; exact (perm_cremove _ _ _ HN)|]. eapply perm_trans; [exact P|].
    apply Permutation_sym. apply Permutation_middle.
  Qed.

  (* [comment removed for export] *)
  Lemma perm_add_one : forall Lc (e : ptr * Z) AK R, Permutation Lc (AK ++ R) -> Permutation (e :: Lc) ((e :: AK) ++ R).
  Proof. intros Lc e AK R P. cbn [app]. apply perm_skip. exact P. Qed.

  (* [comment removed for export] *)
  Lemma perm_replace_one : forall Lc (i : nat) (e e' : ptr * Z) AK1 AK2 R,
    Permutation Lc (AK1 ++ e :: AK2 ++ R) -> nth_error Lc i = Some e -> Permutation (e' :: cremove i Lc) ((e' :: AK1 ++ AK2) ++ R).
  Proof. intros Lc i e e' AK1 AK2 R P HN. cbn [app]. rewrite <- app_assoc. apply perm_skip. exact (perm_remove_one _ _ _ _ _ _ P HN). Qed.
End Perm.

(* [comment removed for export] *)
Definition bents (bs : list block) : @clist bptr := map (fun b => (blk_id b, blk_size b)) bs.
Lemma bents_app : forall bs cs, bents (bs ++ cs) = bents bs ++ bents cs.
Proof. intros. unfold bents. apply map_app. Qed.
Lemma map_fst_bents : forall bs, map fst (bents bs) = map blk_id bs.
Proof. intros bs. unfold bents. rewrite map_map. reflexivity. Qed.
Lemma length_bents : forall bs, length (bents bs) = length bs.
Proof. intros bs. unfold bents. apply length_map. Qed.
Lemma in_bents : forall bs q nm, In (q, nm) (bents bs) <-> exists b, In b bs /\ blk_id b = q /\ blk_size b = nm.
Proof.
  intros bs q nm. unfold bents. rewrite in_map_iff. split.
  - intros (b & E & Hb). inversion E. exists b. auto.
  - intros (b & Hb & E1 & E2). exists b. subst. split; [reflexivity| exact Hb].
Qed.
