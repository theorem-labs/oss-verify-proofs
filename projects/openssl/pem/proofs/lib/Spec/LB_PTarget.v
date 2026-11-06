(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad MSafe Stdio Harness Target Driver LB_Logic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac red_ops := cbn [ret bind unreachable lib_malloc lib_free choose out_stderr out_stdout msg_store Target.ops lib_free_opt].

(* [comment removed for export] *)
Definition smallX {ptr : Type} (X : list (ptr * Z)) : Prop :=
  Forall (fun xb => 0 <= snd xb <= MAX_INPUT + 1) X.

(* [comment removed for export] *)
Definition cinv {ptr : Type} (L : @clist ptr) : Prop :=
  cntA L <= CAP_A /\ cntB L <= CAP_B /\ bigsum L <= BIG_ROOM /\ Forall (fun xb => 0 <= snd xb) L.

Section ClistFacts.
Context {ptr : Type}.
Implicit Types L : @clist ptr.

Lemma cntA_cons x L : cntA (x :: L) = (if snd x <=? TIER_A_MAX then 1 else 0) + cntA L.
Proof. unfold cntA. cbn [List.filter]. destruct (snd x <=? TIER_A_MAX); cbn [length]; rewrite ?Nat2Z.inj_succ; Lia.lia. Qed.
Lemma cntB_cons x L : cntB (x :: L) = (if TIER_A_MAX <? snd x then 1 else 0) + cntB L.
Proof. unfold cntB. cbn [List.filter]. destruct (TIER_A_MAX <? snd x); cbn [length]; rewrite ?Nat2Z.inj_succ; Lia.lia. Qed.
Lemma bigsum_cons x L : bigsum (x :: L) = (if TIER_A_MAX <? snd x then snd x + 8192 else 0) + bigsum L.
Proof. reflexivity. Qed.
Lemma cntA_nonneg L : 0 <= cntA L. Proof. unfold cntA. lia. Qed.
Lemma cntB_nonneg L : 0 <= cntB L. Proof. unfold cntB. lia. Qed.
Lemma bigsum_nonneg L : Forall (fun xb => 0 <= snd xb) L -> 0 <= bigsum L.
Proof.
  induction L as [|x L IH]; intros H; [cbn; lia|]. rewrite bigsum_cons. inversion H; subst.
  specialize (IH ltac:(assumption)). destruct (TIER_A_MAX <? snd x); lia.
Qed.

Lemma cinv_nil : cinv (@nil (ptr * Z)).
Proof. unfold cinv, cntA, cntB, bigsum, CAP_A, CAP_B, BIG_ROOM. cbn. repeat split; try lia. constructor. Qed.

Lemma cinv_cons p n L : cinv L -> 0 <= n ->
  (n <= TIER_A_MAX -> cntA L < CAP_A) -> (TIER_A_MAX < n -> cntB L < CAP_B /\ bigsum L + n + 8192 <= BIG_ROOM) ->
  cinv ((p, n) :: L).
Proof.
  intros (HA & HB & HS & HF) Hn H1 H2. unfold cinv. rewrite cntA_cons, cntB_cons, bigsum_cons. cbn [snd].
  destruct (Z.leb_spec n TIER_A_MAX) as [Hle|Hgt]; destruct (Z.ltb_spec TIER_A_MAX n) as [Hlt|Hge]; try lia.
  - specialize (H1 Hle). repeat split; try lia. constructor; [exact Hn| exact HF].
  - destruct (H2 Hgt) as [H3 H4]. repeat split; try lia. constructor; [exact Hn| exact HF].
Qed.

Lemma cremove_perm : forall L i x, nth_error L i = Some x -> Permutation L (x :: cremove i L).
Proof.
  induction L as [|y L IH]; intros i x H; destruct i; cbn in *; try discriminate.
  - inversion H; subst. apply Permutation_refl.
  - specialize (IH i x H). eapply Permutation_trans; [apply perm_skip; exact IH| apply perm_swap].
Qed.

Lemma perm_counts : forall M N : @clist ptr, Permutation M N -> cntA M = cntA N /\ cntB M = cntB N /\ bigsum M = bigsum N.
Proof.
  induction 1 as [|z M N _ IHp|z w M|M N O _ IH1 _ IH2].
  - auto.
  - rewrite !cntA_cons, !cntB_cons, !bigsum_cons. lia.
  - rewrite !cntA_cons, !cntB_cons, !bigsum_cons. lia.
  - lia.
Qed.

Lemma cinv_remove : forall L i x, nth_error L i = Some x -> cinv L -> cinv (cremove i L).
Proof.
  intros L i x H (HA & HB & HS & HF).
  pose proof (cremove_perm L i x H) as HP.
  destruct (perm_counts _ _ HP) as (E1 & E2 & E3). rewrite cntA_cons in E1. rewrite cntB_cons in E2. rewrite bigsum_cons in E3.
  assert (HF' : Forall (fun xb => 0 <= snd xb) (x :: cremove i L)) by (eapply Permutation_Forall; [exact HP| exact HF]).
  pose proof (Forall_inv HF') as Hx. pose proof (Forall_inv_tail HF') as HFt. cbn beta in Hx.
  unfold cinv. destruct (snd x <=? TIER_A_MAX), (TIER_A_MAX <? snd x); repeat split; try lia; exact HFt.
Qed.
End ClistFacts.

Section TargetL.
Context {St ptr : Type}.
Variable B : Z.
Variable raw_malloc : Z -> Monad.M St (option ptr).
Variable raw_free : ptr -> Monad.M St unit.
Variable get_so : St -> stdout_st.
Variable set_so : stdout_st -> St -> St.
Variable own : list (ptr * Z) -> assn St.
Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
  mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
         (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hout : forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X).

(* [comment removed for export] *)
Definition amb_ok (A : list (ptr * Z)) : Prop := (length A <= 2)%nat /\ smallX A.
Hypothesis OK_cl : forall L A n, cinv L -> amb_ok A -> 0 <= n < SZ_MAX ->
  (n <= TIER_A_MAX -> cntA L < CAP_A) -> (TIER_A_MAX < n -> cntB L < CAP_B /\ bigsum L + n + 8192 <= BIG_ROOM) ->
  mal_ok (L ++ A) n.
Hypothesis OK_drv : forall L A n, cinv L -> (length A <= 1)%nat -> smallX A -> 0 <= n <= MAX_INPUT + 1 -> mal_ok (L ++ A) n.

Let ops : target_ops (Monad.M St) ptr := Target.ops raw_malloc raw_free get_so set_so.

Lemma mspecL_ret_ops {A} (a : A) (P : assn St) (Q : A -> assn St) :
  (forall s mo, P s mo -> Q a s mo) -> mspecL B P (ret ops a) Q.
Proof. intros H. cbn. apply mspecL_ret. exact H. Qed.

Lemma mspecL_bind_ops {A C} (m : Monad.M St A) (f : A -> Monad.M St C) P Q1 Q :
  mspecL B P m Q1 -> (forall a, mspecL B (Q1 a) (f a) Q) -> mspecL B P (bind ops m f) Q.
Proof. intros. cbn. eapply mspecL_bind; eauto. Qed.

(* [comment removed for export] *)
Lemma client_any_L : forall fuel L A, cinv L -> amb_ok A ->
  mspecL B (own (L ++ A)) (client_any ops fuel L) (fun L' s mo => own (L' ++ A) s mo /\ cinv L').
Proof.
  induction fuel as [|f IH]; intros L A HC HA; cbn [client_any].
  - apply mspecL_ret_ops. auto.
  - apply (mspecL_bind_ops _ _ _ (fun a s mo => cvalid L a /\ own (L ++ A) s mo)).
    { red_ops. apply mspecL_choice. intros a s mo Hv H. split; assumption. }
    intros [k n i]. apply mspecL_pure_l. intros Hv.
    destruct k as [|k|k]; [apply mspecL_ret_ops; auto| |apply mspecL_ret_ops; auto].
    destruct k as [k|k|]; [apply mspecL_ret_ops; auto| |].
    + (* [comment removed for export] *)
      destruct k as [k|k|]; try (apply mspecL_ret_ops; auto; fail).
      cbn in Hv. destruct (nth_error L (Z.to_nat n)) as [[p sz]|] eqn:E.
      * apply (mspecL_bind_ops _ _ _ (fun _ => own (cremove (Z.to_nat n) L ++ A))).
        { red_ops. eapply mspecL_pre; [apply (Hdf (cremove (Z.to_nat n) L ++ A) p sz)|].
          intros s mo H. eapply Hperm; [|exact H].
          change ((p, sz) :: cremove (Z.to_nat n) L ++ A) with (((p, sz) :: cremove (Z.to_nat n) L) ++ A).
          apply Permutation_app_tail. exact (cremove_perm L _ (p, sz) E). }
        intros _. apply IH; [exact (cinv_remove L _ _ E HC)| exact HA].
      * red_ops. apply mspecL_munr.
    + (* [comment removed for export] *)
      cbn in Hv. destruct Hv as (Hn & H1 & H2).
      apply (mspecL_bind_ops _ _ _ (fun r s mo => match r with Some p => own (((p, n) :: L) ++ A) s mo | None => own (L ++ A) s mo end)).
      { red_ops. eapply mspecL_conseq; [apply (Hdm (L ++ A) n); lia| |].
        - intros s mo H. split; [exact H| apply OK_cl; assumption].
        - intros [p|] s mo H; [exact (proj1 H)| exact H]. }
      intros [p|]; [| red_ops; apply mspecL_munr].
      apply IH; [apply cinv_cons; [exact HC| lia| exact H1| exact H2]| exact HA].
Qed.

Lemma fuzz_one_L : forall d L A, cinv L -> amb_ok A ->
  mspecL B (own (L ++ A)) (fuzz_one ops d L) (fun r s mo => own (snd r ++ A) s mo /\ cinv (snd r) /\ fst r = 0).
Proof.
  intros d L A HC HA. unfold fuzz_one.
  apply (mspecL_bind_ops _ _ _ (fun L' s mo => own (L' ++ A) s mo /\ cinv L')); [apply client_any_L; assumption|].
  intros L'. apply mspecL_ret_ops. intros s mo [H1 H2]. cbn [fst snd]. auto.
Qed.

Lemma run_calls_L : forall d A n rc L, cinv L -> amb_ok A -> rc = 0 ->
  mspecL B (own (L ++ A)) (run_calls ops d n rc L)
         (fun rc' => fun s mo => (exists L' : @clist ptr, own (L' ++ A) s mo) /\ rc' = 0).
Proof.
  intros d A n. induction n as [|n IH]; intros rc L HC HA Hrc; cbn [run_calls].
  - apply mspecL_ret_ops. intros s mo H. split; [exists L; exact H| exact Hrc].
  - apply (mspecL_bind_ops _ _ _ (fun r => fun s mo => own (snd r ++ A) s mo /\ cinv (snd r) /\ fst r = 0)); [apply fuzz_one_L; assumption|].
    intros [rc' L']. cbn [fst snd]. apply mspecL_pointwise. intros s0 mo0 (Ho & HC' & ->).
    apply (mspecL_bind_ops _ _ _ (fun _ => own (L' ++ A))).
    + red_ops. eapply mspecL_pre; [apply Hout|]. intros s mo [-> ->]. exact Ho.
    + intros u. apply IH; [exact HC'| exact HA| reflexivity].
Qed.
End TargetL.

(* [comment removed for export] *)
Theorem target_run_L {St ptr : Type} (B : Z)
  (raw_malloc : Z -> Monad.M St (option ptr)) (raw_free : ptr -> Monad.M St unit)
  (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St)
  (own : list (ptr * Z) -> assn St) (mal_ok : list (ptr * Z) -> Z -> Prop) :
  (forall X n, 0 <= n ->
     mspecL B (fun s mo => own X s mo /\ mal_ok X n) (raw_malloc n)
            (fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end)) ->
  (forall X p n, mspecL B (own ((p, n) :: X)) (raw_free p) (fun _ => own X)) ->
  (forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo) ->
  (forall X ps, mspecL B (own X) (stdout_vprintf get_so set_so ps) (fun _ => own X)) ->
  (forall L A n, cinv L -> @amb_ok ptr A -> 0 <= n < SZ_MAX ->
     (n <= TIER_A_MAX -> cntA L < CAP_A) -> (TIER_A_MAX < n -> cntB L < CAP_B /\ bigsum L + n + 8192 <= BIG_ROOM) -> mal_ok (L ++ A) n) ->
  (forall L A n, cinv L -> (length A <= 1)%nat -> smallX A -> 0 <= n <= MAX_INPUT + 1 -> mal_ok (L ++ A) n) ->
  forall X0 cfg payload, (length X0 <= 1)%nat -> smallX X0 -> zlength payload <= MAX_INPUT ->
  mspecL B (own X0) (Target.target_run raw_malloc raw_free get_so set_so cfg payload) (fun _ s mo => exists Y, own (Y ++ X0) s mo).
Proof.
  intros Hdm Hdf Hperm Hout OKc OKd X0 cfg payload HX0 SX0 Hpl.
  unfold Target.target_run, Harness.target_run.
  assert (HA0 : @amb_ok ptr X0) by (split; [lia| exact SX0]).
  (* [comment removed for export] *)
  apply (mspecL_bind _ _ _ _ (fun L0 s mo => own (L0 ++ X0) s mo /\ cinv L0)).
  { unfold fuzz_init. apply (client_any_L B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm OKc INIT_FUEL [] X0 cinv_nil HA0). }
  intros L0. apply mspecL_pointwise. intros s0 mo0 (Ho0 & HC0).
  set (owned_blocks := fun (o : option ptr) => match o with Some p => [(p, zlength payload)] | None => [] end).
  apply (mspecL_bind _ _ _ _ (fun a => match a with None => fun s mo => exists Y, own (Y ++ X0) s mo
                                          | Some owned => own (L0 ++ owned_blocks owned ++ X0) end)).
  - destruct (zlength payload =? 0) eqn:EZ.
    + cbn. apply mspecL_ret. intros s mo [-> ->]. exact Ho0.
    + cbn -[MAX_INPUT]. apply (mspecL_bind _ _ _ _ (fun r s mo => match r with Some p => own ((p, zlength payload) :: L0 ++ X0) s mo | None => own (L0 ++ X0) s mo end)).
      * eapply mspecL_conseq; [apply (Hdm (L0 ++ X0) (zlength payload)); unfold zlength; lia| |].
        -- intros s mo [-> ->]. split; [exact Ho0|]. apply OKd; [exact HC0| exact HX0| exact SX0| unfold zlength in *; lia].
        -- intros [p|] s mo H; [exact (proj1 H)| exact H].
      * intros [p|]; apply mspecL_ret; intros s mo H; [| exists L0; exact H].
        eapply Hperm; [|exact H]. cbn [owned_blocks app]. apply Permutation_middle.
  - intros [owned|]; [| cbn; apply mspecL_ret; intros s mo H; exact H].
    assert (HAA : @amb_ok ptr (owned_blocks owned ++ X0)).
    { split; [destruct owned; cbn [owned_blocks length app]; lia|].
      destruct owned as [p|]; cbn [owned_blocks app]; [| exact SX0]. constructor; [cbn [snd]; unfold zlength in *; lia| exact SX0]. }
    cbn -[MAX_INPUT run_calls].
    apply (mspecL_bind _ _ _ _ (fun rc => fun s mo => (exists L' : @clist ptr, own (L' ++ owned_blocks owned ++ X0) s mo) /\ rc = 0)).
    { apply (run_calls_L B raw_malloc raw_free get_so set_so own mal_ok Hdm Hdf Hperm Hout OKc payload _ _ 0 L0 HC0 HAA). reflexivity. }
    intros rc. apply mspecL_pure. intros ->. apply mspecL_exI. intros L'.
    apply (mspecL_bind _ _ _ _ (fun _ => own (L' ++ X0))).
    + destruct owned as [p|]; cbn [owned_blocks app lib_free_opt].
      * eapply mspecL_pre; [apply (Hdf (L' ++ X0) p (zlength payload))|]. intros s mo H. eapply Hperm; [|exact H].
        apply Permutation_sym, Permutation_middle.
      * apply mspecL_ret; intros s mo H; exact H.
    + intros u. apply mspecL_ret. intros s mo H. exists L'. exact H.
Qed.
