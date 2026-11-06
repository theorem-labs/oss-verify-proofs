(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "iff"; "not"; "False"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "mslot"; "astate"; "mupdate"; "mlookup"; "bit"; "sptr_eqb"; "ameta"; "lowbit"; "MUsed"; "lupd"; "ones"; "set_metas"; "st_metas"; "M"; "znth"; "zset"; "zupd"; "ask"; "askz"; "bind"; "ctz32"; "fail"; "get"; "get_links"; "getm"; "ibind"; "links_of"; "massert"; "mcheck"; "modify"; "osptr_eqb"; "put"; "ret"; "set_links"; "setm"; "setslot"; "with_links"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "pair"; "option"; "unit"; "Some"; "length"; "true"; "fst"; "false"; "tt"; "andb"; "nat"; "app"; "cons"; "list"; "nil"; "None"; "negb"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLemmasBase"; "itok"; "@Stdlib.ZArith.BinInt.Z"; "le"; "testbit"; "lt"; "mul"; "add"; "eqb"; "pow"; "land"; "leb"; "ldiff"; "lor"; "ltb"; "of_nat"; "ones"; "sub"; "@Stdlib.Lists.List"; "In"; "NoDup"; "nth_error"; "forallb"; "@Corelib.Lists.ListDef"; "map"; "nth"; "repeat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "answer_ok"; "req_ok"; "zseq"; "keys"; "reqs_ok"; "safe"; "used_metas"; "yields"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"; "eqb"; "@Corelib.Init.Specif"; "sumbool"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope mm_scope.

Fixpoint itok {A : Type} (t : itree astate A) (Q : A -> Prop) : Prop :=
  match t with
  | IRet a => Q a
  | IFail _ => False
  | IAsk q snap k => req_ok snap q /\ forall z, answer_ok q z -> itok (k z) Q
  end.

Lemma itok_mono {A} (t : itree astate A) (Q Q' : A -> Prop) : ltac2:(tb__ "0|0|
VA;VQ;R1A1VQ';R2A1F_;Fa;S42VA;Vt;VQ;A3S42VA;Vt;VQ';A3F_;F_;").
Proof.
  induction t as [a | q snap k IH | f]; cbn; intros HQ H.
  - apply HQ, H.
  - destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH; [exact HQ | apply Hk, Hz].
  - exact H.
Qed.

Lemma itok_ibind {A B} (t : itree astate A) (k : A -> itree astate B) (Q : B -> Prop) : ltac2:(tb__ "0|0|
S42VA;Vt;VA;S42VB;Vk;R1A1VQ;A3La;A3S42VB;S21S9VA;VB;Vt;Vk;A5VQ;A3F_;").
Proof.
  induction t as [a | q snap c IH | f]; cbn; intros H.
  - exact H.
  - destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply IH. apply Hk, Hz.
  - exact H.
Qed.

Lemma itok_safe {A} (t : itree astate A) Q : ltac2:(tb__ "0|0|
S42VA;Vt;VQ;A3S5fVA;Vt;A2F_;").
Proof.
  induction t as [a | q snap k IH | f]; cbn; intros H; [exact I | | exact H].
  destruct H as [_ Hk]. intros z Hz. apply (IH z). apply Hk, Hz.
Qed.

Lemma itok_reqs_ok {A} (t : itree astate A) Q : ltac2:(tb__ "0|0|
S42VA;Vt;VQ;A3S5eVA;Vt;A2F_;").
Proof.
  induction t as [a | q snap k IH | f]; cbn; intros H; [exact I | | exact I].
  destruct H as [Hr Hk]. split; [exact Hr|]. intros z Hz. apply (IH z). apply Hk, Hz.
Qed.

Lemma itok_yields {A} (t : itree astate A) Q tr a : ltac2:(tb__ "0|0|
S42VA;Vt;VQ;A3S61VA;Vt;Vtr;Va;A4VQ;Va;A1F_;F_;").
Proof.
  revert tr. induction t as [a' | q snap k IH | f]; cbn; intros tr H Hy.
  - destruct tr; [subst; exact H | destruct Hy].
  - destruct tr as [|[q' z] tr']; [destruct Hy|].
    destruct Hy as (-> & Hz & Hy). destruct H as [_ Hk]. eapply IH; [apply Hk, Hz | exact Hy].
  - destruct tr; destruct Hy.
Qed.

Lemma itok_conj {A} (t : itree astate A) (Q1 Q2 : A -> Prop) : ltac2:(tb__ "0|0|
S42VA;Vt;VQ1;A3S42VA;Vt;VQ2;A3S42VA;Vt;VA;S1VQ1;R1A1VQ2;R1A1A2La;A3F_;F_;").
Proof.
  induction t as [a | q snap k IH | f]; cbn; intros H1 H2.
  - split; assumption.
  - destruct H1 as [Hr H1], H2 as [_ H2]. split; [exact Hr|]. intros z Hz. apply IH; auto.
  - exact H1.
Qed.

Section MonadRules.
  Context {A B : Type}.
  Implicit Types (Q : A * astate -> Prop) (s : astate).

  Lemma itok_ret (a : A) s Q : ltac2:(tb__ "0|0|
VQ;S2fVA;S9Va;Vs;A4A1S42S2eVA;S9A2S28VA;Va;Vs;A3VQ;A3F_;").
  Proof using . intros H. exact H. Qed.

  Lemma itok_bind (m : M B) (k : B -> M A) s Q : ltac2:(tb__ "0|2|
S42S2eVB;S9A2M0Vm;Vs;A1G0S42S2eVA;S9A2M1Vk;S35VB;S9R1A3S40VB;S9R1A3A2VQ;A3Lr;A3S42G1S1bVB;VA;Vm;Vk;Vs;A5VQ;A3F_;").
  Proof using .
    intros H. unfold bind. apply itok_ibind.
    eapply itok_mono; [|exact H]. intros [b s'] Hb. exact Hb.
  Qed.

  Lemma itok_fail f s Q : ltac2:(tb__ "0|0|
S4S42S2eVA;S9A2S1dVA;Vf;Vs;A3VQ;A3F_;").
  Proof using . intros []. Qed.

  Lemma itok_get s (Q : astate * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S2fS9S9Vs;Vs;A4A1S42S2eS9S9A2S1eVs;A1VQ;A3F_;").
  Proof using . intros H. exact H. Qed.

  Lemma itok_put s s' (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S2fS31S9S37Vs';A4A1S42S2eS31S9A2S27Vs';Vs;A2VQ;A3F_;").
  Proof using . intros H. exact H. Qed.

  Lemma itok_modify f s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S2fS31S9S37Vf;Vs;A1A4A1S42S2eS31S9A2S25Vf;Vs;A2VQ;A3F_;").
  Proof using . intros H. exact H. Qed.

  Lemma itok_ask q s (Q : bool * astate -> Prop) : ltac2:(tb__ "0|0|
S5bVs;Vq;A2S41S5aVq;R1A2VQ;S2fS2dS9S3fS48R2Z0A2A1Vs;A4A1F_;Fz;S42S2eS2dS9A2S19Vq;Vs;A2VQ;A3F_;F_;").
  Proof using . intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.

  Lemma itok_askz q s (Q : Z * astate -> Prop) : ltac2:(tb__ "0|0|
S5bVs;Vq;A2S41S5aVq;R1A2VQ;S2fS41S9R2Vs;A4A1F_;Fz;S42S2eS41S9A2S1aVq;Vs;A2VQ;A3F_;F_;").
  Proof using . intros Hr H. cbn. split; [exact Hr|]. intros z Hz. apply H, Hz. Qed.

  Lemma itok_massert (b : bool) site s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S2dVb;S34A3VQ;S2fS31S9S37Vs;A4A1S42S2eS31S9A2S23Vb;Vsite;Vs;A3VQ;A3F_;F_;").
  Proof using . intros -> H. exact H. Qed.

  Lemma itok_mcheck (b : bool) tag s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S2dVb;S34A3VQ;S2fS31S9S37Vs;A4A1S42S2eS31S9A2S24Vb;Vtag;Vs;A3VQ;A3F_;F_;").
  Proof using . intros -> H. exact H. Qed.

  Lemma itok_if_true (b : bool) (m1 m2 : M A) s Q : ltac2:(tb__ "0|1|
S0S2dVb;S34A3S42S2eVA;S9A2M0Vm1;Vs;A1VQ;A3S42G0S2dS15VA;A1Lb;Vb;Vm1;Vm2;X2dx2Vs;A1VQ;A3F_;F_;").
  Proof using . intros -> H. exact H. Qed.

  Lemma itok_if_false (b : bool) (m1 m2 : M A) s Q : ltac2:(tb__ "0|1|
S0S2dVb;S36A3S42S2eVA;S9A2M0Vm2;Vs;A1VQ;A3S42G0S2dS15VA;A1Lb;Vb;Vm1;Vm2;X2dx2Vs;A1VQ;A3F_;F_;").
  Proof using . intros -> H. exact H. Qed.
End MonadRules.

Lemma itok_getm p s am (Q : ameta * astate -> Prop) : ltac2:(tb__ "0|0|
S0S30S8A1S59Vs;Vp;A2S32S8S10Vam;A1A2A3VQ;S2fSeS9Vam;Vs;A4A1S42S2eSeS9A2S20Vp;Vs;A2VQ;A3F_;F_;").
Proof.
  intros Hm H. unfold getm. apply itok_bind. apply itok_get. cbn [fst snd].
  unfold MT in Hm. rewrite Hm. exact H.
Qed.

Lemma itok_setm p am s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S2fS31S9S37S13SaS14Vs;A1Vp;S10Vam;A1A3Vs;A2A4A1S42S2eS31S9A2S2aVp;Vam;Vs;A3VQ;A3F_;").
Proof. intros H. exact H. Qed.

Lemma itok_setslot p x s (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
VQ;S2fS31S9S37S13SaS14Vs;A1Vp;Vx;A3Vs;A2A4A1S42S2eS31S9A2S2bVp;Vx;Vs;A3VQ;A3F_;").
Proof. intros H. exact H. Qed.

Lemma itok_get_links p s x (Q : (option sptr * option sptr) * astate -> Prop) : ltac2:(tb__ "0|2|
S0S30S8A1S59Vs;Vp;A2S32S8Vx;A2A3VQ;S2fS2eS30S7A1M0G0A2M1S9S22Vx;A1Vs;A4A1S42S2eG1S9A2S1fVp;Vs;A2VQ;A3F_;F_;").
Proof.
  intros Hm H. unfold get_links. apply itok_bind. apply itok_get. cbn [fst snd].
  unfold MT in Hm. rewrite Hm. exact H.
Qed.

Lemma itok_set_links p pr nx s x (Q : unit * astate -> Prop) : ltac2:(tb__ "0|0|
S0S30S8A1S59Vs;Vp;A2S32S8Vx;A2A3VQ;S2fS31S9S37S13SaS14Vs;A1Vp;S2cVx;Vpr;Vnx;A3A3Vs;A2A4A1S42S2eS31S9A2S29Vp;Vpr;Vnx;Vs;A4VQ;A3F_;F_;").
Proof.
  intros Hm H. unfold set_links. apply itok_bind. apply itok_get. cbn [fst snd].
  unfold MT in Hm. rewrite Hm. exact H.
Qed.

Lemma itok_get_head h s (Q : option sptr * astate -> Prop) :
  Q (match h with HActive sc => nth (Z.to_nat sc) (st_active s) None | HFreeMeta => st_free_meta_head s end, s) ->
  itok (get_head h s) Q.
Proof. intros H. unfold get_head. apply itok_bind. apply itok_get. cbn [fst snd]. destruct h; exact H. Qed.

Lemma itok_set_head h v s (Q : unit * astate -> Prop) :
  Q (tt, match h with
         | HActive sc => set_active (lupd (st_active s) (Z.to_nat sc) v) s
         | HFreeMeta => set_free_meta_head v s
         end) ->
  itok (set_head h v s) Q.
Proof. intros H. unfold set_head. destruct h; exact H. Qed.

Ltac mstep :=
  lazymatch goal with
  | |- itok (bind _ _ _) _ => apply itok_bind
  | |- itok (ret _ _) _ => apply itok_ret
  | |- itok (get _) _ => apply itok_get
  | |- itok (put _ _) _ => apply itok_put
  | |- itok (modify _ _) _ => apply itok_modify
  | |- itok (setm _ _ _) _ => apply itok_setm
  | |- itok (setslot _ _ _) _ => apply itok_setslot
  | |- itok (get_head _ _) _ => apply itok_get_head
  | |- itok (set_head _ _ _) _ => apply itok_set_head
  | |- itok (massert _ _ _) _ => apply itok_massert
  | |- itok (mcheck _ _ _) _ => apply itok_mcheck
  | |- itok (ask _ _) _ => apply itok_ask
  | |- itok (askz _ _) _ => apply itok_askz
  | |- itok (IRet _) _ => cbn [itok]
  end.

Ltac msimp := cbn beta iota delta [fst snd].

Ltac mrun := repeat (mstep; msimp).

Lemma sptr_eqb_refl p : ltac2:(tb__ "0|0|
S0S2dSdVp;Vp;A2S34A3").
Proof. destruct p; cbn. rewrite Nat.eqb_refl, Z.eqb_refl. reflexivity. Qed.

Lemma sptr_eqb_eq p q : ltac2:(tb__ "0|0|
S2S0S2dSdVp;Vq;A2S34A3S0S7Vp;Vq;A3A2").
Proof.
  destruct p as [r o], q as [r' o']; cbn. rewrite andb_true_iff, Nat.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; injection H; auto].
Qed.

Lemma sptr_eqb_neq p q : ltac2:(tb__ "0|0|
S2S0S2dSdVp;Vq;A2S36A3S3S0S7Vp;Vq;A3A1A2").
Proof.
  destruct (sptr_eqb p q) eqn:E.
  - apply sptr_eqb_eq in E. split; [discriminate | intros H; exfalso; exact (H E)].
  - split; [|reflexivity]. intros _ Heq. subst. rewrite sptr_eqb_refl in E. discriminate.
Qed.

Lemma sptr_eqb_sym p q : ltac2:(tb__ "0|0|
S0S2dSdVp;Vq;A2SdVq;Vp;A2A3").
Proof.
  destruct (sptr_eqb p q) eqn:E1, (sptr_eqb q p) eqn:E2; try reflexivity.
  - apply sptr_eqb_eq in E1. subst. rewrite sptr_eqb_refl in E2. discriminate.
  - apply sptr_eqb_eq in E2. subst. rewrite sptr_eqb_refl in E1. discriminate.
Qed.

Lemma sptr_eq_dec (p q : sptr) : ltac2:(tb__ "0|1|
S64S0S7Vp;Vq;A3M0S3G0A1A2").
Proof.
  destruct (sptr_eqb p q) eqn:E; [left; apply sptr_eqb_eq, E | right; apply sptr_eqb_neq, E].
Defined.

Lemma osptr_eqb_eq a b : ltac2:(tb__ "0|0|
S2S0S2dS26Va;Vb;A2S34A3S0S30S7A1Va;Vb;A3A2").
Proof.
  destruct a as [p|], b as [q|]; cbn; try (split; [discriminate|discriminate]); try (split; reflexivity).
  rewrite sptr_eqb_eq. split; [intros ->; reflexivity | intros H; injection H; auto].
Qed.

Lemma mlookup_mupdate_same l p x : ltac2:(tb__ "0|0|
S0S30S8A1SbSaVl;Vp;Vx;A3Vp;A2S32S8Vx;A2A3").
Proof.
  induction l as [|[q y] t IH]; cbn.
  - rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E; cbn; rewrite E; [reflexivity | exact IH].
Qed.

Lemma mlookup_mupdate_other l p q x : ltac2:(tb__ "0|0|
S3S0S7Vq;Vp;A3A1S0S30S8A1SbSaVl;Vp;Vx;A3Vq;A2SbVl;Vq;A2A3F_;").
Proof.
  intros Hne. induction l as [|[k y] t IH]; cbn.
  - destruct (sptr_eqb q p) eqn:E; [apply sptr_eqb_eq in E; congruence | reflexivity].
  - destruct (sptr_eqb p k) eqn:E; cbn.
    + apply sptr_eqb_eq in E. subst k.
      destruct (sptr_eqb q p) eqn:E2; [apply sptr_eqb_eq in E2; congruence | reflexivity].
    + destruct (sptr_eqb q k); [reflexivity | exact IH].
Qed.

Lemma mlookup_mupdate l p q x : ltac2:(tb__ "0|1|
S0S30S8A1M0SbSaVl;Vp;Vx;A3Vq;A2S2dG0L_;SdVq;Vp;A2S32S8Vx;A2SbVl;Vq;A2X2dx2A3").
Proof.
  destruct (sptr_eqb q p) eqn:E.
  - apply sptr_eqb_eq in E. subst. apply mlookup_mupdate_same.
  - apply mlookup_mupdate_other. apply sptr_eqb_neq, E.
Qed.

Lemma mlookup_In_keys l p x : ltac2:(tb__ "0|0|
S0S30S8A1SbVl;Vp;A2S32S8Vx;A2A3S52S7Vp;S56S2eS7S8A2S7S35S7S8A2Vl;A4A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [discriminate|].
  destruct (sptr_eqb p q) eqn:E; intros H.
  - left. symmetry. apply sptr_eqb_eq, E.
  - right. apply IH, H.
Qed.

Lemma mlookup_None_iff l p : ltac2:(tb__ "0|0|
S2S0S30S8A1SbVl;Vp;A2S3eS8A1A3S3S52S7Vp;S56S2eS7S8A2S7S35S7S8A2Vl;A4A3A1A2").
Proof.
  induction l as [|[q y] t IH]; cbn.
  - split; [intros _ [] | reflexivity].
  - destruct (sptr_eqb p q) eqn:E.
    + apply sptr_eqb_eq in E. subst. split; [discriminate | intros H; exfalso; apply H; left; reflexivity].
    + rewrite IH. apply sptr_eqb_neq in E. split; [intros H [Hq|Ht]; [congruence | exact (H Ht)] | intros H Ht; apply H; right; exact Ht].
Qed.

Lemma map_fst_mupdate_In l p x : ltac2:(tb__ "0|3|
S52S7Vp;S56S2eS7S8A2M0S7S35S7S8A2M1Vl;A4M2A3S0S3cS7A1S56G0S7G1SaVl;Vp;Vx;A3A4G2A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [intros [] |].
  destruct (sptr_eqb p q) eqn:E; cbn; [reflexivity|].
  intros [Hq | Ht]; [apply sptr_eqb_neq in E; congruence |]. rewrite IH by exact Ht. reflexivity.
Qed.

Lemma map_fst_mupdate_notIn l p x : ltac2:(tb__ "0|3|
S3S52S7Vp;S56S2eS7S8A2M0S7S35S7S8A2M1Vl;A4M2A3A1S0S3cS7A1S56G0S7G1SaVl;Vp;Vx;A3A4S3aS7G2S3bS7Vp;S3dS7A1A3A3A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [reflexivity|].
  destruct (sptr_eqb p q) eqn:E; cbn.
  - apply sptr_eqb_eq in E. subst. intros H. exfalso. apply H. left. reflexivity.
  - intros H. rewrite IH; [reflexivity|]. intros Ht. apply H. right. exact Ht.
Qed.

Lemma In_mupdate_iff l p x e : ltac2:(tb__ "0|1|
S53S7S56S2eS7S8A2M0S7S35S7S8A2Vl;A4A2S2S52G0Ve;SaVl;Vp;Vx;A3A3S6S0G0Ve;S2fS7S8Vp;Vx;A4A3S1S3S0S7S35S7S8Ve;A3Vp;A3A1S52G0Ve;Vl;A3A2A2A2F_;").
Proof.
  intros Hnd. induction l as [|[q y] t IH]; cbn.
  - split.
    + intros [H|[]]. left. symmetry. exact H.
    + intros [H|[_ []]]. left. symmetry. exact H.
  - inversion Hnd as [|q' t' Hq Ht]; subst.
    destruct (sptr_eqb p q) eqn:E; cbn.
    + apply sptr_eqb_eq in E. subst q. split.
      * intros [H|H]; [left; symmetry; exact H | right].
        split; [| right; exact H].
        intros Heq. apply Hq. rewrite <- Heq. apply in_map. exact H.
      * intros [H | [Hne [H|H]]]; [left; symmetry; exact H | | right; exact H].
        exfalso. apply Hne. rewrite <- H. reflexivity.
    + rewrite (IH Ht). apply sptr_eqb_neq in E. split.
      * intros [H | [H | [Hne H]]].
        -- right. split; [rewrite <- H; cbn; congruence | left; exact H].
        -- left. exact H.
        -- right. split; [exact Hne | right; exact H].
      * intros [H | [Hne [H | H]]].
        -- right. left. exact H.
        -- left. exact H.
        -- right. right. split; assumption.
Qed.

Lemma NoDup_app_single {T} (l : list T) (a : T) : ltac2:(tb__ "0|0|
S53VT;Vl;A2S3S52VT;Va;Vl;A3A1S53VT;S3aVT;Vl;S3bVT;Va;S3dVT;A1A3A3A2F_;F_;").
Proof.
  induction l as [|b t IH]; cbn; intros Hnd Hn.
  - constructor; [intros [] | constructor].
  - inversion Hnd; subst. constructor.
    + rewrite in_app_iff. cbn. intros [H | [H | []]]; [auto | subst; apply Hn; left; reflexivity].
    + apply IH; [assumption | intros H; apply Hn; right; exact H].
Qed.

Lemma NoDup_keys_mupdate l p x : ltac2:(tb__ "0|2|
S53S7S56S2eS7S8A2M0S7S35S7S8A2M1Vl;A4A2S53S7S56G0S7G1SaVl;Vp;Vx;A3A4A2F_;").
Proof.
  intros H. destruct (in_dec sptr_eq_dec p (map fst l)) as [Hi|Hn].
  - rewrite map_fst_mupdate_In by exact Hi. exact H.
  - rewrite map_fst_mupdate_notIn by exact Hn. apply NoDup_app_single; assumption.
Qed.

Lemma mlookup_of_In l p x : ltac2:(tb__ "0|1|
S53S7S56S2eS7S8A2M0S7S35S7S8A2Vl;A4A2S52G0S2fS7S8Vp;Vx;A4Vl;A3S0S30S8A1SbVl;Vp;A2S32S8Vx;A2A3F_;F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [intros _ [] |].
  intros Hnd [H|H]; inversion Hnd; subst.
  - injection H as -> ->. rewrite sptr_eqb_refl. reflexivity.
  - destruct (sptr_eqb p q) eqn:E.
    + apply sptr_eqb_eq in E. subst. exfalso. apply H2. apply (in_map fst) in H. exact H.
    + apply IH; assumption.
Qed.

Lemma In_of_mlookup l p x : ltac2:(tb__ "0|0|
S0S30S8A1SbVl;Vp;A2S32S8Vx;A2A3S52S2eS7S8A2S2fS7S8Vp;Vx;A4Vl;A3F_;").
Proof.
  induction l as [|[q y] t IH]; cbn; [discriminate|].
  destruct (sptr_eqb p q) eqn:E; intros H.
  - injection H as ->. apply sptr_eqb_eq in E. subst. left. reflexivity.
  - right. apply IH, H.
Qed.

Lemma used_metas_iff s g am : ltac2:(tb__ "0|0|
S53S7S5dVs;A1A2S2S52S2eS7SeA2S2fS7SeVg;Vam;A4S60Vs;A1A3S0S30S8A1S59Vs;Vg;A2S32S8S10Vam;A1A2A3A2F_;").
Proof.
  intros Hnd. unfold used_metas, MT, keys in *. split.
  - intros H. apply in_flat_map in H as [[p x] [Hin Hx]].
    destruct x; cbn in Hx; try (destruct Hx as [Hx|[]]); try contradiction.
    injection Hx as -> ->. apply mlookup_of_In; assumption.
  - intros H. apply in_flat_map. exists (g, MUsed am). split; [apply In_of_mlookup, H | left; reflexivity].
Qed.

Lemma length_lupd {X} (l : list X) i v : ltac2:(tb__ "0|0|
S0S39S33VX;S11VX;Vl;Vi;Vv;A4A2S33VX;Vl;A2A3").
Proof. revert i. induction l; intros [|i]; cbn; auto. Qed.

Lemma nth_lupd {X} (l : list X) i j v d : ltac2:(tb__ "0|0|
S0VX;S57VX;Vj;S11VX;Vl;Vi;Vv;A4Vd;A4S2dVX;L_;S38S63Vj;Vi;A2S62Vi;S33VX;Vl;A2A2A2Vv;S57VX;Vj;Vl;Vd;A4X2dx2A3").
Proof.
  revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
  - destruct (Nat.eqb j i); reflexivity.
  - rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
    unfold Nat.ltb. cbn. reflexivity.
Qed.

Lemma nth_error_lupd {X} (l : list X) i j v : ltac2:(tb__ "0|1|
S0S30VX;A1M0S54VX;S11VX;Vl;Vi;Vv;A4Vj;A3S2dG0L_;S38S63Vj;Vi;A2S62Vi;S33VX;Vl;A2A2A2S32VX;Vv;A2S54VX;Vl;Vj;A3X2dx2A3").
Proof.
  revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
  - destruct (Nat.eqb j i); reflexivity.
  - rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
    unfold Nat.ltb. cbn. reflexivity.
Qed.

Lemma length_zupd l i v : ltac2:(tb__ "0|0|
S0S39S33S41S18Vl;Vi;Vv;A3A2S33S41Vl;A2A3").
Proof. revert i. induction l; intros [|i]; cbn; auto. Qed.

Lemma nth_zupd l i j v d : ltac2:(tb__ "0|0|
S0S41S57S41Vj;S18Vl;Vi;Vv;A3Vd;A4S2dS41L_;S38S63Vj;Vi;A2S62Vi;S33S41Vl;A2A2A2Vv;S57S41Vj;Vl;Vd;A4X2dx2A3").
Proof.
  revert i j. induction l as [|h t IH]; intros [|i] [|j]; cbn; try reflexivity.
  - destruct (Nat.eqb j i); reflexivity.
  - rewrite IH. destruct (Nat.eqb j i); cbn; [|reflexivity].
    unfold Nat.ltb. cbn. reflexivity.
Qed.

Lemma znth_zset i j v l : ltac2:(tb__ "0|1|
S43Z0M0Vi;A2S43G0Vj;A2S0S41S16Vj;S17Vi;Vv;Vl;A3A2S2dS41L_;S38S48Vj;Vi;A2S4eVi;S4fS33S41Vl;A2A1A2A2Vv;S16Vj;Vl;A2X2dx2A3F_;F_;").
Proof.
  intros Hi Hj. unfold znth, zset. rewrite nth_zupd.
  replace (Nat.eqb (Z.to_nat j) (Z.to_nat i)) with (j =? i).
  2:{ destruct (j =? i) eqn:E; symmetry.
      - apply Nat.eqb_eq. apply Z.eqb_eq in E. subst. reflexivity.
      - apply Nat.eqb_neq. apply Z.eqb_neq in E. intros H. apply E. lia. }
  replace (Nat.ltb (Z.to_nat i) (length l)) with (i <? Z.of_nat (length l)).
  2:{ destruct (i <? Z.of_nat (length l)) eqn:E; symmetry.
      - apply Nat.ltb_lt. apply Z.ltb_lt in E. lia.
      - apply Nat.ltb_ge. apply Z.ltb_ge in E. lia. }
  reflexivity.
Qed.

Lemma length_zset i v l : ltac2:(tb__ "0|0|
S0S39S33S41S17Vi;Vv;Vl;A3A2S33S41Vl;A2A3").
Proof. apply length_zupd. Qed.

Lemma In_zseq lo n x : ltac2:(tb__ "0|0|
S2S52S41Vx;S5cVlo;Vn;A2A3S1S43Vlo;Vx;A2S45Vx;S47Vlo;Vn;A2A2A2A2").
Proof.
  unfold zseq. rewrite in_map_iff. split.
  - intros [k [<- Hk]]. apply in_seq in Hk. lia.
  - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma forallb_zseq_iff f lo n : ltac2:(tb__ "0|0|
S2S0S2dS55S41Vf;S5cVlo;Vn;A2A3S34A3S41S1S43Vlo;R1A2S45R1S47Vlo;Vn;A2A2A2S0S2dVf;R2A1S34A3F_;Fx;A2").
Proof.
  rewrite forallb_forall. split; intros H x Hx; apply H; apply In_zseq; exact Hx.
Qed.

Lemma nth_repeat' {X} (x d : X) n i : ltac2:(tb__ "0|0|
S0VX;S57VX;Vi;S58VX;Vx;Vn;A3Vd;A4S2dVX;L_;S62Vi;Vn;A2Vx;Vd;X2dx2A3").
Proof.
  revert i. induction n as [|n IH]; intros [|i]; cbn; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma ones_eq k : ltac2:(tb__ "0|0|
S0S41S12Vk;A1S50S47Vk;Z1A2A1A3").
Proof. unfold ones. rewrite Z.ones_equiv. lia. Qed.

Lemma testbit_ones k i : ltac2:(tb__ "0|1|
S43Z0M0Vk;A2S0S2dS44S12Vk;A1Vi;A2S38S4bG0Vi;A2S4bVi;Vk;A2A2A3F_;").
Proof.
  intros Hk. rewrite ones_eq, Z.testbit_ones by lia.
  destruct (0 <=? i); cbn; [|reflexivity].
  destruct (i <? k + 1) eqn:E1, (i <=? k) eqn:E2; try reflexivity.
  - apply Z.ltb_lt in E1. apply Z.leb_gt in E2. lia.
  - apply Z.ltb_ge in E1. apply Z.leb_le in E2. lia.
Qed.

Lemma ones_nonneg k : ltac2:(tb__ "0|1|
S43Z0M0Vk;A2S43G0S12Vk;A1A2F_;").
Proof. intros. unfold ones. assert (0 < 2 ^ (k + 1)) by (apply Z.pow_pos_nonneg; lia). lia. Qed.

Lemma bit_eq k : ltac2:(tb__ "0|0|
S0S41ScVk;A1S49Z2Vk;A2A3").
Proof. reflexivity. Qed.

Lemma testbit_bit k i : ltac2:(tb__ "0|0|
S43Z0Vk;A2S0S2dS44ScVk;A1Vi;A2S48Vk;Vi;A2A3F_;").
Proof. intros. unfold bit. apply Z.pow2_bits_eqb. assumption. Qed.

Lemma testbit_neg_idx a i : ltac2:(tb__ "0|0|
S45Vi;Z0A2S0S2dS44Va;Vi;A2S36A3F_;").
Proof. intros. destruct i; try lia. reflexivity. Qed.

Lemma bits_inj_nonneg a b : ltac2:(tb__ "0|0|
S41S43Z0R1A2S0S2dS44Va;R2A2S44Vb;R2A2A3F_;Fi;S0S41Va;Vb;A3F_;").
Proof. intros H. apply Z.bits_inj'. exact H. Qed.

Lemma add_bit_lor m k : ltac2:(tb__ "0|1|
S43Z0Vk;A2S0S2dS44Vm;Vk;A2S36A3S0S41S47Vm;ScVk;A1M0A2S4dVm;G0A2A3F_;F_;").
Proof.
  intros Hk Hb. rewrite <- Z.lxor_lor.
  - apply Z.add_nocarry_lxor. apply bits_inj_nonneg. intros i Hi.
    rewrite Z.land_spec, testbit_bit, Z.bits_0 by lia.
    destruct (Z.eq_dec k i); [subst; rewrite Hb; reflexivity|].
    replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
  - apply bits_inj_nonneg. intros i Hi.
    rewrite Z.land_spec, testbit_bit, Z.bits_0 by lia.
    destruct (Z.eq_dec k i); [subst; rewrite Hb; reflexivity|].
    replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.

Lemma sub_bit_ldiff m k : ltac2:(tb__ "0|1|
S43Z0Vk;A2S0S2dS44Vm;Vk;A2S34A3S0S41S51Vm;ScVk;A1M0A2S4cVm;G0A2A3F_;F_;").
Proof.
  intros Hk Hb.
  assert (E : Z.ldiff m (bit k) + bit k = m).
  { rewrite add_bit_lor by (try lia; rewrite Z.ldiff_spec, testbit_bit, Z.eqb_refl by lia; cbn; rewrite andb_false_r; reflexivity).
    apply bits_inj_nonneg. intros i Hi. rewrite Z.lor_spec, Z.ldiff_spec, testbit_bit by lia.
    destruct (Z.eq_dec k i); [subst; rewrite Hb, Z.eqb_refl; reflexivity|].
    replace (k =? i) with false by (symmetry; apply Z.eqb_neq; lia). cbn.
    rewrite andb_true_r, orb_false_r. reflexivity. }
  lia.
Qed.

Lemma land_double a b : ltac2:(tb__ "0|1|
S0S41S4aS46Z2M0Va;A2S46G0Vb;A2A2S46G0S4aVa;Vb;A2A2A3").
Proof.
  apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite !Z.testbit_even_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_even_succ by lia. rewrite Z.land_spec. reflexivity.
Qed.

Lemma lowbit_double a : ltac2:(tb__ "0|1|
S0S41SfS46Z2M0Va;A2A1S46G0SfVa;A1A2A3").
Proof. unfold lowbit. replace (- (2 * a)) with (2 * (- a)) by lia. apply land_double. Qed.

Lemma lowbit_odd a : ltac2:(tb__ "0|1|
S0S41SfS47S46Z2Va;A2Z1M0A2A1G0A3").
Proof.
  unfold lowbit. apply bits_inj_nonneg. intros i Hi. rewrite Z.land_spec.
  replace (- (2 * a + 1)) with (2 * (- a - 1) + 1) by lia.
  destruct (Z.eq_dec i 0) as [->|Hne].
  - rewrite !Z.testbit_odd_0. reflexivity.
  - replace i with (Z.succ (i - 1)) by lia.
    rewrite !Z.testbit_odd_succ by lia.
    replace (- a - 1) with (Z.lnot a) by (unfold Z.lnot; lia).
    rewrite Z.lnot_spec by lia.
    replace (Z.testbit 1 (Z.succ (i - 1))) with false
      by (symmetry; apply Z.bits_above_log2; [lia | cbn; lia]).
    destruct (Z.testbit a (i - 1)); reflexivity.
Qed.

Lemma lowbit_spec m : ltac2:(tb__ "0|2|
S45Z0M0Vm;A2S5S41S41S1S43G0R1A2M1S1S0S41SfVm;A1ScR1A1A3S1S0S2dS44Vm;R1A2S34A3S41S1G1S45R1R2A2A2S0S2dS44Vm;R2A2S36A3F_;Fj;A2A2A2Lk;A2F_;").
Proof.
  intros Hm.
  remember (Z.to_nat m) as n eqn:En. revert m Hm En.
  induction n as [n IH] using (well_founded_induction Wf_nat.lt_wf); intros m Hm En.
  destruct (Z.Even_or_Odd m) as [[a Ha] | [a Ha]].
  - subst m. assert (0 < a) by lia.
    destruct (IH (Z.to_nat a) ltac:(lia) a ltac:(lia) eq_refl) as (k & Hk & Hl & Hb & Hlow).
    exists (k + 1). split; [lia|]. split.
    { rewrite lowbit_double, Hl. unfold bit. rewrite Z.pow_add_r by lia. lia. }
    split.
    { replace (k + 1) with (Z.succ k) by lia. rewrite Z.testbit_even_succ by lia. exact Hb. }
    intros j Hj. destruct (Z.eq_dec j 0) as [->|Hne].
    + apply Z.testbit_even_0.
    + replace j with (Z.succ (j - 1)) by lia. rewrite Z.testbit_even_succ by lia. apply Hlow. lia.
  - subst m. exists 0. split; [lia|]. split; [apply lowbit_odd|]. split.
    + apply Z.testbit_odd_0.
    + intros j Hj. lia.
Qed.

Lemma ctz32_bit k : ltac2:(tb__ "0|0|
S43Z0Vk;A2S0S41S1cScVk;A1A1Vk;A3F_;").
Proof.
  intros Hk. unfold ctz32.
  pose proof (lowbit_spec (bit k) ltac:(unfold bit; apply Z.pow_pos_nonneg; lia)) as (k' & Hk' & Hl & Hb & _).
  rewrite Hl. rewrite testbit_bit in Hb by lia. apply Z.eqb_eq in Hb. subst k'.
  unfold bit. apply Z.log2_pow2. exact Hk.
Qed.

Lemma testbit_false_of_lt m n i : ltac2:(tb__ "0|1|
S1S43Z0M0Vm;A2S45Vm;S49Z2Vn;A2A2A2S1S43G0Vn;A2S43Vn;Vi;A2A2S0S2dS44Vm;Vi;A2S36A3F_;F_;").
Proof.
  intros Hm Hi. destruct (Z.eq_dec m 0) as [->|Hne]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|].
  assert (Z.log2 m < n) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lt_pow2_of_testbit m n : ltac2:(tb__ "0|1|
S43Z0M0Vm;A2S43G0Vn;A2S41S43Vn;R1A2S0S2dS44Vm;R2A2S36A3F_;Fi;S45Vm;S49Z2Vn;A2A2F_;F_;F_;").
Proof.
  intros Hm Hn H. destruct (Z.eq_dec m 0) as [->|Hne]; [apply Z.pow_pos_nonneg; lia|].
  destruct (Z_lt_dec m (2 ^ n)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
  assert (Hl : n <= Z.log2 m) by (apply Z.log2_le_pow2; lia).
  pose proof (Z.bit_log2 m ltac:(lia)) as Hb. rewrite H in Hb; [discriminate | exact Hl].
Qed.
