(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import RunConst ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps ProgA HarnessP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.BothW Require Import BImg AProto AU_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ITree.Exc.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Lemma iall_mono : forall {N R} (P Q : R -> Prop) (t : itree N R), (forall r, P r -> Q r) -> iall P t -> iall Q t.
Proof. intros N R P Q t H. induction t as [r|n k IH]; cbn; [apply H| intros Hk rsp; apply IH; apply Hk]. Qed.

Lemma iall_bind : forall {N A B} (P1 : A -> Prop) (P : B -> Prop) (t : itree N A) (g : A -> itree N B),
  iall P1 t -> (forall x, P1 x -> iall P (g x)) -> iall P (bind N t g).
Proof. intros N A B P1 P t g. induction t as [r|n k IH]; cbn; intros H Hg; [exact (Hg r H)| intros rsp; apply IH; [apply H| exact Hg]]. Qed.

Lemma iall_impl : forall {N R} (A : Prop) (P : R -> Prop) (t : itree N R), (A -> iall P t) -> iall (fun r => A -> P r) t.
Proof. intros N R A P t. induction t as [r|n k IH]; cbn; intros H; [exact H| intros rsp; apply IH; intros a; exact (H a rsp)]. Qed.

Lemma iall_and : forall {N R} (P Q : R -> Prop) (t : itree N R), iall P t -> iall Q t -> iall (fun r => P r /\ Q r) t.
Proof. intros N R P Q t. induction t as [r|n k IH]; cbn; intros H1 H2; [split; assumption| intros rsp; apply IH; [apply H1| apply H2]]. Qed.

Lemma iall_true : forall {N R} (t : itree N R), iall (fun _ => True) t.
Proof. intros N R t. induction t as [r|n k IH]; cbn; [exact I| exact IH]. Qed.

Lemma sallA_impl : forall {R} (A : Prop) (P : R -> Prop) (t : AM R), (A -> sallA P t) -> sallA (fun r => A -> P r) t.
Proof.
  intros R A P t. induction t as [r|e k IH]; cbn; [auto|].
  destruct e; try exact (fun _ => I); intros G z; apply IH; intros HF; exact (G HF z).
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition mleaves {A} (P : A -> APS -> Prop) (c : MA A) (s : APS) : Prop :=
  iall (eprop (fun p : A * APS => P (fst p) (snd p))) (c s).

Lemma mleaves_mono : forall {A} (P Q : A -> APS -> Prop) c s, (forall a s', P a s' -> Q a s') -> mleaves P c s -> mleaves Q c s.
Proof. intros A P Q c s H. unfold mleaves. apply iall_mono. intros [|p]; cbn; [auto| apply H]. Qed.

Lemma mleaves_ret : forall {A} (P : A -> APS -> Prop) (a : A) s, P a s -> mleaves P (mret a) s.
Proof. intros. exact H. Qed.

Lemma mleaves_unr : forall {A} (P : A -> APS -> Prop) s, mleaves P (munr (A:=A)) s.
Proof. intros. exact I. Qed.

Lemma mleaves_bind : forall {A B} (P1 : A -> APS -> Prop) (P : B -> APS -> Prop) (ma : MA A) (f : A -> MA B) s,
  mleaves P1 ma s -> (forall a s', P1 a s' -> mleaves P (f a) s') -> mleaves P (mbind ma f) s.
Proof.
  intros A B P1 P ma f s H Hf. unfold mleaves, mbind, ebind in *.
  eapply iall_bind; [exact H|]. intros [|[a s']]; cbn; [intros _; exact I| intros Ha; exact (Hf a s' Ha)].
Qed.

Lemma mleaves_get : forall (P : APS -> APS -> Prop) s, P s s -> mleaves P mget s.
Proof. intros. exact H. Qed.

Lemma mleaves_upd : forall (P : unit -> APS -> Prop) f s, P tt (f s) -> mleaves P (mupd f) s.
Proof. intros. exact H. Qed.

(* [comment removed for export] *)
Lemma mleaves_alift_bind : forall {R B} (t : AM R) (f : R -> MA B) s (PR : R -> Prop) (P : B -> APS -> Prop),
  sallA PR t -> (forall r, PR r -> mleaves P (f r) s) -> mleaves P (mbind (alift t) f) s.
Proof.
  intros R B t f s PR P HS Hf. unfold mleaves, mbind, alift, ebind in *.
  apply (iall_bind (eprop (fun p : R * APS => PR (fst p) /\ snd p = s))).
  - apply (iall_bind (eprop PR)); [exact (sallA_embed (aps_atop s) PR t HS)|].
    intros [|r] Hr; cbn; [exact I|]. split; [exact Hr| reflexivity].
  - intros [|[r s']]; cbn; [intros _; exact I|]. intros [Hr ->]. exact (Hf r Hr).
Qed.

(* [comment removed for export] *)
Lemma implMA_leaves : forall {A} RNG (c : MA A) s (Q : A -> APS -> footprint -> machine_state -> Prop) (P : A -> APS -> Prop) ms,
  implMA RNG c s Q ms -> mleaves P c s -> implMA RNG c s (fun a s' RNG' ms' => Q a s' RNG' ms' /\ P a s') ms.
Proof.
  intros A RNG c s Q P ms H HP. unfold implMA in *.
  pose proof (implF_iall _ _ _ _ _ _ _ _ _ H HP) as H1.
  eapply implF_mono; [exact H1|]. intros [|[a s']] RNG' ms'; cbn; [auto| intros [X Y]; split; assumption].
Qed.

(* [comment removed for export] *)
Lemma implMA_with_leaves : forall {A} RNG (c : MA A) s (Q : A -> APS -> footprint -> machine_state -> Prop) (P : A -> APS -> Prop) ms,
  mleaves P c s -> implMA RNG c s (fun a s' RNG' ms' => P a s' -> Q a s' RNG' ms') ms -> implMA RNG c s Q ms.
Proof.
  intros A RNG c s Q P ms HP H. eapply implMA_mono; [exact (implMA_leaves RNG c s _ P ms H HP)|]. cbv beta. intros a s' RNG' ms' [X Y]. exact (X Y).
Qed.

(* [comment removed for export] *)
Definition DK (k : Z) (s s' : APS) : Prop :=
  (AFRESH (aps_m s) -> AFRESH (aps_m s') /\ dk (aps_m s) <= dk (aps_m s') <= dk (aps_m s) + k)
  /\ aps_cl s' = aps_cl s /\ aps_rest s' = aps_rest s.

Lemma DK_refl : forall s, DK 0 s s.
Proof. intros s. split; [intros H; split; [exact H| lia]| split; reflexivity]. Qed.

Lemma DK_trans : forall k1 k2 s1 s2 s3, DK k1 s1 s2 -> DK k2 s2 s3 -> DK (k1 + k2) s1 s3.
Proof.
  intros k1 k2 s1 s2 s3 (F1 & C1 & R1) (F2 & C2 & R2). split; [| split; congruence].
  intros H. destruct (F1 H) as [H2 D1]. destruct (F2 H2) as [H3 D2]. split; [exact H3| lia].
Qed.

Lemma DK_le : forall k k' s s', k <= k' -> DK k s s' -> DK k' s s'.
Proof. intros k k' s s' Hk (F & C & R). split; [| split; assumption]. intros H. destruct (F H) as [H1 D]. split; [exact H1| lia]. Qed.

Definition mpresk {A} (k : Z) (c : MA A) : Prop := forall s, mleaves (fun _ s' => DK k s s') c s.

Lemma mpresk_ret : forall {A} (a : A), mpresk 0 (mret a).
Proof. intros A a s. apply mleaves_ret. apply DK_refl. Qed.

Lemma mpresk_le : forall {A} k k' (c : MA A), k <= k' -> mpresk k c -> mpresk k' c.
Proof. intros A k k' c Hk H s. eapply mleaves_mono; [| exact (H s)]. intros a s' D. exact (DK_le k k' s s' Hk D). Qed.

Lemma mpresk_bind : forall {A B} k1 k2 (ma : MA A) (f : A -> MA B),
  mpresk k1 ma -> (forall a, mpresk k2 (f a)) -> mpresk (k1 + k2) (mbind ma f).
Proof.
  intros A B k1 k2 ma f H Hf s. eapply mleaves_bind; [exact (H s)|]. intros a s' D1.
  eapply mleaves_mono; [| exact (Hf a s')]. intros b s'' D2. exact (DK_trans k1 k2 s s' s'' D1 D2).
Qed.

Lemma mpresk_unr_bind : forall {A B} k (f : A -> MA B), mpresk k (mbind (munr (A:=A)) f).
Proof. intros A B k f s. exact I. Qed.

(* [comment removed for export] *)
Lemma amalloc_M_dk : forall n, mpresk 0 (amalloc_M n).
Proof.
  intros n s. unfold amalloc_M. apply (mleaves_bind (fun a s' => a = s /\ s' = s)); [split; reflexivity|].
  intros a s' [-> ->].
  apply (mleaves_alift_bind _ _ _ (fun r => AFRESH (aps_m s) -> AFRESH (fst r) /\ dk (fst r) = dk (aps_m s))).
  { apply sallA_impl. intros HF. exact (amalloc_fresh_dk _ _ _ _ HF). }
  intros r Hr. apply (mleaves_bind (fun _ s' => s' = aset_m (fst r) s)); [apply mleaves_upd; reflexivity|].
  intros [] s' ->. apply mleaves_ret. unfold DK. cbn [aps_m aset_m aps_cl]. split; [| split; [reflexivity| reflexivity]].
  intros HF. destruct (Hr HF) as [H1 H2]. split; [exact H1| lia].
Qed.

Lemma afree_M_dk : forall p, mpresk 1 (afree_M p).
Proof.
  intros p s. unfold afree_M. apply (mleaves_bind (fun a s' => a = s /\ s' = s)); [split; reflexivity|].
  intros a s' [-> ->].
  apply (mleaves_alift_bind _ _ _ (fun r => AFRESH (aps_m s) -> AFRESH r /\ dk (aps_m s) <= dk r <= dk (aps_m s) + 1)).
  { apply sallA_impl. intros HF. exact (afree_fresh_dk _ _ HF). }
  intros r Hr. apply mleaves_upd. unfold DK. cbn [aps_m aset_m aps_cl]. split; [| split; [reflexivity| reflexivity]].
  intros HF. exact (Hr HF).
Qed.

(* [comment removed for export] *)
Notation opnewA := (HarnessP.opnew amalloc_M (new_handlerA AAllocAsan)).

Lemma opnew_dk : forall n, mpresk 0 (opnewA n).
Proof.
  intros n. unfold HarnessP.opnew. cbv zeta. change 0 with (0 + 0). apply mpresk_bind; [apply amalloc_M_dk|].
  intros [p|]; [apply mpresk_ret| apply mpresk_unr_bind].
Qed.

Lemma opdelete_dk : forall p, mpresk 1 (HarnessP.opdelete afree_M p).
Proof. intros p. apply afree_M_dk. Qed.

Lemma odelete_dk : forall b, mpresk 1 (HarnessP.odelete afree_M b).
Proof. intros [p|]; [apply opdelete_dk| apply (mpresk_le 0); [lia| apply mpresk_ret]]. Qed.

Lemma doc_allocate_dk : forall len, mpresk 0 (HarnessP.doc_allocate amalloc_M (new_handlerA AAllocAsan) len).
Proof.
  intros len. unfold HarnessP.doc_allocate. change 0 with (0 + (0 + 0)).
  apply mpresk_bind; [apply opnew_dk| intros sb; apply mpresk_bind; [apply opnew_dk| intros tp; apply mpresk_ret]].
Qed.

Lemma impl_create_dk : forall len, mpresk 0 (HarnessP.impl_create amalloc_M (new_handlerA AAllocAsan) len).
Proof.
  intros len. unfold HarnessP.impl_create, HarnessP.impl_set_capacity, HarnessP.impl_set_max_depth. change 0 with (0 + (0 + (0 + 0))).
  apply mpresk_bind; [apply opnew_dk| intros im]. apply mpresk_bind; [apply opnew_dk| intros si].
  apply mpresk_bind; [change 0 with (0 + (0 + 0)); apply mpresk_bind; [apply opnew_dk| intros oc; apply mpresk_bind; [apply opnew_dk| intros ia; apply mpresk_ret]]|].
  intros [oc ia]. apply mpresk_ret.
Qed.

Lemma padded_alloc_dk : forall len, mpresk 0 (HarnessP.padded_alloc amalloc_M (new_handlerA AAllocAsan) len).
Proof.
  intros len. unfold HarnessP.padded_alloc. destruct (HarnessP.copy_made len); [| apply mpresk_ret].
  change 0 with (0 + 0). apply mpresk_bind; [apply opnew_dk| intros p; apply mpresk_ret].
Qed.

Lemma parse_impl_dk : forall data, mpresk 1 (HarnessP.parse_impl amalloc_M afree_M (new_handlerA AAllocAsan) data).
Proof.
  intros data. unfold HarnessP.parse_impl, HarnessP.root_copy. destruct (SjStage1.root_number_alloc data) as [n|].
  - change 1 with (0 + 1). apply mpresk_bind; [apply opnew_dk| intros c; apply opdelete_dk].
  - apply (mpresk_le 0); [lia| apply mpresk_ret].
Qed.

Lemma parse_into_doc_dk : forall data, mpresk 1 (HarnessP.parse_into_doc amalloc_M afree_M (new_handlerA AAllocAsan) data).
Proof.
  intros data. unfold HarnessP.parse_into_doc. cbv zeta. change 1 with (0 + (0 + (0 + (1 + 0)))).
  apply mpresk_bind; [apply doc_allocate_dk| intros dd]. apply mpresk_bind; [apply impl_create_dk| intros ii].
  apply mpresk_bind; [apply padded_alloc_dk| intros lb]. apply mpresk_bind; [| intros _; apply mpresk_ret].
  destruct lb; [apply parse_impl_dk| apply (mpresk_le 0); [lia| apply mpresk_ret]].
Qed.

Lemma parser_dtor_dk : forall b, mpresk 7 (HarnessP.parser_dtor afree_M b).
Proof.
  intros [[[sb tp] [[[im si] oc] ia]] lb]. unfold HarnessP.parser_dtor, HarnessP.doc_dtor, HarnessP.impl_dtor.
  change 7 with (1 + ((1 + 1) + (1 + (1 + (1 + 1))))).
  apply mpresk_bind; [apply odelete_dk| intros _]. apply mpresk_bind; [apply mpresk_bind; [apply opdelete_dk| intros _; apply opdelete_dk]| intros _].
  apply mpresk_bind; [apply opdelete_dk| intros _]. apply mpresk_bind; [apply opdelete_dk| intros _].
  apply mpresk_bind; [apply opdelete_dk| intros _]. apply opdelete_dk.
Qed.

(* [comment removed for export] *)
Theorem fuzz_oneA_dk : forall data, mpresk 8 (fuzz_oneA AAllocAsan data).
Proof.
  intros data. unfold fuzz_oneA, HarnessP.fuzz_one. change 8 with (1 + (7 + 0)).
  apply mpresk_bind; [apply parse_into_doc_dk| intros b]. apply mpresk_bind; [apply parser_dtor_dk| intros _; apply mpresk_ret].
Qed.

End CANSEC1.
