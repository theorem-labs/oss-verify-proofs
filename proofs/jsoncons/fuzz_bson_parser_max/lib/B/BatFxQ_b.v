(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Definition art_qbatch : Type := (Z * list Z * Z)%type.
Definition qb_addr (b : art_qbatch) : Z := fst (fst b).
Definition qb_items (b : art_qbatch) : list Z := snd (fst b).
Definition qb_size (b : art_qbatch) : Z := snd b.

Definition art_qhead (bs : list art_qbatch) : Z := match bs with [] => 0 | b :: _ => qb_addr b end.

(* [comment removed for export] *)
Definition art_qrec (M : word -> option byte) (b : art_qbatch) : Prop :=
  (length (qb_items b) <= 1021)%nat
  /\ cellA M (qb_addr b + 16) 8 (Z.of_nat (length (qb_items b)))
  /\ cellA M (qb_addr b + 8) 8 (qb_size b)
  /\ (forall j it, nth_error (qb_items b) j = Some it -> cellA M (qb_addr b + 24 + 8 * Z.of_nat j) 8 it).

Fixpoint art_qlist (M : word -> option byte) (bs : list art_qbatch) (first last : Z) : Prop :=
  match bs with
  | [] => first = 0
  | b :: r =>
      first = qb_addr b /\ art_qrec M b
      /\ (match r with [] => last = qb_addr b | _ => True end)
      /\ cellA M (qb_addr b) 8 (art_qhead r)
      /\ art_qlist M r (art_qhead r) last
  end.

Definition art_qbytes (bs : list art_qbatch) : Z := fold_right (fun b z => qb_size b + z) 0 bs.

Lemma art_qbytes_app : forall a b, art_qbytes (a ++ b) = art_qbytes a + art_qbytes b.
Proof. intros a b. unfold art_qbytes. induction a as [|x a IH]; cbn [app fold_right]; lia. Qed.

Lemma art_qlist_first : forall M bs f l, art_qlist M bs f l -> f = art_qhead bs.
Proof. intros M [|b r] f l H; cbn in *; [exact H | tauto]. Qed.

(* [comment removed for export] *)
Definition art_qgeo (W : list (Z * Z)) (b : art_qbatch) : Prop := 0 <= qb_addr b /\ qb_addr b + 8192 < 2 ^ 64 /\ art_gap W (qb_addr b) 8192.

Lemma art_qrec_tr : forall W M M' b, art_agree W M M' -> art_qgeo W b -> art_qrec M b -> art_qrec M' b.
Proof.
  intros W M M' b A (G0 & G1 & G) (L & C1 & C2 & CI). unfold art_qrec.
  split; [exact L|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C1]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C2]|].
  intros j it Hj. assert (Hjl : (j < length (qb_items b))%nat) by (apply nth_error_Some; congruence).
  apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact (CI j it Hj)].
Qed.

Lemma art_qlist_tr : forall W M M' bs f l, art_agree W M M' -> Forall (art_qgeo W) bs -> art_qlist M bs f l -> art_qlist M' bs f l.
Proof.
  intros W M M' bs. induction bs as [|b r IH]; intros f l A F H; cbn [art_qlist] in *; [exact H|].
  inversion F as [|? ? Fb Fr]; subst. destruct H as (Ef & R & El & Cn & Hr).
  split; [exact Ef|]. split; [exact (art_qrec_tr W M M' b A Fb R)|]. split; [exact El|].
  split; [destruct Fb as (G0 & G1 & G); apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact Cn]|].
  exact (IH _ _ A Fr Hr).
Qed.

(* [comment removed for export] *)
Lemma art_qlist_last : forall M bs f l, bs <> [] -> art_qlist M bs f l -> qb_addr (last bs (0, [], 0)) = l /\ cellA M l 8 0.
Proof.
  intros M bs. induction bs as [|b r IH]; intros f l NE H; [congruence|].
  cbn [art_qlist] in H. destruct H as (Ef & R & El & Cn & Hr).
  destruct r as [|b' r'].
  - cbn [last]. split; [symmetry; exact El | rewrite El; exact Cn].
  - change (last (b :: b' :: r') (0, [], 0)) with (last (b' :: r') (0, [], 0)). apply (IH _ _ ltac:(discriminate) Hr).
Qed.

(* [comment removed for export] *)
Fixpoint art_qsep (bs : list art_qbatch) : Prop :=
  match bs with
  | [] => True
  | b :: r => 0 <= qb_addr b /\ qb_addr b + 8192 < 2 ^ 64 /\ Forall (fun b' => apart (qb_addr b) 8192 (qb_addr b') 8192) r /\ art_qsep r
  end.

Lemma art_qsep_rng : forall bs b, art_qsep bs -> In b bs -> 0 <= qb_addr b /\ qb_addr b + 8192 < 2 ^ 64.
Proof. induction bs as [|x r IH]; intros b S Hin; cbn in *; [contradiction|]. destruct S as (S0 & S1 & S2 & S3). destruct Hin as [<-|Hin]; [lia|exact (IH b S3 Hin)]. Qed.

Lemma art_qsep_app_r : forall a b, art_qsep (a ++ b) -> art_qsep b.
Proof. induction a as [|x a IH]; intros b S; cbn [app art_qsep] in *; [exact S|]. apply IH. tauto. Qed.

Lemma art_last_in : forall (A : Type) (l : list A) d, l <> [] -> In (last l d) l.
Proof. intros A l d NE. destruct (exists_last NE) as (l' & x & ->). rewrite last_last. apply in_or_app. right. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_qlist_splice : forall M M' gbs tbs gf gl tf tl,
  gbs <> [] -> art_qlist M gbs gf gl -> art_qlist M tbs tf tl ->
  art_agree [(gl, 8)] M M' -> cellA M' gl 8 tf -> art_qsep (gbs ++ tbs) ->
  art_qlist M' (gbs ++ tbs) gf (match tbs with [] => gl | _ => tl end).
Proof.
  intros M M' gbs tbs gf gl tf tl NEg Hg Ht A Cgl S.
  revert gf Hg S. induction gbs as [|b r IH]; intros gf Hg S; [congruence|].
  cbn [app art_qsep] in S. destruct S as (S0 & S1 & S2 & S3).
  cbn [art_qlist] in Hg. destruct Hg as (Ef & R & El & Cn & Hr).
  destruct r as [|b' r'].
  - (* [comment removed for export] *)
    cbn [app] in *. subst gl. cbn [art_qlist]. split; [exact Ef|].
    split.
    { destruct R as (L & C1 & C2 & CI). unfold art_qrec. split; [exact L|].
      assert (T : forall a (n : nat) v, qb_addr b + 8 <= a -> a + Z.of_nat n <= qb_addr b + 8192 -> cellA M a n v -> cellA M' a n v).
      { intros a n v Ha Hn C. apply (art_cell_tr _ M M' _ _ _ A); [|lia|lia|exact C]. cbn [art_gap fst snd]. split; [unfold apart; lia|exact I]. }
      split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|].
      intros j it Hj. assert (Hjl : (j < length (qb_items b))%nat) by (apply nth_error_Some; congruence). apply T; [lia|cbn; lia|exact (CI j it Hj)]. }
    split; [destruct tbs; [reflexivity|exact I]|].
    rewrite (art_qlist_first M tbs tf tl Ht) in Cgl. split; [exact Cgl|].
    rewrite <- (art_qlist_first M tbs tf tl Ht).
    assert (Ht' : art_qlist M' tbs tf tl).
    { apply (art_qlist_tr [(qb_addr b, 8)] M M' tbs tf tl A); [|exact Ht].
      apply Forall_forall. intros x Hx. destruct (art_qsep_rng tbs x S3 Hx) as (X0 & X1). split; [exact X0|]. split; [exact X1|].
      cbn [art_gap fst snd]. split; [|exact I]. pose proof (proj1 (Forall_forall _ _) S2 x Hx) as AP. unfold apart in *. lia. }
    destruct tbs; [cbn [art_qlist] in *; exact Ht'|exact Ht'].
  - assert (Egl : qb_addr (last (b' :: r') (0, [], 0)) = gl) by (apply (art_qlist_last M (b' :: r') _ gl ltac:(discriminate) Hr)).
    assert (APb : apart (qb_addr b) 8192 gl 8).
    { rewrite <- Egl. pose proof (proj1 (Forall_forall _ _) S2 (last (b' :: r') (0, [], 0)) ltac:(apply in_or_app; left; apply art_last_in; discriminate)) as AP. unfold apart in *. lia. }
    change ((b :: b' :: r') ++ tbs) with (b :: ((b' :: r') ++ tbs)). cbn [art_qlist].
    split; [exact Ef|].
    split; [apply (art_qrec_tr [(gl, 8)] M M' b A); [split; [exact S0|]; split; [exact S1|]; cbn [art_gap fst snd]; split; [exact APb|exact I]|exact R]|].
    split; [exact I|].
    split; [apply (art_cell_tr _ M M' _ _ _ A); [cbn [art_gap fst snd]; split; [unfold apart in *; cbn; lia|exact I]|lia|cbn; lia|exact Cn]|].
    exact (IH ltac:(discriminate) _ Hr S3).
Qed.
