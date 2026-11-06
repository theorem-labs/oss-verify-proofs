(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim BnModel BnTree BgState ApBase ApState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Logic.
Context {ptr : Type}.
Definition blocks : Type := list (ptr * Z).
Variable ok : blocks -> Z -> Prop.
Variable rcrit : Z -> Z -> Prop.          (* [comment removed for export] *)
Variable rcritS : Z -> Z -> Prop.         (* [comment removed for export] *)
Variable rcritI : Z -> Z -> Prop.         (* [comment removed for export] *)
Variable spre : sysop -> Prop.            (* [comment removed for export] *)

Fixpoint awp {A} (t : aprog ptr A) (X : blocks) (Q : A -> blocks -> Prop) : Prop :=
  match t with
  | ARet a => Q a X
  | AUnr => False
  | AMalloc n k =>
      0 <= n < 2^62 /\ ok X n /\ k None = AUnr
      /\ forall p, ~ In p (map fst X) -> awp (k (Some p)) ((p, n) :: X) Q
  | AFree p k => exists m X', Permutation X ((p, m) :: X') /\ awp k X' Q
  | ARealloc p n k =>
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < 2^62 /\ rcrit m n /\ ok X n /\ k None = AUnr
      /\ forall q, ~ In q (map fst X) -> awp (k (Some q)) ((q, n) :: X') Q
  | AReallocS p n k =>
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < 2^62 /\ rcritS m n /\ ok X n /\ k None = AUnr
      /\ forall q, ~ In q (map fst X) -> awp (k (Some q)) ((q, n) :: X') Q
  | ASys o k => spre o /\ forall r, awp (k r) X Q
  | AReallocI p n k =>
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < 2^62 /\ rcritI m n /\ ok X n /\ k None = AUnr
      /\ forall q, (q = p \/ ~ In q (map fst X)) -> awp (k (Some q)) ((q, n) :: X') Q
  end.

Lemma awp_mono : forall {A} (t : aprog ptr A) X (Q Q' : A -> blocks -> Prop),
  awp t X Q -> (forall a X', Q a X' -> Q' a X') -> awp t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros X Q Q' H HQ; cbn [awp] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). intros q Hq. eapply IH; [exact (Hk q Hq)|exact HQ].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. eapply IH; [exact Hk|exact HQ].
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)|exact HQ].
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)|exact HQ].
  - destruct H as [Hs H]. split; [exact Hs|]. intros r. eapply IH; [exact (H r)|exact HQ].
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)|exact HQ].
Qed.

Lemma awp_bind : forall {A B} (m : aprog ptr A) (f : A -> aprog ptr B) X (Q : B -> blocks -> Prop),
  awp m X (fun a X' => awp (f a) X' Q) -> awp (apbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros f X Q H; cbn [awp apbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as [Hs H]. split; [exact Hs|]. intros r. apply IH. exact (H r).
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma awp_abind : forall {A B} (m : AM A) (f : A -> AM B) (s : ap_st ptr) X (Q : B * ap_st ptr -> blocks -> Prop),
  awp (m s) X (fun r X' => awp (f (fst r) (snd r)) X' Q) -> awp (abind m f s) X Q.
Proof. intros. unfold abind. apply awp_bind. exact H. Qed.

Lemma awp_aret : forall {A} (a : A) (s : ap_st ptr) X (Q : A * ap_st ptr -> blocks -> Prop), Q (a, s) X -> awp (aret a s) X Q.
Proof. intros. exact H. Qed.

Lemma awp_amalloc : forall n (s : ap_st ptr) X (Q : ptr * ap_st ptr -> blocks -> Prop),
  0 <= n < 2^62 -> ok X n -> (forall p, ~ In p (map fst X) -> Q (p, s) ((p, n) :: X)) -> awp (amalloc n s) X Q.
Proof. intros n s X Q Hn Hok H. cbn. repeat (split; [assumption|]). split; [reflexivity|]. exact H. Qed.

Lemma awp_afree : forall p m (s : ap_st ptr) X X' (Q : unit * ap_st ptr -> blocks -> Prop),
  Permutation X ((p, m) :: X') -> Q (tt, s) X' -> awp (afree p s) X Q.
Proof. intros p m s X X' Q HP H. cbn. exists m, X'. split; assumption. Qed.

Lemma awp_arealloc : forall p m n (s : ap_st ptr) X X' (Q : ptr * ap_st ptr -> blocks -> Prop),
  Permutation X ((p, m) :: X') -> 0 <= n < 2^62 -> rcrit m n -> ok X n ->
  (forall q, ~ In q (map fst X) -> Q (q, s) ((q, n) :: X')) -> awp (arealloc p n s) X Q.
Proof. intros p m n s X X' Q HP Hn Hc Hok H. cbn. exists m, X'. repeat (split; [assumption|]). split; [reflexivity|]. exact H. Qed.

Lemma awp_areallocS : forall p m n (s : ap_st ptr) X X' (Q : ptr * ap_st ptr -> blocks -> Prop),
  Permutation X ((p, m) :: X') -> 0 <= n < 2^62 -> rcritS m n -> ok X n ->
  (forall q, ~ In q (map fst X) -> Q (q, s) ((q, n) :: X')) -> awp (areallocS p n s) X Q.
Proof. intros p m n s X X' Q HP Hn Hc Hok H. cbn. exists m, X'. repeat (split; [assumption|]). split; [reflexivity|]. exact H. Qed.

Lemma awp_asys : forall o (s : ap_st ptr) X (Q : Z * ap_st ptr -> blocks -> Prop), spre o -> (forall r, Q (r, s) X) -> awp (asys o s) X Q.
Proof. intros o s X Q Hs H. cbn. split; [exact Hs| exact H]. Qed.

(* [comment removed for export] *)
Lemma awp_areallocI : forall p m n (s : ap_st ptr) X X' (Q : ptr * ap_st ptr -> blocks -> Prop),
  Permutation X ((p, m) :: X') -> 0 <= n < 2^62 -> rcritI m n -> ok X n ->
  (forall q, (q = p \/ ~ In q (map fst X)) -> Q (q, s) ((q, n) :: X')) -> awp (areallocI p n s) X Q.
Proof. intros p m n s X X' Q HP Hn Hc Hok H. cbn. exists m, X'. repeat (split; [assumption|]). split; [reflexivity|]. exact H. Qed.

(* [comment removed for export] *)
Fixpoint bwp {A} (t : btree ptr A) (X : blocks) (Q : A -> blocks -> Prop) : Prop :=
  match t with
  | TRet a => Q a X
  | TUnr => False
  | TMalloc n k => 0 <= n < 2^62 /\ ok X n /\ k None = TUnr /\ forall p, ~ In p (map fst X) -> bwp (k (Some p)) ((p, n) :: X) Q
  | TFree p k => exists m X', Permutation X ((p, m) :: X') /\ bwp k X' Q
  end.

Lemma bwp_mono : forall {A} (t : btree ptr A) X (Q Q' : A -> blocks -> Prop),
  bwp t X Q -> (forall a X', Q a X' -> Q' a X') -> bwp t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q Q' H HQ; cbn [bwp] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). intros q Hq. eapply IH; [exact (Hk q Hq)|exact HQ].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. eapply IH; [exact Hk|exact HQ].
Qed.

Lemma bwp_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X (Q : B -> blocks -> Prop),
  bwp m X (fun a X' => bwp (f a) X' Q) -> bwp (tbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [bwp tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
Qed.

Lemma awp_bt_embed : forall {A} (t : btree ptr A) X (Q : A -> blocks -> Prop), bwp t X Q -> awp (bt_embed t) X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [bwp bt_embed awp] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
Qed.

Lemma awp_abt : forall {A} (t : btree ptr A) (s : ap_st ptr) X (Q : A * ap_st ptr -> blocks -> Prop),
  bwp t X (fun a X' => Q (a, s) X') -> awp (abt t s) X Q.
Proof. intros A t s X Q H. unfold abt. apply awp_bind. apply awp_bt_embed. eapply bwp_mono; [exact H|]. intros a X' HQ. exact HQ. Qed.

(* [comment removed for export] *)
Fixpoint aleaves {A} (t : aprog ptr A) (phi : A -> Prop) : Prop :=
  match t with
  | ARet a => phi a
  | AUnr => True
  | AMalloc n k => forall r, aleaves (k r) phi
  | AFree p k => aleaves k phi
  | ARealloc p n k => forall r, aleaves (k r) phi
  | AReallocS p n k => forall r, aleaves (k r) phi
  | ASys o k => forall r, aleaves (k r) phi
  | AReallocI p n k => forall r, aleaves (k r) phi
  end.

Lemma aleaves_bind : forall {A B} (m : aprog ptr A) (f : A -> aprog ptr B) (phi : B -> Prop),
  aleaves m (fun a => aleaves (f a) phi) -> aleaves (apbind m f) phi.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros f phi H; cbn [aleaves apbind] in *; auto;
    intros r; apply IH; exact (H r).
Qed.

Lemma aleaves_true : forall {A} (t : aprog ptr A), aleaves t (fun _ => True).
Proof. intros A t. induction t; cbn [aleaves]; auto. Qed.

End Logic.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Blocks.
Context {ptr : Type}.

Definition bsum (X : list (ptr * Z)) : Z := fold_right Z.add 0 (map snd X).
Definition bnonneg (X : list (ptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb) X.

Lemma bsum_nil : bsum [] = 0. Proof. reflexivity. Qed.
Lemma bsum_cons x X : bsum (x :: X) = snd x + bsum X. Proof. reflexivity. Qed.
Lemma bsum_app X Y : bsum (X ++ Y) = bsum X + bsum Y.
Proof. unfold bsum. rewrite map_app. induction (map snd X) as [|a l IH]; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma bsum_perm X Y : Permutation X Y -> bsum X = bsum Y.
Proof.
  intros HP. unfold bsum. apply (Permutation_map snd) in HP. induction HP; cbn; try lia.
Qed.
Lemma bnonneg_app X Y : bnonneg X -> bnonneg Y -> bnonneg (X ++ Y).
Proof. intros. apply Forall_app. split; assumption. Qed.
Lemma bnonneg_perm X Y : Permutation X Y -> bnonneg X -> bnonneg Y.
Proof. intros HP H. unfold bnonneg in *. rewrite Forall_forall in *. intros x Hx. apply H. eapply Permutation_in; [apply Permutation_sym; exact HP|exact Hx]. Qed.
Lemma bnonneg_sum X : bnonneg X -> 0 <= bsum X.
Proof. induction X as [|x X IH]; intros H; [cbn; unfold bsum; cbn; lia|]. inversion H; subst. rewrite bsum_cons. specialize (IH ltac:(assumption)). lia. Qed.
Lemma zlen_app' (X Y : list (ptr * Z)) : zlength (X ++ Y) = zlength X + zlength Y.
Proof. unfold zlength. rewrite length_app. lia. Qed.
Lemma zlen_perm (X Y : list (ptr * Z)) : Permutation X Y -> zlength X = zlength Y.
Proof. intros HP. unfold zlength. rewrite (Permutation_length HP). reflexivity. Qed.

(* [comment removed for export] *)
Lemma fresh_perm (p : ptr) (X Y : list (ptr * Z)) : Permutation X Y -> ~ In p (map fst X) -> ~ In p (map fst Y).
Proof. intros HP H Hin. apply H. eapply Permutation_in; [apply Permutation_map; apply Permutation_sym; exact HP|exact Hin]. Qed.
Lemma fresh_app_l (p : ptr) (X Y : list (ptr * Z)) : ~ In p (map fst (X ++ Y)) -> ~ In p (map fst X).
Proof. intros H Hin. apply H. rewrite map_app. apply in_app_iff. left. exact Hin. Qed.
Lemma fresh_app_r (p : ptr) (X Y : list (ptr * Z)) : ~ In p (map fst (X ++ Y)) -> ~ In p (map fst Y).
Proof. intros H Hin. apply H. rewrite map_app. apply in_app_iff. right. exact Hin. Qed.

End Blocks.

(* [comment removed for export] *)
Definition okAp {ptr} (NB TOT : Z) (X : list (ptr * Z)) (n : Z) : Prop :=
  zlength X < NB /\ 0 <= n /\ bnonneg X /\ bsum X + n <= TOT.

Definition AP_NB : Z := 400.   (* [comment removed for export] *)
Definition AP_MAX_INPUT : Z := 67108864.          (* [comment removed for export] *)
Definition AP_TOT : Z := AP_MAX_INPUT + 1048576.

Lemma okAp_intro {ptr} (X : list (ptr * Z)) n c t :
  zlength X <= c -> bsum X <= t -> bnonneg X -> 0 <= n -> c + 1 <= AP_NB -> t + n <= AP_TOT -> okAp AP_NB AP_TOT X n.
Proof. intros. unfold okAp. repeat split; try assumption; lia. Qed.
