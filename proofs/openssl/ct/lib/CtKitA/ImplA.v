(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Nodes RzCPS NodesA. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Prog BnBase BnModel BnTree LibProg ApBase ApLogic Malloc CtLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition okA {ptr} (X : list (ptr * Z)) (n : Z) : Prop := okC X n.
Definition REQ_MAX : Z := CT_MAXREQ.

Lemma okA_facts : forall {ptr} (X : list (ptr * Z)) n, okA X n -> zlength X < CT_NBT /\ 0 <= n <= REQ_MAX.
Proof.
  intros ptr X n (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). unfold REQ_MAX. split; [lia|]. split; [exact H1| exact H8].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Safe.
Context {ptr : Type}.

Fixpoint safe {A} (t : btree ptr A) (X : list (ptr * Z)) (Q : A -> list (ptr * Z) -> Prop) : Prop :=
  match t with
  | TRet a => Q a X
  | TUnr => False
  | TMalloc n k => okA X n /\ forall p, ~ In p (map fst X) -> safe (k (Some p)) ((p, n) :: X) Q
  | TFree p k => exists m X', Permutation X ((p, m) :: X') /\ safe k X' Q
  end.

Lemma safe_of_bwp : forall {A} (t : btree ptr A) X Q, bwp okA t X Q -> safe t X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [bwp safe] in *.
  - exact H.
  - exact H.
  - destruct H as (_ & Hok & _ & H). split; [exact Hok|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_mono : forall {A} (t : btree ptr A) X (Q Q' : A -> list (ptr * Z) -> Prop),
  safe t X Q -> (forall a X', Q a X' -> Q' a X') -> safe t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q Q' H HQ; cbn [safe] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. eapply IH; [exact H| exact HQ].
Qed.

Lemma safe_bind : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  safe m X (fun a X' => safe (f a) X' Q) -> safe (tbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [safe tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_bind_inv : forall {A B} (m : btree ptr A) (f : A -> btree ptr B) X Q,
  safe (tbind m f) X Q -> safe m X (fun a X' => safe (f a) X' Q).
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH]; intros f X Q H; cbn [safe tbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_leaves : forall {A} (t : btree ptr A) (phi : A -> Prop) X Q,
  leaves t phi -> safe t X Q -> safe t X (fun a X' => Q a X' /\ phi a).
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH]; intros X Q HL H; cbn [safe leaves] in *.
  - split; [exact H | exact HL].
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH; [exact HL | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint asafe {A} (t : aprog ptr A) (X : list (ptr * Z)) (Q : A -> list (ptr * Z) -> Prop) : Prop :=
  match t with
  | ARet a => Q a X
  | AUnr => False
  | AMalloc n k => okA X n /\ forall p, ~ In p (map fst X) -> asafe (k (Some p)) ((p, n) :: X) Q
  | AFree p k => exists m X', Permutation X ((p, m) :: X') /\ asafe k X' Q
  | ARealloc p n k => exists m X', Permutation X ((p, m) :: X') /\ okA X n /\ forall q, ~ In q (map fst X) -> asafe (k (Some q)) ((q, n) :: X') Q
  | AReallocS p n k => exists m X', Permutation X ((p, m) :: X') /\ okA X n /\ forall q, ~ In q (map fst X) -> asafe (k (Some q)) ((q, n) :: X') Q
  | ASys o k => forall r, asafe (k r) X Q
  | AReallocI p n k => exists m X', Permutation X ((p, m) :: X') /\ okA X n /\ forall q, ~ In q (map fst X) -> asafe (k (Some q)) ((q, n) :: X') Q   (* [comment removed for export] *)
  end.

Lemma asafe_of_awp : forall rc rcS rcI spre {A} (t : aprog ptr A) X Q, awp okA rc rcS rcI spre t X Q -> asafe t X Q.
Proof.
  intros rc rcS rcI spre A t. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros X Q H; cbn [awp asafe] in *.
  - exact H.
  - exact H.
  - destruct H as (_ & Hok & _ & H). split; [exact Hok|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
  - destruct H as (m & X' & E & _ & _ & Hok & _ & H). exists m, X'. split; [exact E|]. split; [exact Hok|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & _ & _ & Hok & _ & H). exists m, X'. split; [exact E|]. split; [exact Hok|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as [_ H]. intros r. apply IH. apply H.
  - destruct H as (m & X' & E & _ & _ & Hok & _ & H). exists m, X'. split; [exact E|]. split; [exact Hok|]. intros q Hq. apply IH. apply H. right. exact Hq.
Qed.

Lemma asafe_mono : forall {A} (t : aprog ptr A) X (Q Q' : A -> list (ptr * Z) -> Prop),
  asafe t X Q -> (forall a X', Q a X' -> Q' a X') -> asafe t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros X Q Q' H HQ; cbn [asafe] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. eapply IH; [exact H| exact HQ].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
  - intros r. eapply IH; [apply H| exact HQ].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. eapply IH; [apply H; exact Hq| exact HQ].
Qed.

Lemma asafe_bind : forall {A B} (m : aprog ptr A) (f : A -> aprog ptr B) X Q,
  asafe m X (fun a X' => asafe (f a) X' Q) -> asafe (apbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros f X Q H; cbn [asafe apbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - intros r. apply IH. apply H.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
Qed.

Lemma asafe_bind_inv : forall {A B} (m : aprog ptr A) (f : A -> aprog ptr B) X Q,
  asafe (apbind m f) X Q -> asafe m X (fun a X' => asafe (f a) X' Q).
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros f X Q H; cbn [asafe apbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - intros r. apply IH. apply H.
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
Qed.

Lemma asafe_leaves : forall {A} (t : aprog ptr A) (phi : A -> Prop) X Q,
  aleaves t phi -> asafe t X Q -> asafe t X (fun a X' => Q a X' /\ phi a).
Proof.
  intros A t phi. induction t as [a| |n k IH|p k IH|p n k IH|p n k IH|o k IH|p n k IH]; intros X Q HL H; cbn [asafe aleaves] in *.
  - split; [exact H | exact HL].
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH; [exact HL | exact H].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
  - intros r. apply IH; [apply HL | apply H].
  - destruct H as (m & X' & E & Hn & H). exists m, X'. split; [exact E|]. split; [exact Hn|]. intros q Hq. apply IH; [apply HL | apply H; exact Hq].
Qed.

(* [comment removed for export] *)
Lemma asafe_bt_embed : forall {A} (t : btree ptr A) X Q, asafe (bt_embed t) X Q -> safe t X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [asafe bt_embed safe] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

Lemma safe_bt_embed : forall {A} (t : btree ptr A) X Q, safe t X Q -> asafe (bt_embed t) X Q.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH]; intros X Q H; cbn [asafe bt_embed safe] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & H). split; [exact Hn|]. intros q Hq. apply IH. apply H. exact Hq.
  - destruct H as (m & X' & E & H). exists m, X'. split; [exact E|]. apply IH. exact H.
Qed.

End Safe.

(* [comment removed for export] *)
Lemma bptr_fresh : forall l : list bptr, exists p : bptr, ~ In p l.
Proof.
  intros l.
  assert (H : forall l : list bptr, exists z : Z, forall q, In q l -> snd q < z).
  { induction l0 as [|q l0 [z Hz]]; [exists 0; intros q []|].
    exists (Z.max z (snd q + 1)). intros q' [<-|Hin]; [lia| specialize (Hz q' Hin); lia]. }
  destruct (H l) as [z Hz]. exists ((0%N, 0), z). intros Hin. specialize (Hz _ Hin). cbn in Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma bptr_fresh_sz : forall (l : list bptr) (n : Z), exists p : bptr, ~ In p l /\ gsz p = n.
Proof.
  intros l n.
  assert (H : forall l : list bptr, exists z : Z, forall q, In q l -> snd q < z).
  { induction l0 as [|q l0 [z Hz]]; [exists 0; intros q []|].
    exists (Z.max z (snd q + 1)). intros q' [<-|Hin]; [lia| specialize (Hz q' Hin); lia]. }
  destruct (H l) as [z Hz]. exists ((0%N, n), z). split; [| reflexivity]. intros Hin. specialize (Hz _ Hin). cbn in Hz. lia.
Qed.

Lemma zlength_cons : forall {A} (x : A) l, zlength (x :: l) = zlength l + 1.
Proof. intros. unfold zlength. cbn [length]. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ImplA.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
(* [comment removed for export] *)
Local Notation PMc := (@ar_PMc AR).
Local Notation PMc_ms := (@ar_PMc_ms AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lwsum (l : list Z) : Z := match l with nil => 0 | n :: l' => lw n + lwsum l' end.
Fixpoint bigcnt (l : list Z) : Z := match l with nil => 0 | n :: l' => (if 64512 <? n then 1 else 0) + bigcnt l' end.
Lemma psum_sizes : forall l, psum l = lwsum (map snd l).
Proof. induction l as [|e l IH]; cbn [psum lwsum map]; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma nbig_sizes : forall l, nbig l = bigcnt (map snd l).
Proof. induction l as [|e l IH]; [reflexivity|]. rewrite nbig_cons, IH. unfold isbig. cbn [map bigcnt]. reflexivity. Qed.
Lemma lwsum_app : forall l1 l2, lwsum (l1 ++ l2) = lwsum l1 + lwsum l2.
Proof. induction l1 as [|n l1 IH]; intros l2; cbn [lwsum app]; [lia|]. rewrite IH. lia. Qed.
Lemma bigcnt_app : forall l1 l2, bigcnt (l1 ++ l2) = bigcnt l1 + bigcnt l2.
Proof. induction l1 as [|n l1 IH]; intros l2; cbn [bigcnt app]; [lia|]. rewrite IH. lia. Qed.
Lemma lwsum_perm : forall l l', Permutation l l' -> lwsum l = lwsum l'.
Proof. intros l l' H. induction H; cbn [lwsum] in *; lia. Qed.
Lemma bigcnt_perm : forall l l', Permutation l l' -> bigcnt l = bigcnt l'.
Proof. intros l l' H. induction H; cbn [bigcnt] in *; lia. Qed.
Lemma lw_le_sm : forall n, 0 <= n -> lw n <= 4 * smsz n + 32.
Proof.
  intros n Hn. unfold lw, smsz, MMAP_THRESHOLD. destruct (Z.leb_spec n 64512); destruct (Z.ltb_spec n 131052); lia.
Qed.
Lemma big_issec : forall n, (if 64512 <? n then 1 else 0) = issec n.
Proof. intros n. unfold issec, ASAN_SEC_MIN. destruct (Z.ltb_spec 64512 n); destruct (Z.leb_spec 64513 n); lia. Qed.
Lemma lwsum_blocks : forall {ptr} (X : list (ptr * Z)), bnonneg X -> lwsum (map snd X) <= 4 * smsum X + 32 * zlength X.
Proof.
  intros ptr X HB. unfold smsum. induction X as [|x X IH].
  - rewrite msum_nil. unfold zlength. cbn. lia.
  - apply Forall_cons_iff in HB as [Hx HB]. specialize (IH HB). cbn [map lwsum]. rewrite msum_cons, zlength_cons.
    pose proof (lw_le_sm (snd x) Hx). lia.
Qed.
Lemma bigcnt_blocks : forall {ptr} (X : list (ptr * Z)), bigcnt (map snd X) = nsec X.
Proof.
  intros ptr X. unfold nsec. induction X as [|x X IH]; [rewrite msum_nil; reflexivity|].
  cbn [map bigcnt]. rewrite msum_cons, IH, big_issec. reflexivity.
Qed.

(* [comment removed for export] *)
Definition room0 (S0 : list Z) : Prop :=
  Z.of_nat (length S0) + CT_NBT <= LIVE_MAX /\ lwsum S0 + (4 * CT_SMB + 32 * CT_NBT) <= PBYTES_MAX /\ bigcnt S0 + CT_NSEC <= NSEC_LIVE.

Lemma room0_of_lroom3 : forall (L : list (Z * Z)) c p b, lroom3 L c p b -> CT_NBT <= c -> 4 * CT_SMB + 32 * CT_NBT <= p -> CT_NSEC <= b -> room0 (map snd L).
Proof.
  intros L c p b (H1 & H2 & H3) Hc Hp Hb. unfold room0. rewrite length_map, <- psum_sizes, <- nbig_sizes. lia.
Qed.

(* [comment removed for export] *)
Definition linked (S0 : list Z) (Σ : rts RT) (X : list (bptr * Z)) : Prop :=
  Permutation (map snd (rt_live RT Σ)) (S0 ++ map snd X) /\ Forall (fun xb => gsz (fst xb) = snd xb) X /\ room0 S0.

Lemma linked_intro0 : forall Σ, room0 (map snd (rt_live RT Σ)) -> linked (map snd (rt_live RT Σ)) Σ [].
Proof. intros Σ R. split; [rewrite app_nil_r; apply Permutation_refl|]. split; [constructor| exact R]. Qed.

(* [comment removed for export] *)
Lemma linked_live : forall S0 Σ X n, linked S0 Σ X -> okA X n -> live_room (rt_live RT Σ) n.
Proof.
  intros S0 Σ X n (P & _ & (R1 & R2 & R3)) (Hn & HB & C1 & C2 & _ & _ & C5 & _).
  pose proof (Permutation_length P) as L. rewrite length_map, length_app, length_map in L.
  pose proof (lwsum_perm _ _ P) as W. rewrite <- psum_sizes, lwsum_app in W.
  pose proof (bigcnt_perm _ _ P) as B. rewrite <- nbig_sizes, bigcnt_app, bigcnt_blocks in B.
  pose proof (lwsum_blocks X HB) as WX. pose proof (lw_le_sm n Hn) as Wn. pose proof (big_issec n) as Bn.
  unfold live_room. unfold zlength in *.
  split; [lia|]. split; [lia|]. destruct (Z.leb_spec n 64512); destruct (Z.ltb_spec 64512 n); lia.
Qed.

Lemma linked_same : forall S0 Σ Σ' X, linked S0 Σ X -> rt_live RT Σ' = rt_live RT Σ -> linked S0 Σ' X.
Proof. intros S0 Σ Σ' X (P & G & R) E. split; [rewrite E; exact P| exact (conj G R)]. Qed.

Lemma linked_perm : forall S0 Σ X X', linked S0 Σ X -> Permutation X X' -> linked S0 Σ X'.
Proof.
  intros S0 Σ X X' (P & G & R) HP. split; [| split; [| exact R]].
  - eapply Permutation_trans; [exact P|]. apply Permutation_app_head. apply Permutation_map. exact HP.
  - eapply Permutation_Forall; [exact HP| exact G].
Qed.

Lemma linked_malloc : forall S0 Σ Σ' X p a n, linked S0 Σ X -> rt_live RT Σ' = (a, n) :: rt_live RT Σ -> gsz p = n -> linked S0 Σ' ((p, n) :: X).
Proof.
  intros S0 Σ Σ' X p a n (P & G & R) E Hg. split; [| split; [constructor; [exact Hg| exact G]| exact R]].
  rewrite E. cbn [map snd]. eapply Permutation_trans; [apply perm_skip; exact P|]. apply Permutation_middle.
Qed.

Lemma linked_gsz : forall S0 Σ X X' p m, linked S0 Σ X -> Permutation X ((p, m) :: X') -> gsz p = m.
Proof.
  intros S0 Σ X X' p m (_ & G & _) HP. pose proof (Permutation_Forall HP G) as G'. apply Forall_cons_iff in G' as [E _]. exact E.
Qed.

Lemma linked_free : forall S0 Σ Σ' X X' p m a, linked S0 Σ X -> Permutation X ((p, m) :: X') ->
  Permutation (rt_live RT Σ) ((a, gsz p) :: rt_live RT Σ') -> linked S0 Σ' X'.
Proof.
  intros S0 Σ Σ' X X' p m a L HP HF. pose proof (linked_gsz _ _ _ _ _ _ L HP) as Eg. destruct L as (P & G & R).
  split; [| split; [| exact R]].
  - apply (Permutation_map snd) in HF. cbn [map snd] in HF. rewrite Eg in HF.
    apply (Permutation_cons_inv (a := m)). eapply Permutation_trans; [symmetry; exact HF|].
    eapply Permutation_trans; [exact P|]. eapply Permutation_trans; [apply Permutation_app_head; apply Permutation_map; exact HP|].
    cbn [map snd]. symmetry. apply Permutation_middle.
  - pose proof (Permutation_Forall HP G) as G'. apply Forall_cons_iff in G' as [_ G']. exact G'.
Qed.

Lemma linked_realloc : forall S0 Σ Σ' X X' p m q n a b, linked S0 Σ X -> Permutation X ((p, m) :: X') ->
  Permutation ((a, gsz p) :: rt_live RT Σ') ((b, n) :: rt_live RT Σ) -> gsz q = n -> linked S0 Σ' ((q, n) :: X').
Proof.
  intros S0 Σ Σ' X X' p m q n a b L HP HF Hq. pose proof (linked_gsz _ _ _ _ _ _ L HP) as Eg. destruct L as (P & G & R).
  split; [| split; [| exact R]].
  - apply (Permutation_map snd) in HF. cbn [map snd] in HF. rewrite Eg in HF.
    apply (Permutation_cons_inv (a := m)). eapply Permutation_trans; [exact HF|].
    eapply Permutation_trans; [apply perm_skip; exact P|]. eapply Permutation_trans; [apply perm_skip; apply Permutation_app_head; apply Permutation_map; exact HP|].
    cbn [map snd]. eapply Permutation_trans; [apply perm_skip; symmetry; apply Permutation_middle|].
    eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply Permutation_middle.
  - constructor; [exact Hq|]. pose proof (Permutation_Forall HP G) as G'. apply Forall_cons_iff in G' as [_ G']. exact G'.
Qed.

(* [comment removed for export] *)
Definition implA {A} (t : btree bptr A) (Σ : rts RT) (Q : A -> rts RT -> machine_state -> Prop) (ms : machine_state) : Prop :=
  forall (X : list (bptr * Z)) (Φ : A -> list (bptr * Z) -> Prop) (D : list Z), safe t X Φ -> linked D Σ X ->
    cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ linked D Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c).

(* [comment removed for export] *)
Definition implAp {A} (t : aprog bptr A) (Σ : rts RT) (Q : A -> rts RT -> machine_state -> Prop) (ms : machine_state) : Prop :=
  forall (X : list (bptr * Z)) (Φ : A -> list (bptr * Z) -> Prop) (D : list Z), asafe t X Φ -> linked D Σ X ->
    cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ linked D Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c).

Lemma PMc_mat_stable : forall Σ, mat_stable (fun mo => ARTM RT Σ mo /\ PMc mo).
Proof. intros Σ. apply mat_stable_and; [exact (af_mat_stable RT AF Σ)| exact PMc_ms]. Qed.

(* [comment removed for export] *)
Lemma asta_evtA : forall Σ Pm Q, (forall ms, Pm ms -> evt ctasegs Q ms) ->
  cps ctasegs (ASTA RT Σ PMc Pm) (ASTA RT Σ PMc Q).
Proof.
  intros Σ Pm Q H. unfold ASTA.
  apply (ast_evt ctasegs SEGTOP_A asegs_wx asegs_below); [apply PMc_mat_stable| exact H].
Qed.

(* [comment removed for export] *)
Lemma cps_from_evt : forall Σ (P : machine_state -> Prop) (Q : config -> Prop) ms,
  evt ctasegs P ms -> (forall ms', P ms' -> cps ctasegs (ASTA RT Σ PMc (eq ms')) Q) -> cps ctasegs (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ P Q ms HE HK T c Hc Hk.
  apply (asta_evtA Σ (eq ms) P ltac:(intros ms0 <-; exact HE) T c Hc).
  intros c' Hc'. destruct (ASTA_unpack RT Σ PMc P c' Hc') as (ms' & HP & Hc'').
  exact (HK ms' HP T c' Hc'' Hk).
Qed.

Lemma cps_from_evt' : forall Σ (Q : config -> Prop) ms,
  evt ctasegs (fun ms' => cps ctasegs (ASTA RT Σ PMc (eq ms')) Q) ms -> cps ctasegs (ASTA RT Σ PMc (eq ms)) Q.
Proof. intros Σ Q ms H. eapply cps_from_evt; [exact H|]. intros ms' H'. exact H'. Qed.

(* [comment removed for export] *)
Lemma cps_step_same : forall Σ ms (R : machine_state -> Prop) (Q : config -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R) ->
  (forall ms', R ms' -> cps ctasegs (ASTA RT Σ PMc (eq ms')) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ ms R Q H1 H2. eapply cps_seq; [exact H1|]. intros T c Hc Hk.
  destruct (ASTA_unpack RT Σ PMc R c Hc) as (ms' & HR & Hc'). exact (H2 ms' HR T c Hc' Hk).
Qed.

(* [comment removed for export] *)
Lemma cps_unpack : forall Σ (R : machine_state -> Prop) (Q : config -> Prop),
  (forall ms, R ms -> cps ctasegs (ASTA RT Σ PMc (eq ms)) Q) -> cps ctasegs (ASTA RT Σ PMc R) Q.
Proof. intros Σ R Q H T c Hc Hk. destruct (ASTA_unpack RT Σ PMc R c Hc) as (ms & HR & Hc'). exact (H ms HR T c Hc' Hk). Qed.

Lemma cps_post : forall (P Q : config -> Prop), (forall c, P c -> Q c) -> cps ctasegs P Q.
Proof. intros P Q H T c Hc Hk. apply Hk. apply H. exact Hc. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implA_evt : forall {A} (t : btree bptr A) Σ Q (P : machine_state -> Prop) ms,
  evt ctasegs P ms -> (forall ms', P ms' -> implA t Σ Q ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q P ms HE HK X Φ D S L T c Hc Hk.
  apply (asta_evtA Σ (eq ms) P ltac:(intros ms0 <-; exact HE) T c Hc).
  intros c' Hc'. destruct (ASTA_unpack RT Σ PMc P c' Hc') as (ms' & HP & Hc'').
  exact (HK ms' HP X Φ D S L T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_from_evt : forall {A} (t : btree bptr A) Σ Q ms,
  evt ctasegs (fun ms' => implA t Σ Q ms') ms -> implA t Σ Q ms.
Proof. intros A t Σ Q ms H. eapply implA_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implA_ret : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  Q a Σ ms -> implA (TRet a) Σ Q ms.
Proof.
  intros A a Σ Q ms HQ X Φ D S L T c Hc Hk. cbn [safe] in S. apply Hk. exists a, X, Σ. split; [exact S|]. split; [exact L|].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HQ.
Qed.

Lemma implA_ret_evt : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  evt ctasegs (Q a Σ) ms -> implA (TRet a) Σ Q ms.
Proof. intros A a Σ Q ms H. eapply implA_evt; [exact H|]. intros ms' HQ. apply implA_ret. exact HQ. Qed.

Lemma implA_unr : forall {A} Σ (Q : A -> rts RT -> machine_state -> Prop) ms, implA TUnr Σ Q ms.
Proof. intros A Σ Q ms X Φ D []. Qed.

Lemma implA_mono : forall {A} (t : btree bptr A) Σ (Q Q' : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q ms -> (forall a Σ' ms', Q a Σ' ms' -> Q' a Σ' ms') -> implA t Σ Q' ms.
Proof.
  intros A t Σ Q Q' ms H HQ X Φ D S L T c Hc Hk. apply (H X Φ D S L T c Hc).
  intros c' (a & X' & Σ' & HΦ & L' & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0. apply HQ.
Qed.

(* [comment removed for export] *)
Lemma implA_post_evt : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> evt ctasegs (Q a Σ') ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HQ X Φ D S L T c Hc Hk. apply (H X Φ D S L T c Hc).
  intros c' (a & X' & Σ' & HΦ & L' & Hc').
  apply (asta_evtA Σ' (Q1 a Σ') (Q a Σ') ltac:(intros ms0 H0; exact (HQ a Σ' ms0 H0)) T c' Hc').
  intros c'' Hc''. apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'| exact Hc''].
Qed.

(* [comment removed for export] *)
Lemma implA_bind : forall {A B} (m : btree bptr A) (f : A -> btree bptr B) Σ Q1 Q ms,
  implA m Σ Q1 ms ->
  (forall a Σ' ms', Q1 a Σ' ms' -> implA (f a) Σ' Q ms') ->
  implA (tbind m f) Σ Q ms.
Proof.
  intros A B m f Σ Q1 Q ms Hm Hf X Φ D S L T c Hc Hk.
  apply safe_bind_inv in S.
  apply (Hm X (fun a X' => safe (f a) X' Φ) D S L T c Hc).
  intros c' (a & X' & Σ' & S' & L' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (Hf a Σ' ms' HQ1 X' Φ D S' L' T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_step : forall {A} (t : btree bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c /\ rt_live RT Σ' = rt_live RT Σ) ->      (* [comment removed for export] *)
  (forall Σ' ms', R Σ' ms' -> implA t Σ' Q ms') ->
  implA t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2 X Φ D S L T c Hc Hk.
  apply (H1 T c Hc). intros c' (Σ' & Hc' & EL).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X Φ D S (linked_same D Σ Σ' X L EL) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_step_same : forall {A} (t : btree bptr A) Σ Q ms (R : machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R) ->
  (forall ms', R ms' -> implA t Σ Q ms') ->
  implA t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2. eapply (implA_step t Σ Q ms (fun Σ' ms' => Σ' = Σ /\ R ms')).
  - eapply cps_conseq; [exact H1 | intros c Hc; exact Hc |]. intros c Hc. exists Σ. split; [| reflexivity].
    eapply ASTA_conseq; [exact Hc|]. intros ms0 HR. split; [reflexivity | exact HR].
  - intros Σ' ms' [-> HR]. exact (H2 ms' HR).
Qed.

(* [comment removed for export] *)
Lemma implA_malloc : forall {A} n (k : option bptr -> btree bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= REQ_MAX -> live_room (rt_live RT Σ) n ->      (* [comment removed for export] *)
     cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c /\ exists a, rt_live RT Σ' = (a, n) :: rt_live RT Σ)) ->
  (forall p Σ' ms', 0 <= n <= REQ_MAX -> ~ In p avoid -> gsz p = n -> R Σ' ms' -> implA (k (Some p)) Σ' Q ms') ->
  implA (TMalloc n k) Σ Q ms.
Proof.
  intros A n k Σ Q ms avoid R H1 H2 X Φ D S L T c Hc Hk. cbn [safe] in S. destruct S as (HOK & S).
  pose proof (okA_facts X n HOK) as [_ Hn]. pose proof (linked_live D Σ X n L HOK) as LIVE.
  apply (H1 Hn LIVE T c Hc). intros c' (Σ' & Hc' & (a & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh_sz (avoid ++ map fst X) n) as [p [Hp Hg]].
  assert (Hp1 : ~ In p avoid) by (intros Hin; apply Hp; apply in_or_app; left; exact Hin).
  assert (Hp2 : ~ In p (map fst X)) by (intros Hin; apply Hp; apply in_or_app; right; exact Hin).
  exact (H2 p Σ' ms' Hn Hp1 Hg HR ((p, n) :: X) Φ D (S p Hp2) (linked_malloc D Σ Σ' X p a n L EL Hg) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_free : forall {A} p (k : btree bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c
                                            /\ exists a, Permutation (rt_live RT Σ) ((a, gsz p) :: rt_live RT Σ')) ->      (* [comment removed for export] *)
  (forall Σ' ms', R Σ' ms' -> implA k Σ' Q ms') ->
  implA (TFree p k) Σ Q ms.
Proof.
  intros A p k Σ Q ms R H1 H2 X Φ D S L T c Hc Hk. cbn [safe] in S. destruct S as (m0 & X' & HP & S).
  apply (H1 T c Hc). intros c' (Σ' & Hc' & (a & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X' Φ D S (linked_free D Σ Σ' X X' p m0 a L HP EL) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implA_leaves : forall {A} (t : btree bptr A) (phi : A -> Prop) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  leaves t phi -> implA t Σ Q ms -> implA t Σ (fun a Σ' ms' => Q a Σ' ms' /\ phi a) ms.
Proof.
  intros A t phi Σ Q ms HL H X Φ D S L T c Hc Hk.
  apply (H X (fun a X' => Φ a X' /\ phi a) D (safe_leaves t phi X Φ HL S) L T c Hc).
  intros c' (a & X' & Σ' & (HΦ & Hphi) & L' & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0 HQ. split; [exact HQ | exact Hphi].
Qed.

(* [comment removed for export] *)
Lemma implA_run : forall {A} (t : btree bptr A) Σ Q ms X (Φ : A -> list (bptr * Z) -> Prop) D,
  implA t Σ Q ms -> bwp okA t X Φ -> linked D Σ X ->
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ linked D Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c).
Proof. intros A t Σ Q ms X Φ D H W L. exact (H X Φ D (safe_of_bwp t X Φ W) L). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implAp_evt : forall {A} (t : aprog bptr A) Σ Q (P : machine_state -> Prop) ms,
  evt ctasegs P ms -> (forall ms', P ms' -> implAp t Σ Q ms') -> implAp t Σ Q ms.
Proof.
  intros A t Σ Q P ms HE HK X Φ D S L T c Hc Hk.
  apply (asta_evtA Σ (eq ms) P ltac:(intros ms0 <-; exact HE) T c Hc).
  intros c' Hc'. destruct (ASTA_unpack RT Σ PMc P c' Hc') as (ms' & HP & Hc'').
  exact (HK ms' HP X Φ D S L T c' Hc'' Hk).
Qed.

Lemma implAp_from_evt : forall {A} (t : aprog bptr A) Σ Q ms,
  evt ctasegs (fun ms' => implAp t Σ Q ms') ms -> implAp t Σ Q ms.
Proof. intros A t Σ Q ms H. eapply implAp_evt; [exact H|]. intros ms' H'. exact H'. Qed.

Lemma implAp_ret : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  Q a Σ ms -> implAp (ARet a) Σ Q ms.
Proof.
  intros A a Σ Q ms HQ X Φ D S L T c Hc Hk. cbn [asafe] in S. apply Hk. exists a, X, Σ. split; [exact S|]. split; [exact L|].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. exact HQ.
Qed.

Lemma implAp_ret_evt : forall {A} (a : A) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  evt ctasegs (Q a Σ) ms -> implAp (ARet a) Σ Q ms.
Proof. intros A a Σ Q ms H. eapply implAp_evt; [exact H|]. intros ms' HQ. apply implAp_ret. exact HQ. Qed.

Lemma implAp_unr : forall {A} Σ (Q : A -> rts RT -> machine_state -> Prop) ms, implAp AUnr Σ Q ms.
Proof. intros A Σ Q ms X Φ D []. Qed.

Lemma implAp_mono : forall {A} (t : aprog bptr A) Σ (Q Q' : A -> rts RT -> machine_state -> Prop) ms,
  implAp t Σ Q ms -> (forall a Σ' ms', Q a Σ' ms' -> Q' a Σ' ms') -> implAp t Σ Q' ms.
Proof.
  intros A t Σ Q Q' ms H HQ X Φ D S L T c Hc Hk. apply (H X Φ D S L T c Hc).
  intros c' (a & X' & Σ' & HΦ & L' & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0. apply HQ.
Qed.

Lemma implAp_post_evt : forall {A} (t : aprog bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implAp t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> evt ctasegs (Q a Σ') ms') -> implAp t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HQ X Φ D S L T c Hc Hk. apply (H X Φ D S L T c Hc).
  intros c' (a & X' & Σ' & HΦ & L' & Hc').
  apply (asta_evtA Σ' (Q1 a Σ') (Q a Σ') ltac:(intros ms0 H0; exact (HQ a Σ' ms0 H0)) T c' Hc').
  intros c'' Hc''. apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'| exact Hc''].
Qed.

Lemma implAp_bind : forall {A B} (m : aprog bptr A) (f : A -> aprog bptr B) Σ Q1 Q ms,
  implAp m Σ Q1 ms ->
  (forall a Σ' ms', Q1 a Σ' ms' -> implAp (f a) Σ' Q ms') ->
  implAp (apbind m f) Σ Q ms.
Proof.
  intros A B m f Σ Q1 Q ms Hm Hf X Φ D S L T c Hc Hk.
  apply asafe_bind_inv in S.
  apply (Hm X (fun a X' => asafe (f a) X' Φ) D S L T c Hc).
  intros c' (a & X' & Σ' & S' & L' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (Hf a Σ' ms' HQ1 X' Φ D S' L' T c' Hc'' Hk).
Qed.

Lemma implAp_step : forall {A} (t : aprog bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c /\ rt_live RT Σ' = rt_live RT Σ) ->      (* [comment removed for export] *)
  (forall Σ' ms', R Σ' ms' -> implAp t Σ' Q ms') ->
  implAp t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2 X Φ D S L T c Hc Hk.
  apply (H1 T c Hc). intros c' (Σ' & Hc' & EL).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X Φ D S (linked_same D Σ Σ' X L EL) T c' Hc'' Hk).
Qed.

Lemma implAp_step_same : forall {A} (t : aprog bptr A) Σ Q ms (R : machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc R) ->
  (forall ms', R ms' -> implAp t Σ Q ms') ->
  implAp t Σ Q ms.
Proof.
  intros A t Σ Q ms R H1 H2. eapply (implAp_step t Σ Q ms (fun Σ' ms' => Σ' = Σ /\ R ms')).
  - eapply cps_conseq; [exact H1 | intros c Hc; exact Hc |]. intros c Hc. exists Σ. split; [| reflexivity].
    eapply ASTA_conseq; [exact Hc|]. intros ms0 HR. split; [reflexivity | exact HR].
  - intros Σ' ms' [-> HR]. exact (H2 ms' HR).
Qed.

Lemma implAp_malloc : forall {A} n (k : option bptr -> aprog bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= REQ_MAX -> live_room (rt_live RT Σ) n ->      (* [comment removed for export] *)
     cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c /\ exists a, rt_live RT Σ' = (a, n) :: rt_live RT Σ)) ->
  (forall p Σ' ms', 0 <= n <= REQ_MAX -> ~ In p avoid -> gsz p = n -> R Σ' ms' -> implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc n k) Σ Q ms.
Proof.
  intros A n k Σ Q ms avoid R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S. destruct S as (HOK & S).
  pose proof (okA_facts X n HOK) as [_ Hn]. pose proof (linked_live D Σ X n L HOK) as LIVE.
  apply (H1 Hn LIVE T c Hc). intros c' (Σ' & Hc' & (a & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh_sz (avoid ++ map fst X) n) as [p [Hp Hg]].
  assert (Hp1 : ~ In p avoid) by (intros Hin; apply Hp; apply in_or_app; left; exact Hin).
  assert (Hp2 : ~ In p (map fst X)) by (intros Hin; apply Hp; apply in_or_app; right; exact Hin).
  exact (H2 p Σ' ms' Hn Hp1 Hg HR ((p, n) :: X) Φ D (S p Hp2) (linked_malloc D Σ Σ' X p a n L EL Hg) T c' Hc'' Hk).
Qed.

Lemma implAp_free : forall {A} p (k : aprog bptr A) Σ Q ms (R : rts RT -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c
                                            /\ exists a, Permutation (rt_live RT Σ) ((a, gsz p) :: rt_live RT Σ')) ->      (* [comment removed for export] *)
  (forall Σ' ms', R Σ' ms' -> implAp k Σ' Q ms') ->
  implAp (AFree p k) Σ Q ms.
Proof.
  intros A p k Σ Q ms R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S. destruct S as (m0 & X' & HP & S).
  apply (H1 T c Hc). intros c' (Σ' & Hc' & (a & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  exact (H2 Σ' ms' HR X' Φ D S (linked_free D Σ Σ' X X' p m0 a L HP EL) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implAp_realloc : forall {A} p n (k : option bptr -> aprog bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= REQ_MAX -> live_room (rt_live RT Σ) n ->      (* [comment removed for export] *)
     cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c
                                               /\ exists a b, Permutation ((a, gsz p) :: rt_live RT Σ') ((b, n) :: rt_live RT Σ))) ->
  (forall q Σ' ms', 0 <= n <= REQ_MAX -> ~ In q avoid -> gsz q = n -> R Σ' ms' -> implAp (k (Some q)) Σ' Q ms') ->
  implAp (ARealloc p n k) Σ Q ms.
Proof.
  intros A p n k Σ Q ms avoid R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S. destruct S as (m0 & X' & HP & HOK & S).
  pose proof (okA_facts X n HOK) as [_ Hn]. pose proof (linked_live D Σ X n L HOK) as LIVE.
  apply (H1 Hn LIVE T c Hc). intros c' (Σ' & Hc' & (a & b & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh_sz (avoid ++ map fst X) n) as [q [Hq Hg]].
  assert (Hq1 : ~ In q avoid) by (intros Hin; apply Hq; apply in_or_app; left; exact Hin).
  assert (Hq2 : ~ In q (map fst X)) by (intros Hin; apply Hq; apply in_or_app; right; exact Hin).
  exact (H2 q Σ' ms' Hn Hq1 Hg HR ((q, n) :: X') Φ D (S q Hq2) (linked_realloc D Σ Σ' X X' p m0 q n a b L HP EL Hg) T c' Hc'' Hk).
Qed.

Lemma implAp_reallocS : forall {A} p n (k : option bptr -> aprog bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= REQ_MAX -> live_room (rt_live RT Σ) n ->      (* [comment removed for export] *)
     cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c
                                               /\ exists a b, Permutation ((a, gsz p) :: rt_live RT Σ') ((b, n) :: rt_live RT Σ))) ->
  (forall q Σ' ms', 0 <= n <= REQ_MAX -> ~ In q avoid -> gsz q = n -> R Σ' ms' -> implAp (k (Some q)) Σ' Q ms') ->
  implAp (AReallocS p n k) Σ Q ms.
Proof.
  intros A p n k Σ Q ms avoid R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S. destruct S as (m0 & X' & HP & HOK & S).
  pose proof (okA_facts X n HOK) as [_ Hn]. pose proof (linked_live D Σ X n L HOK) as LIVE.
  apply (H1 Hn LIVE T c Hc). intros c' (Σ' & Hc' & (a & b & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh_sz (avoid ++ map fst X) n) as [q [Hq Hg]].
  assert (Hq1 : ~ In q avoid) by (intros Hin; apply Hq; apply in_or_app; left; exact Hin).
  assert (Hq2 : ~ In q (map fst X)) by (intros Hin; apply Hq; apply in_or_app; right; exact Hin).
  exact (H2 q Σ' ms' Hn Hq1 Hg HR ((q, n) :: X') Φ D (S q Hq2) (linked_realloc D Σ Σ' X X' p m0 q n a b L HP EL Hg) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implAp_reallocI : forall {A} p n (k : option bptr -> aprog bptr A) Σ Q ms (avoid : list bptr) (R : rts RT -> machine_state -> Prop),
  (0 <= n <= REQ_MAX -> live_room (rt_live RT Σ) n ->      (* [comment removed for export] *)
     cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c
                                               /\ exists a b, Permutation ((a, gsz p) :: rt_live RT Σ') ((b, n) :: rt_live RT Σ))) ->
  (forall q Σ' ms', 0 <= n <= REQ_MAX -> ~ In q avoid -> gsz q = n -> R Σ' ms' -> implAp (k (Some q)) Σ' Q ms') ->
  implAp (AReallocI p n k) Σ Q ms.
Proof.
  intros A p n k Σ Q ms avoid R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S. destruct S as (m0 & X' & HP & HOK & S).
  pose proof (okA_facts X n HOK) as [_ Hn]. pose proof (linked_live D Σ X n L HOK) as LIVE.
  apply (H1 Hn LIVE T c Hc). intros c' (Σ' & Hc' & (a & b & EL)).
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HR & Hc'').
  destruct (bptr_fresh_sz (avoid ++ map fst X) n) as [q [Hq Hg]].
  assert (Hq1 : ~ In q avoid) by (intros Hin; apply Hq; apply in_or_app; left; exact Hin).
  assert (Hq2 : ~ In q (map fst X)) by (intros Hin; apply Hq; apply in_or_app; right; exact Hin).
  exact (H2 q Σ' ms' Hn Hq1 Hg HR ((q, n) :: X') Φ D (S q Hq2) (linked_realloc D Σ Σ' X X' p m0 q n a b L HP EL Hg) T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implAp_sys : forall {A} o (k : Z -> aprog bptr A) Σ Q ms (R : Z -> machine_state -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (ASTA RT Σ PMc (fun ms' => exists r, R r ms')) ->
  (forall r ms', R r ms' -> implAp (k r) Σ Q ms') ->
  implAp (ASys o k) Σ Q ms.
Proof.
  intros A o k Σ Q ms R H1 H2 X Φ D S L T c Hc Hk. cbn [asafe] in S.
  apply (H1 T c Hc). intros c' Hc'.
  destruct (ASTA_unpack RT Σ PMc _ c' Hc') as (ms' & (r & HR) & Hc'').
  exact (H2 r ms' HR X Φ D (S r) L T c' Hc'' Hk).
Qed.

Lemma implAp_leaves : forall {A} (t : aprog bptr A) (phi : A -> Prop) Σ (Q : A -> rts RT -> machine_state -> Prop) ms,
  aleaves t phi -> implAp t Σ Q ms -> implAp t Σ (fun a Σ' ms' => Q a Σ' ms' /\ phi a) ms.
Proof.
  intros A t phi Σ Q ms HL H X Φ D S L T c Hc Hk.
  apply (H X (fun a X' => Φ a X' /\ phi a) D (asafe_leaves t phi X Φ HL S) L T c Hc).
  intros c' (a & X' & Σ' & (HΦ & Hphi) & L' & Hc'). apply Hk. exists a, X', Σ'. split; [exact HΦ|]. split; [exact L'|].
  eapply ASTA_conseq; [exact Hc'|]. intros ms0 HQ. split; [exact HQ | exact Hphi].
Qed.

(* [comment removed for export] *)
Lemma implAp_bt : forall {A} (t : btree bptr A) Σ Q ms, implA t Σ Q ms -> implAp (bt_embed t) Σ Q ms.
Proof. intros A t Σ Q ms H X Φ D S L. exact (H X Φ D (asafe_bt_embed t X Φ S) L). Qed.

(* [comment removed for export] *)
Lemma implAp_run : forall rc rcS rcI spre {A} (t : aprog bptr A) Σ Q ms X (Φ : A -> list (bptr * Z) -> Prop) D,
  implAp t Σ Q ms -> awp okA rc rcS rcI spre t X Φ -> linked D Σ X ->
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists a X' Σ', Φ a X' /\ linked D Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c).
Proof. intros rc rcS rcI spre A t Σ Q ms X Φ D H W L. exact (H X Φ D (asafe_of_awp rc rcS rcI spre t X Φ W) L). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End ImplA.
