(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KStepC
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Resize LB_Alloc ProgDetIface ProgDetLogic ProgDetNodes ProgDetMalloc LibProg NLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition slotsX (X : list (bptr * Z)) : list cptr := map (fun xb => fst (fst xb)) X.

(* [comment removed for export] *)
Definition SBc (c : Z) : Z := if c <? 34 then S_ c else Z.max (S_ c) ((S_ c + 4111) / 4096 * 4096 - UNIT).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SBc2 (c : Z) : Z := if (4 <=? c) && (c <? 32) && Z.even c && negb (c =? 6) then Z.max (SBc c) (SBc (c + 1)) else SBc c.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition realloc_crit (m n : Z) : Prop :=
  0 <= m < MMAP_THRESHOLD /\ SBc2 (size_to_class m) - IB < n.
Definition realloc_crit_b (m n : Z) : bool :=
  (0 <=? m) && (m <? MMAP_THRESHOLD) && (SBc2 (size_to_class m) - IB <? n).
Lemma realloc_crit_b_ok m n : realloc_crit_b m n = true -> realloc_crit m n.
Proof. unfold realloc_crit_b, realloc_crit. intros H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. lia. Qed.

(* [comment removed for export] *)
Definition realloc_crit_s (m n : Z) : Prop :=
  0 <= n < m /\ m < MMAP_THRESHOLD /\ size_to_class n + 1 < size_to_class m.
Definition realloc_crit_s_b (m n : Z) : bool :=
  (0 <=? n) && (n <? m) && (m <? MMAP_THRESHOLD) && (size_to_class n + 1 <? size_to_class m).
Lemma realloc_crit_s_b_ok m n : realloc_crit_s_b m n = true -> realloc_crit_s m n.
Proof.
  unfold realloc_crit_s_b, realloc_crit_s. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. lia.
Qed.

(* [comment removed for export] *)
Definition inplace_crit (m n : Z) : Prop :=
  0 <= n <= m /\ m < MMAP_THRESHOLD /\ size_to_class n = size_to_class m.
Definition inplace_crit_b (m n : Z) : bool :=
  (0 <=? n) && (n <=? m) && (m <? MMAP_THRESHOLD) && (size_to_class n =? size_to_class m).
Lemma inplace_crit_b_ok m n : inplace_crit_b m n = true -> inplace_crit m n.
Proof.
  unfold inplace_crit_b, inplace_crit. intros H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. lia.
Qed.

Section LWF.
Variable ok : list (bptr * Z) -> Z -> Prop.

Fixpoint lwf {A} (t : lprog A) (X : list (bptr * Z)) (Q : A -> list (bptr * Z) -> Prop) : Prop :=
  match t with
  | LRet a => Q a X
  | LUnr => False
  | LMalloc n k =>
      0 <= n < 2^62 /\ ok X n /\ k None = LUnr
      /\ forall p, ~ In (fst p) (slotsX X) -> lwf (k (Some p)) ((p, n) :: X) Q
  | LFree p k => exists m X', Permutation X ((p, m) :: X') /\ lwf k X' Q
  | LRealloc p n k =>
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < 2^62 /\ realloc_crit m n /\ ok X n /\ k None = LUnr
      /\ forall q, ~ In (fst q) (slotsX X) -> lwf (k (Some q)) ((q, n) :: X') Q
  | LSys o k => sys_pre o /\ forall r, sys_res o r -> lwf (k r) X Q   (* [comment removed for export] *)
  | LAligned al n k =>                                          (* [comment removed for export] *)
      (al = 32 \/ al = 64) /\ 0 <= n /\ aligned_req al n < MMAP_THRESHOLD /\ size_to_class n = size_to_class (aligned_req al n)
      /\ ok X (aligned_req al n) /\ k None = LUnr
      /\ forall p, ~ In (fst p) (slotsX X) -> lwf (k (Some p)) ((p, n) :: X) Q
  | LReallocS p n k =>                                          (* [comment removed for export] *)
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n < m /\ m < MMAP_THRESHOLD /\ size_to_class n + 1 < size_to_class m
      /\ ok X n /\ k None = LUnr
      /\ forall q, ~ In (fst q) (slotsX X) -> lwf (k (Some q)) ((q, n) :: X') Q
  | LReallocI p n k =>                                          (* [comment removed for export] *)
      exists m X', Permutation X ((p, m) :: X') /\ 0 <= n <= m /\ m < MMAP_THRESHOLD /\ size_to_class n = size_to_class m
      /\ ok X n /\ k None = LUnr
      /\ forall q, (q = p \/ ~ In (fst q) (slotsX X)) -> lwf (k (Some q)) ((q, n) :: X') Q
  end.

Lemma lwf_mono : forall {A} (t : lprog A) X (Q Q' : A -> list (bptr * Z) -> Prop),
  lwf t X Q -> (forall a X', Q a X' -> Q' a X') -> lwf t X Q'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros X Q Q' H HQ; cbn [lwf] in *.
  - apply HQ. exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. eapply IH; [exact Hk| exact HQ].
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
  - destruct H as [Hpre H]. split; [exact Hpre|]. intros r Hr. eapply IH; [exact (H r Hr)| exact HQ].
  - destruct H as (Ha & Hp & Hn & Hr & Hok & HN & Hk). repeat (split; [assumption|]). intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. eapply IH; [exact (Hk q Hq)| exact HQ].
Qed.

Lemma lwf_bind : forall {A B} (m : lprog A) (f : A -> lprog B) X (Q : B -> list (bptr * Z) -> Prop),
  lwf m X (fun a X' => lwf (f a) X' Q) -> lwf (lbind m f) X Q.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros f X Q H; cbn [lwf lbind] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as [Hpre H]. split; [exact Hpre|]. intros r Hr. apply IH. exact (H r Hr).
  - destruct H as (Ha & Hp & Hn & Hr & Hok & HN & Hk). repeat (split; [assumption|]). split; [rewrite HN; reflexivity|].
    intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Hok & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    split; [rewrite HN; reflexivity|]. intros q Hq. apply IH. exact (Hk q Hq).
Qed.
End LWF.

Lemma lwf_ok_mono : forall (ok ok' : list (bptr * Z) -> Z -> Prop) {A} (t : lprog A) X Q,
  (forall X n, ok X n -> ok' X n) -> lwf ok t X Q -> lwf ok' t X Q.
Proof.
  intros ok ok' A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros X Q Hok H; cbn [lwf] in *.
  - exact H.
  - exact H.
  - destruct H as (Hn & Ho & HN & Hk). split; [exact Hn|]. split; [apply Hok; exact Ho|]. split; [exact HN|].
    intros q Hq. apply IH; [exact Hok| exact (Hk q Hq)].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH; [exact Hok| exact Hk].
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk). exists m, X'. split; [exact HP|]. split; [exact Hn|].
    split; [exact Hc|]. split; [apply Hok; exact Ho|]. split; [exact HN|]. intros q Hq. apply IH; [exact Hok| exact (Hk q Hq)].
  - destruct H as [Hpre H]. split; [exact Hpre|]. intros r Hr. apply IH; [exact Hok| exact (H r Hr)].
  - destruct H as (Ha & Hp & Hn & Hr & Ho & HN & Hk). split; [exact Ha|]. split; [exact Hp|]. split; [exact Hn|]. split; [exact Hr|].
    split; [apply Hok; exact Ho|]. split; [exact HN|]. intros q Hq. apply IH; [exact Hok| exact (Hk q Hq)].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk). exists m, X'. split; [exact HP|]. split; [exact Hn|]. split; [exact Hm|].
    split; [exact Hc|]. split; [apply Hok; exact Ho|]. split; [exact HN|]. intros q Hq. apply IH; [exact Hok| exact (Hk q Hq)].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk). exists m, X'. split; [exact HP|]. split; [exact Hn|]. split; [exact Hm|].
    split; [exact Hc|]. split; [apply Hok; exact Ho|]. split; [exact HN|]. intros q Hq. apply IH; [exact Hok| exact (Hk q Hq)].
Qed.

(* [comment removed for export] *)
Fixpoint lleaves {A} (t : lprog A) (phi : A -> Prop) : Prop :=
  match t with
  | LRet a => phi a
  | LUnr => True
  | LMalloc n k => forall r, lleaves (k r) phi
  | LFree p k => lleaves k phi
  | LRealloc p n k => forall r, lleaves (k r) phi
  | LSys o k => forall r, lleaves (k r) phi                    (* [comment removed for export] *)
  | LAligned al n k => forall r, lleaves (k r) phi             (* [comment removed for export] *)
  | LReallocS p n k => forall r, lleaves (k r) phi             (* [comment removed for export] *)
  | LReallocI p n k => forall r, lleaves (k r) phi             (* [comment removed for export] *)
  end.

Lemma lleaves_mono : forall {A} (t : lprog A) (phi phi' : A -> Prop),
  lleaves t phi -> (forall a, phi a -> phi' a) -> lleaves t phi'.
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros phi phi' H Hp; cbn [lleaves] in *.
  - apply Hp. exact H.
  - exact I.
  - intros r. eapply IH; [exact (H r)| exact Hp].
  - eapply IH; [exact H| exact Hp].
  - intros r. eapply IH; [exact (H r)| exact Hp].
  - intros r. eapply IH; [exact (H r)| exact Hp].
  - intros r. eapply IH; [exact (H r)| exact Hp].
  - intros r. eapply IH; [exact (H r)| exact Hp].
  - intros r. eapply IH; [exact (H r)| exact Hp].
Qed.

Lemma lleaves_bind : forall {A B} (m : lprog A) (f : A -> lprog B) (phi : B -> Prop),
  lleaves m (fun a => lleaves (f a) phi) -> lleaves (lbind m f) phi.
Proof.
  intros A B m. induction m as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros f phi H; cbn [lleaves lbind] in *.
  - exact H.
  - exact I.
  - intros r. apply IH. exact (H r).
  - apply IH. exact H.
  - intros r. apply IH. exact (H r).
  - intros r. apply IH. exact (H r).
  - intros r. apply IH. exact (H r).
  - intros r. apply IH. exact (H r).
  - intros r. apply IH. exact (H r).
Qed.

Lemma lleaves_true : forall {A} (t : lprog A), lleaves t (fun _ => True).
Proof. intros A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; cbn [lleaves]; auto. Qed.

(* [comment removed for export] *)
Lemma lwf_lleaves : forall ok {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop) (phi : A -> Prop),
  lwf ok t X Q -> lleaves t phi -> lwf ok t X (fun a X' => Q a X' /\ phi a).
Proof.
  intros ok A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros X Q phi H HL; cbn [lwf lleaves] in *.
  - split; assumption.
  - exact H.
  - destruct H as (Hn & Ho & HN & Hk). repeat (split; [assumption|]). intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
  - destruct H as (m & X' & HP & Hk). exists m, X'. split; [exact HP|]. apply IH; [exact Hk| exact HL].
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
  - destruct H as [Hpre H]. split; [exact Hpre|]. intros r Hr. apply IH; [exact (H r Hr)| exact (HL r)].
  - destruct H as (Ha & Hp & Hn & Hr & Ho & HN & Hk). repeat (split; [assumption|]). intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
  - destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk). exists m, X'. repeat (split; [assumption|]).
    intros q Hq. apply IH; [exact (Hk q Hq)| exact (HL (Some q))].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Alloc.
Context {CE__ : Ceiling}.
Variable G : PState -> Model -> Prop.
Hypothesis HG : frame_ok G.
Variable P : Z -> Z.

(* [comment removed for export] *)
Definition mal_okP (X : list (bptr * Z)) (n : Z) : Prop :=
  ROOMX X P n /\ PHI P + R63X X + bigb n <= LBUDGET.

Definition OQ (X : list (bptr * Z)) : assn PState := fun s mo => OWN (map fst X) G s mo /\ QI X P s mo.

Lemma OQ_perm : forall X Y s mo, Permutation X Y -> OQ X s mo -> OQ Y s mo.
Proof.
  intros X Y s mo HP [H1 H2]. split; [eapply OWN_perm; [apply Permutation_map; exact HP| exact H1]| eapply QI_perm; [exact HP| exact H2]].
Qed.

Lemma QI_fresh : forall p n X s mo, QI ((p, n) :: X) P s mo -> ~ In (fst p) (slotsX X).
Proof. intros p n X s mo H. pose proof (QI_nodup _ _ _ _ H) as ND. cbn [map fst] in ND. inversion ND; subst. assumption. Qed.

Lemma OQ_fresh : forall p n X s mo, OQ ((p, n) :: X) s mo -> ~ In (fst p) (slotsX X).
Proof. intros p n X s mo [_ H]. exact (QI_fresh _ _ _ _ _ H). Qed.

Lemma OQ_minv : forall X s mo, OQ X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [_ H]. exact (QI_minv _ _ _ _ H). Qed.

Lemma fstable_True : fstable (fun _ _ _ => True).
Proof. intros s mo tr s' mo' _ _ _ _. exact I. Qed.

Lemma size_ok62 : forall n, n < 2^62 -> size_overflows n = false.
Proof. intros n H. unfold size_overflows. apply Z.leb_gt. lia. Qed.

Lemma raw_malloc_N : forall X n, 0 <= n < 2^62 ->
  mspecN (fun s mo => OQ X s mo /\ mal_okP X n) (raw_malloc n)
         (fun r s mo => exists p, r = Some p /\ OQ ((p, n) :: X) s mo).
Proof.
  intros X n Hn.
  eapply mspecN_conseq;
    [eapply (mspecN_combine LBUDGET (fun _ => True));
       [apply (raw_malloc_spec_c (map fst X) G n HG (proj1 Hn))
       |apply (raw_malloc_LQ X P n (proj1 Hn))
       |apply (raw_malloc_E None (fun _ => True) n (fun _ _ _ => True) fstable_True (size_ok62 n (proj2 Hn)))]| |].
  - intros s mo [[HO HQ] [HR HB]]. split; [exact HO|]. split; [auto|]. split; [exists []; exact I|]. exact (QI_minv _ _ _ _ HQ).
  - intros r s mo (H1 & H2 & tr & _ & Hr). destruct r as [p|]; [|contradiction Hr; reflexivity].
    exists p. split; [reflexivity|]. split; [exact (proj1 H1)| exact (proj1 H2)].
Qed.

Lemma raw_free_N : forall X p n, mspecN (OQ ((p, n) :: X)) (raw_free p) (fun _ => OQ X).
Proof.
  intros X p n.
  eapply mspecN_conseq;
    [eapply (mspecN_combine LBUDGET (fun _ => True));
       [apply (raw_free_spec_c (map fst X) G p HG)
       |apply (raw_free_LQ X P p n)
       |apply (raw_free_E None (fun _ => True) p (fun _ _ _ => True) fstable_True)]| |].
  - intros s mo [HO HQ]. split; [exact HO|]. split; [exact HQ|]. split; [exists []; exact I|]. exact (QI_minv _ _ _ _ HQ).
  - intros r s mo (H1 & H2 & _). split; assumption.
Qed.

(* [comment removed for export] *)

Lemma lsys_N : forall X o, sys_pre o ->
  mspecN (OQ X) (lsys o) (fun r s mo => OQ X s mo /\ sys_res o r).
Proof.
  intros X o Hpre. apply mspec_N. unfold lsys. apply mspec_sys. intros s mo HO. split; [apply sys_pre_nsafe; exact Hpre|].
  intros rsp mo' evs Hst. destruct o; cbn [sys_node sys_dec sys_res] in Hst |- *.
  5: { apply nstep_dec_cnf in Hst as (-> & -> & -> & Hd). eexists. split; [exact Hd|]. split; [exact HO| reflexivity]. }
  all: apply nstep_dec_getid in Hst as (-> & -> & -> & Hd); eexists; (split; [exact Hd|]); (split; [exact HO|]);
       match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; lia end.
Qed.

Lemma lsys_L : forall X o, sys_pre o ->
  mspecL LBUDGET (QI X P) (lsys o) (fun r s mo => QI X P s mo /\ sys_res o r).
Proof.
  intros X o Hpre. unfold lsys. apply mspecL_sys; [intros s mo _; destruct o; exact I|].
  intros s mo HQ rsp mo' evs Hst.
  destruct o; cbn [sys_node sys_dec sys_res] in Hst |- *.
  5: { apply nstep_dec_cnf in Hst as (-> & -> & -> & Hd). split; [apply (QI_live X P s mo HQ)|].
       intros a Ha. rewrite Hd in Ha. injection Ha as <-. split; [exact HQ| reflexivity]. }
  all: apply nstep_dec_getid in Hst as (-> & -> & -> & Hd); (split; [apply (QI_live X P s mo HQ)|]);
       intros a Ha; rewrite Hd in Ha; injection Ha as <-; (split; [exact HQ|]);
       match goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as R; unfold bv_modulus in R; lia end.
Qed.

(* [comment removed for export] *)

Lemma SBc_bound : forall mr,
  0 <= m_sizeclass mr < 48 ->
  (get_stride mr <= S_ (m_sizeclass mr) \/ 34 <= m_sizeclass mr) ->
  (m_maplen mr <> 0 -> m_maplen mr * 4096 <= (m_last_idx mr + 1) * S_ (m_sizeclass mr) + 4111) ->
  get_stride mr <= SBc (m_sizeclass mr).
Proof.
  intros mr Hc Hs Hmap. unfold SBc. destruct (Z.ltb_spec (m_sizeclass mr) 34) as [Hlt|Hge]; [destruct Hs; lia|].
  unfold get_stride in *. destruct (Z.eqb_spec (m_last_idx mr) 0) as [E0|NE0]; cbn [andb]; [|unfold S_; lia].
  destruct (Z.eqb_spec (m_maplen mr) 0) as [M0|MN0]; cbn [negb]; [unfold S_; lia|].
  specialize (Hmap MN0). rewrite E0 in Hmap.
  assert (m_maplen mr <= (S_ (m_sizeclass mr) + 4111) / 4096).
  { apply Z.div_le_lower_bound; lia. }
  unfold UNIT. nia.
Qed.

Lemma realloc_moves_of_QI : forall p m X n s mo,
  QI ((p, m) :: X) P s mo -> realloc_crit m n -> realloc_moves (ps_m s) (fst p) n = true.
Proof.
  intros p m X n s mo [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) _] [Hm Hcrit].
  assert (Hin : In (fst p, m) (map bs BL)). { eapply Permutation_in; [exact HP|]. left. reflexivity. }
  apply in_map_iff in Hin. destruct Hin as (k & Hk & HkBL). unfold bs in Hk. injection Hk as Hslot Hsize.
  destruct (qb_cls _ _ _ SI k HkBL) as (mt & i & Hs & Hlt48 & H63).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hg) & Hi & _).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO.
  assert (Hc : 0 <= m_sizeclass (MR st mt) < 48).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hc _]|[Hc _]]; [exact Hc|]. destruct (H63 Hc) as [Hbig _]. lia. }
  destruct (Hlt48 (proj2 Hc)) as [_ Hcls].
  destruct (g_stride _ _ _ _ _ _ GO (proj2 Hc)) as (Hstr & _ & _).
  assert (Hb : get_stride (MR st mt) <= SBc (m_sizeclass (MR st mt))).
  { apply SBc_bound; [exact Hc| exact Hstr|]. intros MN0. exact (qg_map _ _ _ SI _ _ _ Hg (proj2 Hc) MN0). }
  unfold realloc_moves. rewrite <- E. cbn [strip s_slots]. rewrite <- Hslot, Hs.
  unfold MR in *. unfold get_meta_rec in *. cbn [strip s_metas].
  apply andb_true_intro. split; [|apply orb_true_intro; left; apply Z.ltb_lt; exact (proj2 Hc)].
  apply Z.ltb_lt. rewrite Hsize in Hcls. unfold SBc2 in Hcrit.
  destruct Hcls as [Ec|(Ec & Hco & Hev & Hn6)].
  - rewrite <- Ec in Hb. destruct ((4 <=? size_to_class m) && (size_to_class m <? 32) && Z.even (size_to_class m) && negb (size_to_class m =? 6)); lia.
  - replace (m_sizeclass (default meta0 (s_metas st !! mt))) with (size_to_class m + 1) in Hb by lia.
    replace ((4 <=? size_to_class m) && (size_to_class m <? 32) && Z.even (size_to_class m) && negb (size_to_class m =? 6)) with true in Hcrit; [lia|].
    symmetry. apply andb_true_intro. split; [apply andb_true_intro; split; [apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia| exact Hev]|].
    apply negb_true_iff. apply Z.eqb_neq. exact Hn6.
Qed.

Lemma slotsX_app : forall X Y, slotsX (X ++ Y) = slotsX X ++ slotsX Y.
Proof. intros. unfold slotsX. apply map_app. Qed.

(* [comment removed for export] *)
Lemma realloc_shrinks_of_QI : forall p m X n s mo,
  QI ((p, m) :: X) P s mo -> realloc_crit_s m n -> realloc_shrinks (ps_m s) (fst p) n = true.
Proof.
  intros p m X n s mo [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) _] (Hn & Hm & Hcrit).
  assert (Hin : In (fst p, m) (map bs BL)). { eapply Permutation_in; [exact HP|]. left. reflexivity. }
  apply in_map_iff in Hin. destruct Hin as (k & Hk & HkBL). unfold bs in Hk. injection Hk as Hslot Hsize.
  destruct (qb_cls _ _ _ SI k HkBL) as (mt & i & Hs & Hlt48 & H63).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hg) & Hi & _).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO.
  assert (Hc : 0 <= m_sizeclass (MR st mt) < 48).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hc _]|[Hc _]]; [exact Hc|]. destruct (H63 Hc) as [Hbig _]. lia. }
  destruct (Hlt48 (proj2 Hc)) as [_ Hcls].
  unfold realloc_shrinks. rewrite <- E. cbn [strip s_slots]. rewrite <- Hslot, Hs.
  unfold MR in *. unfold get_meta_rec in *. cbn [strip s_metas].
  apply andb_true_intro. split; apply Z.ltb_lt; [| exact (proj2 Hc)].
  rewrite Hsize in Hcls. destruct Hcls as [Ec|(Ec & _)]; lia.
Qed.

Lemma raw_realloc_N : forall X p m n, 0 <= n < 2^62 -> realloc_crit m n ->
  mspecN (fun s mo => OQ ((p, m) :: X) s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc p n)
         (fun r s mo => exists q, r = Some q /\ OQ ((q, n) :: X) s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))).
Proof.
  intros X p m n Hn Hcrit. unfold raw_realloc.
  eapply mspecN_bind; [apply mspecN_get|]. intros s0.
  apply mspecN_pointwise. intros s1 mo1 [-> [HOQ Hok]].
  rewrite (size_ok62 n (proj2 Hn)). rewrite (realloc_moves_of_QI p m X n s1 mo1 (proj2 HOQ) Hcrit).
  eapply mspecN_bind.
  { eapply mspecN_pre; [apply (raw_malloc_N ((p, m) :: X) n Hn)|]. intros s mo [-> ->]. split; assumption. }
  intros r. apply mspecN_pointwise. intros s2 mo2 (q & -> & HOQ2).
  pose proof (OQ_fresh _ _ _ _ _ HOQ2) as Hfr.
  eapply mspecN_seq with (R := OQ ((q, n) :: X)).
  { eapply mspecN_pre; [apply (raw_free_N ((q, n) :: X) p m)|]. intros s mo [-> ->].
    eapply OQ_perm; [apply perm_swap| exact HOQ2]. }
  intros _. apply mspecN_ret. intros s mo H. exists q. split; [reflexivity|]. split; [exact H| exact Hfr].
Qed.

Lemma raw_realloc_L : forall X p m n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI ((p, m) :: X) P s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc p n)
         (fun r s mo => match r with
                        | Some q => QI ((q, n) :: X) P s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))
                        | None => True
                        end).
Proof.
  intros X p m n Hn. unfold raw_realloc.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> [HQ Hok]].
  destruct (size_overflows n); [apply mspecL_ret; intros; exact I|].
  destruct (realloc_moves (ps_m s1) (fst p) n); [|apply mspecL_munr].
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply (raw_malloc_LQ ((p, m) :: X) P n Hn)|]. intros s mo [-> ->]. split; [exact HQ| exact Hok]. }
  intros [q|]; [|apply mspecL_ret; intros; exact I].
  apply mspecL_pointwise. intros s2 mo2 [HQ2 _].
  pose proof (QI_fresh _ _ _ _ _ HQ2) as Hfr.
  eapply mspecL_seq with (R := QI ((q, n) :: X) P).
  { eapply mspecL_pre; [apply (raw_free_LQ ((q, n) :: X) P p m)|]. intros s mo [-> ->].
    eapply QI_perm; [apply perm_swap| exact HQ2]. }
  intros _. apply mspecL_ret. intros s mo H. split; [exact H| exact Hfr].
Qed.

(* [comment removed for export] *)
Lemma raw_realloc_shrink_N : forall X p m n, 0 <= n < 2^62 -> realloc_crit_s m n ->
  mspecN (fun s mo => OQ ((p, m) :: X) s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc_shrink p n)
         (fun r s mo => exists q, r = Some q /\ OQ ((q, n) :: X) s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))).
Proof.
  intros X p m n Hn Hcrit. unfold raw_realloc_shrink.
  eapply mspecN_bind; [apply mspecN_get|]. intros s0.
  apply mspecN_pointwise. intros s1 mo1 [-> [HOQ Hok]].
  rewrite (size_ok62 n (proj2 Hn)). rewrite (realloc_shrinks_of_QI p m X n s1 mo1 (proj2 HOQ) Hcrit).
  eapply mspecN_bind.
  { eapply mspecN_pre; [apply (raw_malloc_N ((p, m) :: X) n Hn)|]. intros s mo [-> ->]. split; assumption. }
  intros r. apply mspecN_pointwise. intros s2 mo2 (q & -> & HOQ2).
  pose proof (OQ_fresh _ _ _ _ _ HOQ2) as Hfr.
  eapply mspecN_seq with (R := OQ ((q, n) :: X)).
  { eapply mspecN_pre; [apply (raw_free_N ((q, n) :: X) p m)|]. intros s mo [-> ->].
    eapply OQ_perm; [apply perm_swap| exact HOQ2]. }
  intros _. apply mspecN_ret. intros s mo H. exists q. split; [reflexivity|]. split; [exact H| exact Hfr].
Qed.

Lemma raw_realloc_shrink_L : forall X p m n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI ((p, m) :: X) P s mo /\ mal_okP ((p, m) :: X) n) (raw_realloc_shrink p n)
         (fun r s mo => match r with
                        | Some q => QI ((q, n) :: X) P s mo /\ ~ In (fst q) (slotsX ((p, m) :: X))
                        | None => True
                        end).
Proof.
  intros X p m n Hn. unfold raw_realloc_shrink.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> [HQ Hok]].
  destruct (size_overflows n); [apply mspecL_ret; intros; exact I|].
  destruct (realloc_shrinks (ps_m s1) (fst p) n); [|apply mspecL_munr].
  eapply mspecL_bind.
  { eapply mspecL_pre; [apply (raw_malloc_LQ ((p, m) :: X) P n Hn)|]. intros s mo [-> ->]. split; [exact HQ| exact Hok]. }
  intros [q|]; [|apply mspecL_ret; intros; exact I].
  apply mspecL_pointwise. intros s2 mo2 [HQ2 _].
  pose proof (QI_fresh _ _ _ _ _ HQ2) as Hfr.
  eapply mspecL_seq with (R := QI ((q, n) :: X) P).
  { eapply mspecL_pre; [apply (raw_free_LQ ((q, n) :: X) P p m)|]. intros s mo [-> ->].
    eapply QI_perm; [apply perm_swap| exact HQ2]. }
  intros _. apply mspecL_ret. intros s mo H. split; [exact H| exact Hfr].
Qed.

(* [comment removed for export] *)
Lemma realloc_inplace_of_QI : forall p m X n s mo,
  QI ((p, m) :: X) P s mo -> inplace_crit m n -> realloc_inplace (ps_m s) (fst p) n = true.
Proof.
  intros p m X n s mo [(st & L & BL & LS & E & INV & SI & HAQ & HK & HL & HP) _] (Hn & Hm & Hcrit).
  assert (Hin : In (fst p, m) (map bs BL)). { eapply Permutation_in; [exact HP|]. left. reflexivity. }
  apply in_map_iff in Hin. destruct Hin as (k & Hk & HkBL). unfold bs in Hk. injection Hk as Hslot Hsize.
  destruct (qb_cls _ _ _ SI k HkBL) as (mt & i & Hs & Hlt48 & H63).
  destruct INV as (IR & IA & IM & IL & IG & IS & ISH).
  destruct (is_valid _ _ _ IS _ _ _ Hs) as ((b & ai & Hg) & Hi & _).
  pose proof (ig_ok _ _ _ IG _ _ _ Hg) as GO.
  assert (Hc : 0 <= m_sizeclass (MR st mt) < 48).
  { destruct (g_sc _ _ _ _ _ _ GO) as [[Hc _]|[Hc _]]; [exact Hc|]. destruct (H63 Hc) as [Hbig _]. lia. }
  destruct (Hlt48 (proj2 Hc)) as [_ Hcls].
  unfold realloc_inplace. rewrite <- E. cbn [strip s_slots]. rewrite <- Hslot, Hs.
  unfold MR in *. unfold get_meta_rec in *. cbn [strip s_metas].
  apply andb_true_intro. split; [apply andb_true_intro; split; [apply Z.ltb_lt; lia| apply Z.leb_le]| apply Z.ltb_lt; exact (proj2 Hc)].
  rewrite Hsize in Hcls. destruct Hcls as [Ec|(Ec & _)]; lia.
Qed.

Lemma raw_realloc_inplace_N : forall X p m n, inplace_crit m n ->
  mspecN (OQ ((p, m) :: X)) (raw_realloc_inplace p n)
         (fun r s mo => r = Some p /\ OQ ((p, n) :: X) s mo).
Proof.
  intros X p m n Hcrit. pose proof Hcrit as (Hn & Hm & Hcls). unfold raw_realloc_inplace.
  eapply mspecN_bind; [apply mspecN_get|]. intros s0.
  apply mspecN_pointwise. intros s1 mo1 [-> HOQ].
  rewrite (size_ok62 n ltac:(unfold MMAP_THRESHOLD in Hm; lia)). rewrite (realloc_inplace_of_QI p m X n s1 mo1 (proj2 HOQ) Hcrit).
  apply mspecN_ret. intros s mo [-> ->]. split; [reflexivity|].
  destruct HOQ as [HW HQ]. split; [exact HW|]. eapply QI_resize; [exact HQ| lia| exact Hm| exact Hcls].
Qed.

Lemma raw_realloc_inplace_L : forall X p m n, 0 <= n <= m -> m < MMAP_THRESHOLD -> size_to_class n = size_to_class m ->
  mspecL LBUDGET (QI ((p, m) :: X) P) (raw_realloc_inplace p n)
         (fun r s mo => match r with
                        | Some q => q = p /\ QI ((p, n) :: X) P s mo
                        | None => True
                        end).
Proof.
  intros X p m n Hn Hm Hcls. unfold raw_realloc_inplace.
  eapply mspecL_bind; [apply mspecL_get|]. intros s0.
  apply mspecL_pointwise. intros s1 mo1 [-> HQ].
  destruct (size_overflows n); [apply mspecL_ret; intros; exact I|].
  destruct (realloc_inplace (ps_m s1) (fst p) n); [|apply mspecL_munr].
  apply mspecL_ret. intros s mo [-> ->]. split; [reflexivity|]. eapply QI_resize; [exact HQ| exact Hn| exact Hm| exact Hcls].
Qed.

End Alloc.

(* [comment removed for export] *)
Section AllocE.
Context {CE__ : Ceiling}.
Variable sel : option bool.
Variable XT : list event -> Prop.

Lemma raw_malloc_E0 : forall n (K : assnE PState), fstable K -> mspecE sel XT K (raw_malloc n) (fun _ => K).
Proof.
  intros n K HK. unfold raw_malloc.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr /\ s = s0);
    [apply mspecE_get; intros s mo tr H; exact (conj H (eq_refl s))|]. intros s0.
  eapply mspecE_bind.
  { eapply mspecE_pre; [apply membed_E; [exact HK| apply oktree_true]| intros s mo tr [H _]; exact H]. }
  intros [st' p]. cbv beta iota.
  eapply mspecE_seq with (R := K).
  { apply mspecE_upd. intros s mo tr [H _]. eapply HK; [exact H| reflexivity| reflexivity| reflexivity]. }
  intros _. apply mspecE_ret. intros s mo tr H. exact H.
Qed.

Lemma raw_realloc_E : forall p n (K : assnE PState), fstable K -> mspecE sel XT K (raw_realloc p n) (fun _ => K).
Proof.
  intros p n K HK. unfold raw_realloc.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr);
    [apply mspecE_get; intros s mo tr H; exact H|]. intros s0.
  destruct (size_overflows n); [apply mspecE_ret; auto|].
  destruct (realloc_moves (ps_m s0) (fst p) n); [|apply mspecE_munr].
  eapply mspecE_bind; [apply raw_malloc_E0; exact HK|].
  intros [q|]; [|apply mspecE_ret; auto].
  eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply mspecE_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma lsys_E : forall o (K : assnE PState), mspecE sel XT K (lsys o) (fun _ => K).
Proof.
  intros o K. unfold lsys. apply msysE_node; [destruct o; exact I| intros s mo tr _; destruct o; cbn [sys_node]; first [apply nprog_getid| apply nprog_opencnf]|].
  intros s mo tr rsp mo' evs a HK Hst Hd. destruct o; cbn [sys_node sys_dec] in *;
    first [ destruct (stepR_getid _ _ _ _ _ _ _ Hst Hd) as (_ & -> & ->)
          | destruct (stepR_opencnf _ _ _ _ _ _ Hst Hd) as (_ & -> & ->) ]; rewrite app_nil_r; exact HK.
Qed.

Lemma raw_realloc_shrink_E : forall p n (K : assnE PState), fstable K -> mspecE sel XT K (raw_realloc_shrink p n) (fun _ => K).
Proof.
  intros p n K HK. unfold raw_realloc_shrink.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr);
    [apply mspecE_get; intros s mo tr H; exact H|]. intros s0.
  destruct (size_overflows n); [apply mspecE_ret; auto|].
  destruct (realloc_shrinks (ps_m s0) (fst p) n); [|apply mspecE_munr].
  eapply mspecE_bind; [apply raw_malloc_E0; exact HK|].
  intros [q|]; [|apply mspecE_ret; auto].
  eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply mspecE_ret. auto.
Qed.

(* [comment removed for export] *)
Lemma raw_realloc_inplace_E : forall p n (K : assnE PState), fstable K -> mspecE sel XT K (raw_realloc_inplace p n) (fun _ => K).
Proof.
  intros p n K HK. unfold raw_realloc_inplace.
  eapply mspecE_bind with (Q1 := fun s0 s mo tr => K s mo tr);
    [apply mspecE_get; intros s mo tr H; exact H|]. intros s0.
  destruct (size_overflows n); [apply mspecE_ret; auto|].
  destruct (realloc_inplace (ps_m s0) (fst p) n); [|apply mspecE_munr].
  apply mspecE_ret. auto.
Qed.

Theorem interp_E : forall (K : assnE PState), fstable K ->
  forall {A} (t : lprog A) (phi : A -> Prop), lleaves t phi ->
  mspecE sel XT K (interp t) (fun a s mo tr => K s mo tr /\ phi a).
Proof.
  intros K HK A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros phi H; cbn [interp lleaves] in *.
  - apply mspecE_ret. intros s mo tr HKs. split; [exact HKs| exact H].
  - apply mspecE_munr.
  - eapply mspecE_bind; [apply raw_malloc_E0; exact HK|]. intros r. apply IH. exact (H r).
  - eapply mspecE_seq; [apply raw_free_E; exact HK|]. intros _. apply IH. exact H.
  - eapply mspecE_bind; [apply raw_realloc_E; exact HK|]. intros r. apply IH. exact (H r).
  - (* [comment removed for export] *) eapply mspecE_bind; [apply lsys_E|]. intros r. apply IH. exact (H r).
  - (* [comment removed for export] *) unfold raw_aligned_alloc. eapply mspecE_bind; [apply raw_malloc_E0; exact HK|]. intros r. apply IH. exact (H r).
  - (* [comment removed for export] *) eapply mspecE_bind; [apply raw_realloc_shrink_E; exact HK|]. intros r. apply IH. exact (H r).
  - (* [comment removed for export] *) eapply mspecE_bind; [apply raw_realloc_inplace_E; exact HK|]. intros r. apply IH. exact (H r).
Qed.
End AllocE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Interp.
Context {CE__ : Ceiling}.
Variable G : PState -> Model -> Prop.
Hypothesis HG : frame_ok G.
Variable P : Z -> Z.
Variable ok : list (bptr * Z) -> Z -> Prop.
Variable F : list (bptr * Z).                 (* [comment removed for export] *)
Hypothesis Hok : forall X n, 0 <= n -> ok X n -> mal_okP P (X ++ F) n.

Lemma fresh_app_l : forall (q : bptr) X, ~ In (fst q) (slotsX (X ++ F)) -> ~ In (fst q) (slotsX X).
Proof. intros q X H Hin. apply H. rewrite slotsX_app. apply in_or_app. left. exact Hin. Qed.

Theorem interp_N : forall {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop),
  lwf ok t X Q ->
  mspecN (OQ G P (X ++ F)) (interp t) (fun a s mo => exists X', Q a X' /\ OQ G P (X' ++ F) s mo).
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros X Q H; cbn [interp lwf] in *;
    [| | | | | (* [comment removed for export] *) destruct H as [Hpre H]; eapply mspecN_bind; [apply (lsys_N G P (X ++ F) o Hpre)|]; intros r; apply mspecN_pure; intros Hr; apply IH; exact (H r Hr)
    | | | ].
  - apply mspecN_ret. intros s mo HO. exists X. split; [exact H| exact HO].
  - destruct H.
  - destruct H as (Hn & Ho & HN & Hk).
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_malloc_N G HG P (X ++ F) n Hn)|]. intros s mo HO. split; [exact HO| apply Hok; [exact (proj1 Hn)| exact Ho]]. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1).
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (OQ_fresh G P _ _ _ _ _ HO1)|].
    intros s mo [-> ->]. exact HO1.
  - destruct H as (m & X' & HP & Hk).
    eapply mspecN_seq with (R := OQ G P (X' ++ F)).
    { eapply mspecN_pre; [apply (raw_free_N G HG P (X' ++ F) p m)|]. intros s mo HO.
      eapply OQ_perm; [|exact HO]. change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    intros _. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_realloc_N G HG P (X' ++ F) p m n Hn Hc)|]. intros s mo HO. split.
      - eapply OQ_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1 & Hfr).
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
  - (* [comment removed for export] *)
    destruct H as (Ha & Hn & Hr & Hc & Ho & HN & Hk). unfold raw_aligned_alloc.
    assert (Hn' : 0 <= aligned_req al n < 2^62) by (unfold aligned_req, MMAP_THRESHOLD in *; lia).
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_malloc_N G HG P (X ++ F) (aligned_req al n) Hn')|]. intros s mo HO. split; [exact HO| apply Hok; [exact (proj1 Hn')| exact Ho]]. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1).
    assert (HO2 : OQ G P ((q, n) :: X ++ F) s1 mo1).
    { destruct HO1 as [HW HQ]. split; [exact HW|]. eapply QI_resize; [exact HQ| unfold aligned_req in *; lia| exact Hr| exact Hc]. }
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (OQ_fresh G P _ _ _ _ _ HO2)|].
    intros s mo [-> ->]. exact HO2.
  - (* [comment removed for export] *)
    destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk).
    assert (Hn62 : 0 <= n < 2^62) by (unfold MMAP_THRESHOLD in Hm; lia).
    assert (Hcs : realloc_crit_s m n) by (split; [exact Hn| split; [exact Hm| exact Hc]]).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_realloc_shrink_N G HG P (X' ++ F) p m n Hn62 Hcs)|]. intros s mo HO. split.
      - eapply OQ_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (q & -> & HO1 & Hfr).
    eapply mspecN_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
  - (* [comment removed for export] *)
    destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk).
    assert (Hcs : inplace_crit m n) by (split; [exact Hn| split; [exact Hm| exact Hc]]).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecN_bind.
    { eapply mspecN_pre; [apply (raw_realloc_inplace_N G P (X' ++ F) p m n Hcs)|]. intros s mo HO. eapply OQ_perm; [exact HPF| exact HO]. }
    intros r. apply mspecN_pointwise. intros s1 mo1 (-> & HO1).
    eapply mspecN_pre; [apply (IH (Some p) ((p, n) :: X') Q); apply Hk; left; reflexivity|].
    intros s mo [-> ->]. exact HO1.
Qed.

Theorem interp_L : forall {A} (t : lprog A) X (Q : A -> list (bptr * Z) -> Prop),
  lwf ok t X Q ->
  mspecL LBUDGET (QI (X ++ F) P) (interp t) (fun a s mo => exists X', Q a X' /\ QI (X' ++ F) P s mo).
Proof.
  intros A t. induction t as [a| |n k IH|p k IH|p n k IH|o k IH|al n k IH|p n k IH|p n k IH]; intros X Q H; cbn [interp lwf] in *;
    [| | | | | (* [comment removed for export] *) destruct H as [Hpre H]; eapply mspecL_bind; [apply (lsys_L P (X ++ F) o Hpre)|]; intros r; apply mspecL_pure; intros Hr; apply IH; exact (H r Hr)
    | | | ].
  - apply mspecL_ret. intros s mo HO. exists X. split; [exact H| exact HO].
  - destruct H.
  - destruct H as (Hn & Ho & HN & Hk).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_malloc_LQ (X ++ F) P n (proj1 Hn))|]. intros s mo HO. split; [exact HO| apply Hok; [exact (proj1 Hn)| exact Ho]]. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 _].
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (QI_fresh P _ _ _ _ _ HO1)|].
    intros s mo [-> ->]. exact HO1.
  - destruct H as (m & X' & HP & Hk).
    eapply mspecL_seq with (R := QI (X' ++ F) P).
    { eapply mspecL_pre; [apply (raw_free_LQ (X' ++ F) P p m)|]. intros s mo HO.
      eapply QI_perm; [|exact HO]. change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    intros _. apply IH. exact Hk.
  - destruct H as (m & X' & HP & Hn & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_realloc_L P (X' ++ F) p m n (proj1 Hn))|]. intros s mo HO. split.
      - eapply QI_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 Hfr].
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
  - (* [comment removed for export] *)
    destruct H as (Ha & Hn & Hr & Hc & Ho & HN & Hk). unfold raw_aligned_alloc.
    assert (Hn' : 0 <= aligned_req al n) by (unfold aligned_req in *; lia).
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_malloc_LQ (X ++ F) P (aligned_req al n) Hn')|]. intros s mo HO. split; [exact HO| apply Hok; [exact Hn'| exact Ho]]. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 _].
    assert (HO2 : QI ((q, n) :: X ++ F) P s1 mo1).
    { eapply QI_resize; [exact HO1| unfold aligned_req in *; lia| exact Hr| exact Hc]. }
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X) Q); apply Hk; apply fresh_app_l; exact (QI_fresh P _ _ _ _ _ HO2)|].
    intros s mo [-> ->]. exact HO2.
  - (* [comment removed for export] *)
    destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_realloc_shrink_L P (X' ++ F) p m n (proj1 Hn))|]. intros s mo HO. split.
      - eapply QI_perm; [exact HPF| exact HO].
      - destruct (Hok X n (proj1 Hn) Ho) as [[R1 R2] HB]. unfold mal_okP, ROOMX.
        unfold LRX, n63X in *. rewrite <- !(zcount_perm _ _ _ HPF). unfold R63X in *.
        rewrite <- (zsum_map_perm _ _ _ HPF). auto. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [HO1 Hfr].
    eapply mspecL_pre; [apply (IH (Some q) ((q, n) :: X') Q); apply Hk|].
    + intros Hin. apply Hfr. unfold slotsX in *.
      assert (Hin' : In (fst q) (map (fun xb : bptr * Z => fst (fst xb)) (X ++ F))) by (rewrite map_app; apply in_or_app; left; exact Hin).
      eapply Permutation_in; [apply Permutation_map; exact HPF| exact Hin'].
    + intros s mo [-> ->]. exact HO1.
  - (* [comment removed for export] *)
    destruct H as (m & X' & HP & Hn & Hm & Hc & Ho & HN & Hk).
    assert (HPF : Permutation (X ++ F) ((p, m) :: X' ++ F)).
    { change ((p, m) :: X' ++ F) with (((p, m) :: X') ++ F). apply Permutation_app_tail. exact HP. }
    eapply mspecL_bind.
    { eapply mspecL_pre; [apply (raw_realloc_inplace_L P (X' ++ F) p m n Hn Hm Hc)|]. intros s mo HO. eapply QI_perm; [exact HPF| exact HO]. }
    intros [q|]; [|rewrite HN; cbn [interp]; apply mspecL_munr].
    apply mspecL_pointwise. intros s1 mo1 [-> HO1].
    eapply mspecL_pre; [apply (IH (Some p) ((p, n) :: X') Q); apply Hk; left; reflexivity|].
    intros s mo [-> ->]. exact HO1.
Qed.

End Interp.
