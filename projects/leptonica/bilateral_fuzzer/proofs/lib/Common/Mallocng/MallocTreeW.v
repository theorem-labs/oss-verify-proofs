(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML}.


Inductive wmode := WAll | WFail | WOk.

Definition wmode_eq_dec : forall a b : wmode, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(* [comment removed for export] *)
Definition mm_len (len : word) : Z := page_round_up_Z (bv_unsigned len).

(* [comment removed for export] *)
Fixpoint tsall {A : Type} (W : wmode) (t : itree A) (P : A -> mstate -> Prop) : Prop :=
  match t with
  | TRet a s => P a s
  | TCrash => False
  | TBrk req vm kf ko =>
      (* [comment removed for export] *)
      (brk_grow_ok_vm vm req req = false -> tsall W kf P) /\ (W = WAll -> brk_grow_ok_vm vm req req = true -> tsall W ko P)
  | TMmap k len vm kf ko =>
      ((forall a, mmap_grant_ok k vm a (mm_len len) = false) -> tsall W kf P) /\
      (W <> WFail -> forall a, mmap_grant_ok k vm a (mm_len len) = true -> tsall W (ko a) P)
  | TMmapFixed addr len k1 k2 k3 =>
      (W <> WFail -> tsall W k2 P)
  | TMprot addr len vm kf ko =>
      (mprot_ok_vm vm addr (page_round_up len) = false -> tsall W kf P) /\
      (W <> WFail -> mprot_ok_vm vm addr (page_round_up len) = true -> tsall W ko P)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tsall_of_tsafe : forall {A} W (t : itree A) P, tsafe t P -> tsall W t P.
Proof.
  intros A W t; induction t; intros P Hs; cbn in *; try exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; apply IHt1; exact (H1 Hb) | intros _ Hb; apply IHt2; exact (H2 Hb)].
  - destruct Hs as [H1 H2]. split.
    + intros Hng. apply IHt. apply H1. apply mmap_refusable_k_iff. exact Hng.
    + intros _ a Hg. apply H. exact (H2 a Hg).
  - intros _. apply IHt2. exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; apply IHt1; exact (H1 Hb) | intros _ Hb; apply IHt2; exact (H2 Hb)].
Qed.

Lemma tsafe_of_tsall : forall {A} (t : itree A) P, tsall WAll t P -> tsafe t P.
Proof.
  intros A t; induction t; intros P Hs; cbn in *; try exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; apply IHt1; exact (H1 Hb) | intros Hb; apply IHt2; exact (H2 eq_refl Hb)].
  - destruct Hs as [H1 H2]. split.
    + intros Hr. apply IHt. apply H1. apply mmap_refusable_k_iff. exact Hr.
    + intros a Hg. apply H. apply H2; [discriminate | exact Hg].
  - apply IHt2. apply Hs. discriminate.
  - destruct Hs as [H1 H2]. split; [intros Hb; apply IHt1; exact (H1 Hb) | intros Hb; apply IHt2; apply H2; [discriminate | exact Hb]].
Qed.

Lemma tsall_WAll : forall {A} (t : itree A) P, tsall WAll t P <-> tsafe t P.
Proof. intros A t P. split; [apply tsafe_of_tsall | apply tsall_of_tsafe]. Qed.

Lemma tsall_mono : forall {A} W (t : itree A) (P Q : A -> mstate -> Prop),
  (forall a s, P a s -> Q a s) -> tsall W t P -> tsall W t Q.
Proof.
  intros A W t; induction t; intros P Q HPQ Hs; cbn in *.
  - apply HPQ. exact Hs.
  - exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; eapply IHt1; eauto | intros HW Hb; eapply IHt2; eauto].
  - destruct Hs as [H1 H2]. split; [intros HW; eapply IHt; eauto | intros HW a Hg; eapply H; eauto].
  - intros HW. eapply IHt2; eauto.
  - destruct Hs as [H1 H2]. split; [intros HW; eapply IHt1; eauto | intros HW Hb; eapply IHt2; eauto].
Qed.

Lemma tsall_bind : forall {A B} W (t : itree A) (f : A -> M B) (P : A -> mstate -> Prop) (Q : B -> mstate -> Prop),
  tsall W t P -> (forall a s, P a s -> tsall W (f a s) Q) -> tsall W (tbind t f) Q.
Proof.
  intros A B W t; induction t; intros f P Q Hs Hf; cbn in *.
  - apply Hf. exact Hs.
  - exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; eapply IHt1; eauto | intros HW Hb; eapply IHt2; eauto].
  - destruct Hs as [H1 H2]. split; [intros HW; eapply IHt; eauto | intros HW a Hg; eapply H; eauto].
  - intros HW. eapply IHt2; eauto.
  - destruct Hs as [H1 H2]. split; [intros HW; eapply IHt1; eauto | intros HW Hb; eapply IHt2; eauto].
Qed.

(* [comment removed for export] *)
Lemma tsall_bind_inv : forall {A B} W (t : itree A) (f : A -> M B) (Q : B -> mstate -> Prop),
  tsall W (tbind t f) Q -> tsall W t (fun a s => tsall W (f a s) Q).
Proof.
  intros A B W t; induction t; intros f Q Hs; cbn in *; try exact Hs.
  - destruct Hs as [H1 H2]. split; [intros Hb; apply IHt1; exact (H1 Hb) | intros HW Hb; apply IHt2; exact (H2 HW Hb)].
  - destruct Hs as [H1 H2]. split; [intros HW; apply IHt; exact (H1 HW) | intros HW a Hg; apply H; exact (H2 HW a Hg)].
  - intros HW. apply IHt2; auto.
  - destruct Hs as [H1 H2]. split; [intros HW; apply IHt1; auto | intros HW Hb; apply IHt2; auto].
Qed.

Lemma tsall_ret : forall {R} W (v : R) s (P : R -> mstate -> Prop), P v s -> tsall W (mret v s) P.
Proof. intros R W v s P H. exact H. Qed.

Lemma tsall_bind_ret : forall {B R} W (x : B) (k : B -> M R) s P,
  tsall W (k x s) P -> tsall W ((y <- mret x ;; k y) s) P.
Proof. intros B R W x k s P H. exact H. Qed.

Lemma tsall_assert : forall {R} W b (k : unit -> M R) s P,
  b = true -> tsall W (k tt s) P -> tsall W ((massert b ;; k tt) s) P.
Proof. intros R W b k s P -> H. exact H. Qed.

(* [comment removed for export] *)
Lemma tsall_tbind_assoc : forall {A B C} W (t : itree A) (f : A -> M B) (g : B -> M C) P,
  tsall W (tbind t (fun x s => tbind (f x s) g)) P <-> tsall W (tbind (tbind t f) g) P.
Proof.
  intros A B C W t f g P. induction t; cbn; try tauto.
  - split; intros [H1 H2]; split; try tauto; intros HW a Ha; apply (H a); apply H2; assumption.
Qed.

Lemma tsall_assoc : forall {R B C} W (m0 : M B) (f : B -> M C) (g : C -> M R) s P,
  tsall W ((x <- m0 ;; y <- f x ;; g y) s) P -> tsall W ((y <- (x <- m0 ;; f x) ;; g y) s) P.
Proof.
  intros R B C W m0 f g s P H. unfold mbind in *. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). exact H.
Qed.

Lemma tsall_assoc_r : forall {R B C} W (m0 : M B) (f : B -> M C) (g : C -> M R) s P,
  tsall W ((y <- (x <- m0 ;; f x) ;; g y) s) P -> tsall W ((x <- m0 ;; y <- f x ;; g y) s) P.
Proof.
  intros R B C W m0 f g s P H. unfold mbind in *. apply (proj2 (tsall_tbind_assoc _ _ _ _ _)). exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tsafe_tbind_mret : forall {A} (t : itree A) P, tsafe (tbind t (fun a s => TRet a s)) P <-> tsafe t P.
Proof.
  intros A t P; induction t; cbn; try tauto.
  split; intros [H1 H2]; split; try tauto; intros a Ha; apply (H a); apply H2; exact Ha.
Qed.

(* [comment removed for export] *)
Lemma tw_lift : forall {B R} W (op : M B) s (Post : B -> mstate -> Prop) (K : B -> M R) (P : R -> mstate -> Prop),
  (forall (K' : B -> M B) (P' : B -> mstate -> Prop),
      (forall x s', Post x s' -> tsafe (K' x s') P') -> tsafe ((x <- op ;; K' x) s) P') ->
  (forall x s', Post x s' -> tsall W (K x s') P) ->
  tsall W ((x <- op ;; K x) s) P.
Proof.
  intros B R W op s Post K P Hop HK.
  assert (Hs : tsafe (op s) Post).
  { specialize (Hop (fun x s' => mret x s') Post (fun x s' H => H)).
    unfold mbind in Hop. unfold mret in Hop. apply (proj1 (tsafe_tbind_mret _ _)). exact Hop. }
  unfold mbind. eapply tsall_bind; [apply tsall_of_tsafe; exact Hs | exact HK].
Qed.

(* [comment removed for export] *)
Lemma tw_lift_leaves : forall {B R} W (op : M B) s (Post : B -> mstate -> Prop) (K : B -> M R) (P : R -> mstate -> Prop),
  tsafe (op s) Post ->
  (forall x s', Post x s' -> tsall W (K x s') P) ->
  tsall W ((x <- op ;; K x) s) P.
Proof.
  intros B R W op s Post K P Hs HK. unfold mbind. eapply tsall_bind; [apply tsall_of_tsafe; exact Hs | exact HK].
Qed.

(* [comment removed for export] *)
Lemma tsafe_leaves_of_cps : forall {B} (op : M B) s (Post : B -> mstate -> Prop),
  (forall (K' : B -> M B) (P' : B -> mstate -> Prop),
      (forall x s', Post x s' -> tsafe (K' x s') P') -> tsafe ((x <- op ;; K' x) s) P') ->
  tsafe (op s) Post.
Proof.
  intros B op s Post Hop.
  specialize (Hop (fun x s' => mret x s') Post (fun x s' H => H)).
  unfold mbind, mret in Hop. apply (proj1 (tsafe_tbind_mret _ _)). exact Hop.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
  Context {A : Type}.
  Variable W : wmode.
  Implicit Types P : A -> mstate -> Prop.

  Lemma tw_ret_node : forall a s P, P a s -> tsall W (TRet a s) P.
  Proof. intros a s P H. exact H. Qed.

  Lemma tw_brk : forall req vm (kf ko : itree A) P,
    tsall W kf P ->
    (W = WAll -> brk_grow_ok_vm vm req req = true -> tsall W ko P) ->
    tsall W (TBrk req vm kf ko) P.
  Proof. intros req vm kf ko P Hf Ho. cbn. split; [intros _; exact Hf | exact Ho]. Qed.

  Lemma tw_mmap : forall k len vm (kf : itree A) (ko : word -> itree A) P,
    ((W <> WOk \/ forall a, mmap_grant_ok k vm a (mm_len len) = false) -> tsall W kf P) ->
    (W <> WFail -> forall a, mmap_grant_ok k vm a (mm_len len) = true -> tsall W (ko a) P) ->
    tsall W (TMmap k len vm kf ko) P.
  Proof. intros k len vm kf ko P Hf Ho. cbn. split; [intros Hng; apply Hf; right; exact Hng | exact Ho]. Qed.

  (* [comment removed for export] *)
  Lemma tw_mmap04 : forall k len vm (kf : itree A) (ko : word -> itree A) P,
    ((forall a, mmap_grant_ok k vm a (mm_len len) = false) -> tsall W kf P) ->
    (W <> WFail -> forall a, mmap_grant_ok k vm a (mm_len len) = true -> tsall W (ko a) P) ->
    tsall W (TMmap k len vm kf ko) P.
  Proof. intros k len vm kf ko P Hf Ho. cbn. split; [exact Hf | exact Ho]. Qed.

  (* [comment removed for export] *)
  Lemma tw_mmap_both : forall k len vm (kf : itree A) (ko : word -> itree A) P,
    tsall W kf P ->
    (forall a, mmap_grant_ok k vm a (mm_len len) = true -> tsall W (ko a) P) ->
    tsall W (TMmap k len vm kf ko) P.
  Proof. intros k len vm kf ko P Hf Ho. cbn. split; [intros _; exact Hf | intros _; exact Ho]. Qed.

  Lemma tw_mmap_fixed : forall addr len (k1 k2 k3 : itree A) P,
    (W <> WOk -> tsall W k1 P) -> (W <> WFail -> tsall W k2 P) -> (W = WAll -> tsall W k3 P) ->
    tsall W (TMmapFixed addr len k1 k2 k3) P.
  Proof. intros addr len k1 k2 k3 P H1 H2 H3. cbn. exact H2. Qed.

  (* [comment removed for export] *)
  Lemma tw_mmap_fixed04 : forall addr len (k1 k2 k3 : itree A) P,
    (W <> WFail -> tsall W k2 P) -> tsall W (TMmapFixed addr len k1 k2 k3) P.
  Proof. intros addr len k1 k2 k3 P H2. cbn. exact H2. Qed.

  Lemma tw_mprot : forall addr len vm (kf ko : itree A) P,
    ((W <> WOk \/ mprot_ok_vm vm addr (page_round_up len) = false) -> tsall W kf P) ->
    (W <> WFail -> mprot_ok_vm vm addr (page_round_up len) = true -> tsall W ko P) ->
    tsall W (TMprot addr len vm kf ko) P.
  Proof. intros addr len vm kf ko P H1 H2. cbn. split; [intros Hb; apply H1; right; exact Hb | exact H2]. Qed.

  (* [comment removed for export] *)
  Lemma tw_mprot04 : forall addr len vm (kf ko : itree A) P,
    (mprot_ok_vm vm addr (page_round_up len) = false -> tsall W kf P) ->
    (W <> WFail -> mprot_ok_vm vm addr (page_round_up len) = true -> tsall W ko P) ->
    tsall W (TMprot addr len vm kf ko) P.
  Proof. intros addr len vm kf ko P H1 H2. cbn. split; assumption. Qed.
End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SysW.
  Context {R : Type}.
  Variable W : wmode.
  Implicit Types P : R -> mstate -> Prop.

  (* [comment removed for export] *)
  Lemma tw_sys_brk_grow : forall (req : word) s (K : word -> M R) P,
    0 < bv_unsigned (vm_brk (ms_vm s)) ->
    bv_unsigned (vm_start_brk (ms_vm s)) <= bv_unsigned req ->
    bv_unsigned (vm_brk (ms_vm s)) < bv_unsigned req ->
    tsall W (K (vm_brk (ms_vm s)) s) P ->
    (W = WAll -> brk_grow_ok_vm (ms_vm s) req req = true ->
       tsall W (K req (upd s (apply_zeros (ms_mem s) (brk_zeros req req (vm_brk (ms_vm s)))) (vm_brk_grow req (ms_vm s)))) P) ->
    tsall W ((x <- sys_brk_grow req ;; K x) s) P.
  Proof.
    intros req s K P H1 H2 H3 Hf Ho. unfold mbind, sys_brk_grow.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2), (proj2 (Z.ltb_lt _ _) H3). cbn.
    split; [intros _; exact Hf | exact Ho].
  Qed.

  Lemma tw_sys_brk_query : forall s (K : word -> M R) P,
    tsall W (K (vm_brk (ms_vm s)) s) P -> tsall W ((x <- sys_brk_query ;; K x) s) P.
  Proof. intros s K P H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma tw_sys_mmap : forall mk (len : word) s (K : word -> M R) P,
    0 < bv_unsigned len -> bv_unsigned len < 2^62 ->
    ((W <> WOk \/ forall a, mmap_grant_ok mk (ms_vm s) a (mm_len len) = false) ->
       tsall W ((set_errno ENOMEM ;; K MAP_FAILED) s) P) ->
    (W <> WFail -> forall a, mmap_grant_ok mk (ms_vm s) a (mm_len len) = true ->
       tsall W (K a (match mk with
                     | MMrw => upd s (zfill a (page_round_up len) (ms_mem s)) (vm_mmap a (page_round_up len) (ms_vm s))
                     | MMnone => upd s (unfill a (page_round_up len) (ms_mem s)) (vm_noacc a (page_round_up len) (ms_vm s))
                     end)) P) ->
    tsall W ((x <- sys_mmap mk len ;; K x) s) P.
  Proof.
    intros mk len s K P H1 H2 Hf Ho. unfold mbind, sys_mmap.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2). cbn - [tsall].
    apply tw_mmap.
    - intros HW. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall]. exact (Hf HW).
    - intros HW a Hg. specialize (Ho HW a Hg). destruct mk; exact Ho.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_sys_mmap04 : forall mk (len : word) s (K : word -> M R) P,
    0 < bv_unsigned len -> bv_unsigned len < 2^62 ->
    ((forall a, mmap_grant_ok mk (ms_vm s) a (mm_len len) = false) ->
       tsall W ((set_errno ENOMEM ;; K MAP_FAILED) s) P) ->
    (W <> WFail -> forall a, mmap_grant_ok mk (ms_vm s) a (mm_len len) = true ->
       tsall W (K a (match mk with
                     | MMrw => upd s (zfill a (page_round_up len) (ms_mem s)) (vm_mmap a (page_round_up len) (ms_vm s))
                     | MMnone => upd s (unfill a (page_round_up len) (ms_mem s)) (vm_noacc a (page_round_up len) (ms_vm s))
                     end)) P) ->
    tsall W ((x <- sys_mmap mk len ;; K x) s) P.
  Proof.
    intros mk len s K P H1 H2 Hf Ho. unfold mbind, sys_mmap.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2). cbn - [tsall].
    apply tw_mmap04.
    - intros HW. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall]. exact (Hf HW).
    - intros HW a Hg. specialize (Ho HW a Hg). destruct mk; exact Ho.
  Qed.

  (* [comment removed for export] *)
  Lemma tw_sys_mmap_fixed_none04 : forall (addr len : word) s (K : word -> M R) P,
    0 < bv_unsigned len -> bv_unsigned len < 2^62 ->
    bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s) ->
    bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
    region_free (vm_reserved (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    (W <> WFail -> tsall W (K addr (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_fixed_ok addr (page_round_up len) (ms_vm s)))) P) ->
    tsall W ((x <- sys_mmap_fixed_none addr len ;; K x) s) P.
  Proof.
    intros addr len s K P H1 H2 H3 H4 H0 H5 H6 Ho. unfold mbind, sys_mmap_fixed_none.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3),
            (proj2 (Z.eqb_eq _ _) H4), (proj2 (Z.ltb_lt _ _) H0), H5, H6. cbn - [tsall].
    apply tw_mmap_fixed04. exact Ho.
  Qed.

  Lemma tw_sys_mmap_fixed_none : forall (addr len : word) s (K : word -> M R) P,
    0 < bv_unsigned len -> bv_unsigned len < 2^62 ->
    bv_unsigned addr + page_round_up_Z (bv_unsigned len) <= alloc_top (ms_vm s) ->
    bv_unsigned addr mod page_size = 0 -> 0 < bv_unsigned addr ->
    region_free (vm_reserved (ms_vm s)) addr (page_round_up len) = true ->
    map_contains (vm_maps (ms_vm s)) addr (page_round_up len) = true ->
    (W <> WOk -> tsall W ((set_errno ENOMEM ;; K MAP_FAILED) s) P) ->
    (W <> WFail -> tsall W (K addr (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_fixed_ok addr (page_round_up len) (ms_vm s)))) P) ->
    (W = WAll -> tsall W ((set_errno ENOMEM ;; K MAP_FAILED)
                   (upd s (unfill addr (page_round_up len) (ms_mem s)) (vm_fixed_destroy addr (page_round_up len) (ms_vm s)))) P) ->
    tsall W ((x <- sys_mmap_fixed_none addr len ;; K x) s) P.
  Proof.
    intros addr len s K P H1 H2 H3 H4 H0 H5 H6 Hk Ho Hd. unfold mbind, sys_mmap_fixed_none.
    rewrite (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3),
            (proj2 (Z.eqb_eq _ _) H4), (proj2 (Z.ltb_lt _ _) H0), H5, H6. cbn - [tsall].
    apply tw_mmap_fixed.
    - intros HW. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall]. exact (Hk HW).
    - exact Ho.
    - intros HW. apply (proj1 (tsall_tbind_assoc _ _ _ _ _)). cbn - [tsall]. exact (Hd HW).
  Qed.

  (* [comment removed for export] *)
  Lemma tw_sys_mprotect_node : forall (addr len : word) vm (kf ko : itree R) P,
    ((W <> WOk \/ mprot_ok_vm vm addr (page_round_up len) = false) -> tsall W kf P) ->
    (W <> WFail -> mprot_ok_vm vm addr (page_round_up len) = true -> tsall W ko P) ->
    tsall W (TMprot addr len vm kf ko) P.
  Proof. intros. apply tw_mprot; assumption. Qed.
End SysW.

End WithLayout.
