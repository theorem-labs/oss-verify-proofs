(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SimInv Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_win (s : mstate) (a : word) : Prop :=
  ms_lo s <= bv_unsigned a < ms_hi s.

Definition magree (s : mstate) (mm : word -> option byte) : Prop :=
  forall a : word, ~ in_win s a -> mm a = ms_mem s a.

Lemma magree_refl : forall s, magree s (ms_mem s).
Proof. intros s a _. reflexivity. Qed.

Lemma acc_ok_out : forall s (a : word) n (x : word),
  acc_ok s a n = true ->
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + n ->
  ~ in_win s x.
Proof.
  intros s a n x Hok Hx Hin. unfold acc_ok in Hok. unfold in_win in Hin.
  apply Bool.orb_true_iff in Hok. destruct Hok as [H | H].
  - apply Z.leb_le in H. lia.
  - apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Lemma acc_ok_nowrap : forall s (a : word) n,
  0 <= n -> ms_lo s <= 2^64 -> acc_ok s a n = true -> bv_unsigned a + n <= 2^64.
Proof.
  intros s a n Hn Hlo Hok. unfold acc_ok in Hok.
  apply Bool.orb_true_iff in Hok. destruct Hok as [H | H].
  - apply Z.leb_le in H. lia.
  - apply andb_prop in H. destruct H as [_ H2]. apply Z.leb_le in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_ext : forall segs n m1 m2 (a : word),
  bv_unsigned a + Z.of_nat n <= 2^64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> m1 x = m2 x) ->
  store_ok segs m1 a n = store_ok segs m2 a n.
Proof.
  intros segs n. induction n as [|n IH]; intros m1 m2 a Hnw Hext; [reflexivity|].
  cbn [store_ok]. unfold wview.
  rewrite (Hext a ltac:(pose proof (u64_range a); lia)).
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    rewrite (IH m1 m2 (a + 1)%bv ltac:(lia) ltac:(intros x Hx; apply Hext; lia)).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma wbytes_pointwise : forall bs m1 m2 (a x : word),
  m1 x = m2 x -> wbytes m1 a bs x = wbytes m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. cbn. destruct (bv_eqb x a); [reflexivity | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma magree_wbytes : forall s mm (a : word) bs h,
  magree s mm -> magree (upd s (wbytes (ms_mem s) a bs) h) (wbytes mm a bs).
Proof.
  intros s mm a bs h Hag x Hx. cbn. apply wbytes_pointwise. apply Hag. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma magree_wbytes_win : forall s mm (a : word) bs,
  magree s mm ->
  bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
  ms_lo s <= bv_unsigned a -> bv_unsigned a + Z.of_nat (length bs) <= ms_hi s ->
  magree s (wbytes mm a bs).
Proof.
  intros s mm a bs Hag Hnw Hlo Hhi x Hx. unfold in_win in Hx.
  pose proof (u64_range x) as Hxr.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hb | Hb].
  - rewrite wbytes_below by lia. apply Hag. unfold in_win. lia.
  - destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hc | Hc].
    + exfalso. apply Hx. lia.
    + rewrite wbytes_above by lia. apply Hag. unfold in_win. lia.
Qed.

(* [comment removed for export] *)
Lemma magree_zfill : forall s mm (a n : word) h,
  magree s mm -> magree (upd s (zfill a n (ms_mem s)) h) (zfill a n mm).
Proof.
  intros s mm a n h Hag x Hx. cbn. unfold zfill, zmem. rewrite (Hag x Hx). reflexivity.
Qed.

Lemma magree_unfill : forall s mm (a n : word) h,
  magree s mm -> magree (upd s (unfill a n (ms_mem s)) h) (unfill a n mm).
Proof.
  intros s mm a n h Hag x Hx. cbn. unfold unfill. rewrite (Hag x Hx). reflexivity.
Qed.

Lemma magree_apply_zeros : forall s mm zs h,
  magree s mm -> magree (upd s (apply_zeros (ms_mem s) zs) h) (apply_zeros mm zs).
Proof.
  intros s mm zs h Hag x Hx. cbn. unfold apply_zeros.
  destruct zs; [apply Hag; exact Hx|]. rewrite (Hag x Hx). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma magree_upd_vm : forall s mm h, magree s mm -> magree (upd s (ms_mem s) h) mm.
Proof. intros s mm h Hag x Hx. cbn. apply Hag. exact Hx. Qed.

Lemma upd_lo : forall s m h, ms_lo (upd s m h) = ms_lo s. Proof. reflexivity. Qed.
Lemma upd_hi : forall s m h, ms_hi (upd s m h) = ms_hi s. Proof. reflexivity. Qed.
Lemma upd_mem : forall s m h, ms_mem (upd s m h) = m. Proof. reflexivity. Qed.
Lemma upd_vm : forall s m h, ms_vm (upd s m h) = h. Proof. reflexivity. Qed.
Lemma upd_upd : forall s m h m' h', upd (upd s m h) m' h' = upd s m' h'.
Proof. reflexivity. Qed.

Section WithLayout.
Context {ML : MallocLayout}.

(* [comment removed for export] *)
Lemma magree_rdn : forall s mm (a : word) (n : nat),
  magree s mm -> ms_lo s <= 2^64 -> acc_ok s a (Z.of_nat n) = true ->
  rdn ml_segs mm a n = rdn ml_segs (ms_mem s) a n.
Proof.
  intros s mm a n Hag Hlo Hok.
  apply rdn_ext; [apply (acc_ok_nowrap s a (Z.of_nat n)); [lia | exact Hlo | exact Hok] |].
  intros x Hx. apply Hag. eapply acc_ok_out; [exact Hok | exact Hx].
Qed.

Lemma magree_store_ok : forall s mm (a : word) (n : nat),
  magree s mm -> ms_lo s <= 2^64 -> acc_ok s a (Z.of_nat n) = true ->
  store_ok ml_segs mm a n = store_ok ml_segs (ms_mem s) a n.
Proof.
  intros s mm a n Hag Hlo Hok.
  apply store_ok_ext; [apply (acc_ok_nowrap s a (Z.of_nat n)); [lia | exact Hlo | exact Hok] |].
  intros x Hx. apply Hag. eapply acc_ok_out; [exact Hok | exact Hx].
Qed.

(* [comment removed for export] *)
Lemma magree_rd : forall s mm (a : word) (n : nat) bs,
  magree s mm -> ms_lo s <= 2^64 -> acc_ok s a (Z.of_nat n) = true ->
  rdn ml_segs (ms_mem s) a n = Some bs -> rdn ml_segs mm a n = Some bs.
Proof. intros s mm a n bs Hag Hlo Hok H. rewrite (magree_rdn s mm a n Hag Hlo Hok). exact H. Qed.

Lemma magree_sok : forall s mm (a : word) (n : nat),
  magree s mm -> ms_lo s <= 2^64 -> acc_ok s a (Z.of_nat n) = true ->
  store_ok ml_segs (ms_mem s) a n = true -> store_ok ml_segs mm a n = true.
Proof. intros s mm a n Hag Hlo Hok H. rewrite (magree_store_ok s mm a n Hag Hlo Hok). exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma le_val_u : forall bs, (length bs <= 8)%nat -> bytes_le_to_Z bs = bv_unsigned (le_val bs).
Proof.
  intros bs Hlen. unfold le_val.
  pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as H0.
  assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^64) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_small_unsigned by lia. reflexivity.
Qed.

Lemma rdn_length : forall segs m n (a : word) bs, rdn segs m a n = Some bs -> length bs = n.
Proof.
  intros segs m n. induction n as [|n IH]; intros a bs H; cbn [rdn] in H.
  - inversion H. reflexivity.
  - destruct (match m a with Some b => Some b | None => seg_rom segs a end) as [b|]; [|discriminate].
    destruct (rdn segs m (a + 1) n) as [rest|] eqn:E; [|discriminate].
    inversion H; subst. cbn. f_equal. eapply IH. exact E.
Qed.

Section Inversions.
  Context {A : Type}.
  Implicit Types (k : word -> M A) (P : A -> mstate -> Prop) (s : mstate) (a v : word).

  Lemma tsafe_rd_inv : forall n a (k : list byte -> M A) s P,
    tsafe ((bs <- m_rd n a ;; k bs) s) P ->
    exists bs, acc_ok s a (Z.of_nat n) = true /\ rdn ml_segs (ms_mem s) a n = Some bs /\
               length bs = n /\ (bs <- m_rd n a ;; k bs) s = k bs s.
  Proof.
    intros n a k s P H. unfold mbind, m_rd in *.
    destruct (acc_ok s a (Z.of_nat n)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a n) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    exists bs. split; [reflexivity | split; [reflexivity | split; [eapply rdn_length; exact Hrd | reflexivity]]].
  Qed.

  Lemma tsafe_ld_inv : forall a k s P,
    tsafe ((x <- m_ld a ;; k x) s) P ->
    exists bs, acc_ok s a 8 = true /\ rdn ml_segs (ms_mem s) a 8 = Some bs /\
               bytes_le_to_Z bs = bv_unsigned (le_val bs) /\ (x <- m_ld a ;; k x) s = k (le_val bs) s.
  Proof.
    intros a k s P H. unfold m_ld, mbind, m_rd, mret in *.
    destruct (acc_ok s a (Z.of_nat 8)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a 8) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    exists bs. cbn. split; [exact Hok | split; [reflexivity | split; [|reflexivity]]].
    apply le_val_u. rewrite (rdn_length _ _ _ _ _ Hrd). lia.
  Qed.

  Lemma tsafe_lwu_inv : forall a k s P,
    tsafe ((x <- m_lwu a ;; k x) s) P ->
    exists bs, acc_ok s a 4 = true /\ rdn ml_segs (ms_mem s) a 4 = Some bs /\
               bytes_le_to_Z bs = bv_unsigned (le_val bs) /\ (x <- m_lwu a ;; k x) s = k (le_val bs) s.
  Proof.
    intros a k s P H. unfold m_lwu, mbind, m_rd, mret in *.
    destruct (acc_ok s a (Z.of_nat 4)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a 4) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    exists bs. cbn. split; [exact Hok | split; [reflexivity | split; [|reflexivity]]].
    apply le_val_u. rewrite (rdn_length _ _ _ _ _ Hrd). lia.
  Qed.

  Lemma tsafe_lw_inv : forall a k s P,
    tsafe ((x <- m_lw a ;; k x) s) P ->
    exists bs, acc_ok s a 4 = true /\ rdn ml_segs (ms_mem s) a 4 = Some bs /\
               bytes_le_to_Z bs = bv_unsigned (le_val bs) /\ (x <- m_lw a ;; k x) s = k (v_lw (le_val bs)) s.
  Proof.
    intros a k s P H. unfold m_lw, mbind, m_rd, mret in *.
    destruct (acc_ok s a (Z.of_nat 4)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a 4) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    exists bs. cbn. split; [exact Hok | split; [reflexivity | split; [|reflexivity]]].
    apply le_val_u. rewrite (rdn_length _ _ _ _ _ Hrd). lia.
  Qed.

  Lemma tsafe_lhu_inv : forall a k s P,
    tsafe ((x <- m_lhu a ;; k x) s) P ->
    exists bs, acc_ok s a 2 = true /\ rdn ml_segs (ms_mem s) a 2 = Some bs /\
               bytes_le_to_Z bs = bv_unsigned (le_val bs) /\ (x <- m_lhu a ;; k x) s = k (le_val bs) s.
  Proof.
    intros a k s P H. unfold m_lhu, mbind, m_rd, mret in *.
    destruct (acc_ok s a (Z.of_nat 2)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a 2) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    exists bs. cbn. split; [exact Hok | split; [reflexivity | split; [|reflexivity]]].
    apply le_val_u. rewrite (rdn_length _ _ _ _ _ Hrd). lia.
  Qed.

  Lemma tsafe_lbu_inv : forall a k s P,
    tsafe ((x <- m_lbu a ;; k x) s) P ->
    exists b, acc_ok s a 1 = true /\ rdn ml_segs (ms_mem s) a 1 = Some [b] /\
              (x <- m_lbu a ;; k x) s = k (Z_to_bv 64 (bv_unsigned b)) s.
  Proof.
    intros a k s P H. unfold m_lbu, mbind, m_rd, mret, mcrash in *.
    destruct (acc_ok s a (Z.of_nat 1)) eqn:Hok; [|cbn in H; contradiction].
    destruct (rdn ml_segs (ms_mem s) a 1) as [bs|] eqn:Hrd; [|cbn in H; contradiction].
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    destruct bs as [|b [|b' bs']]; cbn in Hlen; try discriminate.
    exists b. cbn. split; [exact Hok | split; reflexivity].
  Qed.

  Lemma tsafe_st_inv : forall n a v (k : unit -> M A) s P,
    tsafe ((x <- m_st n a v ;; k x) s) P ->
    acc_ok s a (Z.of_nat n) = true /\ store_ok ml_segs (ms_mem s) a n = true /\
    (x <- m_st n a v ;; k x) s = k tt (upd s (wbytes (ms_mem s) a (word_to_le_bytes n v)) (ms_vm s)).
  Proof.
    intros n a v k s P H. unfold m_st, mbind in *.
    destruct (acc_ok s a (Z.of_nat n)) eqn:Hok; [|cbn in H; contradiction].
    destruct (st_zone a (Z.of_nat n)) eqn:Hz; [|cbn in H; contradiction].
    destruct (store_ok ml_segs (ms_mem s) a n) eqn:Hso; [|cbn in H; contradiction].
    cbn. split; [reflexivity | split; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma tsafe_st_inv0 : forall n a v s (Q : unit -> mstate -> Prop),
    tsafe (m_st n a v s) Q ->
    acc_ok s a (Z.of_nat n) = true /\ store_ok ml_segs (ms_mem s) a n = true /\
    m_st n a v s = mret tt (upd s (wbytes (ms_mem s) a (word_to_le_bytes n v)) (ms_vm s)).
  Proof.
    intros n a v s Q H. unfold m_st in *.
    destruct (acc_ok s a (Z.of_nat n)) eqn:Hok; [|cbn in H; contradiction].
    destruct (st_zone a (Z.of_nat n)) eqn:Hz; [|cbn in H; contradiction].
    destruct (store_ok ml_segs (ms_mem s) a n) eqn:Hso; [|cbn in H; contradiction].
    repeat split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma tsafe_st_zone : forall n a v (k : unit -> M A) s P,
    tsafe ((x <- m_st n a v ;; k x) s) P -> st_zone a (Z.of_nat n) = true.
  Proof.
    intros n a v k s P H. unfold m_st, mbind in *.
    destruct (acc_ok s a (Z.of_nat n)); [|cbn in H; contradiction].
    destruct (st_zone a (Z.of_nat n)); [reflexivity | cbn in H; contradiction].
  Qed.

  Lemma st_zone_spec : forall a n, st_zone a n = true <->
    (bv_unsigned a + n <= IMG_LO \/ IMG_HI <= bv_unsigned a \/
     (bv_unsigned A_ERRNO <= bv_unsigned a /\ bv_unsigned a + n <= bv_unsigned A_ERRNO + 4) \/
     (bv_unsigned A_CTX <= bv_unsigned a /\ bv_unsigned a + n <= bv_unsigned A_CTX + CTX_SIZE)).
  Proof.
    intros a n. unfold st_zone. rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.leb_le. tauto.
  Qed.

  Lemma tsafe_assert_inv : forall b (k : unit -> M A) s P,
    tsafe ((x <- massert b ;; k x) s) P -> b = true /\ (x <- massert b ;; k x) s = k tt s.
  Proof.
    intros b k s P H. unfold massert, mbind, mret, mcrash in *.
    destruct b; [split; reflexivity | cbn in H; contradiction].
  Qed.

  (* [comment removed for export] *)
  Lemma mret_bind : forall {B} (x : B) (k : B -> M A) s, (y <- mret x ;; k y) s = k x s.
  Proof. reflexivity. Qed.

  Lemma mbind_assoc : forall {B C} (m : M B) (f : B -> M C) (g : C -> M A) s,
    (y <- (x <- m ;; f x) ;; g y) s = (x <- m ;; y <- f x ;; g y) s.
  Proof.
    intros B C m f g s. unfold mbind. generalize (m s). clear m.
    fix IH 1. intros t. destruct t; cbn; try reflexivity.
    - rewrite (IH t1), (IH t2). reflexivity.
    - rewrite (IH t). f_equal. apply functional_extensionality. intros a. apply IH.
    - rewrite (IH t1), (IH t2), (IH t3). reflexivity.
    - rewrite (IH t1), (IH t2). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma mret_bind_k : forall {B} (x : B) (k : B -> M A) s, mbind (mret x) k s = k x s.
  Proof. reflexivity. Qed.
  Lemma mbind_assoc_k : forall {B C} (m : M B) (f : B -> M C) (k : C -> M A) s,
    mbind (mbind m f) k s = mbind m (fun x => mbind (f x) k) s.
  Proof. intros. apply mbind_assoc. Qed.

  (* [comment removed for export] *)
  Lemma tsafe_bind_inv : forall {B} (t : itree B) (f : B -> M A) (Q : A -> mstate -> Prop),
    tsafe (tbind t f) Q -> tsafe t (fun x s => tsafe (f x s) Q).
  Proof.
    intros B t; induction t; intros f Q Hs; cbn in *; intuition eauto.
  Qed.

  (* [comment removed for export] *)
  Lemma tsafe_teq : forall (t t' : itree A) P, tsafe t' P -> t = t' -> tsafe t P.
  Proof. intros t t' P H ->. exact H. Qed.
End Inversions.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tshape_TRet : forall {A} (a : A) s L, tshape (TRet a s) L = L a s.
Proof. reflexivity. Qed.
Lemma tshape_mret : forall {A} (a : A) s L, tshape (mret a s) L = L a s.
Proof. reflexivity. Qed.
Lemma tshape_TCrash : forall {A} (L : A -> mstate -> TSet), tshape TCrash L = t_nil.
Proof. reflexivity. Qed.

Section Rz.
  Context {fx : FPState}.

  Lemma rz_tshape_eq : forall {A} c (t t' : itree A) (L : A -> mstate -> TSet),
    realizes ml_segs c (tshape t L) -> t = t' -> realizes ml_segs c (tshape t' L).
  Proof. intros A c t t' L H <-. exact H. Qed.

  (* [comment removed for export] *)
  Lemma rz_bind_shape : forall {A B} c (m : M A) (k : A -> M B) (s : mstate) (L : B -> mstate -> TSet),
    realizes ml_segs c (tshape (m s) (fun a s' => tshape (k a s') L)) ->
    realizes ml_segs c (tshape (mbind m k s) L).
  Proof.
    intros A B c m k s L H. unfold mbind.
    eapply rz_conseq; [exact H | apply t_eq_sym; apply tshape_bind].
  Qed.
End Rz.

End WithLayout.
