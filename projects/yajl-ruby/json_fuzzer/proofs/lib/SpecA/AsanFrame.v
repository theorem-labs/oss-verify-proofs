(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanWf1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope am_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac pzW := lazymatch goal with |- presW _ (poison_zero _ _) => unfold poison_zero; apply presW_ret end.

Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition mu (s : astate) (c : Z) : Z := rg_mapped_user (get_region s c).

(* [comment removed for export] *)
Definition fsame (s0 s : astate) : Prop := (forall c, mu s c = mu s0 c) /\ as_residue s = as_residue s0.
Definition fgrow (c : Z) (s0 s : astate) : Prop :=
  (forall c', c' <> c -> mu s c' = mu s0 c') /\ mu s0 c <= mu s c <= mu s0 c + kUserMapSize /\ as_residue s = as_residue s0.

Lemma fsame_refl : forall s, fsame s s. Proof. intros s; split; reflexivity. Qed.
Lemma fsame_trans : forall a b c, fsame a b -> fsame b c -> fsame a c.
Proof. intros a b c [A1 A2] [B1 B2]. split; [intros x; rewrite B1, A1; reflexivity| congruence]. Qed.
Lemma fgrow_refl : forall c s, fgrow c s s. Proof. intros c s. split; [auto|]. split; [unfold kUserMapSize; lia| reflexivity]. Qed.
Lemma fsame_fgrow : forall c a b, fsame a b -> fgrow c a b.
Proof. intros c a b [A1 A2]. split; [auto|]. split; [rewrite A1; unfold kUserMapSize; lia| exact A2]. Qed.
Lemma fgrow_fsame_trans : forall c x y z, fgrow c x y -> fsame y z -> fgrow c x z.
Proof. intros c x y z (A1 & A2 & A3) [B1 B2]. split; [intros c' H; rewrite (B1 c'); auto|]. split; [rewrite B1; lia| congruence]. Qed.
Lemma fsame_fgrow_trans : forall c x y z, fsame x y -> fgrow c y z -> fgrow c x z.
Proof. intros c x y z [B1 B2] (A1 & A2 & A3). split; [intros c' H; rewrite (A1 c' H); auto|]. split; [rewrite <- (B1 c); lia| congruence]. Qed.

(* [comment removed for export] *)
Lemma residue_pages_len : forall mb msz, 0 < msz ->
  zlen (residue_pages mb msz) <= (if msz <? kBigMapSize then 20 else 2).
Proof.
  intros mb msz POS. unfold residue_pages. destruct (msz <? kBigMapSize) eqn:SM; [| unfold zlen; cbn; lia].
  apply Z.ltb_lt in SM. unfold hull_pages, zlen. rewrite length_map, length_seq.
  unfold shadow_page, mem_to_shadow, round_down, kPageSize, kBigMapSize in *.
  set (a := kShadowBase + mb / 8). set (b := kShadowBase + (mb + msz - 1) / 8).
  assert (D8 : b - a <= msz / 8 + 1).
  { subst a b. pose proof (Z.div_mod mb 8 ltac:(lia)). pose proof (Z.mod_pos_bound mb 8 ltac:(lia)).
    pose proof (Z.div_mod (mb + msz - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (mb + msz - 1) 8 ltac:(lia)).
    pose proof (Z.div_mod msz 8 ltac:(lia)). pose proof (Z.mod_pos_bound msz 8 ltac:(lia)). nia. }
  assert (PD : b / 4096 * 4096 - a / 4096 * 4096 <= b - a + 4096).
  { pose proof (Z.div_mod a 4096 ltac:(lia)). pose proof (Z.mod_pos_bound a 4096 ltac:(lia)).
    pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)). lia. }
  assert (Q : (b / 4096 * 4096 - a / 4096 * 4096) / 4096 <= 17).
  { apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|].
    assert (msz / 8 < 65536) by (apply Z.div_lt_upper_bound; lia). lia. }
  destruct (Z_lt_le_dec ((b / 4096 * 4096 - a / 4096 * 4096) / 4096 + 1) 0); [rewrite Z2Nat.nonpos by lia; lia|].
  rewrite Z2Nat.id by lia. lia.
Qed.

Section FR.
Variable E : aenv.
Local Notation SB := (ae_space_beg E).

Lemma mu_upd_region : forall s c r c', mu (set_region c r s) c' = if Z.eq_dec c' c then rg_mapped_user r else mu s c'.
Proof. intros. unfold mu. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite get_set_region_eq| rewrite get_set_region_ne by auto]; reflexivity. Qed.

(* [comment removed for export] *)
Lemma call_mmap_fixed_W : forall I a l, presW I (call_mmap_fixed a l).
Proof. intros; unfold call_mmap_fixed. pw. Qed.
Lemma call_munmap_W : forall I a l, presW I (call_munmap a l).
Proof. intros; unfold call_munmap. pw. Qed.
Lemma call_mmap_anon_W : forall I l, presW I (call_mmap_anon E l).
Proof. intros; unfold call_mmap_anon. pw. Qed.
Lemma poison_zero_W : forall I u L, presW I (poison_zero u L).
Proof. intros; unfold poison_zero. pw. Qed.

(* [comment removed for export] *)
Ltac fr_solve :=
  match goal with
  | H : fsame ?s0 ?s |- fsame ?s0 _ =>
      destruct H as [?FM ?FRs]; split; [intros ?cc; unfold mu in *; cbn -[get_region set_region]; rewrite ?get_region_upd_ts; try rewrite FM; auto| cbn; exact FRs]
  end.

(* [comment removed for export] *)
Ltac fs_close :=
  lazymatch goal with |- fsame ?s0 ?t =>
    match goal with H : fsame s0 ?st |- _ =>
      lazymatch t with context [st] =>
        let A := fresh "A" in let B := fresh "B" in destruct H as [A B];
        split; [intros ?; unfold mu in *; apply A | cbn; exact B]
      end
    end
  end.

Lemma call_mmap_ordie_W : forall I l fl, presW I (call_mmap_ordie E l fl).
Proof. intros; unfold call_mmap_ordie. pw. Qed.
Lemma store_alloc_once_W : forall s0 c, presW (fsame s0) (store_alloc_once E c).
Proof. intros; unfold store_alloc_once. pw; try apply call_mmap_ordie_W; fs_close. Qed.
Lemma store_alloc_W : forall s0 c, presW (fsame s0) (store_alloc E c).
Proof. intros; unfold store_alloc. pw; try apply store_alloc_once_W. Qed.
Lemma depot_put_W : forall s0 k, presW (fsame s0) (depot_put E k).
Proof. intros; unfold depot_put. pw; try apply call_mmap_ordie_W; try apply store_alloc_W; fs_close. Qed.

Lemma ensure_free_array_space_same : forall s0 c nf, presW (fsame s0) (ensure_free_array_space E c nf).
Proof.
  intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W.
  destruct H0 as [A B]. destruct H as [A0 B0]. split; [|exact B].
  intros c'. unfold mu in *. rewrite get_region_upd_ts. destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite get_set_region_eq. cbn. apply A0.
  - rewrite get_set_region_ne by auto. apply A.
Qed.

Lemma fgrow_regions : forall c s0 s s', as_regions s' = as_regions s -> as_residue s' = as_residue s -> fgrow c s0 s -> fgrow c s0 s'.
Proof. intros c s0 s s' HR HS G. unfold fgrow, mu, get_region in *. rewrite HR, HS. exact G. Qed.
Lemma fsame_regions : forall s0 s s', as_regions s' = as_regions s -> as_residue s' = as_residue s -> fsame s0 s -> fsame s0 s'.
Proof. intros s0 s s' HR HS G. unfold fsame, mu, get_region in *. rewrite HR, HS. exact G. Qed.

(* [comment removed for export] *)
Lemma call_mmap_fixed_eq : forall s0 a l, hoareW (fun s => s = s0) (call_mmap_fixed a l) (fun s _ => s = s0).
Proof. intros. apply (call_mmap_fixed_W (fun s => s = s0)). Qed.
Lemma call_mmap_anon_eq : forall s0 l, hoareW (fun s => s = s0) (call_mmap_anon E l) (fun s _ => s = s0).
Proof. intros. apply (call_mmap_anon_W (fun s => s = s0)). Qed.
Lemma poison_zero_eq : forall s0 u L, hoareW (fun s => s = s0) (poison_zero u L) (fun s _ => s = s0).
Proof. intros. apply (poison_zero_W (fun s => s = s0)). Qed.
Lemma call_munmap_eq : forall s0 a l, hoareW (fun s => s = s0) (call_munmap a l) (fun s _ => s = s0).
Proof. intros. apply (call_munmap_W (fun s => s = s0)). Qed.

(* [comment removed for export] *)
Lemma presW_from : forall {X} (Rl : astate -> astate -> Prop) (m : AM X) s0,
  (forall s, Rl s s) -> presW (Rl s0) m -> hoareW (fun s => s = s0) m (fun s' _ => Rl s0 s').
Proof. intros X Rl m s0 RF H. eapply hoareW_conseq; [exact H| intros s ->; apply RF| auto]. Qed.

(* [comment removed for export] *)
Definition regs_ok (s : astate) : Prop := forall c, rg_alloc_user (get_region s c) <= rg_mapped_user (get_region s c).
Lemma regs_ok_of_AWf : forall E' P D s, AWf E' P D s -> regs_ok s.
Proof.
  intros E' P D s (_ & [R1 R2] & _) c. destruct (Z_le_dec 1 c); [destruct (Z_le_dec c kLargestClassID)|].
  - destruct (R2 c ltac:(lia)) as (A1 & _). unfold region_of in A1. lia.
  - unfold get_region. destruct (as_regions s !! c) eqn:H; [pose proof (R1 _ _ H); lia| cbn; lia].
  - unfold get_region. destruct (as_regions s !! c) eqn:H; [pose proof (R1 _ _ H); lia| cbn; lia].
Qed.

Lemma populate_free_array_grow : forall s0 c req,
  1 <= c <= kLargestClassID -> 0 <= req <= hint c -> regs_ok s0 ->
  hoareW (fun s => s = s0) (populate_free_array E c req) (fun s' _ => fgrow c s0 s').
Proof.
  intros s0 c req Hc Hreq ROK; unfold populate_free_array. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind with (Q := fun s1 _ => fgrow c s0 s1).
  { match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:HB end; [| apply hoareW_ret; intros s ->; apply fgrow_refl].
    apply Z.ltb_lt in HB.
    eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s0); auto|]. intros [].
    eapply hoareW_bind; [apply call_mmap_fixed_eq|]. intros ok. apply hoareW_pre. intros s ->.
    destruct ok; [| apply hoareW_ret; intros s ->; apply fgrow_refl].
    eapply hoareW_bind; [apply hoareW_upd with (Q := fun s' _ => fgrow c s0 s')| intros []; apply hoareW_ret; auto].
    intros s ->. split; [| split; [| reflexivity]].
    - intros c' NE. unfold mu. rewrite get_region_upd_cache_mapped, get_region_upd_ts, get_set_region_ne by auto. reflexivity.
    - unfold mu. rewrite get_region_upd_cache_mapped, get_region_upd_ts, get_set_region_eq. cbn.
      pose proof (hint_size_bound c Hc) as [HS _]. pose proof (ROK c) as A1. pose proof (class_size_mod c Hc) as [_ SZ].
      assert (RS : req * class_size c <= hint c * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia).
      set (x := rg_alloc_user (get_region s0 c) + req * class_size c - rg_mapped_user (get_region s0 c)) in *.
      assert (X : 0 < x <= kUserMapSize) by (subst x; unfold kUserMapSize; lia).
      rewrite (round_up_small x kUserMapSize ltac:(unfold kUserMapSize; lia) X). unfold kUserMapSize. lia. }
  intros ok1. destruct (negb ok1); [apply hoareW_ret; auto|].
  apply hoareW_get_bind. intros s1 G1.
  eapply hoareW_bind; [apply (presW_from fsame _ s1 fsame_refl); apply ensure_free_array_space_same|].
  intros ok2. destruct (negb ok2); [apply hoareW_ret; intros s FS; eapply fgrow_fsame_trans; [exact G1| exact FS]|].
  apply hoareW_get_bind. intros s2 FS2. apply hoareW_upd_bind. apply hoareW_ret. intros s (sx & -> & ->).
  destruct G1 as (A & B & C). destruct FS2 as [A2 B2]. split; [| split; [| cbn; congruence]].
  - intros c' NE. unfold mu in *. rewrite get_set_region_ne by auto. rewrite A2. apply A. exact NE.
  - unfold mu in *. rewrite get_set_region_eq. cbn. rewrite A2. exact B.
Qed.

Lemma get_from_allocator_grow : forall s0 c,
  1 <= c <= kLargestClassID -> regs_ok s0 ->
  hoareW (fun s => s = s0) (get_from_allocator E c (hint c)) (fun s' _ => fgrow c s0 s').
Proof.
  intros s0 c Hc ROK; unfold get_from_allocator. apply hoareW_get_bind. intros s ->.
  pose proof (hint_range c Hc) as HR.
  eapply hoareW_bind with (Q := fun s1 _ => fgrow c s0 s1).
  { match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b eqn:HB end;
    [apply Z.ltb_lt in HB; apply populate_free_array_grow; [exact Hc| unfold rg_num_freed in *; lia| exact ROK]| apply hoareW_ret; intros s ->; apply fgrow_refl]. }
  intros ok. destruct (negb ok); [apply hoareW_ret; auto|].
  apply hoareW_get_bind. intros s1 G1.
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s1); auto|]. intros []. apply hoareW_pre. intros s ->.
  eapply hoareW_bind; [apply hoareW_upd with (Q := fun s' _ => fgrow c s0 s')| intros []; apply hoareW_ret; auto].
  intros s ->. destruct G1 as (A & B & C). split; [| split; [| cbn; exact C]].
  - intros c' NE. unfold mu in *. rewrite get_set_region_ne by auto. apply A; exact NE.
  - unfold mu in *. rewrite get_set_region_eq. cbn. exact B.
Qed.

Lemma refill_grow : forall s0 c, 1 <= c <= kLargestClassID -> regs_ok s0 ->
  hoareW (fun s => s = s0) (refill E c) (fun s' _ => fgrow c s0 s').
Proof.
  intros s0 c Hc ROK; unfold refill, init_cache. apply hoareW_upd_bind. apply hoareW_pre. intros s (s1 & -> & ->).
  eapply hoareW_bind; [apply get_from_allocator_grow; [exact Hc| exact ROK]|]. intros r. destruct r as [l|]; [| apply hoareW_ret; intros s G; exact G].
  eapply hoareW_bind; [apply hoareW_upd with (Q := fun s' _ => fgrow c s0 s')| intros []; apply hoareW_ret; auto].
  intros s (A & B & C). split; [| split; [| cbn; exact C]].
  - intros c' NE. unfold mu in *. rewrite get_region_upd_cache_stale, get_region_set_cache. apply A; exact NE.
  - unfold mu in *. rewrite get_region_upd_cache_stale, get_region_set_cache. exact B.
Qed.

Lemma cache_pop_grow : forall s0 c, 1 <= c <= kLargestClassID -> regs_ok s0 ->
  hoareW (fun s => s = s0) (cache_pop E c) (fun s' _ => fgrow c s0 s').
Proof.
  intros s0 c Hc ROK; unfold cache_pop. apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind with (Q := fun s1 _ => fgrow c s0 s1).
  { destruct (get_cache s0 c); [apply refill_grow; [exact Hc| exact ROK]| apply hoareW_ret; intros s ->; apply fgrow_refl]. }
  intros ok. destruct (negb ok); [apply hoareW_ret; auto|].
  apply hoareW_get_bind. intros s1 G1. destruct (get_cache s1 c); [apply hoareW_undef|].
  eapply hoareW_bind; [apply hoareW_upd with (Q := fun s' _ => fgrow c s0 s')| intros []; apply hoareW_ret; auto].
  intros s ->. destruct G1 as (A & B & C). split; [| split; [| cbn; exact C]].
  - intros c' NE. unfold mu in *. rewrite get_region_upd_cache_allocated, get_region_upd_cache_stale, get_region_set_cache. apply A; exact NE.
  - unfold mu in *. rewrite get_region_upd_cache_allocated, get_region_upd_cache_stale, get_region_set_cache. exact B.
Qed.

(* [comment removed for export] *)
Definition fsec (mb msz : Z) (s0 s : astate) : Prop :=
  (forall c, mu s c = mu s0 c) /\ as_residue s = as_residue s0 ++ residue_pages mb msz.

Lemma sec_alloc_frame : forall s0 needed2,
  hoareW (fun s => s = s0) (sec_alloc E needed2)
    (fun s' r => match r with None => s' = s0 | Some ab => fsec (ab - kPageSize) (round_up needed2 kPageSize + kPageSize) s0 s' end).
Proof.
  intros; unfold sec_alloc.
  eapply hoareW_bind; [apply call_mmap_anon_eq|]. intros r. apply hoareW_pre. intros s ->.
  destruct r as [mb|]; [| apply hoareW_ret; auto].
  apply hoareW_upd_bind. apply hoareW_pre. intros s (s1 & -> & ->).
  apply hoareW_get_bind. intros s ->.
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s' _ => s' = upd_ts (ts_on_mmap (round_up needed2 kPageSize + kPageSize)) s0); auto|]. intros [].
  apply hoareW_pre. intros s ->.
  eapply hoareW_bind with (Q := fun s' _ => exists pc, s' = upd_ptr_committed pc (upd_ts (ts_on_mmap (round_up needed2 kPageSize + kPageSize)) s0)).
  { match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b end.
    - eapply hoareW_bind; [apply call_mmap_fixed_eq|]. intros ok. apply hoareW_pre. intros s ->.
      destruct ok; [apply hoareW_upd; intros s ->; eexists; reflexivity| apply hoareW_spin].
    - apply hoareW_ret. intros s ->. exists (as_ptr_committed s0). destruct s0; reflexivity. }
  intros []. apply hoareW_pre. intros s (pc & ->).
  apply hoareW_upd_bind. apply hoareW_pre. intros s (s2 & -> & ->). apply hoareW_ret. intros s ->.
  replace (mb + kPageSize - kPageSize) with mb by lia. split; [intros c; reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fcall (k : Z) (cs : list Z) (extra : list Z) (s0 s : astate) : Prop :=
  (forall c, ~ In c cs -> mu s c = mu s0 c) /\ (forall c, mu s0 c <= mu s c <= mu s0 c + k * kUserMapSize)
  /\ as_residue s = as_residue s0 ++ extra.

Lemma fcall_of_fgrow : forall c cs s0 s, In c cs -> fgrow c s0 s -> fcall 1 cs [] s0 s.
Proof.
  intros c cs s0 s Hin (A & B & C). split; [| split; [| rewrite app_nil_r; exact C]].
  - intros c' NI. apply A. intros ->. exact (NI Hin).
  - intros c'. destruct (Z.eq_dec c' c) as [->|NE]; [lia| rewrite (A c' NE); unfold kUserMapSize; lia].
Qed.
Lemma fcall_of_fsame : forall k cs s0 s, 0 <= k -> fsame s0 s -> fcall k cs [] s0 s.
Proof. intros k cs s0 s Hk [A B]. split; [auto|]. split; [intros c; rewrite A; unfold kUserMapSize; nia| rewrite app_nil_r; exact B]. Qed.
Lemma fcall_trans : forall k1 k2 cs e1 e2 a b c, fcall k1 cs e1 a b -> fcall k2 cs e2 b c -> fcall (k1 + k2) cs (e1 ++ e2) a c.
Proof.
  intros k1 k2 cs e1 e2 a b c (A1 & A2 & A3) (B1 & B2 & B3). split; [| split].
  - intros x NI. rewrite (B1 x NI). apply A1. exact NI.
  - intros x. specialize (A2 x). specialize (B2 x). lia.
  - rewrite B3, A3, app_assoc. reflexivity.
Qed.
Lemma fcall_mono : forall k k' cs cs' e a b, k <= k' -> (forall c, In c cs -> In c cs') -> fcall k cs e a b -> fcall k' cs' e a b.
Proof.
  intros k k' cs cs' e a b LE SUB (A & B & C). split; [| split; [| exact C]].
  - intros c NI. apply A. intros H. exact (NI (SUB c H)).
  - intros c. specialize (B c). unfold kUserMapSize in *. nia.
Qed.
Lemma fcall_pre_same : forall k cs e s0 s1 s, fsame s0 s1 -> fcall k cs e s1 s -> fcall k cs e s0 s.
Proof.
  intros k cs e s0 s1 s [A B] (C1 & C2 & C3). split; [| split].
  - intros c NI. rewrite (C1 c NI). apply A.
  - intros c. specialize (C2 c). rewrite (A c) in C2. exact C2.
  - rewrite C3, B. reflexivity.
Qed.
Lemma fcall_post_grow : forall k cs e s0 s1 s c, fcall k cs e s0 s1 -> In c cs -> fgrow c s1 s -> fcall (k + 1) cs e s0 s.
Proof.
  intros k cs e s0 s1 s c (C1 & C2 & C3) Hin (A & B & C). split; [| split].
  - intros c' NI. rewrite A; [apply C1; exact NI|]. intros ->. exact (NI Hin).
  - intros c'. specialize (C2 c'). destruct (Z.eq_dec c' c) as [->|NE]; [lia|]. rewrite (A c' NE). unfold kUserMapSize in *. lia.
  - rewrite C, C3. reflexivity.
Qed.
Lemma fcall_post_same : forall k cs e s0 s1 s, fcall k cs e s0 s1 -> fsame s1 s -> fcall k cs e s0 s.
Proof.
  intros k cs e s0 s1 s (C1 & C2 & C3) [A B]. split; [| split].
  - intros c' NI. rewrite A. apply C1; exact NI.
  - intros c'. rewrite A. apply C2.
  - rewrite B, C3. reflexivity.
Qed.

Lemma fcall_same_core : forall k cs e a b b', fcall k cs e a b ->
  as_regions b' = as_regions b -> as_residue b' = as_residue b -> fcall k cs e a b'.
Proof.
  intros k cs e a b b' (A & B & C) HR HS. unfold fcall, mu, get_region in *. rewrite HR, HS. auto.
Qed.

Lemma amalloc_core_frame : forall s0 key n, 0 <= n -> regs_ok s0 ->
  hoareW (fun s => s = s0) (amalloc_core E key n)
    (fun s' r => exists extra, fcall 1 [class_id (needed1 n)] extra s0 s'
                 /\ (extra = [] \/ (from_primary n = false /\ r <> None /\ extra = residue_pages (match r with Some p => p - rz_size n - kPageSize | None => 0 end) (map_size n)))).
Proof.
  intros s00 key n Hn ROK0; unfold amalloc_core.
  eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s00); auto|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s1 (s & -> & ->). set (s0 := upd_nprimc _ _ s00).
  assert (ROK : regs_ok s0) by exact ROK0.
  enough (GOAL : hoareW (fun s => s = s0) 
    (ab <- (if from_primary n then cache_pop E (class_id (needed1 n)) else sec_alloc E (needed n));;
     match ab with
     | Some alloc_beg =>
         id <- depot_put E key;;
         sK <- aget ;;
         acheck (match as_chunks sK !! (alloc_beg + rz_size n - kChunkHeaderSize) with None => true | Some _ => false end) 9 ;;;
         aupd (fun s => upd_dead (delete (alloc_beg + rz_size n - kChunkHeaderSize))
                 (upd_chunks (fun cm => <[alloc_beg + rz_size n - kChunkHeaderSize:=
                      {| cm_alloc_beg := alloc_beg; cm_rz_log := rz_log n; cm_n := req n;
                         cm_prim := if from_primary n then Some (class_id (needed1 n)) else None; cm_state := CAllocated id |}]> cm) s));;;
         poison_zero (alloc_beg + rz_size n) (req n / 8 * 8);;;
         aupd (upd_ts (ts_on_malloc (req n) (needed n) (kMaxSize <? needed n) (class_id (needed n))));;;
         aret (Some (alloc_beg + rz_size n))
     | None => aupd (upd_oom true);;; aret None
     end)
    (fun s' r => exists extra, fcall 1 [class_id (needed1 n)] extra s0 s'
       /\ (extra = [] \/ from_primary n = false /\ r <> None /\ extra = residue_pages match r with Some p => p - rz_size n - kPageSize | None => 0 end (map_size n)))).
  { eapply hoareW_conseq; [exact GOAL| auto|]. cbn beta. intros s r (extra & F & C). exists extra. split; [| exact C].
    eapply fcall_pre_same; [| exact F]. apply (fsame_regions s00 s00); [reflexivity| reflexivity| apply fsame_refl]. }
  set (c := class_id (needed1 n)).
  eapply hoareW_bind with (Q := fun s1 r => match r with
     | None => fcall 1 [c] [] s0 s1
     | Some ab => (from_primary n = true /\ fgrow c s0 s1) \/ (from_primary n = false /\ fsec (ab - kPageSize) (map_size n) s0 s1) end).
  { destruct (from_primary n) eqn:PR.
    - pose proof (malloc_class_ok n ltac:(pose proof (proj1 (from_primary_iff n Hn) PR); lia)) as [Hc _]. unfold malloc_class in Hc.
      eapply hoareW_conseq; [apply cache_pop_grow; [exact Hc| exact ROK]| intros ? ->; reflexivity|]. cbn beta. intros s [ab|] G; [left; auto| eapply fcall_of_fgrow; [left; reflexivity| exact G]].
    - eapply hoareW_conseq; [apply sec_alloc_frame| intros ? ->; reflexivity|]. cbn beta. intros s [ab|] G; [right; split; [reflexivity| exact G]| subst s; apply fcall_of_fsame; [lia| apply fsame_refl]]. }
  intros [ab|].
  2:{ apply hoareW_upd_bind. apply hoareW_ret. intros s (s1 & F & ->). exists []. split; [| left; reflexivity].
      eapply fcall_same_core; [exact F| reflexivity| reflexivity]. }
  apply hoareW_pre. intros s1 CASE.
  eapply hoareW_bind; [apply (presW_from fsame _ s1 fsame_refl); apply depot_put_W|]. intros id.
  apply hoareW_pre. intros s2 F2.
  apply hoareW_get_bind. intros s ->. eapply hoareW_bind; [apply hoareW_check with (Q := fun s _ => s = s2); auto|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_pre. intros s (sx & -> & ->).
  eapply hoareW_bind; [apply poison_zero_eq|]. intros []. apply hoareW_pre. intros s ->.
  apply hoareW_upd_bind. apply hoareW_ret. intros s (sy & -> & ->).
  destruct F2 as [M2 R2].
  destruct CASE as [[PR G]|[PR [M1 R1]]].
  - exists []. split; [| left; reflexivity].
    destruct G as (A & B & C). split; [| split].
    + intros c' NI. match goal with |- mu ?st c' = _ => change (mu st c') with (mu s2 c') end.
      rewrite M2. apply A. intros ->. apply NI. left; reflexivity.
    + intros c'. match goal with |- _ <= mu ?st c' <= _ => change (mu st c') with (mu s2 c') end. rewrite M2.
      destruct (Z.eq_dec c' c) as [->|NE]; [lia| rewrite (A c' NE); unfold kUserMapSize; lia].
    + cbn. rewrite R2, C, app_nil_r. reflexivity.
  - exists (residue_pages (ab - kPageSize) (map_size n)). split.
    + split; [| split].
      * intros c' _. match goal with |- mu ?st c' = _ => change (mu st c') with (mu s2 c') end. rewrite M2. apply M1.
      * intros c'. match goal with |- _ <= mu ?st c' <= _ => change (mu st c') with (mu s2 c') end. rewrite M2, M1. unfold kUserMapSize; lia.
      * cbn. rewrite R2, R1. reflexivity.
    + right. split; [exact PR|]. split; [discriminate|]. f_equal. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma return_to_allocator_same : forall s0 c l, presW (fsame s0) (return_to_allocator E c l).
Proof.
  intros; unfold return_to_allocator. pw; try apply ensure_free_array_space_same.
  match goal with H : fsame s0 ?sa, H' : fsame s0 ?sb |- _ => destruct H as [A B]; destruct H' as [A' B'] end.
  split; [| cbn; assumption]. intros c'. unfold mu in *. destruct (Z.eq_dec c' c) as [->|NE].
  - rewrite get_set_region_eq. cbn. auto.
  - rewrite get_set_region_ne by auto. auto.
Qed.

Lemma local_dealloc_same : forall s0 c p, presW (fsame s0) (local_dealloc E c p).
Proof.
  intros; unfold local_dealloc, init_cache. pw; try apply return_to_allocator_same; fs_close.
Qed.

Lemma large_dealloc_same : forall s0 p, presW (fsame s0) (large_dealloc p).
Proof.
  intros; unfold large_dealloc. pw; try pzW; try apply call_munmap_W; fs_close.
Qed.

Lemma qcb_recycle_same : forall s0 m, presW (fsame s0) (qcb_recycle E m).
Proof.
  intros; unfold qcb_recycle. pw; try apply local_dealloc_same; try apply large_dealloc_same; fs_close.
Qed.

Lemma recycle_items_same : forall s0 l, presW (fsame s0) (recycle_items E l).
Proof. intros s0 l; induction l as [|m l IH]; cbn; pw; [apply qcb_recycle_same| exact IH]. Qed.

Lemma do_recycle_same : forall s0 bs, presW (fsame s0) (do_recycle E bs).
Proof.
  intros s0 bs; induction bs as [|b bs IH]; cbn; pw; try apply recycle_items_same; try apply local_dealloc_same; try exact IH.
Qed.

Lemma recycle_same : forall s0, presW (fsame s0) (recycle E).
Proof.
  intros; unfold recycle. pw; try apply do_recycle_same; fs_close.
Qed.

Lemma drain_same : forall s0, presW (fsame s0) (drain_if_needed E).
Proof.
  intros; unfold drain_if_needed. pw; try apply recycle_same; fs_close.
Qed.

Lemma enqueue_grow : forall s0 cb n, regs_ok s0 -> hoareW (fun s => s = s0) (enqueue E cb n) (fun s' _ => fgrow kBatchClass s0 s').
Proof.
  intros s0 cb n ROK; unfold enqueue, batch_alloc. apply hoareW_get_bind. intros s ->.
  match goal with |- hoareW _ (if ?b then _ else _) _ => destruct b end.
  - eapply hoareW_bind with (Q := fun s1 _ => fgrow kBatchClass s0 s1).
    + eapply hoareW_bind; [apply cache_pop_grow; [unfold kBatchClass, kLargestClassID; lia| exact ROK]|]. intros [b|]; [| apply hoareW_spin]. destruct (b =? 0); [apply hoareW_spin| apply hoareW_ret; auto].
    + intros b. apply hoareW_upd. intros s G. apply (fgrow_regions _ s0 s); [reflexivity| reflexivity| exact G].
  - apply hoareW_upd. intros s ->. apply (fgrow_regions _ s0 s0); [reflexivity| reflexivity| apply fgrow_refl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition KS (K : list (list Z)) (s : astate) : Prop := as_keys s = K.
Ltac ks_same := match goal with H : KS ?K ?st |- KS ?K _ => unfold KS in *; cbn; exact H end.

Lemma ensure_ks : forall K c nf, presW (KS K) (ensure_free_array_space E c nf).
Proof. intros; unfold ensure_free_array_space. pw; try apply call_mmap_fixed_W; ks_same. Qed.
Lemma populate_ks : forall K c r, presW (KS K) (populate_free_array E c r).
Proof. intros; unfold populate_free_array. pw; try apply call_mmap_fixed_W; try apply ensure_ks; ks_same. Qed.
Lemma gfa_ks : forall K c n, presW (KS K) (get_from_allocator E c n).
Proof. intros; unfold get_from_allocator. pw; try apply populate_ks; ks_same. Qed.
Lemma refill_ks : forall K c, presW (KS K) (refill E c).
Proof. intros; unfold refill, init_cache. pw; try apply gfa_ks; ks_same. Qed.
Lemma cache_pop_ks : forall K c, presW (KS K) (cache_pop E c).
Proof. intros; unfold cache_pop. pw; try apply refill_ks; ks_same. Qed.
Lemma return_ks : forall K c l, presW (KS K) (return_to_allocator E c l).
Proof. intros; unfold return_to_allocator. pw; try apply ensure_ks; ks_same. Qed.
Lemma local_dealloc_ks : forall K c p, presW (KS K) (local_dealloc E c p).
Proof. intros; unfold local_dealloc, init_cache. pw; try apply return_ks; ks_same. Qed.
Lemma large_dealloc_ks : forall K p, presW (KS K) (large_dealloc p).
Proof. intros; unfold large_dealloc. pw; try pzW; try apply call_munmap_W; ks_same. Qed.
Lemma qcb_recycle_ks : forall K m, presW (KS K) (qcb_recycle E m).
Proof. intros; unfold qcb_recycle. pw; try apply local_dealloc_ks; try apply large_dealloc_ks; ks_same. Qed.
Lemma recycle_items_ks : forall K l, presW (KS K) (recycle_items E l).
Proof. intros K l; induction l; cbn; pw; [apply qcb_recycle_ks| assumption]. Qed.
Lemma do_recycle_ks : forall K bs, presW (KS K) (do_recycle E bs).
Proof. intros K bs; induction bs; cbn; pw; try apply recycle_items_ks; try apply local_dealloc_ks; try assumption. Qed.
Lemma recycle_ks : forall K, presW (KS K) (recycle E).
Proof. intros; unfold recycle. pw; try apply do_recycle_ks; ks_same. Qed.
Lemma drain_ks : forall K, presW (KS K) (drain_if_needed E).
Proof. intros; unfold drain_if_needed. pw; try apply recycle_ks; ks_same. Qed.
Lemma enqueue_ks : forall K cb n, presW (KS K) (enqueue E cb n).
Proof. intros; unfold enqueue, batch_alloc. pw; try apply cache_pop_ks; ks_same. Qed.

End FR.
End RC__1.
