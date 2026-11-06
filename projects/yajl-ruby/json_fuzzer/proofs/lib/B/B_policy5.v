(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LazyModel NodesA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanOps AsanRep AsanFakeStack AsanPS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pgdn (a : Z) : Z := a - a mod 4096.
Definition pgup (a : Z) : Z := pgdn (a + 4095).
Lemma pgdn_mod : forall a, pgdn a mod 4096 = 0.
Proof. intros a. unfold pgdn. Z.div_mod_to_equations; lia. Qed.
Lemma pgdn_le : forall a, pgdn a <= a. Proof. intros a. unfold pgdn. Z.div_mod_to_equations; lia. Qed.
Lemma pgdn_gt : forall a, a < pgdn a + 4096. Proof. intros a. unfold pgdn. Z.div_mod_to_equations; lia. Qed.
Lemma pgup_ge : forall a, a <= pgup a. Proof. intros a. unfold pgup, pgdn. Z.div_mod_to_equations; lia. Qed.

Definition in_ivs_Z (l : list (Z * Z)) (a : Z) : Prop := exists iv, In iv l /\ fst iv <= a < snd iv.
(* [comment removed for export] *)
Definition zpoints (lo : Z) (n : Z) : list word := map (fun i => Z_to_bv 64 (lo + 4096 * Z.of_nat i)) (seq 0 (Z.to_nat n)).
Lemma zpoints_length : forall lo n, length (zpoints lo n) = Z.to_nat n.
Proof. intros. unfold zpoints. rewrite length_map, length_seq. reflexivity. Qed.
Lemma In_zpoints : forall lo n p, lo mod 4096 = 0 -> p mod 4096 = 0 -> lo <= p -> p < lo + 4096 * n ->
  In (Z_to_bv 64 p) (zpoints lo n).
Proof.
  intros lo n p Hlo Hp H1 H2. unfold zpoints. apply in_map_iff.
  exists (Z.to_nat ((p - lo) / 4096)). split.
  - f_equal. Z.div_mod_to_equations. nia.
  - apply in_seq. split; [lia|]. Z.div_mod_to_equations. nia.
Qed.
Lemma flat_map_length_bound : forall {A B} (f : A -> list B) (g : A -> Z) l,
  (forall x, In x l -> Z.of_nat (length (f x)) <= g x) -> (forall x, In x l -> 0 <= g x) ->
  Z.of_nat (length (flat_map f l)) <= fold_right (fun x acc => g x + acc) 0 l.
Proof.
  intros A B f g l H G. induction l as [|x l IH]; cbn; [lia|]. rewrite length_app.
  pose proof (H x (or_introl eq_refl)). pose proof (IH ltac:(intros; apply H; right; assumption) ltac:(intros; apply G; right; assumption)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section POLICY.
Variable A0 : list (Z * Z).
Variable EB0 : Z.
(* [comment removed for export] *)
Hypothesis A0_ok : Forall (fun iv => fst iv <= snd iv) A0.

(* [comment removed for export] *)
Definition in_interiors (a : astate) (p : Z) : Prop :=
  exists sc, In sc (as_sec a) /\ kBigMapSize <= sc_map_size sc
             /\ fst (remap_range (sc_map_beg sc) (sc_map_size sc)) <= p
                < fst (remap_range (sc_map_beg sc) (sc_map_size sc)) + snd (remap_range (sc_map_beg sc) (sc_map_size sc)).
(* [comment removed for export] *)
Definition in_stores (a : astate) (p : Z) : Prop :=
  exists b, In b (as_store_blocks a) /\ b <= p < b + kStoreBlockBytes.

Definition aSa (a : astate) (w : word) : Prop :=
  let p := bv_unsigned w in
  p mod 4096 = 0 /\ (in_ivs_Z A0 p \/ in_interiors a p \/ In p (as_residue a) \/ in_stores a p).

Definition A0_pages : Z := fold_right (fun iv acc => (snd iv - fst iv) / 4096 + 2 + acc) 0 A0.
Definition interiors_bound (a : astate) : Z :=
  fold_right (fun sc acc => (if kBigMapSize <=? sc_map_size sc then sc_map_size sc / 32768 else 0) + acc) 0 (as_sec a).
(* [comment removed for export] *)
Definition aNza (a : astate) : Z :=
  A0_pages + interiors_bound a + zlen (as_residue a) + 2050 * zlen (as_store_blocks a).

(* [comment removed for export] *)
Definition cover_A0 : list word := flat_map (fun iv => zpoints (pgdn (fst iv)) ((snd iv - fst iv) / 4096 + 2)) A0.
Definition cover_int (a : astate) : list word :=
  flat_map (fun sc => if kBigMapSize <=? sc_map_size sc
                      then zpoints (fst (remap_range (sc_map_beg sc) (sc_map_size sc))) (sc_map_size sc / 32768) else [])
           (as_sec a).
Definition cover_res (a : astate) : list word := map (fun p => Z_to_bv 64 p) (as_residue a).
Definition cover_st (a : astate) : list word := flat_map (fun b => zpoints (pgdn b) 2050) (as_store_blocks a).
Definition cover (a : astate) : list word := cover_A0 ++ cover_int a ++ cover_res a ++ cover_st a.
Definition aNa (a : astate) : nat := length (cover a).

(* [comment removed for export] *)
Definition aEBa (a : astate) : Z := EB0 + a_eager_bytes a + kDepotNodeBlockBytes * zlen (as_node_blocks a).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aS_cover : forall a w, aSa a w -> In w (cover a).
Proof.
  intros a w [AL HS]. unfold cover. rewrite <- (Z_to_bv_bv_unsigned 64 w). set (p := bv_unsigned w) in *.
  pose proof (bv_unsigned_in_range 64 w) as Hw. fold p in Hw. clearbody p.
  destruct HS as [(iv & Hiv & R)|[(sc & Hsc & BIG & R1 & R2)|[HR|(b & Hb & R1 & R2)]]].
  - apply in_app_iff. left. unfold cover_A0. apply in_flat_map. exists iv. split; [exact Hiv|].
    apply In_zpoints; [apply pgdn_mod| exact AL| pose proof (pgdn_le (fst iv)); lia|].
    unfold pgdn. clear -R AL. Z.div_mod_to_equations. nia.
  - apply in_app_iff. right. apply in_app_iff. left. unfold cover_int. apply in_flat_map. exists sc. split; [exact Hsc|].
    replace (kBigMapSize <=? sc_map_size sc) with true by (symmetry; apply Z.leb_le; exact BIG).
    unfold remap_range in *. cbn [fst snd] in *. unfold round_up, round_down, mem_to_shadow, kPageSize in *.
    apply In_zpoints; [clear; Z.div_mod_to_equations; nia| exact AL| lia|].
    clear -R1 R2 AL BIG. unfold kBigMapSize in BIG. Z.div_mod_to_equations. nia.
  - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. unfold cover_res. apply in_map_iff. exists p. auto.
  - apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right. unfold cover_st. apply in_flat_map. exists b. split; [exact Hb|].
    apply In_zpoints; [apply pgdn_mod| exact AL| pose proof (pgdn_le b); lia|].
    unfold pgdn. change kStoreBlockBytes with 8388608 in R2. clear -R1 R2 AL. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma aS_card : forall a l, List.NoDup l -> Forall (aSa a) l -> (length l <= aNa a)%nat.
Proof.
  intros a l ND HF. unfold aNa. apply NoDup_incl_length; [exact ND|]. intros w Hw. apply aS_cover.
  exact (proj1 (Forall_forall _ _) HF w Hw).
Qed.

Lemma A0_pages_cover : Z.of_nat (length cover_A0) <= A0_pages.
Proof.
  unfold cover_A0, A0_pages. apply (flat_map_length_bound _ (fun iv => (snd iv - fst iv) / 4096 + 2)).
  - intros iv Hiv. rewrite zpoints_length. pose proof (proj1 (Forall_forall _ _) A0_ok iv Hiv) as H. cbn beta in H.
    assert (0 <= (snd iv - fst iv) / 4096) by (apply Z.div_pos; lia). rewrite Z2Nat.id by lia. lia.
  - intros iv Hiv. pose proof (proj1 (Forall_forall _ _) A0_ok iv Hiv) as H. cbn beta in H.
    assert (0 <= (snd iv - fst iv) / 4096) by (apply Z.div_pos; lia). lia.
Qed.
Lemma A0_pages_nonneg : 0 <= A0_pages.
Proof. pose proof A0_pages_cover. lia. Qed.

Lemma aN_bound : forall a, Z.of_nat (aNa a) <= aNza a.
Proof.
  intros a. unfold aNa, aNza, cover.
  rewrite (length_app cover_A0 (cover_int a ++ cover_res a ++ cover_st a)), (length_app (cover_int a) (cover_res a ++ cover_st a)),
          (length_app (cover_res a) (cover_st a)).
  pose proof A0_pages_cover as A.
  assert (B : Z.of_nat (length (cover_int a)) <= interiors_bound a).
  { unfold cover_int, interiors_bound. apply flat_map_length_bound.
    - intros sc _. destruct (Z.leb_spec kBigMapSize (sc_map_size sc)); [rewrite zpoints_length| cbn; lia].
      unfold kBigMapSize in *. rewrite Z2Nat.id; Z.div_mod_to_equations; lia.
    - intros sc _. destruct (Z.leb_spec kBigMapSize (sc_map_size sc)); [| lia]. unfold kBigMapSize in *. Z.div_mod_to_equations. lia. }
  assert (C : Z.of_nat (length (cover_res a)) = zlen (as_residue a)).
  { unfold cover_res, zlen. rewrite length_map. reflexivity. }
  assert (D : Z.of_nat (length (cover_st a)) <= 2050 * zlen (as_store_blocks a)).
  { unfold cover_st, zlen. induction (as_store_blocks a) as [|b l IH]; cbn -[Z.mul Z.of_nat zpoints]; [lia|].
    rewrite length_app, zpoints_length. lia. }
  rewrite !Nat2Z.inj_add. clear -A B C D. lia.
Qed.

(* [comment removed for export] *)
Lemma interiors_bound_nonneg : forall a, (forall sc, In sc (as_sec a) -> 0 <= sc_map_size sc) -> 0 <= interiors_bound a.
Proof.
  intros a H. unfold interiors_bound. induction (as_sec a) as [|sc l IH]; cbn; [lia|].
  pose proof (H sc ltac:(left; reflexivity)). specialize (IH ltac:(intros; apply H; right; assumption)).
  destruct (kBigMapSize <=? sc_map_size sc); [| lia]. pose proof (Z.div_pos (sc_map_size sc) 32768 ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma aS_static : forall a w iv, In iv A0 -> fst iv <= bv_unsigned w < snd iv -> bv_unsigned w mod 4096 = 0 -> aSa a w.
Proof. intros a w iv Hiv R AL. split; [exact AL|]. left. exists iv. auto. Qed.
Lemma aS_residue : forall a w, In (bv_unsigned w) (as_residue a) -> bv_unsigned w mod 4096 = 0 -> aSa a w.
Proof. intros a w H AL. split; [exact AL|]. right; right; left. exact H. Qed.
Lemma aS_interior : forall a w sc, In sc (as_sec a) -> kBigMapSize <= sc_map_size sc ->
  fst (remap_range (sc_map_beg sc) (sc_map_size sc)) <= bv_unsigned w
    < fst (remap_range (sc_map_beg sc) (sc_map_size sc)) + snd (remap_range (sc_map_beg sc) (sc_map_size sc)) ->
  bv_unsigned w mod 4096 = 0 -> aSa a w.
Proof. intros a w sc H B R AL. split; [exact AL|]. right; left. exists sc. auto. Qed.
Lemma aS_store : forall a w b, In b (as_store_blocks a) -> b <= bv_unsigned w < b + kStoreBlockBytes -> bv_unsigned w mod 4096 = 0 -> aSa a w.
Proof. intros a w b H R AL. split; [exact AL|]. right; right; right. exists b. auto. Qed.
(* [comment removed for export] *)
Lemma aS_mono : forall a a' w,
  (forall sc, In sc (as_sec a) -> In sc (as_sec a')) -> (forall p, In p (as_residue a) -> In p (as_residue a')) ->
  (forall b, In b (as_store_blocks a) -> In b (as_store_blocks a')) -> aSa a w -> aSa a' w.
Proof.
  intros a a' w HS HR HB [AL H]. split; [exact AL|].
  destruct H as [H|[(sc & Hsc & X)|[H|(b & Hb & X)]]]; [left; exact H| right; left; exists sc; auto| right; right; left; auto| right; right; right; exists b; auto].
Qed.

(* [comment removed for export] *)
Lemma policy_frame : forall a a',
  as_sec a' = as_sec a -> as_residue a' = as_residue a -> as_store_blocks a' = as_store_blocks a ->
  (forall w, aSa a' w <-> aSa a w) /\ aNa a' = aNa a /\ aNza a' = aNza a.
Proof.
  intros a a' S R ST. unfold aSa, aNa, aNza, cover, cover_int, cover_res, cover_st, in_interiors, in_stores, interiors_bound.
  rewrite S, R, ST. split; [intros w; tauto| split; reflexivity].
Qed.

End POLICY.

(* [comment removed for export] *)
Definition aS (A0 : list (Z * Z)) (s : aps) : word -> Prop := aSa A0 (aps_alloc s).
Definition aN (A0 : list (Z * Z)) (s : aps) : nat := aNa A0 (aps_alloc s).
Definition aNz (A0 : list (Z * Z)) (s : aps) : Z := aNza A0 (aps_alloc s).
Definition aEB (EB0 : Z) (s : aps) : Z := aEBa EB0 (aps_alloc s).
