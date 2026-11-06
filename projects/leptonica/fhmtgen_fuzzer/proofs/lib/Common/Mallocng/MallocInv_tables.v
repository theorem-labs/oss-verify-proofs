(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition debruijn32 : list Z := debruijn32_tab.

Fixpoint Zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: Zseq (lo + 1) n' end.

Lemma Zseq_In : forall n lo x, lo <= x < lo + Z.of_nat n -> In x (Zseq lo n).
Proof.
  induction n as [|n IH]; intros lo x H; [lia|]. cbn.
  destruct (Z.eq_dec lo x) as [-> | Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma rom_bytes_nth : forall rom bs a k, rom_bytes rom a bs -> (k < length bs)%nat ->
  rom (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (nth k bs 0)).
Proof.
  intros rom bs. induction bs as [|b bs IH]; intros a k H Hk; [cbn in Hk; lia|].
  destruct H as [H0 H1]. destruct k as [|k].
  - cbn [nth]. replace (a + Z.of_nat 0) with a by lia. exact H0.
  - cbn [nth]. replace (a + Z.of_nat (S k)) with ((a + 1) + Z.of_nat k) by lia. apply IH; [exact H1 | cbn in Hk; lia].
Qed.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Definition rodata_clear (m : word -> option byte) : Prop :=
  forall a, IMG_LO <= a < RW_LO -> m (Z_to_bv 64 a) = None.

Lemma rdn_rodata : forall m a (n : nat), rodata_clear m -> IMG_LO <= a -> a + Z.of_nat n <= RW_LO ->
  rdn ml_segs m (Z_to_bv 64 a) n = rdn ml_segs (fun _ => None) (Z_to_bv 64 a) n.
Proof.
  intros m a n Hc Ha Hn. pose proof layout_tabs. apply rdn_ext; [rewrite uZ by lia; lia|].
  intros x Hx. rewrite uZ in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hc. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_rom_bytes : forall (tbl : list Z) base a n,
  rom_bytes (seg_rom ml_segs) base tbl ->
  0 <= base -> base <= a -> a + Z.of_nat n <= base + Z.of_nat (length tbl) -> base + Z.of_nat (length tbl) <= 2^64 ->
  exists bs, rdn ml_segs (fun _ => None) (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
             forall k, (k < n)%nat -> nth k bs (Z_to_bv 8 0) = Z_to_bv 8 (nth (Z.to_nat (a - base) + k) tbl 0).
Proof.
  intros tbl base a n Hrb Hb. revert a. induction n as [|n IH]; intros a Hba Hn Hnw.
  - exists []. split; [reflexivity|]. split; [reflexivity|]. intros k Hk. lia.
  - destruct (IH (a + 1)) as (bs & Hbs & Hlen & Hnth); [lia | lia | lia |].
    pose proof (rom_bytes_nth _ _ _ (Z.to_nat (a - base)) Hrb ltac:(lia)) as Hr.
    replace (base + Z.of_nat (Z.to_nat (a - base))) with a in Hr by lia.
    exists (Z_to_bv 8 (nth (Z.to_nat (a - base)) tbl 0) :: bs). split; [| split; [cbn; lia|]].
    + cbn [rdn]. rewrite Hr. rewrite u_add1_lit. rewrite Hbs. reflexivity.
    + intros k Hk. destruct k as [|k]; cbn [nth]; [f_equal; f_equal; lia|].
      rewrite Hnth by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma size_class_range : forall sc, 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros sc Hsc. unfold size_class.
  assert (E : exists k, (k < 48)%nat /\ Z.to_nat sc = k) by (exists (Z.to_nat sc); split; [lia | reflexivity]).
  destruct E as (k & Hk & ->).
  do 48 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

Lemma nth_flat_map2 : forall (l : list Z) k,
  (k < length l)%nat ->
  nth (2 * k) (flat_map (fun c => [c mod 256; c / 256]) l) 0 = nth k l 0 mod 256 /\
  nth (2 * k + 1) (flat_map (fun c => [c mod 256; c / 256]) l) 0 = nth k l 0 / 256.
Proof.
  induction l as [|c l IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k]; [split; reflexivity|].
  cbn [flat_map app]. replace (2 * S k)%nat with (S (S (2 * k))) by lia.
  replace (S (S (2 * k)) + 1)%nat with (S (S (2 * k + 1))) by lia. cbn [nth]. apply IH. cbn in Hk. lia.
Qed.

Lemma length_flat_map2 : forall (l : list Z), length (flat_map (fun c => [c mod 256; c / 256]) l) = (2 * length l)%nat.
Proof. induction l as [|c l IH]; [reflexivity|]. cbn [flat_map app length]. rewrite IH. lia. Qed.

Lemma read_size_class : forall m sc, rodata_clear m -> 0 <= sc < 48 ->
  exists bs, rdn ml_segs m (Z_to_bv 64 (T_SIZE_CLASSES + 2 * sc)) 2 = Some bs /\ length bs = 2%nat /\
             bytes_le_to_Z bs = size_class sc.
Proof.
  intros m sc Hc Hsc. pose proof layout_tabs as L. unfold T_SIZE_CLASSES in *.
  rewrite (rdn_rodata m) by (try exact Hc; lia).
  pose proof (mlo_size_classes (ML:=ML)) as Hrb.
  assert (Hlen : length (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab) = 96%nat)
    by (rewrite length_flat_map2; reflexivity).
  destruct (rdn_rom_bytes _ _ (bv_unsigned A_SIZE_CLASSES + 2 * sc) 2 Hrb) as (bs & Hbs & Hl & Hnth);
    [lia | lia | rewrite Hlen; cbn [Z.of_nat]; lia | rewrite Hlen; lia |].
  exists bs. split; [exact Hbs|]. split; [exact Hl|].
  destruct bs as [|b0 [|b1 [|]]]; try (cbn in Hl; lia).
  pose proof (Hnth 0%nat ltac:(lia)) as H0. pose proof (Hnth 1%nat ltac:(lia)) as H1. cbn [nth] in H0, H1.
  replace (Z.to_nat (bv_unsigned A_SIZE_CLASSES + 2 * sc - bv_unsigned A_SIZE_CLASSES) + 0)%nat with (2 * Z.to_nat sc)%nat in H0 by lia.
  replace (Z.to_nat (bv_unsigned A_SIZE_CLASSES + 2 * sc - bv_unsigned A_SIZE_CLASSES) + 1)%nat with (2 * Z.to_nat sc + 1)%nat in H1 by lia.
  destruct (nth_flat_map2 size_classes_tab (Z.to_nat sc) ltac:(cbn; lia)) as [E0 E1].
  rewrite E0 in H0. rewrite E1 in H1. subst b0 b1.
  pose proof (size_class_range sc Hsc) as Hr. unfold size_class in *.
  set (c := nth (Z.to_nat sc) size_classes_tab 0) in *.
  cbn [bytes_le_to_Z]. rewrite !Z_to_bv_unsigned.
  assert (Hq : 0 <= c / 256 < 256) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  pose proof (Z.mod_pos_bound c 256 ltac:(lia)) as Hm.
  rewrite !(bv_wrap_small 8) by (change (bv_modulus 8) with 256; lia).
  rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite lor_shiftl_8 by lia.
  pose proof (Z_div_mod_eq_full c 256). lia.
Qed.


(* [comment removed for export] *)
Lemma read_byte_table : forall (tbl : list Z) (base : Z) m k,
  rom_bytes (seg_rom ml_segs) base tbl -> Forall (fun z => 0 <= z < 256) tbl ->
  rodata_clear m -> IMG_LO <= base -> base + Z.of_nat (length tbl) <= RW_LO ->
  0 <= k < Z.of_nat (length tbl) ->
  exists b, rdn ml_segs m (Z_to_bv 64 (base + k)) 1 = Some [b] /\ bv_unsigned b = nth (Z.to_nat k) tbl 0.
Proof.
  intros tbl base m k Hrb Hall Hc Hb Hn Hk. pose proof layout_tabs as L.
  rewrite (rdn_rodata m) by (try exact Hc; lia).
  destruct (rdn_rom_bytes tbl base (base + k) 1 Hrb) as (bs & Hbs & Hl & Hnth); [lia | lia | lia | lia |].
  destruct bs as [|b [|]]; try (cbn in Hl; lia).
  exists b. split; [exact Hbs|]. pose proof (Hnth 0%nat ltac:(lia)) as H0. cbn [nth] in H0.
  replace (Z.to_nat (base + k - base) + 0)%nat with (Z.to_nat k) in H0 by lia. subst b.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256.
  apply (Forall_nth (fun z => 0 <= z < 256) tbl); [exact Hall | lia].
Qed.

Lemma read_debruijn : forall m k, rodata_clear m -> 0 <= k < 32 ->
  exists b, rdn ml_segs m (Z_to_bv 64 (T_DEBRUIJN + k)) 1 = Some [b] /\ bv_unsigned b = debruijn k.
Proof.
  intros m k Hc Hk. pose proof layout_tabs. unfold T_DEBRUIJN, debruijn.
  apply (read_byte_table debruijn32_tab); [exact mlo_debruijn | | exact Hc | lia | cbn [length Z.of_nat]; cbn; lia | cbn; lia].
  unfold debruijn32_tab. repeat constructor; lia.
Qed.

Lemma read_small_cnt : forall m j, rodata_clear m -> 0 <= j < 27 ->
  exists b, rdn ml_segs m (Z_to_bv 64 (T_SMALL_CNT + j)) 1 = Some [b] /\ bv_unsigned b = small_cnt j.
Proof.
  intros m j Hc Hj. pose proof layout_tabs. unfold T_SMALL_CNT, small_cnt.
  apply (read_byte_table small_cnt_tab); [exact mlo_small_cnt | | exact Hc | lia | cbn; lia | cbn; lia].
  unfold small_cnt_tab. repeat constructor; lia.
Qed.

Lemma read_med_cnt : forall m j, rodata_clear m -> 0 <= j < 4 ->
  exists b, rdn ml_segs m (Z_to_bv 64 (T_MED_CNT + j)) 1 = Some [b] /\ bv_unsigned b = med_cnt j.
Proof.
  intros m j Hc Hj. pose proof layout_tabs. unfold T_MED_CNT, med_cnt.
  apply (read_byte_table med_cnt_tab); [exact mlo_med_cnt | | exact Hc | lia | cbn; lia | cbn; lia].
  unfold med_cnt_tab. repeat constructor; lia.
Qed.

(* [comment removed for export] *)
Lemma rodata_clear_wbytes : forall m a bs, rodata_clear m ->
  0 <= a < 2^64 -> a + Z.of_nat (length bs) <= 2^64 -> (a + Z.of_nat (length bs) <= IMG_LO \/ RW_LO <= a) ->
  rodata_clear (wbytes m (Z_to_bv 64 a) bs).
Proof.
  intros m a bs Hc Ha Hnw Hout x Hx. pose proof layout_nums.
  destruct Hout as [Hlo | Hhi].
  - rewrite wbytes_above; [apply Hc; exact Hx | rewrite !uZ by lia; lia].
  - rewrite wbytes_below; [apply Hc; exact Hx | rewrite uZ by lia; exact Hnw | rewrite !uZ by lia; lia].
Qed.

End WithLayout.
