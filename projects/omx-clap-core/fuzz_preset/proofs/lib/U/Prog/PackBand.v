From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack.
Import ListNotations.
Local Open Scope Z_scope.

Lemma cou_step_tab :
  forallb (fun k => class_of_units k <=? class_of_units (k + 1)) (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cou_step : forall k, 0 <= k < 8191 -> class_of_units k <= class_of_units (k + 1).
Proof.
  intros k Hk. pose proof cou_step_tab as T. rewrite forallb_forall in T.
  apply Z.leb_le, T. unfold zseq. apply in_map_iff. exists (Z.to_nat k). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma cou_mono : forall a b, 0 <= a <= b -> b <= 8191 -> class_of_units a <= class_of_units b.
Proof.
  intros a b Hab Hb. replace b with (a + Z.of_nat (Z.to_nat (b - a))) by lia.
  assert (Hd : a + Z.of_nat (Z.to_nat (b - a)) <= 8191) by lia. revert Hd.
  generalize (Z.to_nat (b - a)) as d. induction d as [|d IH]; intros Hd.
  { change (Z.of_nat 0) with 0. rewrite Z.add_0_r. lia. }
  rewrite Nat2Z.inj_succ in *. specialize (IH ltac:(lia)).
  replace (a + Z.succ (Z.of_nat d)) with (a + Z.of_nat d + 1) by lia.
  pose proof (cou_step (a + Z.of_nat d) ltac:(lia)). lia.
Qed.

Lemma stc_mono : forall a b, 0 <= a <= b -> b < MMAP_THRESHOLD -> size_to_class a <= size_to_class b.
Proof.
  intros a b Hab Hb. unfold size_to_class. rewrite !Z.shiftr_div_pow2 by lia.
  change (2 ^ 4) with 16. unfold IB, MMAP_THRESHOLD in *.
  apply cou_mono.
  - split; [apply Z.div_pos; lia|]. apply Z.div_le_mono; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.

Lemma band_le48 : forall n, 0 <= n -> band n <= 48.
Proof.
  intros n Hn. unfold band. destruct (MMAP_THRESHOLD <=? n) eqn:E; [lia|].
  apply Z.leb_gt in E. pose proof (size_to_class_range n ltac:(lia)). lia.
Qed.

Lemma band_mono : forall a b, 0 <= a <= b -> band a <= band b.
Proof.
  intros a b Hab. unfold band.
  destruct (MMAP_THRESHOLD <=? b) eqn:Eb.
  - destruct (MMAP_THRESHOLD <=? a) eqn:Ea; [lia|].
    apply Z.leb_gt in Ea. pose proof (size_to_class_range a ltac:(lia)). lia.
  - apply Z.leb_gt in Eb.
    replace (MMAP_THRESHOLD <=? a) with false by (symmetry; apply Z.leb_gt; lia).
    apply stc_mono; lia.
Qed.

Lemma band_nonneg : forall n, 0 <= n -> 0 <= band n.
Proof.
  intros n Hn. unfold band. destruct (MMAP_THRESHOLD <=? n) eqn:E; [lia|].
  apply Z.leb_gt in E. pose proof (size_to_class_range n ltac:(lia)). lia.
Qed.
