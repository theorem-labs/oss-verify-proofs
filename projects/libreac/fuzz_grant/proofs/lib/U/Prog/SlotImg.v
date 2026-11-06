From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem Cells Frame Step.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rsegs_extents : map (fun s => (seg_base s, seg_size s)) rsegs =
  [(65536%N, 8192%N); (73728%N, 49152%N); (122880%N, 4096%N); (126976%N, 204800%N)].
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_rsegs_high : forall a, 0x51000 <= a -> find_segment rsegs a 1 = None.
Proof.
  intros a Ha. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
  pose proof (YK1j.find_segment_in _ _ _ _ E) as Hin.
  pose proof (YK1j.find_segment_range _ _ _ _ E) as Hr.
  apply (in_map (fun s => (seg_base s, seg_size s))) in Hin. rewrite rsegs_extents in Hin.
  cbn [In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as E1 E2; rewrite <- E1, <- E2 in Hr; cbn in Hr; lia.
Qed.
Lemma resv_extents : map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved rsegs) =
  [(65536, 8192); (73728, 49152); (122880, 4096); (126976, 204800)].
Proof. vm_compute. reflexivity. Qed.

Lemma resv_nth : forall k, (k < 4)%nat ->
  In (nth k (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)) (segments_reserved rsegs) /\
  (bv_unsigned (fst (nth k (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0))),
   bv_unsigned (snd (nth k (segments_reserved rsegs) (Z_to_bv 64 0, Z_to_bv 64 0)))) =
  nth k [(65536, 8192); (73728, 49152); (122880, 4096); (126976, 204800)] (0, 0).
Proof.
  intros k Hk. split.
  - apply nth_In. replace (length (segments_reserved rsegs)) with 4%nat by (vm_compute; reflexivity). exact Hk.
  - rewrite <- resv_extents. rewrite <- (map_nth (fun p : word * word => (bv_unsigned (fst p), bv_unsigned (snd p)))).
    reflexivity.
Qed.
Lemma in_img_rsegs : forall (B : malloc_syms) a, ms_segs B = rsegs ->
  (in_img B a <-> (65536 <= a < 73728 \/ 73728 <= a < 122880 \/ 122880 <= a < 126976 \/ 126976 <= a < 331776)).
Proof.
  intros B a Hs. unfold in_img. rewrite Hs. split.
  - intros [_ (p & Hp & Hr)]. apply (in_map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p)))) in Hp.
    rewrite resv_extents in Hp. cbn [In] in Hp.
    destruct Hp as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; rewrite <- E1, <- E2 in Hr; lia.
  - intros H. split; [unfold rsegs; discriminate|].
    destruct H as [H|[H|[H|H]]].
    + destruct (resv_nth 0 ltac:(lia)) as [Hin _]. eexists. split; [exact Hin|].
      match goal with |- context [bv_unsigned (fst ?p)] => replace (bv_unsigned (fst p)) with 65536 by (vm_compute; reflexivity) end.
      match goal with |- context [bv_unsigned (snd ?p)] => replace (bv_unsigned (snd p)) with 8192 by (vm_compute; reflexivity) end.
      lia.
    + destruct (resv_nth 1 ltac:(lia)) as [Hin _]. eexists. split; [exact Hin|].
      match goal with |- context [bv_unsigned (fst ?p)] => replace (bv_unsigned (fst p)) with 73728 by (vm_compute; reflexivity) end.
      match goal with |- context [bv_unsigned (snd ?p)] => replace (bv_unsigned (snd p)) with 49152 by (vm_compute; reflexivity) end.
      lia.
    + destruct (resv_nth 2 ltac:(lia)) as [Hin _]. eexists. split; [exact Hin|].
      match goal with |- context [bv_unsigned (fst ?p)] => replace (bv_unsigned (fst p)) with 122880 by (vm_compute; reflexivity) end.
      match goal with |- context [bv_unsigned (snd ?p)] => replace (bv_unsigned (snd p)) with 4096 by (vm_compute; reflexivity) end.
      lia.
    + destruct (resv_nth 3 ltac:(lia)) as [Hin _]. eexists. split; [exact Hin|].
      match goal with |- context [bv_unsigned (fst ?p)] => replace (bv_unsigned (fst p)) with 126976 by (vm_compute; reflexivity) end.
      match goal with |- context [bv_unsigned (snd ?p)] => replace (bv_unsigned (snd p)) with 204800 by (vm_compute; reflexivity) end.
      lia.
Qed.
Lemma noimg_noseg : forall (B : malloc_syms) a, ms_segs B = rsegs -> ~ in_img B a -> find_segment rsegs a 1 = None.
Proof.
  intros B a Hs Hn. destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|reflexivity]. exfalso. apply Hn.
  apply (in_img_rsegs B a Hs).
  pose proof (YK1j.find_segment_in _ _ _ _ E) as Hin.
  pose proof (YK1j.find_segment_range _ _ _ _ E) as Hr.
  apply (in_map (fun s => (seg_base s, seg_size s))) in Hin. rewrite rsegs_extents in Hin. cbn [In] in Hin.
  destruct Hin as [H|[H|[H|[H|[]]]]]; injection H as E1 E2; rewrite <- E1, <- E2 in Hr; cbn in Hr; lia.
Qed.
