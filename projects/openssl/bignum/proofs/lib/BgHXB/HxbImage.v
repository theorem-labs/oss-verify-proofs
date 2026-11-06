(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Mem. 
From OSSVerify.openssl.bignum.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxVal HxMem HxMemSound HxToolkit HxImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation bgbsegs := ImageBgA.bgbsegs.

Definition seg0 := AsanUbsan_segment_000.
Definition seg1 := AsanUbsan_segment_001.
Definition seg2 := AsanUbsan_segment_002.
Definition seg3 := AsanUbsan_segment_003.

Lemma asegs_eq : bgbsegs = [seg0; seg1; seg2; seg3].
Proof. reflexivity. Qed.

Local Ltac seg_consts :=
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 65536%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 1589248%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 1654784%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 4009984%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 5664768%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 491520%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 6156288%Z by (vm_compute; reflexivity);
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 6397952%Z by (vm_compute; reflexivity).

Lemma find_seg : forall a n, 1 <= n ->
  find_segment bgbsegs a n =
    if (65536 <=? a) && (a + n <=? 1654784) then Some seg0
    else if (1654784 <=? a) && (a + n <=? 5664768) then Some seg1
    else if (5664768 <=? a) && (a + n <=? 6156288) then Some seg2
    else if (6156288 <=? a) && (a + n <=? 12554240) then Some seg3
    else None.
Proof.
  intros a n Hn. unfold bgbsegs, AsanUbsan.M.loaded_segments, AsanUbsan.AsanUbsan_loaded_segments.
  cbn [find_segment]. seg_consts. reflexivity.
Qed.

Lemma seg0_ro : seg_writable seg0 = false. Proof. vm_compute. reflexivity. Qed.
Lemma seg0_rd : seg_readable seg0 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_wr : seg_writable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg2_rd : seg_readable seg2 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_wr : seg_writable seg3 = true. Proof. vm_compute. reflexivity. Qed.
Lemma seg3_rd : seg_readable seg3 = true. Proof. vm_compute. reflexivity. Qed.

Lemma ro_addr_seg0 : forall a, 65536 <= a < 1654784 -> ro_addr bgbsegs (wa a) = true.
Proof.
  intros a Ha. unfold ro_addr. rewrite wa_unsigned by lia. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 1654784)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.leb_le]; lia).
  rewrite seg0_ro. reflexivity.
Qed.

Definition chunk_of (sg : Segment) : PrimString.string := match seg_bytes sg with [c] => c | _ => PrimString.make 0%uint63 0%uint63 end.
Lemma seg0_chunk : seg_bytes seg0 = [chunk_of seg0]. Proof. reflexivity. Qed.
Lemma seg2_chunk : seg_bytes seg2 = [chunk_of seg2]. Proof. reflexivity. Qed.
Lemma seg3_chunk : seg_bytes seg3 = [chunk_of seg3]. Proof. reflexivity. Qed.

Lemma find_seg0_in : forall a, 65536 <= a < 1654784 -> find_segment bgbsegs a 1 = Some seg0.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 1654784)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg2_in : forall a, 5664768 <= a < 6156288 -> find_segment bgbsegs a 1 = Some seg2.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 1654784)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((1654784 <=? a) && (a + 1 <=? 5664768)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((5664768 <=? a) && (a + 1 <=? 6156288)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma find_seg3_in : forall a, 6156288 <= a < 12554240 -> find_segment bgbsegs a 1 = Some seg3.
Proof.
  intros a Ha. rewrite find_seg by lia.
  replace ((65536 <=? a) && (a + 1 <=? 1654784)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((1654784 <=? a) && (a + 1 <=? 5664768)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((5664768 <=? a) && (a + 1 <=? 6156288)) with false by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((6156288 <=? a) && (a + 1 <=? 12554240)) with true by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia). reflexivity.
Qed.

Lemma ro_none (m : word -> option byte) (a : Z) : mem_inv bgbsegs m -> 65536 <= a < 1654784 -> m (wa a) = None.
Proof.
  intros MI Ha. destruct (m (wa a)) as [b|] eqn:E; [|reflexivity]. pose proof (mem_inv_ro bgbsegs m _ _ MI E) as H.
  rewrite (ro_addr_seg0 a Ha) in H. discriminate.
Qed.

Lemma asegs_wr_rd : forall sg, In sg bgbsegs -> seg_writable sg = true -> seg_readable sg = true.
Proof.
  intros sg Hin Hw. rewrite asegs_eq in Hin. cbn [In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; vm_compute; reflexivity.
Qed.

Lemma img_region_ok_view (segs : list Segment) (rho : valuation) (t : int) (lo size al : int) (wr : bool) (i : nat) (dl : int) (d : nat)
    (sg : Segment) (c : string) (m : word -> option byte) :
  nth_error segs i = Some sg -> seg_bytes sg = [c] -> seg_readable sg = true -> (wr = true -> seg_writable sg = true) ->
  to_Z lo = Z.of_N (seg_base sg) + to_Z dl ->
  (forall a, to_Z lo <= a < to_Z lo + to_Z size -> find_segment segs a 1 = Some sg) ->
  2 * (to_Z dl + to_Z size) <= to_Z (PrimString.length c) -> to_Z dl + to_Z size < 2 ^ 59 ->
  img_valid c dl (Z.to_nat (to_Z size)) = true ->
  (forall a, to_Z lo <= a < to_Z lo + to_Z size -> mrd segs m (wa a) = seg_rom segs (wa a)) ->
  0 < to_Z lo -> to_Z lo + to_Z size < two63 -> to_Z size <= 8 * 2 ^ Z.of_nat d -> Z.of_nat d <= 59 ->
  to_Z al < 63 -> to_Z lo mod 2 ^ to_Z al = 0 ->
  region_ok segs rho t (RG (Some lo) size al wr (DImage i dl) d IEmpty) m.
Proof.
  intros Hn Hc Hrd Hwr Elo Hseg Hlen H59 Hval Hview Hpos Hhi Hd Hd59 Hal Hmod.
  pose proof (img_region_ok segs rho t lo size al wr i dl d sg c (fun _ => None) Hn Hc Hrd Hwr Elo Hseg Hlen H59 Hval
                (fun _ _ => eq_refl) Hpos Hhi Hd Hd59 Hal Hmod) as H0.
  apply (region_ok_frame segs rho t _ (fun _ => None) m H0).
  intros k Hk. unfold rbase. cbn [rg_abs rg_size] in *. split.
  - rewrite (Hview (to_Z lo + k) ltac:(lia)). reflexivity.
  - intros Hw. unfold wview in *. destruct (m (wa (to_Z lo + k))) as [b|]; [discriminate | exact Hw].
Qed.
