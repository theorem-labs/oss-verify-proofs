(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitState.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_ok (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint scanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_ok s base
      else let h := N.div2 n in (scanN s f base h && scanN s f (base + h) (n - h))%bool
  end.

Lemma scanN_sound : forall s fuel base n,
  scanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N <> None.
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [scanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold byte_ok in H.
      destruct (hex_byte_at s base); [discriminate|discriminate].
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

Lemma segment_byte_at_some1 : forall s (n : N) (off : N),
  scanN s 64 0 n = true ->
  (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  (off < n)%N ->
  exists b, segment_byte_at [s] off = Some b.
Proof.
  intros s n off Hs Hn Hoff. cbn [segment_byte_at].
  replace (off <? Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N with true
    by (symmetry; apply N.ltb_lt; lia).
  pose proof (scanN_sound s 64 0 n Hs off Hoff) as H. rewrite N.add_0_l in H.
  destruct (hex_byte_at s off) as [b|]; [exists b; reflexivity | congruence].
Qed.

Section Pointwise.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition byte_cond (a : Z) : Prop :=
  (exists b, image_byte segs (Z_to_bv 64 a) = Some b)
  /\ exists seg b, find_segment segs a 1 = Some seg /\ seg_writable seg = true
       /\ segment_byte_at (seg_bytes seg) (Z.to_N (a - Z.of_N (seg_base seg))) = Some b.

Lemma data_ok_from_intro : forall n a,
  (forall j, (j < n)%nat -> byte_cond (a + Z.of_nat j)) -> data_ok_from segs a n = true.
Proof.
  induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [data_ok_from].
  destruct (H 0%nat ltac:(lia)) as [[b Hb] (seg & b' & Hf & Hw & Hs)]. rewrite Z.add_0_r in Hb, Hf, Hs.
  rewrite Hb, Hf, Hw, Hs. cbn [andb].
  apply IH. intros j Hj. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. apply H. lia.
Qed.

Lemma data_ok_b_intro : forall lo hi, 0 <= lo <= hi ->
  (forall x, lo <= x < hi -> byte_cond x) -> data_ok_b segs lo hi = true.
Proof.
  intros lo hi Hlh H. unfold data_ok_b.
  replace (0 <=? lo) with true by (symmetry; apply Z.leb_le; lia).
  replace (lo <=? hi) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  apply data_ok_from_intro. intros j Hj. apply H. lia.
Qed.
End Pointwise.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition segsA : list Segment := AsanUbsan.M.loaded_segments.

Lemma scan_002 : scanN AsanUbsan_seg_bytes_002 64 0 0x5000 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma scan_003 : scanN AsanUbsan_seg_bytes_003 64 0 0x55d000 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma len_002 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 0x5000%N.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma len_003 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55d000%N.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

(* [comment removed for export] *)
Lemma find_segment_A_rw : forall x, 0xe1000 <= x < 0x643000 ->
  find_segment segsA x 1 =
    Some (if x <? 0xe6000 then AsanUbsan_segment_002 else AsanUbsan_segment_003).
Proof.
  intros x Hx. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 176128%N) with 176128.
  change (Z.of_N 241664%N) with 241664. change (Z.of_N 679936%N) with 679936.
  change (Z.of_N 921600%N) with 921600. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 942080%N) with 942080. change (Z.of_N 5623808%N) with 5623808.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 176128)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 241664 x); destruct (Z.leb_spec (x + 1) (241664 + 679936)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 921600 x); destruct (Z.leb_spec (x + 1) (921600 + 20480)); cbn [andb]; try lia.
  all: destruct (Z.ltb_spec x 0xe6000); try lia; try reflexivity.
  all: destruct (Z.leb_spec 942080 x); destruct (Z.leb_spec (x + 1) (942080 + 5623808)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma seg2_facts : seg_readable AsanUbsan_segment_002 = true /\ seg_writable AsanUbsan_segment_002 = true
  /\ Z.of_N (seg_base AsanUbsan_segment_002) = 0xe1000 /\ seg_bytes AsanUbsan_segment_002 = [AsanUbsan_seg_bytes_002].
Proof. repeat split; reflexivity. Qed.
Lemma seg3_facts : seg_readable AsanUbsan_segment_003 = true /\ seg_writable AsanUbsan_segment_003 = true
  /\ Z.of_N (seg_base AsanUbsan_segment_003) = 0xe6000 /\ seg_bytes AsanUbsan_segment_003 = [AsanUbsan_seg_bytes_003].
Proof. repeat split; reflexivity. Qed.

Lemma byte_cond_of_seg : forall x seg s base n,
  find_segment segsA x 1 = Some seg ->
  seg_readable seg = true -> seg_writable seg = true -> Z.of_N (seg_base seg) = base -> seg_bytes seg = [s] ->
  scanN s 64 0 n = true -> (n <= Z.to_N (Uint63.to_Z (PrimString.length s) / 2))%N ->
  base <= x -> (Z.to_N (x - base) < n)%N -> 0 <= x < 2 ^ 64 ->
  byte_cond segsA x.
Proof.
  intros x seg s base n Hf Hr Hw Hb Hs Hscan Hn Hbx Hxn Hx.
  assert (Hu : bv_unsigned (Z_to_bv 64 x) = x).
  { rewrite Z_to_bv_unsigned. apply (bv_wrap_small 64 x). change (bv_modulus 64) with (2 ^ 64). lia. }
  destruct (segment_byte_at_some1 s n (Z.to_N (x - base)) Hscan Hn Hxn) as [b Hbyte].
  split.
  - exists b. unfold image_byte, memory_read. rewrite Hu. change (Z.of_N 1) with 1. rewrite Hf, Hr, Hb, Hs.
    change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite Hbyte. reflexivity.
  - exists seg, b. split; [exact Hf|]. split; [exact Hw|]. rewrite Hb, Hs. exact Hbyte.
Qed.

Lemma byte_cond_A : forall x, 0xe1000 <= x < 0x643000 -> byte_cond segsA x.
Proof.
  intros x Hx. pose proof (find_segment_A_rw x Hx) as Hf.
  destruct seg2_facts as (R2 & W2 & B2 & S2). destruct seg3_facts as (R3 & W3 & B3 & S3).
  destruct (Z.ltb_spec x 0xe6000) as [Hlt|Hge].
  - apply (byte_cond_of_seg x _ _ 0xe1000 0x5000 Hf R2 W2 B2 S2 scan_002); [rewrite len_002; lia|lia|lia|lia].
  - apply (byte_cond_of_seg x _ _ 0xe6000 0x55d000 Hf R3 W3 B3 S3 scan_003); [rewrite len_003; lia|lia|lia|lia].
Qed.

Theorem dataA_ok : data_ok_b segsA 0xe1000 0x643000 = true.
Proof.
  apply data_ok_b_intro; [lia|]. exact byte_cond_A.
Qed.
