(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import PrimString.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxFetchFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition fimg_c (c : PrimString.string) (x : int) : option int :=
  if (x <? 1152921504606846976)%uint63 &&& ((x << 1) + 1 <? PrimString.length c)%uint63 then hbyte c (x << 1)%uint63 else None.

Definition fimg_i (segs : list Segment) (i : nat) (x : int) : option int :=
  match nth_error segs i with
  | Some sg => match seg_bytes sg with [c] => fimg_c c x | _ => None end
  | None => None
  end.

Lemma fimg_c_spec (c : PrimString.string) (x b : int) :
  fimg_c c x = Some b -> segment_byte_at [c] (Z.to_N (to_Z x)) = Some (Z_to_bv 8 (to_Z b)) /\ to_Z b < 256.
Proof.
  unfold fimg_c. intros H.
  destruct (ltbP x 1152921504606846976) as [Hx|Hx]; [|discriminate]. change (to_Z 1152921504606846976%uint63) with (2 ^ 60) in Hx.
  pose proof (to_Z_bounded x) as Bx. change wB with (2 ^ 63) in Bx.
  assert (Hsh : to_Z (x << 1)%uint63 = 2 * to_Z x).
  { rewrite lsl_spec. change (to_Z 1%uint63) with 1. change wB with (2 ^ 63). rewrite Z.mod_small by lia. lia. }
  destruct (ltbP ((x << 1) + 1)%uint63 (PrimString.length c)) as [Hl|Hl]; [|discriminate].
  rewrite add_spec, Hsh in Hl. change (to_Z 1%uint63) with 1 in Hl. change wB with (2 ^ 63) in Hl. rewrite Z.mod_small in Hl by lia.
  assert (Ej : (x << 1)%uint63 = of_Z (2 * Z.of_N (Z.to_N (to_Z x)))).
  { apply to_Z_inj. rewrite Hsh, Z2N.id by lia. rewrite of_Z_spec. change wB with (2 ^ 63). rewrite Z.mod_small by lia. reflexivity. }
  rewrite Ej in H. cbn [segment_byte_at].
  assert (Hc : (Z.to_N (to_Z x) <? Z.to_N (to_Z (PrimString.length c) / 2))%N = true).
  { apply N.ltb_lt. apply Z2N.inj_lt; [lia | apply Z.div_pos; lia |].
    apply (Z.lt_le_trans _ (to_Z x + 1)); [lia|]. apply Z.div_le_lower_bound; lia. }
  rewrite Hc. apply hex_byte_at_hbyte; [rewrite Z2N.id by lia; lia | rewrite Z2N.id by lia; lia | exact H].
Qed.

Lemma fimg_i_spec (segs : list Segment) (i : nat) (x b : int) (sg : Segment) :
  nth_error segs i = Some sg -> fimg_i segs i x = Some b ->
  segment_byte_at (seg_bytes sg) (Z.to_N (to_Z x)) = Some (Z_to_bv 8 (to_Z b)) /\ to_Z b < 256.
Proof.
  intros Hn H. unfold fimg_i in H. rewrite Hn in H. destruct (seg_bytes sg) as [|c [|c' r]]; try discriminate.
  exact (fimg_c_spec c x b H).
Qed.

(* [comment removed for export] *)
Lemma fimg_i_rom (segs : list Segment) (i : nat) (x b : int) (sg : Segment) :
  nth_error segs i = Some sg -> fimg_i segs i x = Some b ->
  find_segment segs (Z.of_N (seg_base sg) + to_Z x) 1 = Some sg -> seg_readable sg = true ->
  Z.of_N (seg_base sg) + to_Z x < 2 ^ 64 ->
  seg_rom segs (Z_to_bv 64 (Z.of_N (seg_base sg) + to_Z x)) = Some (Z_to_bv 8 (to_Z b)).
Proof.
  intros Hn H Hf Hr H64. destruct (fimg_i_spec segs i x b sg Hn H) as [Hb _].
  pose proof (to_Z_bounded x) as Bx.
  unfold seg_rom, memory_read.
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_N (seg_base sg) + to_Z x)) = Z.of_N (seg_base sg) + to_Z x).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite Hu. change (Z.of_N 1) with 1. rewrite Hf, Hr. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  replace (Z.of_N (seg_base sg) + to_Z x - Z.of_N (seg_base sg)) with (to_Z x) by lia. rewrite Hb. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fimg_i_wview (segs : list Segment) (m : word -> option byte) (i : nat) (x b : int) (sg : Segment) :
  nth_error segs i = Some sg -> fimg_i segs i x = Some b ->
  find_segment segs (Z.of_N (seg_base sg) + to_Z x) 1 = Some sg -> seg_writable sg = true ->
  Z.of_N (seg_base sg) + to_Z x < 2 ^ 64 ->
  wview segs m (Z_to_bv 64 (Z.of_N (seg_base sg) + to_Z x)) <> None.
Proof.
  intros Hn H Hf Hw H64. destruct (fimg_i_spec segs i x b sg Hn H) as [Hb _].
  pose proof (to_Z_bounded x) as Bx. unfold wview.
  destruct (m (Z_to_bv 64 (Z.of_N (seg_base sg) + to_Z x))); [discriminate|].
  assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_N (seg_base sg) + to_Z x)) = Z.of_N (seg_base sg) + to_Z x).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
  rewrite Hu, Hf, Hw. replace (Z.of_N (seg_base sg) + to_Z x - Z.of_N (seg_base sg)) with (to_Z x) by lia.
  rewrite Hb. discriminate.
Qed.
