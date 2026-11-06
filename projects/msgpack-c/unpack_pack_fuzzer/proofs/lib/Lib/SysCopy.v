(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame SysStep.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section Copy1.
Variable segs : list Segment.
Variables (before m : word -> option byte) (src dst len : Z).
Hypothesis Hs : 0 <= src /\ src + len <= 2^64.
Hypothesis Hd : 0 <= dst /\ dst + len <= 2^64.
Hypothesis Hl : 0 < len < 2^64.
Let m' := apply_copies before m [mkCopy (wa src) (Z_to_bv 64 dst) (Z_to_bv 64 len)].

Lemma copies1_spec : forall x,
  m' x = if in_range dst len x then before (wa (src + (bv_unsigned x - dst))) else m x.
Proof.
  intros x. unfold m'. cbn [apply_copies]. unfold apply_copy. cbn [copy_src copy_dst copy_len]. unfold in_range, wa.
  rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma copies_outside : forall x, (bv_unsigned x < dst \/ dst + len <= bv_unsigned x) -> m' x = m x.
Proof.
  intros x Hx. rewrite copies1_spec. unfold in_range.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + len)); cbn [andb]; try reflexivity. lia.
Qed.

Lemma copies_inside : forall i, 0 <= i < len -> m' (wa (dst + i)) = before (wa (src + i)).
Proof.
  intros i Hi. rewrite copies1_spec. unfold in_range. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 dst (dst + i)); destruct (Z.ltb_spec0 (dst + i) (dst + len)); cbn [andb]; try lia.
  f_equal. unfold wa. f_equal. lia.
Qed.

Lemma bytes_at_copies_other : forall A bs,
  bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= dst \/ dst + len <= A) -> bytes_at segs m' A bs.
Proof.
  intros A bs (H0 & H1 & H) HD. split; [lia|]. split; [lia|]. intros i Hi.
  unfold mrd. rewrite copies_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

Lemma wr_at_copies_other : forall A k,
  wr_at segs m A k -> (A + k <= dst \/ dst + len <= A) -> wr_at segs m' A k.
Proof.
  intros A k (H0 & H1 & H) HD. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite copies_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed.

Lemma rw_cells_copies_other : forall A cs,
  rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= dst \/ dst + len <= A) -> rw_cells segs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] HD. split; [split; [exact Hwf|]|].
  - apply bytes_at_copies_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact HD.
  - apply wr_at_copies_other; [exact Hw| exact HD].
Qed.

Lemma stk_copies_other : forall lo hi, stk segs m lo hi -> (hi <= dst \/ dst + len <= lo) -> stk segs m' lo hi.
Proof.
  intros lo hi (H0 & H1 & H) HD. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)].
  assert (E : m' (wa x) = m (wa x)). { apply copies_outside. rewrite wa_unsigned by lia. lia. }
  split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

Lemma bytes_at_copies_moved : forall o bs,
  bytes_at segs before (src + o) bs -> 0 <= o -> o + Z.of_nat (length bs) <= len ->
  (forall i, 0 <= i < len -> seg_rom segs (wa (dst + i)) = None /\ seg_rom segs (wa (src + i)) = None) ->
  bytes_at segs m' (dst + o) bs.
Proof.
  intros o bs (H0 & H1 & H) Ho HL NSEG. split; [lia|]. split; [lia|]. intros i Hi.
  specialize (H i Hi). unfold mrd in *. replace (dst + o + Z.of_nat i) with (dst + (o + Z.of_nat i)) by lia.
  rewrite copies_inside by lia. replace (src + o + Z.of_nat i) with (src + (o + Z.of_nat i)) in H by lia.
  destruct (NSEG (o + Z.of_nat i) ltac:(lia)) as [ND NS]. rewrite ND. rewrite NS in H. exact H.
Qed.

Lemma copies_moved_byte : forall i, 0 <= i < len -> m' (wa (dst + i)) = before (wa (src + i)).
Proof. intros i Hi. apply copies_inside. exact Hi. Qed.

Lemma mem_inv_copies : mem_inv segs m ->
  (forall x : word, dst <= bv_unsigned x < dst + len -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
  intros Hinv NRO x b Hx. rewrite copies1_spec in Hx. unfold in_range in Hx.
  destruct (Z.leb_spec0 dst (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (dst + len)); cbn [andb] in Hx;
    try exact (Hinv _ _ Hx).
  apply NRO. lia.
Qed.
End Copy1.

End CEIL.
