(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Exec Frame ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Lemma nret_MSsvc_copy1 : forall R F pc x8 fc rv m ro r zs us c cis,
  nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r [] zs us [c] cis)
  = MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4)%bv fc rv (apply_copy m (apply_zeros (apply_unmaps m us) zs) c) ro.
Proof. reflexivity. Qed.

Definition in_rangeZ (a n : Z) (x : word) : bool :=
  (a <=? bv_unsigned x) && (bv_unsigned x <? a + n).

Lemma apply_copy_spec : forall before mem (src dst len : Z) x,
  0 <= src -> 0 <= dst < 2^64 -> 0 <= len < 2^64 ->
  apply_copy before mem (mkCopy (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 len)) x =
  if in_rangeZ dst len x then before (Z_to_bv 64 (src mod 2^64 + (bv_unsigned x - dst))) else mem x.
Proof.
  intros before mem src dst len x Hs Hd Hl. unfold apply_copy. cbn [copy_src copy_dst copy_len].
  rewrite !(unsigned_lit dst) by lia. rewrite (unsigned_lit len) by lia. rewrite unsigned_lit_wrap.
  unfold in_rangeZ. reflexivity.
Qed.

Section Move.
  Variable segs : list Segment.
  Variables (m : word -> option byte) (old d on nn : Z).
  Hypothesis Hold : 0 <= old /\ old + on <= 2^64.
  Hypothesis Hd : 0 <= d /\ d + nn <= 2^64.
  Hypothesis Hon : 0 < on.
  Hypothesis Hnn : on < nn.
  (* [comment removed for export] *)
  Hypothesis Hdisj : old + on <= d \/ d + nn <= old.

  (* [comment removed for export] *)
  Definition move_mem : word -> option byte :=
    apply_copy m (apply_zeros (apply_unmaps m [(Z_to_bv 64 old, Z_to_bv 64 on)])
                                [((Z_to_bv 64 d + Z_to_bv 64 on)%bv, Z_to_bv 64 (nn - on))])
               (mkCopy (Z_to_bv 64 old) (Z_to_bv 64 d) (Z_to_bv 64 on)).

  Lemma move_mem_eq : forall x,
    move_mem x =
      if in_rangeZ d on x then m (Z_to_bv 64 (old + (bv_unsigned x - d)))
      else if in_rangeZ (d + on) (nn - on) x then Some (Z_to_bv 8 0)
      else if in_rangeZ old on x then None
      else m x.
  Proof.
    intros x. unfold move_mem. rewrite apply_copy_spec by lia. rewrite (Z.mod_small old) by lia.
    destruct (in_rangeZ d on x); [reflexivity|].
    rewrite lit_add_lit. cbn [apply_zeros apply_unmaps zeros_cover existsb fst snd].
    rewrite !unsigned_lit by lia. rewrite !orb_false_r. unfold in_rangeZ.
    destruct ((d + on <=? bv_unsigned x) && (bv_unsigned x <? d + on + (nn - on))) eqn:E1;
    destruct ((d + on <=? bv_unsigned x) && (bv_unsigned x <? d + (nn - on) + on)) eqn:E2 || idtac.
    all: try reflexivity.
    all: replace (d + on + (nn - on)) with (d + nn) in * by lia.
    all: try (destruct ((old <=? bv_unsigned x) && (bv_unsigned x <? old + on)); reflexivity).
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hsrc : forall i, 0 <= i < on -> m (wa (old + i)) <> None.

  Lemma move_mem_inside : forall i, 0 <= i < on -> move_mem (wa (d + i)) = m (wa (old + i)).
  Proof.
    intros i Hi. rewrite move_mem_eq. unfold in_rangeZ. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 d (d + i)); destruct (Z.ltb_spec0 (d + i) (d + on)); cbn [andb]; try lia.
    unfold wa. f_equal. f_equal. lia.
  Qed.

  Lemma move_mem_tail : forall i, on <= i < nn -> move_mem (wa (d + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros i Hi. rewrite move_mem_eq. unfold in_rangeZ. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 d (d + i)); destruct (Z.ltb_spec0 (d + i) (d + on)); cbn [andb]; try lia.
    destruct (Z.leb_spec0 (d + on) (d + i)); destruct (Z.ltb_spec0 (d + i) (d + on + (nn - on))); cbn [andb]; try lia.
    reflexivity.
  Qed.

  Lemma move_mem_source : forall i, 0 <= i < on -> move_mem (wa (old + i)) = None.
  Proof.
    intros i Hi. rewrite move_mem_eq. unfold in_rangeZ. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 d (old + i)); destruct (Z.ltb_spec0 (old + i) (d + on)); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 (d + on) (old + i)); destruct (Z.ltb_spec0 (old + i) (d + on + (nn - on))); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 old (old + i)); destruct (Z.ltb_spec0 (old + i) (old + on)); cbn [andb]; try lia; reflexivity.
  Qed.

  Lemma move_mem_outside : forall x : word,
    (bv_unsigned x < d \/ d + nn <= bv_unsigned x) -> (bv_unsigned x < old \/ old + on <= bv_unsigned x) ->
    move_mem x = m x.
  Proof.
    intros x Hx1 Hx2. rewrite move_mem_eq. unfold in_rangeZ.
    destruct (Z.leb_spec0 d (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (d + on)); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 (d + on) (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (d + on + (nn - on))); cbn [andb]; try lia.
    all: destruct (Z.leb_spec0 old (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (old + on)); cbn [andb]; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_mremap_move : forall off bs,
    0 <= off -> off + Z.of_nat (length bs) <= on ->
    bytes_at segs m (old + off) bs -> bytes_at segs move_mem (d + off) bs.
  Proof.
    intros off bs Hoff Hlen (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi.
    unfold mrd. replace (d + off + Z.of_nat i) with (d + (off + Z.of_nat i)) by lia.
    rewrite move_mem_inside by lia. replace (old + (off + Z.of_nat i)) with (old + off + Z.of_nat i) by lia.
    specialize (H i Hi). unfold mrd in H.
    pose proof (Hsrc (off + Z.of_nat i) ltac:(lia)) as Hs. replace (old + (off + Z.of_nat i)) with (old + off + Z.of_nat i) in Hs by lia.
    destruct (m (wa (old + off + Z.of_nat i))); [exact H | exfalso; apply Hs; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_mremap_tail : bytes_at segs move_mem (d + on) (repeat (Z_to_bv 8 0) (Z.to_nat (nn - on))).
  Proof.
    split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
    unfold mrd. replace (d + on + Z.of_nat i) with (d + (on + Z.of_nat i)) by lia. rewrite move_mem_tail by lia.
    symmetry. apply nth_error_repeat. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma move_mem_dest_some : forall i, 0 <= i < nn -> move_mem (wa (d + i)) <> None.
  Proof.
    intros i Hi. destruct (Z.lt_ge_cases i on).
    - rewrite move_mem_inside by lia. apply Hsrc. lia.
    - rewrite move_mem_tail by lia. discriminate.
  Qed.

  Lemma wr_at_mremap_move : wr_at segs move_mem d nn.
  Proof.
    split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
    destruct (move_mem (wa (d + i))) eqn:E; [discriminate|]. exfalso. exact (move_mem_dest_some i Hi E).
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_mremap_other : forall A bs,
    bytes_at segs m A bs ->
    (A + Z.of_nat (length bs) <= d \/ d + nn <= A) -> (A + Z.of_nat (length bs) <= old \/ old + on <= A) ->
    bytes_at segs move_mem A bs.
  Proof.
    intros A bs (H0 & H1 & H) HD HO. split; [lia|]. split; [lia|]. intros i Hi.
    unfold mrd. rewrite move_mem_outside; [exact (H i Hi) | rewrite wa_unsigned by lia; lia | rewrite wa_unsigned by lia; lia].
  Qed.

  Lemma munch_mremap_move : forall W m0,
    munch W m0 m -> inside W d nn -> inside W old on -> munch W m0 move_mem.
  Proof.
    intros W m0 HM HiD HiO x Hx. pose proof (bv_unsigned_in_range 64 x) as Hxr.
    rewrite move_mem_outside.
    - apply HM. exact Hx.
    - destruct (Z.lt_ge_cases (bv_unsigned x) d); [left; assumption|].
      destruct (Z.le_gt_cases (d + nn) (bv_unsigned x)); [right; assumption|].
      exfalso. eapply (inside_not_outside W d nn (bv_unsigned x) HiD); [lia | exact Hx].
    - destruct (Z.lt_ge_cases (bv_unsigned x) old); [left; assumption|].
      destruct (Z.le_gt_cases (old + on) (bv_unsigned x)); [right; assumption|].
      exfalso. eapply (inside_not_outside W old on (bv_unsigned x) HiO); [lia | exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma mem_inv_mremap_move :
    mem_inv segs m -> (forall x : word, d <= bv_unsigned x < d + nn -> ro_addr segs x = false) ->
    d + nn <= TASK_SIZE ->
    mem_inv segs move_mem.
  Proof.
    intros HM Hro Htask x b Hx. pose proof (bv_unsigned_in_range 64 x) as Hxr.
    destruct (Z.lt_ge_cases (bv_unsigned x) d) as [Hlt|Hge].
    - destruct (Z.lt_ge_cases (bv_unsigned x) old) as [Hlt'|Hge'].
      + rewrite move_mem_outside in Hx by lia. exact (HM _ _ Hx).
      + destruct (Z.lt_ge_cases (bv_unsigned x) (old + on)) as [Hi|Ho].
        * exfalso. rewrite <- (wa_unsigned_id x) in Hx. replace (bv_unsigned x) with (old + (bv_unsigned x - old)) in Hx by lia.
          rewrite move_mem_source in Hx by lia. discriminate.
        * rewrite move_mem_outside in Hx by lia. exact (HM _ _ Hx).
    - destruct (Z.lt_ge_cases (bv_unsigned x) (d + nn)) as [Hi|Ho]; [right; split; [apply Hro; lia| lia]|].
      destruct (Z.lt_ge_cases (bv_unsigned x) old) as [Hlt'|Hge'].
      + rewrite move_mem_outside in Hx by lia. exact (HM _ _ Hx).
      + destruct (Z.lt_ge_cases (bv_unsigned x) (old + on)) as [Hi'|Ho'].
        * exfalso. rewrite <- (wa_unsigned_id x) in Hx. replace (bv_unsigned x) with (old + (bv_unsigned x - old)) in Hx by lia.
          rewrite move_mem_source in Hx by lia. discriminate.
        * rewrite move_mem_outside in Hx by lia. exact (HM _ _ Hx).
  Qed.
End Move.


End CeilWrap.
