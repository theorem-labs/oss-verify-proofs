(** * ZReproQ6C — Q6 leg (c): the TYPEDO arm as dec_blk's two header reads.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19).  At a block
    boundary that is not after the final block ([h_last = 0]), a
    CONTINUING [inf_TYPEDO] step performs exactly [dec_blk]'s prefix:
    [read_bits 1] (the final-block flag) then [read_bits 2] (the block
    type) on the declarative stream, landing in the arm [dec_blk]
    dispatches to — STORED, the fixed tables at [M_LEN_] (with
    [TRlenfix]/[TRdistfix] pinned, which the stage-2 fixed leg reads), or
    [M_TABLE]; type 3 is [M_BAD], absorbed by the success premise.  The
    flush premise kills the [Z_TREES] early-leave in the fixed arm, per
    [ZR_Flush1]'s exclusion.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6A ZReproQ6B.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Lemma zr_typedo_sound : forall c q q',
  n_flush c <> Z_TREES ->
  h_last (s_hdr (q_st q)) = 0 ->
  br_wf (q_br q) ->
  inf_TYPEDO c q = InfCont q' ->
  h_mode (s_hdr (q_st q')) = M_BAD
  \/ (exists lastb ty r1,
        read_bits 1%nat (br_stream (q_br q)) = Some (lastb, r1)
        /\ read_bits 2%nat r1 = Some (ty, br_stream (q_br q'))
        /\ h_last (s_hdr (q_st q')) = lastb
        /\ br_wf (q_br q')
        /\ zr_q6_frame q q'
        /\ ( (ty = 0 /\ h_mode (s_hdr (q_st q')) = M_STORED)
          \/ (ty = 1 /\ h_mode (s_hdr (q_st q')) = M_LEN_
              /\ t_lencode (s_tab (q_st q')) = TRlenfix
              /\ t_lenbits (s_tab (q_st q')) = 9
              /\ t_distcode (s_tab (q_st q')) = TRdistfix
              /\ t_distbits (s_tab (q_st q')) = 5)
          \/ (ty = 2 /\ h_mode (s_hdr (q_st q')) = M_TABLE))).
Proof.
  intros c q q' HF Hlast Hwf H.
  unfold inf_TYPEDO in H. cbv zeta in H.
  rewrite Hlast in H.
  change (negb (0 =? 0)) with false in H.
  destruct (inf_nb 3 (q_br q)) as [b|b] eqn:EN;
    cbv beta iota in H; [| discriminate].
  destruct (inf_nb_ok 3 (q_br q) b Hwf ltac:(lia) EN)
    as (ES & Hwf1 & Hb3).
  (* the two declarative reads, staged once *)
  pose proof (br_read_agree 1 b Hwf1 ltac:(lia)) as R1.
  change (Z.to_nat 1) with 1%nat in R1.
  assert (Hwfd1 : br_wf (br_dropbits 1 b))
    by (apply br_wf_dropbits; [exact Hwf1 | lia]).
  assert (Hbd1 : br_bits (br_dropbits 1 b) = br_bits b - 1)
    by apply br_dropbits_bits.
  pose proof (br_read_agree 2 (br_dropbits 1 b) Hwfd1 ltac:(lia)) as R2.
  change (Z.to_nat 2) with 2%nat in R2.
  assert (Hwfd2 : br_wf (br_dropbits 2 (br_dropbits 1 b)))
    by (apply br_wf_dropbits; [exact Hwfd1 | lia]).
  (* the type dispatch *)
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 0) as [E0|N0].
  { (* stored *)
    injection H as <-. right.
    exists (br_bits_of 1 b), 0, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E0 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    left. split; reflexivity. }
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 1) as [E1|N1].
  { (* fixed: the Z_TREES leave is dead at our flushes *)
    rewrite (proj2 (Z.eqb_neq (n_flush c) Z_TREES) HF) in H.
    cbv beta iota in H.
    injection H as <-. right.
    exists (br_bits_of 1 b), 1, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E1 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    right; left. repeat split; reflexivity. }
  destruct (Z.eqb_spec (br_bits_of 2 (br_dropbits 1 b)) 2) as [E2|N2].
  { (* dynamic *)
    injection H as <-. right.
    exists (br_bits_of 1 b), 2, (br_stream (br_dropbits 1 b)).
    rewrite <- ES.
    rewrite E2 in R2.
    split; [exact R1|].
    split; [exact R2|].
    split; [reflexivity|].
    split; [exact Hwfd2|].
    split; [repeat split; reflexivity|].
    right; right. split; reflexivity. }
  (* type 3: BAD *)
  injection H as <-. left. reflexivity.
Qed.

(** The post-final-block boundary trip: with [h_last <> 0] the arm
    byte-aligns and moves to [M_CHECK], touching nothing else — the tail
    leg (e) reads this at the trailer.  [BYTEBITS] drops [bits mod 8]
    bits, which is exactly [align_byte]'s count on the declarative side
    (leg (e) makes that connection; here we pin the state shape). *)
Lemma zr_typedo_final : forall c q q',
  h_last (s_hdr (q_st q)) <> 0 ->
  inf_TYPEDO c q = InfCont q' ->
  q' = qmode (qset_br q (br_bytebits (q_br q))) M_CHECK.
Proof.
  intros c q q' Hlast H.
  unfold inf_TYPEDO in H. cbv zeta in H.
  destruct (Z.eqb_spec (h_last (s_hdr (q_st q))) 0) as [E|N];
    [contradiction|].
  cbn [negb] in H.
  now injection H as <-.
Qed.

Print Assumptions zr_typedo_sound.
