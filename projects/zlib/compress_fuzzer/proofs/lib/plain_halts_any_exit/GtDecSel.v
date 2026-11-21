(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtDecSel — the slow-decode
      selected-entry SHAPE: Hsel's self-serve glue
      (q7-decode lane, zlib-rt, 2026-08-20)

    [GtDecCost]'s parked [Hsel] leaf needs facts about the entry the
    slow LEN decode SELECTS.  This file proves the selection's SHAPE —
    which table index the returned entry sits at, in the vocabulary the
    table-side invariants speak ([lcode_index_range]'s masked root and
    [if_low]-formed chain target) — so that the classification facts
    an earlier development run is landing (ItGSubPtr / the coverage corollary, statement
    trade 2026-08-20) plug in without any index-arithmetic on their
    side.

    The alignment trick: [if_low op s] reads [Z.land (f_hold s) (2^op-1)],
    and the fetch2 low-part L is bounded by [2^op] when [op >= 0] and
    arbitrary-but-total when [op < 0] (the mask degenerates to -1) — so
    choosing the WITNESS state's [f_hold := L] makes [if_low op s = L]
    in BOTH cases, and no [c_op]-sign side condition is ever needed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ZBitsIn.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import InflateThy.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepReach.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import StepPres.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Chunk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Codec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtInfTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import DeclIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZRepro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecPump.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtDecCost.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The fetch loops return THE MASKED ENTRY of their final reader.
   ========================================================================== *)

Lemma inf_fetch_go_ok_shape :
  forall f t nb b h b',
    inf_fetch_go f t nb b = FetchOk h b' ->
    h = t (br_bits_of nb b').
Proof.
  induction f as [|f IH]; intros t nb b h b' H; cbn [inf_fetch_go] in H;
    [discriminate|].
  destruct (Z.leb (c_bits (t (br_bits_of nb b))) (br_bits b)).
  - injection H as <- <-. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

Lemma inf_fetch_ok_shape :
  forall t nb b h b',
    inf_fetch t nb b = FetchOk h b' -> h = t (br_bits_of nb b').
Proof. intros t nb b h b'. apply inf_fetch_go_ok_shape. Qed.

Lemma inf_fetch2_go_ok_shape :
  forall f t lst b h b',
    inf_fetch2_go f t lst b = FetchOk h b' ->
    h = t (c_val lst
           + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)).
Proof.
  induction f as [|f IH]; intros t lst b h b' H; cbn [inf_fetch2_go] in H;
    [discriminate|].
  match type of H with
  | context[Z.leb ?a ?bb] => destruct (Z.leb a bb)
  end.
  - injection H as <- <-. reflexivity.
  - destruct (br_pullbyte b) as [b1|]; [exact (IH _ _ _ _ _ H) | discriminate].
Qed.

Lemma inf_fetch2_ok_shape :
  forall t lst b h b',
    inf_fetch2 t lst b = FetchOk h b' ->
    h = t (c_val lst
           + Z.shiftr (br_bits_of (c_bits lst + c_op lst) b') (c_bits lst)).
Proof. intros t lst b h b'. apply inf_fetch2_go_ok_shape. Qed.

(* ==========================================================================
   2.  The chain target's low part IS an [if_low] image (dummy-hold
       witness; no [c_op]-sign side condition).
   ========================================================================== *)

(** Simplified, carrying the guard the call sites actually have: the
    fetch2 read is guarded by [c_bits lst + c_bits h <= br_bits b'] and
    everything downstream only needs [0 <= L] plus, on [0 <= op], the
    [2^op] cap.  We additionally take [0 <= h] (the reader's hold sign,
    [rc_hold]-tier), which makes both conjuncts unconditional. *)
Lemma chain_low_bounds :
  forall cb op h,
    0 <= cb -> 0 <= h ->
    0 <= Z.shiftr (Z.land h (Z.shiftl 1 (cb + op) - 1)) cb
    /\ (0 <= op ->
        Z.shiftr (Z.land h (Z.shiftl 1 (cb + op) - 1)) cb
          < Z.shiftl 1 op).
Proof.
  intros cb op h Hcb Hh.
  destruct (Z.le_gt_cases 0 (cb + op)) as [Hs|Hs].
  - pose proof (land_ones_range h (cb + op) Hs) as Hm.
    split.
    + apply Z.shiftr_nonneg. lia.
    + intros Hop.
      rewrite Z.shiftr_div_pow2 by lia.
      rewrite !Z.shiftl_1_l.
      pose proof Hm as Hm2. rewrite !Z.shiftl_1_l in Hm2.
      apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
      assert (Hsplit : 2 ^ cb * 2 ^ op = 2 ^ (cb + op)).
      { rewrite <- Z.pow_add_r by lia. reflexivity. }
      lia.
  - (* cb + op < 0 forces op < 0: only the sign conjunct is live, and
       the degenerate mask is -1 (shiftl 1 (neg) = 0). *)
    rewrite Z.shiftl_1_l, Z.pow_neg_r by lia.
    replace (0 - 1) with (-1) by lia.
    rewrite Z.land_m1_r.
    split.
    + apply Z.shiftr_nonneg. lia.
    + intros Hop. lia.
Qed.

(** The witness state making [if_low op s] read exactly L. *)
Lemma if_low_at :
  forall op L,
    0 <= L -> (op < 0 \/ L < Z.shiftl 1 op) ->
    if_low op {| f_in := 0; f_out := 0; f_hold := L; f_bits := 0;
                 f_buf := zzero |} = L.
Proof.
  intros op L HL Hcase. unfold if_low. cbn [f_hold].
  destruct Hcase as [Hneg|Hlt].
  - rewrite Z.shiftl_1_l, Z.pow_neg_r by lia.
    replace (0 - 1) with (-1) by lia.
    apply Z.land_m1_r.
  - destruct (Z.le_gt_cases 0 op) as [Hop|Hop].
    + rewrite Z.shiftl_1_l in Hlt |- *.
      replace (2 ^ op - 1) with (Z.ones op)
        by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by lia.
      apply Z.mod_small. lia.
    + rewrite Z.shiftl_1_l, Z.pow_neg_r by lia.
      replace (0 - 1) with (-1) by lia.
      apply Z.land_m1_r.
Qed.

(* ==========================================================================
   3.  The decode's selection shape: root or chained, indices in the
       invariant vocabulary.
   ========================================================================== *)

Lemma sel_decode_shape :
  forall (sub : Code -> bool) t rb b h b2 nb,
    inf_decode sub t rb b = DecOk h b2 nb ->
    (exists bf,
        h = t (Z.land (br_hold bf) (Z.shiftl 1 rb - 1))
        /\ nb = c_bits h
        /\ sub h = false)
    \/ (exists bf bg h0,
        h0 = t (Z.land (br_hold bf) (Z.shiftl 1 rb - 1))
        /\ sub h0 = true
        /\ h = t (c_val h0
                  + Z.shiftr (Z.land (br_hold bg)
                       (Z.shiftl 1 (c_bits h0 + c_op h0) - 1)) (c_bits h0))
        /\ nb = c_bits h0 + c_bits h
        /\ (0 <= br_hold b -> 0 <= br_bits b -> (forall j, 0 <= br_in b j) ->
            0 <= br_hold bg)).
Proof.
  intros sub t rb b h b2 nb H. unfold inf_decode in H.
  pose proof (inf_fetch_brok t rb b) as HF.
  destruct (inf_fetch t rb b) as [h0 b0|b0|] eqn:Ef; try discriminate.
  pose proof (inf_fetch_ok_shape _ _ _ _ _ Ef) as Hs0.
  destruct HF as (F1&F2&F3&F4&F5).
  destruct (sub h0) eqn:Esub.
  - pose proof (inf_fetch2_brok t h0 b0) as HG.
    destruct (inf_fetch2 t h0 b0) as [h1 b1|b1|] eqn:Ef2; try discriminate.
    pose proof (inf_fetch2_ok_shape _ _ _ _ _ Ef2) as Hs1.
    destruct HG as (G1&G2&G3&G4&G5).
    injection H as E1 E2 E3. subst h nb b2.
    right. exists b0, b1, h0.
    split; [exact Hs0|].
    split; [exact Esub|].
    split; [unfold br_bits_of in Hs1; exact Hs1|].
    split; [reflexivity|].
    intros Hh Hb Hin.
    apply G5; [apply F5; assumption | apply F4; assumption |].
    rewrite F2. exact Hin.
  - injection H as E1 E2 E3. subst h nb b2.
    left. exists b0.
    split; [unfold br_bits_of in Hs0; exact Hs0|].
    split; [reflexivity | exact Esub].
Qed.
