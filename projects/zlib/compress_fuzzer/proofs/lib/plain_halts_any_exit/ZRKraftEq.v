(** * ZRKraftEq — Kraft EQUALITY at [build_tree], in the decoder's list
      vocabulary.  GAP7 strict-decode supply, stage 1.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-21; strict-freeze
    round 3, chair q7-decode).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    The frozen bridge [build_accepts_of_kraft_STMT] (Gap7Strict.v, pin
    ) takes its kraft premises over the TRANSMITTED lengths list:
    [kraft_sum l M = 2^M] plus the range and length bounds.  g1's
    [BtItem6b.build_tree_out] already lands every ingredient at
    [build_tree]'s own call shape — [BlcOf] (the histogram-list bridge),
    the [zksum] EQUALITY over [ts_blcount], the dead-symbol zeros and the
    length range — but stops at [ValidLengths] (the INEQUALITY) on the
    list side.  This file adds the one missing composition: the same
    equality carried to [kraft_sum] over [SendGo.tree_lens], via
    [Kraft15.kraft_sum_hist] (list = its own histogram sum) and
    [BtItem6b.kraft_nat_z] (nat histogram sum = [zksum], one cast).

    The premise block is [build_tree_out]'s VERBATIM, so every call site
    that can discharge the landed theorem discharges this one with the
    same arguments. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec HuffGenCodes SendGo Kraft15
  BtWin BtCensus4 BtPass2 BtItem6 KraftAdjust BuildTree BtItem6b.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem build_tree_kraft_eq :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf,
  3 <= sd_elems k <= L_CODES ->
  1 <= sd_max_length k <= 15 ->
  4 * (hlen1 - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1;
             b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                                  (hlen1 / 2);
             b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
             b_node := sd_elems k |}
    = Some stf ->
  ts_maxcode (build_tree k s) k = maxc1
  /\ (kraft_sum (SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1)
        (Z.to_nat (sd_max_length k))
      = 2 ^ Z.to_nat (sd_max_length k))%nat
  /\ (forall len,
        In len (SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1) ->
        (len <= Z.to_nat (sd_max_length k))%nat)
  /\ length (SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1)
     = Z.to_nat (maxc1 + 1).
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         Hel HM Hcap Hblout Einit Eforce Eloop.
  destruct (build_tree_out k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1
              maxc1 ol1 sl1 stf Hel HM Hcap Hblout Einit Eforce Eloop)
    as (Emc & HVL & HBlc & Hzk & _ & _ & _).
  set (L := SendGo.tree_lens (ts_trees (build_tree k s) k) maxc1) in *.
  destruct HVL as (Hub & _).
  split; [exact Emc|].
  split; [|split].
  - (* the equality, by one Z round trip *)
    apply Nat2Z.inj.
    rewrite (kraft_sum_hist L (Z.to_nat (sd_max_length k)) Hub).
    rewrite (kraft_nat_z L (ts_blcount (build_tree k s)) (sd_max_length k)
               ltac:(lia)
               ltac:(intros b Hb; apply HBlc; unfold MAX_BITS; lia)).
    rewrite Hzk.
    rewrite Nat2Z.inj_pow.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - exact Hub.
  - unfold L, SendGo.tree_lens.
    rewrite length_map, length_seq.
    reflexivity.
Qed.

Print Assumptions build_tree_kraft_eq.
