(** * ZHOAsm4 — the two arithmetic closers (L4 delta grind, leg delta).

    OWNER: huffman-opt (fork).

    States the two lemmas of ZHOMain VERBATIM and
    proves them from ZHOAsm3's certificate; the only work here is the
    per-level literal arithmetic at 12288 (generic) and 2048
    (elems <= 30 — the deep regimes die on the count budget there).

    TRUST BOUNDARY: pure Gallina over the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin BtCensus2 BtCensus3 BtCensus4
  KraftAdjust BtAdjust.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOFib ZHOAsm3.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma zha_delta :
  forall (elems maxc1 M : Z) (tE tL t2 t3 : Tree) (hp3 : zarr)
         (hmaxf ndf : Z) (blc1 blc2 : zarr) (ov ol1 ol2 : Z) (v K : Z),
  BtParked elems maxc1 tE tL hp3 hmaxf ndf ->
  0 < elems <= L_CODES -> maxc1 < elems -> 0 <= hmaxf ->
  M = 15 ->
  (forall n, 0 <= n < elems -> 0 <= t_freq tE n) ->
  wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
       0 (Z.to_nat elems) <= 16384 ->
  (* pass 1 exit invariant (its exports; the caller has Pass1Inv) *)
  (forall p, hmaxf + 1 <= p < HEAP_SIZE ->
     t_len t2 (hp3 p)
     = Z.min (t_len t2 (t_dad tL (hp3 p)) + 1) M) ->
  t_len t2 (ndf - 1) = 0 ->
  (forall p, hmaxf + 1 <= p < HEAP_SIZE -> 1 <= t_len t2 (hp3 p) <= M) ->
  (forall b, 0 <= b <= 15 ->
     blc1 b = wsum (fun p => ind ((hp3 p <=? maxc1)
                                  && (Z.eqb (t_len t2 (hp3 p)) b)))
                   (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) ->
  (* W1 (round-2 repair): entry freqs are non-increasing along the parked
     window at leaf positions (FIB-B transported to tE by bp_frq) *)
  (forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
     hp3 p <= maxc1 -> hp3 q <= maxc1 ->
     t_freq tE (hp3 q) <= t_freq tE (hp3 p)) ->
  (* W2 (round-2 repair): Fibonacci depth cap at entry freqs (FIB-A +
     FIB-C + the p1_len min-chain: len <= chain depth, fibZ monotone) *)
  (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
     fibZ (Z.to_nat (t_len t2 (hp3 p)) + 1) * t_freq tE (hp3 p)
     <= wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
          0 (Z.to_nat elems)) ->
  ov = 2 * v ->
  1 <= v ->
  0 <= K < 2 ^ M ->
  zksum M blc1 = 2 ^ M + v ->
  v <= blc1 M ->
  (forall b, b < 1 \/ M < b -> blc1 b = 0) ->
  (forall b, 0 <= blc1 b <= K - 2 * v) ->
  blc2 = gb_adjust (Z.to_nat ov + 1) M blc1 ov ->
  gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
           hp3 maxc1 t2 blc2 M (blc2 M) HEAP_SIZE ol1 = (t3, ol2) ->
  wsum (fun n => ind (live_b tE maxc1 n) * t_freq tE n * t_len t3 n)
       0 (Z.to_nat elems)
  <= wsum (fun n => ind (live_b tE maxc1 n) * t_freq tE n * t_len t2 n)
       0 (Z.to_nat elems) + 12288.
Proof.
  intros elems maxc1 M tE tL t2 t3 hp3 hmaxf ndf blc1 blc2 ov ol1 ol2 v K
    Hpk Hel Hmc Hmf0 HM Hfnn Hmass Hp1len Hp1root Hp1rng Hblc HW1 HW2
    Hov Hv1 HKrng Hzk HvK Hz1 Hbnd Eblc2 Ep2.
  subst M.
  destruct (zw_core elems maxc1 tE tL t2 t3 hp3 hmaxf ndf blc1 blc2
              ov ol1 ol2 v K Hpk Hel Hmc Hmf0 Hfnn Hmass Hp1len Hp1root
              Hp1rng Hblc HW1 HW2 Hov Hv1 HKrng Hzk HvK Hz1 Hbnd
              Eblc2 Ep2)
    as (SP & SC & TRv & mz & ltr
        & Hle & Htnn & HSCnn & Hratio & HsC & Hmnn & HvE & Hpkg).
  unfold L_CODES in Hel.
  destruct Hpkg as [[-> ->]|Htail]; [lia|].
  destruct Htail as (Hltr & Hm & HvE1 & Htrb & Htrs).
  unfold zw_CAPF in Htrb, Htrs.
  assert (Hc : ltr = 7 \/ ltr = 8 \/ ltr = 9 \/ ltr = 10 \/ ltr = 11
               \/ ltr = 12 \/ ltr = 13 \/ ltr = 14) by lia.
  destruct Hc as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
  - assert (E1 : (2:Z) ^ (15 - 7) = 256) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 7) = 128) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 7 + 1) = 780) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 7))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 8) = 128) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 8) = 64) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 8 + 1) = 481) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 8))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 9) = 64) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 9) = 32) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 9 + 1) = 297) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 9))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 10) = 32) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 10) = 16) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 10 + 1) = 184) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 10))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 11) = 16) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 11) = 8) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 11 + 1) = 113) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 11))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 12) = 8) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 12) = 4) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 12 + 1) = 70) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 12))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 13) = 4) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 13) = 2) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 13 + 1) = 43) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 13))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 14) = 2) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 14) = 1) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 14 + 1) = 26) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 14))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
Qed.

Lemma zha_delta_d :
  forall (elems maxc1 M : Z) (tE tL t2 t3 : Tree) (hp3 : zarr)
         (hmaxf ndf : Z) (blc1 blc2 : zarr) (ov ol1 ol2 : Z) (v K : Z),
  BtParked elems maxc1 tE tL hp3 hmaxf ndf ->
  0 < elems <= L_CODES ->
  elems <= 30 ->
  maxc1 < elems -> 0 <= hmaxf ->
  M = 15 ->
  (forall n, 0 <= n < elems -> 0 <= t_freq tE n) ->
  wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
       0 (Z.to_nat elems) <= 16384 ->
  (forall p, hmaxf + 1 <= p < HEAP_SIZE ->
     t_len t2 (hp3 p)
     = Z.min (t_len t2 (t_dad tL (hp3 p)) + 1) M) ->
  t_len t2 (ndf - 1) = 0 ->
  (forall p, hmaxf + 1 <= p < HEAP_SIZE -> 1 <= t_len t2 (hp3 p) <= M) ->
  (forall b, 0 <= b <= 15 ->
     blc1 b = wsum (fun p => ind ((hp3 p <=? maxc1)
                                  && (Z.eqb (t_len t2 (hp3 p)) b)))
                   (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) ->
  (* W1 (round-2 repair): entry freqs are non-increasing along the parked
     window at leaf positions (FIB-B transported to tE by bp_frq) *)
  (forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
     hp3 p <= maxc1 -> hp3 q <= maxc1 ->
     t_freq tE (hp3 q) <= t_freq tE (hp3 p)) ->
  (* W2 (round-2 repair): Fibonacci depth cap at entry freqs (FIB-A +
     FIB-C + the p1_len min-chain: len <= chain depth, fibZ monotone) *)
  (forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc1 ->
     fibZ (Z.to_nat (t_len t2 (hp3 p)) + 1) * t_freq tE (hp3 p)
     <= wsum (fun x => ind (live_b tE maxc1 x) * t_freq tE x)
          0 (Z.to_nat elems)) ->
  ov = 2 * v ->
  1 <= v ->
  0 <= K < 2 ^ M ->
  zksum M blc1 = 2 ^ M + v ->
  v <= blc1 M ->
  (forall b, b < 1 \/ M < b -> blc1 b = 0) ->
  (forall b, 0 <= blc1 b <= K - 2 * v) ->
  blc2 = gb_adjust (Z.to_nat ov + 1) M blc1 ov ->
  gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
           hp3 maxc1 t2 blc2 M (blc2 M) HEAP_SIZE ol1 = (t3, ol2) ->
  wsum (fun n => ind (live_b tE maxc1 n) * t_freq tE n * t_len t3 n)
       0 (Z.to_nat elems)
  <= wsum (fun n => ind (live_b tE maxc1 n) * t_freq tE n * t_len t2 n)
       0 (Z.to_nat elems) + 2048.
Proof.
  intros elems maxc1 M tE tL t2 t3 hp3 hmaxf ndf blc1 blc2 ov ol1 ol2 v K
    Hpk Hel He30 Hmc Hmf0 HM Hfnn Hmass Hp1len Hp1root Hp1rng Hblc HW1 HW2
    Hov Hv1 HKrng Hzk HvK Hz1 Hbnd Eblc2 Ep2.
  subst M.
  destruct (zw_core elems maxc1 tE tL t2 t3 hp3 hmaxf ndf blc1 blc2
              ov ol1 ol2 v K Hpk Hel Hmc Hmf0 Hfnn Hmass Hp1len Hp1root
              Hp1rng Hblc HW1 HW2 Hov Hv1 HKrng Hzk HvK Hz1 Hbnd
              Eblc2 Ep2)
    as (SP & SC & TRv & mz & ltr
        & Hle & Htnn & HSCnn & Hratio & HsC & Hmnn & HvE & Hpkg).
  unfold L_CODES in Hel.
  destruct Hpkg as [[-> ->]|Htail]; [lia|].
  destruct Htail as (Hltr & Hm & HvE1 & Htrb & Htrs).
  unfold zw_CAPF in Htrb, Htrs.
  assert (Hc : ltr = 7 \/ ltr = 8 \/ ltr = 9 \/ ltr = 10 \/ ltr = 11
               \/ ltr = 12 \/ ltr = 13 \/ ltr = 14) by lia.
  destruct Hc as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]].
  - assert (E1 : (2:Z) ^ (15 - 7) = 256) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 7) = 128) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 7 + 1) = 780) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 7))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 8) = 128) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 8) = 64) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 8 + 1) = 481) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 8))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 9) = 64) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 9) = 32) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 9 + 1) = 297) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 9))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 10) = 32) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 10) = 16) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 10 + 1) = 184) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 10))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 11) = 16) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 11) = 8) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 11 + 1) = 113) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 11))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 12) = 8) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 12) = 4) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 12 + 1) = 70) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 12))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 13) = 4) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 13) = 2) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 13 + 1) = 43) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 13))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
  - assert (E1 : (2:Z) ^ (15 - 14) = 2) by reflexivity.
    assert (E2 : (2:Z) ^ (14 - 14) = 1) by reflexivity.
    assert (E3 : 16384 / fibZ (Z.to_nat 14 + 1) = 26) by reflexivity.
    destruct (Z.le_gt_cases mz (2 ^ (14 - 14))) as [Hsm|Hbg];
      [pose proof (Htrs Hsm)|]; lia.
Qed.
