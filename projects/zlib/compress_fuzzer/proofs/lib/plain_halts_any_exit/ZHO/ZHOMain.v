(** * ZHOMain — build_tree cost-optimality, assembled.

    OWNER: huffman-opt.  Proves ZHOStmt.build_tree_cost_opt from the four
    bed legs + the landed corpus:

      pass1 cost --(ZHOFubini telescope)--> created-freq sum
                 --(ZHOSim SIM-A + Théry build_correct)--> weight_tree-min
                 --(ZHOKraftTree cover of C)--> zho_cost C          [K = 0]
      final cost --(ov = 0: final lens = pass1 lens)--> done
                 --(ov > 0: zho_adjust_delta, THE L4 HOLE)-->
                              pass1 cost + ZHO_K.

    Plumbing: the [build_tree] unfold against the pipeline premises (the
    build_tree_parked / BtAccount2 pattern), [gen_bitlen]'s branch split,
    Pass1Inv via pass1_entry/pass1_walk (the BtItem6 pattern), gen_codes /
    setter frames (lens survive), and the wsum conversions between the
    all-symbols range and the live-masked range (dead symbols have freq 0
    via io_gapz).

    THE ONE ADMITTED: [zho_adjust_delta] (L4) — the adjust+pass2
    redistribution delta is at most ZHO_K.  Falsifier-measured ceiling
    ~930 bits (saturated vertex hill, wide-deep family); the proof route
    (ex-15 shield + Fibonacci weight-depth + window monotonicity) is the
    lane's remaining open mathematics.

    TRUST BOUNDARY: pure Gallina over the vendored Huffman library
    (LGPL-2.1-or-later) + the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtStep BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtCensus5
  BtPass1 BtSized BtForce2 KraftAdjust BtLevels.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOHeap ZHOSim ZHOKraftTree ZHOFubini ZHOStmt
  ZHOFib ZHOAsm4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Import BTree WeightTree Cover CoverMin Build.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The L4 hole: the adjust+pass2 delta is bounded by ZHO_K.

    Stated at [gen_bitlen]'s overflow-branch call shape, over the parked
    window: [t2]/[blc1]/[ov] are pass 1's outputs (lens already capped at
    15), [blc2] the adjusted histogram, [(t3, ol2)] pass 2's output.  The
    conclusion compares the live-masked weighted length sums of [t3] and
    [t2] at the ENTRY freqs. *)
Lemma zho_adjust_delta :
  (* REPAIRED 2026-08-23 (owner ruling): the original [0 < ov] premise was
     the whole constraint on [ov], and the statement is FALSE that way —
     an absurd [ov] u16-scrambles the adjust (machine probe:
     ZHODeltaDefect.v; report: DEFECT-zho-adjust-delta.md).  The repair
     carries BtAdjust's own hypothesis block (verbatim shapes), which the
     caller discharges from BtLevels.pass1_kraft at the call site, plus
     the R39-narrowed entry-freq nonnegativity. *)
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
  exact zha_delta.
Qed.

(** the D-scale instance: at [elems <= 30] the cone arithmetic prices the
    delta at 2048 (numeric max there is 221; countersigned constants
    K_L = 12288 / K_D = 2048). *)
Lemma zho_adjust_delta_d :
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
  exact zha_delta_d.
Qed.

(** ** Assembly helpers *)

Lemma zhom_fibZ_step : forall n, fibZ n <= fibZ (S n).
Proof.
  intro n. destruct n as [|m]; [cbn; lia|].
  rewrite fibZ_SS. pose proof (fibZ_nonneg m). lia.
Qed.

Lemma zhom_fibZ_mono : forall a b, (a <= b)%nat -> fibZ a <= fibZ b.
Proof.
  intros a b Hab. induction Hab as [|b Hab IH]; [lia|].
  pose proof (zhom_fibZ_step b). lia.
Qed.

Lemma zhom_u16_nn : forall v, 0 <= u16 v.
Proof.
  intro v. unfold u16.
  pose proof (Z.mod_pos_bound v 65536 ltac:(lia)). lia.
Qed.

(** freq nonnegativity everywhere survives one trip and the whole loop *)
Lemma zhom_step_freq_nn : forall st st',
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  (forall x, 0 <= t_freq (b_tree st) x) ->
  forall x, 0 <= t_freq (b_tree st') x.
Proof.
  intros st st' Hst Hnn x.
  apply bt_step_succ in Hst. subst st'.
  unfold zho_succ. cbv zeta. cbn [b_tree].
  rewrite !t_freq_setdad.
  unfold t_freq, t_setfreq. cbn [tr_fc].
  destruct (Z.eq_dec x (b_node st)) as [->|Hne].
  - rewrite zset_same. apply zhom_u16_nn.
  - rewrite zset_other by exact Hne. apply Hnn.
Qed.

Lemma zhom_loop_freq_nn : forall fuel st,
  (forall x, 0 <= t_freq (b_tree st) x) ->
  match bt_loop fuel st with
  | Some stf => forall x, 0 <= t_freq (b_tree stf) x
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st Hnn; cbn [bt_loop]; [exact I|].
  destruct (bt_step st) as [st'|st'] eqn:Est.
  - apply IH. apply (zhom_step_freq_nn st st'); [left; exact Est | exact Hnn].
  - apply (zhom_step_freq_nn st st'); [right; exact Est | exact Hnn].
Qed.

(** gen_codes writes only codes (tr_fc); lengths survive *)
Lemma zhom_gc_assign_len : forall fuel n maxc t nc x,
  t_len (gc_assign fuel n maxc t nc) x = t_len t x.
Proof.
  induction fuel as [|f IH]; intros n maxc t nc x; cbn [gc_assign];
    [reflexivity|].
  destruct (Z.ltb maxc n); [reflexivity|].
  destruct (Z.eqb (t_len t n) 0); [apply IH|].
  rewrite IH. reflexivity.
Qed.

Lemma zhom_gen_codes_len : forall t maxc blc x,
  t_len (gen_codes t maxc blc) x = t_len t x.
Proof.
  intros t maxc blc x. unfold gen_codes. apply zhom_gc_assign_len.
Qed.

(** fold_right sums: base extraction, Z.of_nat conversion *)
Lemma zhom_fold_base : forall (g : Z -> Z) b l,
  fold_right (fun s' acc => acc + g s') b l
  = fold_right (fun s' acc => acc + g s') 0 l + b.
Proof.
  intros g b l. induction l as [|v l IH]; cbn [fold_right]; [lia|].
  rewrite IH. lia.
Qed.

Lemma zhom_fold_of_nat : forall (h : Z -> nat) (g : Z -> Z) (l : list Z),
  (forall s', In s' l -> Z.of_nat (h s') = g s') ->
  Z.of_nat (fold_right (fun s' acc => (acc + h s')%nat) 0%nat l)
  = fold_right (fun s' acc => acc + g s') 0 l.
Proof.
  intros h g l Hin. induction l as [|v l IH]; cbn [fold_right]; [reflexivity|].
  rewrite Nat2Z.inj_add.
  rewrite IH by (intros; apply Hin; right; assumption).
  rewrite (Hin v) by (left; reflexivity). lia.
Qed.

(** masked window sums as folds over the filtered symbol list *)
Lemma zhom_wsum_filter : forall (sel : Z -> bool) (g : Z -> Z) (e : nat),
  wsum (fun n => ind (sel n) * g n) 0 e
  = fold_right (fun s' acc => acc + g s') 0
      (filter sel (map Z.of_nat (seq 0 e))).
Proof.
  intros sel g. induction e as [|e IH]; [reflexivity|].
  rewrite wsum_split_last, IH.
  rewrite seq_S, map_app, filter_app, fold_right_app.
  cbn [Nat.add map filter].
  replace (0 + Z.of_nat e) with (Z.of_nat e) by lia.
  destruct (sel (Z.of_nat e)) eqn:Es; cbn [ind fold_right].
  - rewrite (zhom_fold_base g (0 + g (Z.of_nat e))). lia.
  - lia.
Qed.

(** ** The assembly *)

Theorem build_tree_cost_opt_main :
  forall k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf
         (C : Z -> Z),
  3 <= sd_elems k <= L_CODES ->
  sd_max_length k = 15 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (forall n, 0 <= n < sd_elems k -> 0 <= t_freq (ts_trees s k) n) ->
  wsum (fun n => t_freq (ts_trees s k) n) 0 (Z.to_nat (sd_elems k))
    <= 16384 ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  2 <= hlen0 ->
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
  (forall n, 0 <= n < sd_elems k -> zho_live s k n = true ->
     1 <= C n <= 15) ->
  zho_kraft s k C <= 2 ^ 15 ->
  zho_cost s k (fun n => t_len (ts_trees (build_tree k s) k) n)
    <= zho_cost s k C + ZHO_K k.
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 stf C
         Hel EM Hblout Hfnn Htot E0 Hh0 E2 Eloop HCrng HCkraft.
  (* --- 1. bt_force2 is the identity at hlen0 >= 2 --- *)
  pose proof E2 as E2'.
  cbn [bt_force2] in E2'.
  rewrite (proj2 (Z.leb_le 2 hlen0) Hh0) in E2'.
  injection E2' as Et01 Ehp01 Edep01 Ehl01 Emc01 Eol1 Esl1.
  subst t1 hp1 dep1 hlen1 maxc1 ol1 sl1.
  (* --- 2. the landed parked package --- *)
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t0 hp0 dep0 hlen0 maxc0 (ts_optlen s) (ts_statlen s)
              (bt_heapify (Z.to_nat HEAP_SIZE) t0 dep0 hp0 hlen0 (hlen0 / 2))
              stf Hel E0 E2 eq_refl Eloop)
    as (Hpk & Hout & Hh1 & Hnd & Hfr0).
  pose proof (io_maxc _ _ _ _ _ Hout) as Hmc.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hndf1.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hhmx.
  pose proof (bp_root _ _ _ _ _ _ _ Hpk) as Hroot.
  (* --- 3. freq transports and the mass bound --- *)
  assert (Efr : forall i, t_freq t0 i = t_freq (ts_trees s k) i)
    by exact Hfr0.
  assert (Hfnn0 : forall n, 0 <= n < sd_elems k -> 0 <= t_freq t0 n)
    by (intros n Hn; rewrite Efr; apply Hfnn; exact Hn).
  assert (Hmass : wsum (fun x => ind (live_b t0 maxc0 x) * t_freq t0 x)
                       0 (Z.to_nat (sd_elems k)) <= 16384).
  { eapply Z.le_trans; [|exact Htot].
    apply wsum_le. intros i Hi.
    rewrite Z2Nat.id in Hi by lia.
    rewrite Efr.
    pose proof (ind_0_1 (live_b t0 maxc0 i)).
    pose proof (Hfnn i ltac:(lia)). nia. }
  (* --- 4. the simulation exports --- *)
  destruct (zho_sim_main (sd_elems k) maxc0 t0 dep0 hp0 hlen0 stf
              ltac:(lia) ltac:(lia) ltac:(lia) Hfnn0 ltac:(lia) Hout Eloop)
    as (SIMA & SIMB & SIMC & SIMD & SIME).
  (* --- 5. freq nonneg at the loop exit, on the touched range [0, ndf) ---
     (the R39 narrowing removed the everywhere form; symbols transport by
     bp_frq, created indices by SIM-E) *)
  assert (Hfnn2 : forall x, 0 <= x < b_node stf -> 0 <= t_freq (b_tree stf) x).
  { intros x Hx.
    destruct (Z.lt_ge_cases x (sd_elems k)) as [Hxe|Hxe].
    - rewrite (bp_frq _ _ _ _ _ _ _ Hpk x Hxe). apply Hfnn0. lia.
    - apply SIME. lia. }
  (* --- 6. names for the parked window --- *)
  (* --- 5b. the FIB package (posed before the sets so they fold it) --- *)
  pose proof (zho_fib_main (sd_elems k) maxc0 t0 dep0 hp0 hlen0 stf
                ltac:(lia) (proj2 Hmc) Hh1 Hfnn0 ltac:(lia) Hout Eloop)
    as (FIBA & FIBB & FIBC).
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmaxf := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  assert (Hmf0 : 0 <= hmaxf).
  { unfold hmaxf. unfold HEAP_SIZE, L_CODES in *. lia. }
  (* --- 7. unfold build_tree --- *)
  assert (Efin : ts_trees (build_tree k s) k
                 = gen_codes
                     (ts_trees (gen_bitlen k
                        (set_statlen (ts_statlen s) (set_optlen (ts_optlen s)
                          (set_heapmax hmaxf (set_heaplen (b_hlen stf)
                            (set_depth (b_dep stf)
                              (set_heap hp3
                                (set_max k maxc0
                                  (set_tree k (b_tree stf) s))))))))) k)
                     maxc0
                     (ts_blcount (gen_bitlen k
                        (set_statlen (ts_statlen s) (set_optlen (ts_optlen s)
                          (set_heapmax hmaxf (set_heaplen (b_hlen stf)
                            (set_depth (b_dep stf)
                              (set_heap hp3
                                (set_max k maxc0
                                  (set_tree k (b_tree stf) s))))))))))).
  { unfold build_tree.
    rewrite E0. cbv iota beta.
    rewrite E2. cbv iota beta zeta.
    rewrite Eloop. cbv iota beta zeta.
    unfold hp3, hmaxf.
    cbn [ts_trees set_tree set_trees set_statlen set_optlen set_blcount
         set_heapmax set_heaplen set_depth set_heap set_max set_maxcode].
    rewrite Z.eqb_refl. reflexivity. }
  set (s1 := set_statlen (ts_statlen s) (set_optlen (ts_optlen s)
               (set_heapmax hmaxf (set_heaplen (b_hlen stf)
                 (set_depth (b_dep stf)
                   (set_heap hp3
                     (set_max k maxc0
                       (set_tree k (b_tree stf) s)))))))) in *.
  (* --- 8. s1 projections + gen_bitlen unfold --- *)
  assert (Ehp : ts_heap s1 = hp3) by reflexivity.
  assert (Ehm : ts_heapmax s1 = hmaxf) by reflexivity.
  assert (Etf : ts_trees s1 k = b_tree stf)
    by (unfold s1; cbn [ts_trees set_tree set_trees set_statlen set_optlen
                        set_heapmax set_heaplen set_depth set_heap set_max
                        set_maxcode];
        rewrite Z.eqb_refl; reflexivity).
  assert (Emc : ts_maxcode s1 k = maxc0)
    by (unfold s1; cbn [ts_maxcode set_tree set_trees set_statlen set_optlen
                        set_heapmax set_heaplen set_depth set_heap set_max
                        set_maxcode];
        rewrite Z.eqb_refl; reflexivity).
  set (blc0 := arr_zero (Z.to_nat MAX_BITS + 1) 0 (ts_blcount s1)) in *.
  assert (Hblc0 : forall b, blc0 b = 0).
  { intro b. unfold blc0.
    replace (ts_blcount s1) with (ts_blcount s) by reflexivity.
    destruct (Z_le_gt_dec 0 b) as [Hb0|Hb0].
    - destruct (Z_le_gt_dec b 15) as [Hb15|Hb15].
      + apply arr_zero_in.
        change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16. lia.
      + rewrite arr_zero_out
          by (change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16; lia).
        apply Hblout. lia.
    - rewrite arr_zero_out
        by (change (Z.of_nat (Z.to_nat MAX_BITS + 1)) with 16; lia).
      apply Hblout. lia. }
  pose proof (pass1_entry (sd_elems k) maxc0 15 t0 (b_tree stf) hp3 hmaxf ndf
                Hpk blc0 Hblc0) as Hinv0.
  pose proof (pass1_walk (sd_elems k) maxc0 15 t0 (b_tree stf) hp3 hmaxf ndf
                Hpk ltac:(lia) Hmf0
                k (sd_extra_base k) (sd_extra k) (sd_stree k)
                (Z.to_nat HEAP_SIZE + 1) (hmaxf + 1)
                (t_setlen (b_tree stf) (ndf - 1) 0) blc0
                (ts_optlen s1) (ts_statlen s1) 0
                ltac:(unfold HEAP_SIZE, L_CODES in *; lia)
                ltac:(rewrite Nat2Z.inj_add, Z2Nat.id
                        by (unfold HEAP_SIZE; lia);
                      change (Z.of_nat 1) with 1; lia)
                Hinv0) as Hw1.
  destruct (gb_pass1 (Z.to_nat HEAP_SIZE + 1) k hp3 maxc0 15
              (sd_extra_base k) (sd_extra k) (sd_stree k) (hmaxf + 1)
              (t_setlen (b_tree stf) (ndf - 1) 0) blc0
              (ts_optlen s1) (ts_statlen s1) 0)
    as [[[[t2 blc1] olp] slp] ov] eqn:E1.
  pose proof Hw1 as Hfin. clear Hw1.
  (* --- 8b. window value range (hoisted; also used by CORE) --- *)
  assert (Hwin_rng : forall p, hmaxf <= p < HEAP_SIZE ->
                     0 <= hp3 p < ndf).
  { intros p Hp.
    pose proof (pcount_member hp3 hmaxf p Hp) as Hm.
    pose proof (bp_cnt _ _ _ _ _ _ _ Hpk (hp3 p)) as Hc.
    destruct (live_b t0 maxc0 (hp3 p)) eqn:El.
    - unfold live_b in El.
      apply andb_prop in El as [El1 _].
      apply andb_prop in El1 as [El1 El2].
      apply Z.leb_le in El1. apply Z.leb_le in El2. lia.
    - cbn [ind] in Hc.
      destruct ((sd_elems k <=? hp3 p) && (hp3 p <? ndf)) eqn:Ec;
        [|cbn [ind] in Hc; lia].
      apply andb_prop in Ec as [Ec1 Ec2].
      apply Z.leb_le in Ec1. apply Z.ltb_lt in Ec2. lia. }
  (* --- 8c. dad-chains to the root: existence, parked intermediates,
       and the len bound (bp_ord walks toward hmaxf; root sits there) --- *)
  assert (HCH : forall n : nat, forall p,
            (Z.to_nat (p - hmaxf) <= n)%nat ->
            hmaxf + 1 <= p < HEAP_SIZE ->
            exists d : nat,
              dchainN (b_tree stf) (hp3 p) (ndf - 1) d
              /\ (forall j, (1 <= j < d)%nat ->
                    1 <= pcount (b_heap stf) (b_hmax stf)
                           (dpow (b_tree stf) j (hp3 p)))
              /\ t_len t2 (hp3 p) <= Z.of_nat d).
  { intro n. induction n as [|n IH]; intros p Hn Hp.
    - lia.
    - destruct (bp_ord _ _ _ _ _ _ _ Hpk p Hp) as (Hdr & p' & Hp' & Ep').
      destruct (Z.eqb_spec p' hmaxf) as [->|Hne].
      + exists 1%nat. split; [|split].
        * cbn [dchainN]. rewrite <- Ep', Hroot. reflexivity.
        * intros j Hj. lia.
        * rewrite (p1_len _ _ _ _ _ _ _ _ _ _ Hfin p Hp).
          rewrite <- Ep', Hroot.
          rewrite (p1_root _ _ _ _ _ _ _ _ _ _ Hfin).
          cbn [Z.of_nat]. lia.
      + assert (Hp'w : hmaxf + 1 <= p' < HEAP_SIZE) by lia.
        destruct (IH p' ltac:(lia) Hp'w) as (d & Hch & Hint & Hlen).
        exists (S d). split; [|split].
        * cbn [dchainN]. rewrite <- Ep'. exact Hch.
        * intros j Hj. destruct j as [|j']; [lia|].
          cbn [dpow]. rewrite <- Ep'.
          destruct j' as [|j''].
          -- cbn [dpow].
             replace (hp3 p') with (b_heap stf p')
               by (unfold hp3; rewrite zset_other by lia; reflexivity).
             apply pcount_member. unfold hmaxf in Hp'w. lia.
          -- apply (Hint (S j'')). lia.
        * rewrite (p1_len _ _ _ _ _ _ _ _ _ _ Hfin p Hp).
          rewrite <- Ep'.
          apply Z.le_trans with (m := t_len t2 (hp3 p') + 1);
            [apply Z.le_min_l|].
          rewrite Nat2Z.inj_succ. lia. }
  (* --- 8d. the two repaired-premise discharges (W1, W2) --- *)
  assert (HW1 : forall p q, hmaxf + 1 <= p -> p <= q -> q < HEAP_SIZE ->
            hp3 p <= maxc0 -> hp3 q <= maxc0 ->
            t_freq t0 (hp3 q) <= t_freq t0 (hp3 p)).
  { intros p q Hp Hpq Hq Hlp Hlq.
    rewrite <- (bp_frq _ _ _ _ _ _ _ Hpk (hp3 q) ltac:(lia)).
    rewrite <- (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p) ltac:(lia)).
    apply FIBB; lia. }
  assert (HW2 : forall p, hmaxf + 1 <= p < HEAP_SIZE -> hp3 p <= maxc0 ->
            fibZ (Z.to_nat (t_len t2 (hp3 p)) + 1) * t_freq t0 (hp3 p)
            <= wsum (fun x => ind (live_b t0 maxc0 x) * t_freq t0 x)
                 0 (Z.to_nat (sd_elems k))).
  { intros p Hp Hlf.
    destruct (HCH (Z.to_nat (p - hmaxf)) p ltac:(lia) Hp)
      as (d & Hch & Hint & Hlen).
    assert (Ehb : hp3 p = b_heap stf p)
      by (unfold hp3; rewrite zset_other by lia; reflexivity).
    rewrite Ehb in Hch, Hint, Hlen.
    assert (HA : fibZ (d + 1) * t_freq (b_tree stf) (b_heap stf p)
                 <= t_freq (b_tree stf) (ndf - 1)).
    { apply (FIBA p d).
      - unfold hmaxf in Hp. lia.
      - exact Hch.
      - exact Hint. }
    rewrite <- FIBC.
    rewrite <- (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p) ltac:(lia)).
    rewrite Ehb.
    eapply Z.le_trans; [|exact HA].
    apply Z.mul_le_mono_nonneg_r.
    - rewrite <- Ehb.
      rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p) ltac:(lia)).
      apply Hfnn0.
      pose proof (Hwin_rng p ltac:(lia)). lia.
    - apply zhom_fibZ_mono. lia. }
  assert (EG : gen_bitlen k s1
               = if Z.eqb ov 0
                 then set_statlen slp (set_optlen olp
                        (set_blcount blc1 (set_tree k t2 s1)))
                 else
                   match gb_pass2
                           (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                           hp3 maxc0 t2
                           (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov) 15
                           (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov 15)
                           HEAP_SIZE olp with
                   | (t3, ol2) =>
                       set_statlen slp (set_optlen ol2
                         (set_blcount (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov)
                            (set_tree k t3 s1)))
                   end).
  { unfold gen_bitlen. cbv zeta.
    rewrite EM, Ehp, Ehm, Etf, Emc, Hroot.
    fold blc0.
    rewrite E1. reflexivity. }
  (* --- 9. the masked-cost view of zho_cost --- *)
  assert (L2M : forall tl : Z -> Z,
            zho_cost s k tl
            = wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n * tl n)
                   0 (Z.to_nat (sd_elems k))).
  { intro tl. unfold zho_cost. apply wsum_ext. intros n Hn.
    rewrite Z2Nat.id in Hn by lia.
    rewrite <- (Efr n).
    destruct (live_b t0 maxc0 n) eqn:El; cbn [ind]; [ring|].
    assert (Efz : t_freq t0 n = 0).
    { unfold live_b in El.
      destruct (Z.leb 0 n) eqn:Ea; [|apply Z.leb_gt in Ea; lia].
      destruct (Z.leb n maxc0) eqn:Eb.
      - cbn [andb] in El.
        destruct (Z.eqb (t_freq t0 n) 0) eqn:Ec.
        + apply Z.eqb_eq in Ec. exact Ec.
        + cbn [negb] in El. discriminate.
      - apply Z.leb_gt in Eb.
        apply (io_gapz _ _ _ _ _ Hout). lia. }
    rewrite Efz. ring. }
  (* live_b and zho_live agree on the range *)
  assert (Hlive_eq : forall n, 0 <= n < sd_elems k ->
            live_b t0 maxc0 n = zho_live s k n).
  { intros n Hn. unfold zho_live. rewrite <- (Efr n).
    unfold live_b.
    destruct (Z.leb 0 n) eqn:Ea; [|apply Z.leb_gt in Ea; lia].
    cbn [andb].
    destruct (Z.leb n maxc0) eqn:Eb; cbn [andb].
    - destruct (Z.eqb (t_freq t0 n) 0) eqn:Ec; cbn [negb].
      + apply Z.eqb_eq in Ec. rewrite Ec. reflexivity.
      + apply Z.eqb_neq in Ec.
        apply Z.leb_le in Ea. apply Z.leb_le in Eb.
        pose proof (Hfnn0 n ltac:(lia)).
        symmetry. apply Z.ltb_lt. lia.
    - apply Z.leb_gt in Eb.
      assert (Efz : t_freq t0 n = 0)
        by (apply (io_gapz _ _ _ _ _ Hout); lia).
      rewrite Efz. reflexivity. }
  (* --- 10. the syms list and Bridge B --- *)
  set (syms := filter (live_b t0 maxc0)
                 (map Z.of_nat (seq 0 (Z.to_nat (sd_elems k))))) in *.
  assert (Hsyms_in : forall s', In s' syms ->
            0 <= s' < sd_elems k /\ live_b t0 maxc0 s' = true).
  { intros s' Hin. unfold syms in Hin.
    apply filter_In in Hin as [Hin Hlv].
    apply in_map_iff in Hin as (m & Em & Hm).
    apply in_seq in Hm. split; [lia | exact Hlv]. }
  assert (Hsyms_ne : syms <> []).
  { intro Hnil.
    pose proof (Permutation_length SIMD) as Hlenp.
    rewrite Hnil in Hlenp.
    unfold zho_live_idx, zho_slots, zho_st0 in Hlenp.
    cbn [b_hlen length] in Hlenp.
    rewrite length_map, length_map, length_seq in Hlenp.
    apply (f_equal Z.of_nat) in Hlenp.
    rewrite Z2Nat.id in Hlenp by lia.
    cbn [Z.of_nat] in Hlenp. lia. }
  assert (HsymsC : forall s', In s' syms -> 1 <= C s' <= 15).
  { intros s' Hin. destruct (Hsyms_in s' Hin) as [Hrng Hlv].
    apply HCrng; [exact Hrng|]. rewrite <- Hlive_eq by exact Hrng.
    exact Hlv. }
  assert (HsymsK : fold_right (fun s' acc => acc + 2 ^ (15 - C s')) 0 syms
                   <= 2 ^ 15).
  { eapply Z.le_trans; [|exact HCkraft].
    unfold syms.
    rewrite <- (zhom_wsum_filter (live_b t0 maxc0)
                 (fun n => 2 ^ (15 - C n)) (Z.to_nat (sd_elems k))).
    unfold zho_kraft.
    apply Z.eq_le_incl. apply wsum_ext. intros n Hn.
    rewrite Z2Nat.id in Hn by lia.
    rewrite (Hlive_eq n) by lia.
    unfold ind. reflexivity. }
  destruct (kraft_cover_bound (zho_f t0) syms C Hsyms_ne HsymsC HsymsK)
    as (TC & HTCcov & HTCw).
  assert (HTCcov' : cover (zho_forest0 (sd_elems k) t0 dep0 hp0 hlen0) TC).
  { eapply cover_permutation; [exact HTCcov|].
    apply Permutation_sym.
    unfold zho_forest0. apply Permutation_map. exact SIMD. }
  (* --- 11. the telescope inputs --- *)
  assert (Hchld' : forall i, sd_elems k <= i < ndf ->
            t_freq (b_tree stf) i
            = wsum (fun p => ind (Z.eqb (t_dad (b_tree stf) (hp3 p)) i)
                             * t_freq (b_tree stf) (hp3 p))
                   (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))).
  { intros i Hi.
    replace (hmaxf + 1) with (b_hmax stf) by (unfold hmaxf; lia).
    rewrite (SIMB i Hi).
    apply wsum_ext. intros p Hp.
    assert (Hpr : hmaxf < p) by (unfold hmaxf; lia).
    unfold hp3. rewrite zset_other by (unfold hmaxf in Hpr; lia).
    reflexivity. }
  (* --- 12. CORE: masked pass1 cost <= zho_cost C --- *)
  assert (CORE : wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                                * t_len t2 n) 0 (Z.to_nat (sd_elems k))
                 <= zho_cost s k C).
  { (* ZHOFubini's Hfrq_nn quantifies ALL indices, but the narrowed premise
       only reaches [0, ndf).  Apply the telescope at freq-CLAMPED twins:
       tr_dl (dads/lens) untouched, tr_fc zeroed outside [0, ndf), so every
       hypothesis transports on the window and the conclusion converts
       back pointwise. *)
    set (clampf := fun t : Tree => mkTree
          (fun x => if (0 <=? x) && (x <? ndf) then t_freq t x else 0)
          (tr_dl t)).
    assert (Efc : forall t x, 0 <= x < ndf ->
                  t_freq (clampf t) x = t_freq t x).
    { intros t x Hx. unfold clampf, t_freq. cbn [tr_fc].
      replace ((0 <=? x) && (x <? ndf)) with true
        by (symmetry; apply andb_true_iff;
            split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]).
      reflexivity. }
    assert (Efc0 : forall t x, ~ (0 <= x < ndf) ->
                   t_freq (clampf t) x = 0).
    { intros t x Hx. unfold clampf, t_freq. cbn [tr_fc].
      destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x ndf);
        cbn [andb]; try reflexivity; exfalso; apply Hx; lia. }
    assert (Hlb_eq : forall x, live_b (clampf t0) maxc0 x
                               = live_b t0 maxc0 x).
    { intro x. unfold live_b.
      destruct (Z.leb_spec 0 x); destruct (Z.leb_spec x maxc0);
        cbn [andb]; try reflexivity.
      rewrite (Efc t0 x) by lia. reflexivity. }
    assert (Hfnnc : forall x, 0 <= t_freq (clampf (b_tree stf)) x).
    { intro x.
      destruct (Z_lt_ge_dec x 0) as [Hx|Hx];
        [rewrite (Efc0 (b_tree stf) x) by lia; lia|].
      destruct (Z_lt_ge_dec x ndf) as [Hx2|Hx2].
      - rewrite (Efc (b_tree stf) x) by lia. apply Hfnn2. lia.
      - rewrite (Efc0 (b_tree stf) x) by lia. lia. }
    assert (Hpkc : BtParked (sd_elems k) maxc0 (clampf t0)
                     (clampf (b_tree stf)) hp3 hmaxf ndf).
    { destruct Hpk as [m1 m2 m3 m4 m5 m6 m7 m8 m9].
      constructor.
      - exact m1.
      - exact m2.
      - exact m3.
      - intro x. rewrite Hlb_eq. exact (m4 x).
      - exact m5.
      - exact m6.
      - exact m7.
      - intros x Hx.
        destruct (Z_lt_ge_dec x 0) as [Hneg|Hpos].
        + rewrite (Efc0 (b_tree stf) x) by lia.
          rewrite (Efc0 t0 x) by lia. reflexivity.
        + rewrite (Efc (b_tree stf) x) by lia.
          rewrite (Efc t0 x) by lia. exact (m8 x Hx).
      - exact m9. }
    assert (Hchldc : forall i, sd_elems k <= i < ndf ->
              t_freq (clampf (b_tree stf)) i
              = wsum (fun p => ind (Z.eqb (t_dad (clampf (b_tree stf))
                                            (hp3 p)) i)
                               * t_freq (clampf (b_tree stf)) (hp3 p))
                     (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))).
    { intros i Hi.
      rewrite (Efc (b_tree stf) i) by lia.
      rewrite (Hchld' i Hi).
      apply wsum_ext. intros p Hp.
      rewrite Z2Nat.id in Hp by lia.
      rewrite (Efc (b_tree stf) (hp3 p)) by (apply Hwin_rng; lia).
      reflexivity. }
    assert (SIMCc : t_freq (clampf (b_tree stf)) (ndf - 1)
                    = wsum (fun n => ind (live_b (clampf t0) maxc0 n)
                                     * t_freq (clampf t0) n)
                           0 (Z.to_nat (sd_elems k))).
    { rewrite (Efc (b_tree stf) (ndf - 1)) by lia.
      rewrite SIMC.
      apply wsum_ext. intros n Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite Hlb_eq. rewrite (Efc t0 n) by lia.
      reflexivity. }
    pose proof (zho_capped_telescope (sd_elems k) maxc0 (clampf t0)
                  (clampf (b_tree stf)) hp3
                  hmaxf ndf Hpkc ltac:(lia) ltac:(lia)
                  (fun n => t_len t2 n)
                  ltac:(intros p Hp; cbv beta;
                        rewrite (p1_len _ _ _ _ _ _ _ _ _ _ Hfin p Hp);
                        apply Z.le_min_l)
                  (p1_root _ _ _ _ _ _ _ _ _ _ Hfin)
                  Hfnnc Hchldc SIMCc) as TEL.
    assert (Hcnn : 0 <= wsum (fun i => t_freq (b_tree stf) i)
                        (sd_elems k) (Z.to_nat (ndf - sd_elems k))).
    { apply wsum_nonneg. intros i Hi.
      rewrite Z2Nat.id in Hi by lia.
      apply Hfnn2. lia. }
    assert (TEL' : wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                                  * t_len t2 n) 0 (Z.to_nat (sd_elems k))
                   <= wsum (fun i => t_freq (b_tree stf) i)
                        (sd_elems k) (Z.to_nat (ndf - sd_elems k))).
    { eapply Z.le_trans; [|eapply Z.le_trans; [exact TEL|]].
      - apply Z.eq_le_incl. symmetry. apply wsum_ext. intros n Hn.
        rewrite Z2Nat.id in Hn by lia.
        rewrite Hlb_eq. rewrite (Efc t0 n) by lia. reflexivity.
      - apply Z.eq_le_incl. apply wsum_ext. intros i Hi.
        rewrite Z2Nat.id in Hi by lia.
        rewrite (Efc (b_tree stf) i) by lia. reflexivity. }
    eapply Z.le_trans; [exact TEL'|].
    rewrite <- (Z2Nat.id (wsum (fun i => t_freq (b_tree stf) i)
                  (sd_elems k) (Z.to_nat (ndf - sd_elems k)))) by exact Hcnn.
    eapply Z.le_trans with
      (m := Z.of_nat (weight_tree (zho_f t0) TC)).
    { apply (proj1 (Nat2Z.inj_le _ _)). apply SIMA. exact HTCcov'. }
    eapply Z.le_trans with
      (m := Z.of_nat (fold_right
              (fun s' acc => (acc + zho_f t0 s' * Z.to_nat (C s'))%nat)
              0%nat syms)).
    { apply (proj1 (Nat2Z.inj_le _ _)). exact HTCw. }
    rewrite (zhom_fold_of_nat
               (fun s' => (zho_f t0 s' * Z.to_nat (C s'))%nat)
               (fun s' => t_freq t0 s' * C s') syms).
    2:{ intros s' Hin.
        destruct (Hsyms_in s' Hin) as [Hr Hlv].
        unfold zho_f. rewrite Nat2Z.inj_mul.
        rewrite !Z2Nat.id;
          [reflexivity | pose proof (HsymsC s' Hin); lia
           | apply Hfnn0; exact Hr]. }
    rewrite (L2M C).
    unfold syms.
    rewrite <- (zhom_wsum_filter (live_b t0 maxc0)
                 (fun n => t_freq t0 n * C n) (Z.to_nat (sd_elems k))).
    apply Z.eq_le_incl. apply wsum_ext. intros n Hn. ring. }
  (* --- 13. finish, per overflow branch --- *)
  rewrite (L2M (fun n => t_len (ts_trees (build_tree k s) k) n)).
  destruct (Z.eqb_spec ov 0) as [Hov0|Hovpos].
  - (* ov = 0 *)
    assert (Elen : forall n, t_len (ts_trees (build_tree k s) k) n
                             = t_len t2 n).
    { intro n. rewrite Efin. rewrite EG.
      replace (Z.eqb ov 0) with true
        by (symmetry; apply Z.eqb_eq; exact Hov0).
      cbv iota.
      rewrite zhom_gen_codes_len.
      cbn [ts_trees set_statlen set_optlen set_blcount set_tree set_trees].
      rewrite Z.eqb_refl. reflexivity. }
    assert (Emask : wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                          * t_len (ts_trees (build_tree k s) k) n)
                         0 (Z.to_nat (sd_elems k))
                    = wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                            * t_len t2 n) 0 (Z.to_nat (sd_elems k))).
    { apply wsum_ext. intros n Hn. rewrite Elen. reflexivity. }
    rewrite Emask.
    pose proof CORE. unfold ZHO_K.
    destruct (Z.eqb k TK_D); lia.
  - (* ov > 0 *)
    assert (Hovnn : 0 < ov).
    { assert (Hnn : 0 <= ov); [|lia].
      rewrite (p1_ov _ _ _ _ _ _ _ _ _ _ Hfin).
      apply wsum_nonneg. intros i Hi.
      pose proof (ind_0_1 (Z.eqb
        (t_len t2 (t_dad (b_tree stf) (hp3 i))) 15)). lia. }
    destruct (gb_pass2 (2 * Z.to_nat HEAP_SIZE + Z.to_nat MAX_BITS + 4)
                hp3 maxc0 t2 (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov) 15
                (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov 15) HEAP_SIZE olp)
      as [t3 ol2] eqn:E2p.
    assert (Elen3 : forall n, t_len (ts_trees (build_tree k s) k) n
                              = t_len t3 n).
    { intro n. rewrite Efin. rewrite EG.
      replace (Z.eqb ov 0) with false
        by (symmetry; apply Z.eqb_neq; exact Hovpos).
      cbv iota.
      rewrite zhom_gen_codes_len.
      cbn [ts_trees set_statlen set_optlen set_blcount set_tree set_trees].
      rewrite Z.eqb_refl. reflexivity. }
    assert (Emask3 : wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                           * t_len (ts_trees (build_tree k s) k) n)
                          0 (Z.to_nat (sd_elems k))
                     = wsum (fun n => ind (live_b t0 maxc0 n) * t_freq t0 n
                             * t_len t3 n) 0 (Z.to_nat (sd_elems k))).
    { apply wsum_ext. intros n Hn. rewrite Elen3. reflexivity. }
    rewrite Emask3.
    (* the BtAdjust-shaped inputs, from BtLevels.pass1_kraft (the landed
       call-site pattern, cf. BtItem6) *)
    destruct (pass1_kraft (sd_elems k) maxc0 15 t0 (b_tree stf) hp3 hmaxf ndf
                Hpk ltac:(lia) t2 blc1 ov Hfin)
      as (Hzk & Hov & HbM & HW0 & HV0).
    set (V := VIc (sd_elems k) hp3 hmaxf t2 15) in *.
    assert (HV1 : 1 <= V) by lia.
    assert (Hwsz : Z.of_nat (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
                   = 2 * (hlen0 - 1)).
    { rewrite Z2Nat.id by lia. lia. }
    assert (Hovle : ov <= 2 * (hlen0 - 1)).
    { rewrite (p1_ov _ _ _ _ _ _ _ _ _ _ Hfin).
      pose proof (wsum_ind_ub
        (fun p => Z.eqb (t_len t2 (t_dad (b_tree stf) (hp3 p))) 15)
        (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
      lia. }
    assert (HVle : V <= hlen0 - 1) by lia.
    assert (Hz1 : forall b, b < 1 \/ 15 < b -> blc1 b = 0)
      by (intros b Hb; exact (p1_zero _ _ _ _ _ _ _ _ _ _ Hfin b Hb)).
    assert (Hble : forall b, 0 <= b <= 15 ->
                   0 <= blc1 b <= 2 * (hlen0 - 1)).
    { intros b Hb.
      rewrite ((p1_blc _ _ _ _ _ _ _ _ _ _ Hfin) b Hb).
      split.
      - apply wsum_nonneg. intros i _. apply ind_0_1.
      - pose proof (wsum_ind_ub
          (fun p => (hp3 p <=? maxc0) && (Z.eqb (t_len t2 (hp3 p)) b))
          (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))) as HB.
        lia. }
    assert (Hbnd : forall b, 0 <= blc1 b <= 4 * (hlen0 - 1) - 2 * V).
    { intro b.
      destruct (Z_le_gt_dec 0 b) as [Hb0|Hb0];
        [destruct (Z_le_gt_dec b 15) as [Hb15|Hb15]|].
      - pose proof (Hble b ltac:(lia)). lia.
      - rewrite (Hz1 b) by lia. lia.
      - rewrite (Hz1 b) by lia. lia. }
    assert (HKrng : 0 <= 4 * (hlen0 - 1) < 2 ^ 15)
      by (change (2 ^ 15) with 32768; unfold L_CODES in *; lia).
    destruct (Z.eqb_spec k TK_D) as [HkD|HkD].
    + (* the D-scale instance at 2048 *)
      assert (HeD : sd_elems k <= 30)
        by (rewrite HkD; vm_compute; intro Hx; discriminate Hx).
      pose proof (zho_adjust_delta_d (sd_elems k) maxc0 15 t0 (b_tree stf)
                    t2 t3 hp3 hmaxf ndf blc1
                    (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov)
                    ov olp ol2 V (4 * (hlen0 - 1))
                    Hpk ltac:(lia) HeD ltac:(lia) Hmf0 eq_refl
                    Hfnn0 Hmass
                    (fun p Hp => p1_len _ _ _ _ _ _ _ _ _ _ Hfin p Hp)
                    (p1_root _ _ _ _ _ _ _ _ _ _ Hfin)
                    (fun p Hp => p1_rng _ _ _ _ _ _ _ _ _ _ Hfin p Hp)
                    (fun b Hb => p1_blc _ _ _ _ _ _ _ _ _ _ Hfin b Hb)
                    HW1 HW2
                    Hov HV1 HKrng Hzk ltac:(lia) Hz1 Hbnd
                    eq_refl E2p) as HD.
      pose proof CORE. unfold ZHO_K.
      replace (Z.eqb k TK_D) with true
        by (symmetry; apply Z.eqb_eq; exact HkD).
      lia.
    + (* the generic instance at 12288 *)
      pose proof (zho_adjust_delta (sd_elems k) maxc0 15 t0 (b_tree stf)
                    t2 t3 hp3 hmaxf ndf blc1
                    (gb_adjust (Z.to_nat ov + 1) 15 blc1 ov)
                    ov olp ol2 V (4 * (hlen0 - 1))
                    Hpk ltac:(lia) ltac:(lia) Hmf0 eq_refl
                    Hfnn0 Hmass
                    (fun p Hp => p1_len _ _ _ _ _ _ _ _ _ _ Hfin p Hp)
                    (p1_root _ _ _ _ _ _ _ _ _ _ Hfin)
                    (fun p Hp => p1_rng _ _ _ _ _ _ _ _ _ _ Hfin p Hp)
                    (fun b Hb => p1_blc _ _ _ _ _ _ _ _ _ _ Hfin b Hb)
                    HW1 HW2
                    Hov HV1 HKrng Hzk ltac:(lia) Hz1 Hbnd
                    eq_refl E2p) as HD.
      pose proof CORE. unfold ZHO_K.
      replace (Z.eqb k TK_D) with false
        by (symmetry; apply Z.eqb_neq; exact HkD).
      lia.
Qed.
