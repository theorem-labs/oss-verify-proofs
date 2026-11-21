(** * BtCensus5 — the parked-window census at [build_tree]'s own call shape.

    OWNER: an earlier development run.

    BuildChain.v's convention: the two destructuring equations name the calls
    [build_tree] itself performs, so a consumer produces them by
    [destruct ... eqn:] on the same terms; the loop and heapify are pinned by
    their defining equations.  Everything else is discharged here — fuel
    arithmetic via the same rewrites BuildChain used, sizes via BtSized. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtCensus4 BtStep BtSized.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Theorem build_tree_parked : forall k s t0 hp0 dep0 hlen0 maxc0
                                   t1 hp1 dep1 hlen1 maxc1 ol1 sl1 hp2 stf,
  3 <= sd_elems k <= L_CODES ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k) (ts_heap s)
          (ts_depth s) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen s) (ts_statlen s)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  hp2 = bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2) ->
  bt_loop (Z.to_nat HEAP_SIZE)
          {| b_tree := t1; b_heap := hp2; b_dep := dep1;
             b_hlen := hlen1; b_hmax := HEAP_SIZE; b_node := sd_elems k |}
    = Some stf ->
  BtParked (sd_elems k) maxc1 t1 (b_tree stf)
    (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1))
    (b_hmax stf - 1) (b_node stf)
  /\ InitOut (sd_elems k) t1 hp1 hlen1 maxc1
  /\ 2 <= hlen1 <= L_CODES
  /\ b_node stf - sd_elems k = hlen1 - 1
  /\ (forall i, t_freq t0 i = t_freq (ts_trees s k) i).
Proof.
  intros k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1 hp2 stf
         Hel E0 E2 Ehp2 Eloop.
  (* the initial heap is characterized *)
  destruct (bt_init_census_call (Z.to_nat L_CODES + 2) (sd_elems k)
              (ts_trees s k) (ts_heap s) (ts_depth s)
              t0 hp0 dep0 hlen0 maxc0 E0) as [Hout0 Hfr0];
    [ rewrite Nat2Z.inj_add, Z2Nat.id by (unfold L_CODES; lia);
      change (Z.of_nat 2) with 2; unfold L_CODES in *; lia
    | lia | ].
  (* the forced slots keep it characterized and land [hlen1 >= 2] *)
  destruct (bt_force2_census (sd_stree k) (sd_elems k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s)
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E2 ltac:(lia) Hout0)
    as [Hout1 Hh2].
  (* size bound via BtSized *)
  pose proof (bt_sized k s t0 hp0 dep0 hlen0 maxc0
                t1 hp1 dep1 hlen1 maxc1 ol1 sl1
                ltac:(lia) ltac:(lia) E0 E2) as Hsz.
  pose proof (io_maxc _ _ _ _ _ Hout1) as Hmc.
  (* the loop keeps the census *)
  pose proof (census_loop (Z.to_nat HEAP_SIZE) (sd_elems k) maxc1 t1 hlen1
                {| b_tree := t1; b_heap := hp2; b_dep := dep1;
                   b_hlen := hlen1; b_hmax := HEAP_SIZE;
                   b_node := sd_elems k |}) as Hloop.
  cbn [b_hlen b_hmax] in Hloop.
  specialize (Hloop ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (gap_at_entry hlen1 hp2 dep1 t1 (sd_elems k) ltac:(lia))
                ltac:(lia)).
  rewrite Ehp2 in *.
  specialize (Hloop (census_entry (sd_elems k) maxc1 t1 hp1 dep1 hlen1
                       (Z.to_nat HEAP_SIZE) ltac:(lia) Hout1)).
  rewrite Eloop in Hloop.
  destruct Hloop as [Hinvf [Hl1 Hrootid]].
  pose proof (cv_hl _ _ _ _ _ Hinvf) as Htrips.
  rewrite Hl1 in Htrips.
  split; [|split; [exact Hout1 | split; [lia | split; [lia | exact Hfr0]]]].
  apply (census_exit (sd_elems k) maxc1 t1 hlen1 stf Hinvf Hmc ltac:(lia)
           Hl1 Hrootid).
Qed.

Print Assumptions build_tree_parked.
