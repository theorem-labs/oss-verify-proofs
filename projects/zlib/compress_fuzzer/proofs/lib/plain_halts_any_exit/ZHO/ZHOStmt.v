(** * ZHOStmt — build_tree COST-OPTIMALITY, the frozen statement (draft v0).

    OWNER: huffman-opt (zlib z-repro campaign, 2026-08-23; TL commission,
    consumer = l1-adversary's zr_l1_min_fits Case B).

    THE CLAIM.  For tree kind [k] with [sd_max_length k = 15] (the L and D
    trees), the frequency-weighted length sum of the tree [build_tree]
    outputs is within [K] bits of the same sum under ANY Kraft-valid
    length assignment [C] with depths in [1,15] on the live symbols.

    K = 12288 (TK_L) / 2048 (TK_D) slack: the EXACT form (K = 0) is FALSE — the gen_bitlen
    depth-15 overflow adjustment is reachable in-domain (strict phi-chain
    freqs, total 5167) and is not depth-15-optimal; adversarial search
    saturates at gap ~349 bits (falsifier corpus, huffman-opt dir).
    8192 = measured delta ceiling (~930, saturated vertex hill) x ~8.8 safety; the provable route (ex-15 shield + Fibonacci weight-depth) prices at ~4.4K, well inside the consumer's Case-B
    slack (~23945 at its worst vertex).

    PREMISE CONVENTION: the pipeline premise block ([bt_init]/[bt_force2]/
    [bt_loop] defining equations) is BtItem6b.build_tree_out's VERBATIM,
    per the ZRKraftEq precedent — every call site that discharges the
    landed theorems discharges this one with the same arguments.
    [2 <= hlen0] (at least two live symbols) makes [bt_force2] the
    identity; the consumer's L tree always has it (EOB freq 1 from
    init_block + any token), the D tree needs its own degenerate-corner
    lemma (0 or 1 live dist codes — trivial costs, no optimality needed).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  This file froze
    the SPELLING before proof spend (R68; fidelity vm_compute-checked in
    ZHOFid.v); the theorem is PROVEN in ZHOMain (zero axioms) and the
    reviewed name re-exported in ZHOStmtFinal.v. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees BtWin.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** live-symbol indicator at the entry state *)
Definition zho_live (s : TSt) (k n : Z) : bool :=
  Z.ltb 0 (t_freq (ts_trees s k) n).

(** the integer Kraft sum of [C] over live symbols, in units of [2^-15] *)
Definition zho_kraft (s : TSt) (k : Z) (C : Z -> Z) : Z :=
  wsum (fun n => (if zho_live s k n then 1 else 0) * 2 ^ (15 - C n))
       0 (Z.to_nat (sd_elems k)).

(** frequency-weighted cost of a length assignment [L] at entry freqs *)
Definition zho_cost (s : TSt) (k : Z) (L : Z -> Z) : Z :=
  wsum (fun n => t_freq (ts_trees s k) n * L n) 0 (Z.to_nat (sd_elems k)).

(* per-kind slack: the L tree carries the adjust corner window (L4);
   the D tree (30 symbols) prices far smaller.  Constants countersigned
   by l1-adversary 2026-08-23 (kink-enumerated LP margin +5,157 at the
   coarse2 family; their rider: LAST K_L bump at this family). *)
Definition ZHO_K (k : Z) : Z := if Z.eqb k TK_D then 2048 else 12288.

(* The theorem itself is PROVEN as ZHOMain.build_tree_cost_opt_main
   (zero axioms); the reviewed name is re-exported with this exact
   statement in ZHOStmtFinal.v.  This file carries only the frozen
   DEFINITIONS so the spelling stays the single source of truth. *)
