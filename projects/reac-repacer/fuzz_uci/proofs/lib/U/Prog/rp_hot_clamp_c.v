(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of rp_hot_clamp (src/repace_conf.c) on the
   UBSan image, the leaf at 0x1317c. The UBSan twin of lib/Prog/rp_hot_clamp_c.v: same model, same premises, and
   two premises more for the UBSan traps (below). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
Import ListNotations.
Open Scope Z_scope.

Definition RP_HOT_CLAMP : Z := 0x1317c.

(* one int32 field of struct rp_hot, as the four little-endian bytes of x mod 2^32 *)
Definition c4z (x : Z) : cell := C4 (Z_to_bv 64 x).

(* struct rp_hot { int prefill_ms, adapt_min_ms, adapt_max_ms, adapt_margin, servo_clamp_ppm; } : 20 bytes *)
Definition hot_cells (p : rp_hot) : list cell :=
  [c4z (prefill_ms p); c4z (adapt_min_ms p); c4z (adapt_max_ms p);
   c4z (adapt_margin p); c4z (servo_clamp_ppm p)].

Definition RP_HOT_SIZE : Z := 20.

(* every field is an int *)
Definition hot_int (p : rp_hot) : Prop :=
  INT_MIN <= prefill_ms p <= INT_MAX /\ INT_MIN <= adapt_min_ms p <= INT_MAX /\
  INT_MIN <= adapt_max_ms p <= INT_MAX /\ INT_MIN <= adapt_margin p <= INT_MAX /\
  INT_MIN <= servo_clamp_ppm p <= INT_MAX.

Definition rp_hot_clamp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : rp_hot) (mm : Z),
    (* UBSan only: 0x1317c `beqz a0` traps (unimp at 0x1323c) on p == NULL, the null check of p->prefill_ms. *)
    bv_unsigned a0 <> 0 ->
    (* UBSan only: 0x13180 `andi a2, a0, 3` / 0x13184 `bnez` trap (unimp at 0x1323c) on a misaligned p, the
       alignment check of p->prefill_ms. *)
    bv_unsigned a0 mod 4 = 0 ->
    hot_int p ->
    0 <= mm <= INT_MAX ->
    bv_unsigned a1 = mm ->
    rw_cells rsegs m (bv_unsigned a0) (hot_cells p) ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned a0, bv_unsigned a0 + RP_HOT_SIZE)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (bv_unsigned a0) (hot_cells (rp_hot_clamp_m p mm)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_HOT_CLAMP) fc None m (seg_rom rsegs)).
