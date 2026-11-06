(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the contract of rp_uci_int (src/repace_conf.c), the plain
   image's 0x13150. evt / register style of libreac/fuzz_decode's released lib/Prog/reac_frame_counter_c.v, with the
   stack premises of its check_braid_c.v (rp_uci_int has a 32-byte frame; its only callee, memchr, writes nothing).
   The result is lib/Spec/UciModel.v's rp_uci_int_m of the n reply bytes -- so the value depends only on those bytes,
   which is what check_no_overread's abort needs. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
Import ListNotations.
Open Scope Z_scope.

Definition RP_UCI_INT : Z := 0x13150.
Definition RP_UCI_INT_FRAME : Z := 32.

(* the bytes of a reply as the model reads them: Z in [0, 255] *)
Definition zbytes (bs : list byte) : list Z := map (@bv_unsigned 8) bs.

Definition rp_uci_int_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (cur lo : Z),
    bytes_at rsegs m (bv_unsigned a0) bs ->
    (* the reply does not run to the end of the address space: without it the `end = reply + n` of
       repace_conf.c:38 wraps to 0 and every later `p < end` is false, so the function returns cur while the
       model reads the bytes. Every caller has a heap slice, far below alloc_ceiling. Found with
       the counterexample a0 = 2^64-1, n = 1, bs = ["5"], cur = 0: the binary returns 0 at
       0x13288 while rp_uci_int_m [53] 0 = 5. *)
    bv_unsigned a0 + Z.of_nat (length bs) < 2 ^ 64 ->
    Z.of_nat (length bs) = bv_unsigned a1 ->
    a2 = Z_to_bv 64 cur -> INT_MIN <= cur <= INT_MAX ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + RP_UCI_INT_FRAME <= bv_unsigned sp ->
    bv_unsigned sp <= 2 ^ 63 ->
    bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - RP_UCI_INT_FRAME \/
      bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur)) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_UCI_INT_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0) bs)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_UCI_INT) fc None m (seg_rom rsegs)).
