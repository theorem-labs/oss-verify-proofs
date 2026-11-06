(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_clamp_c.v, with its module paths changed; 12 of its 27 lines of code are new or changed and 18 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/check_width_c.v; 10 of its 26 lines of code are new or changed and 11 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/check_meter_c.v, with its module paths and addresses changed; 2 of its 28 lines of code are new or changed. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* static __attribute__((noinline)) void check_meter(const uint8_t *f, size_t n)    fuzz_wire.c:100-131
   {
           size_t eo = (n > 13 && w_is_tag(f)) ? 16 : 12;
           int want = n >= 1000 && n >= eo + 6 && w_is_reac(f, eo);
           uint16_t ctr = UNTOUCHED_CTR;                              UNTOUCHED_CTR = 0xa5c3
           int got = rp_meter_counter(f, n, &ctr);
           if (got != want)
                   abort();
           if (want && ctr != (uint16_t)(f[eo + 2] | f[eo + 3] << 8))
                   abort();
           if (!want && ctr != UNTOUCHED_CTR)
                   abort();
   }
   fuzz_wire ubsan 6e91fe0b5555 at 0x1311c (280 bytes): a 48-byte frame (ra, s0, s1, s2 and ctr at sp + 14), one call
   of rp_meter_counter (0x13848) with &ctr.
   The form is libreac/fuzz_decode's check_braid_c.v (25e3d17bdb5): the check RETURNS NORMALLY from every entry state
   LLVMFuzzerTestOneInput gives it (fuzz_wire.c:268), so its abort() is unreachable; the property it checks is no
   premise.
   Premises: f readable for its n bytes (bs, the fuzz_dup copy of fuzz_wire.c:263), the frame's room on the stack, f
   outside the frame; UBSan build: f non-null (fuzz_dup aborts on a null malloc result), as the callee's UBSan
   contract needs it, and sp even (the callee's UBSan contract wants &ctr = sp - 34 2-aligned). *)
Definition CHECK_METER : Z := 0x1311c.
Definition CHECK_METER_FRAME : Z := 48.

Definition check_meter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    Z.of_nat (length bs) = bv_unsigned a1 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    bv_unsigned a0 <> 0 ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_METER_FRAME <= bv_unsigned sp ->
    bv_unsigned sp mod 2 = 0 ->
    bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_METER_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_METER_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_METER) fc None m (seg_rom rsegs)).
