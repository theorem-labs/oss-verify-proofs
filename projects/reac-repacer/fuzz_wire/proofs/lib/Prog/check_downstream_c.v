(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/Prog/check_clamp_c.v, with its module paths changed; 12 of its 27 lines of code are new or changed and 18 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_wire/lib/Prog/check_width_c.v; 10 of its 26 lines of code are new or changed and 11 lines of the source are left out. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* static __attribute__((noinline)) void check_downstream(const uint8_t *f, size_t n)    fuzz_wire.c:86-98
   {
           int want = n >= 18 && (w_is_reac(f, 12) || (w_is_tag(f) && w_is_reac(f, 16)));
           if (rp_ds_accept(f, n) != want)
                   abort();
   }
   fuzz_wire plain c8763dfc4e81 at 0x12fc8 (128 bytes): a 16-byte frame (ra, s0), one call of rp_ds_accept (0x13530).
   The form is libreac/fuzz_decode's check_braid_c.v (25e3d17bdb5): the check RETURNS NORMALLY from every entry state
   LLVMFuzzerTestOneInput gives it (fuzz_wire.c:267), so its abort() is unreachable; the property it checks is no
   premise.
   Premises: f readable for its n bytes (bs, the fuzz_dup copy of fuzz_wire.c:263), the frame's room on the stack, f
   outside the frame. *)
Definition CHECK_DOWNSTREAM : Z := 0x12fc8.
Definition CHECK_DOWNSTREAM_FRAME : Z := 16.

Definition check_downstream_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    Z.of_nat (length bs) = bv_unsigned a1 ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    stk rsegs m lo (bv_unsigned sp) ->
    lo + CHECK_DOWNSTREAM_FRAME <= bv_unsigned sp ->
    bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_DOWNSTREAM_FRAME \/ bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_DOWNSTREAM_FRAME, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_DOWNSTREAM) fc None m (seg_rom rsegs)).
