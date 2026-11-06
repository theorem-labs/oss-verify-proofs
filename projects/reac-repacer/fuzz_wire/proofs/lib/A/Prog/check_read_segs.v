(* check_read_segs: the footprint statement of one segment of the image-A walk of check_read (fuzz_wire.asan 0x8077c),
   as a Definition only (no proof): S3, the comparison of the twelve samples, +0x1a4 .. +0x35c.

   The code (image A; offsets from 0x8077c):
     +0x1a4  `bne a0, s10` to the abort at +0x488 (not taken: a0 is rp_slot_read's answer, s10 the harness's want,
             and both are got below);
     +0x1a8 .. +0x1f8  the loop set-up: t2 = 3 (slot & ~1), t3 = s1 + 0x12 + 3 (slot & 1), t0 = 3 s11 (s11 = the
             width), a1 .. a6 / t5 = c + 0x36, 0x37, 0x34, 0x32, 0x35, 0x33 / 0x32, a7 = 12, t1 = 0x5a5a5a5a,
             t4 = -0x1000000;
     +0x1fc .. +0x310  the loop, twelve times: `lw t6, 0(s3)` (v[s]); got = 0 (`beqz s10`): `bne t6, t1` to the abort;
             got = 1: the six braid bytes of the group g = c + 50 + 3 (slot & ~1) + 3 W s, each behind the shadow `lb` of
             its address (+0x210 / +0x22c / +0x248 / +0x264 / +0x280 / +0x29c; the arms +0x314 .. +0x354 return to the
             load when the partial granule holds the byte and call __asan_report_load1 otherwise), stored to
             s1 + 0x12 .. s1 + 0x17 in the order g[1], g[0], g[3], g[2], g[5], g[4]; three of them read back from t3, the
             24-bit sample built and sign-extended, `bne t6, a0` to the abort; then s3 += 4, a1 .. a6 / t5 += t0, a7 -= 1,
             `beqz a7` to +0x35c.
   The state at +0x1a4 is the one the walk has after rp_slot_read returns: the callee-saved registers of check_read's
   body (s1 = the realigned sp, s3 = v, s4 = c, s5 = slot, s6 = len, s8 = the shadow base, s10 = got, s11 = the width
   when got = 1), a0 = got, v holding rp_slot_read's samples (got = 1) or still UNTOUCHED_SAMPLE (got = 0). The run
   writes only the six bytes s1 + 0x12 .. s1 + 0x17 and ends at +0x35c with the callee-saved registers it does not
   use as scratch kept. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog Require rp_slot_read_c rp_slot_width_c.
Import ListNotations.
Open Scope Z_scope.
Module PSR := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_read_c.
Module PSW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Prog.rp_slot_width_c.

(* S3: +0x1a4 (pc 0x80920) -> +0x35c (pc 0x80ad8). *)
Definition crd_seg_S3_stmt : Prop :=
  forall (RNG : ExecF.footprint)
         (x1 x2 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x23 x25 x27 x28 x29 x30 x31 : word)
         (wc wn ws : word) (v : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs j6 : list byte),
    bv_unsigned wn <= 1600 -> Z.of_nat (length bs) = bv_unsigned wn ->
    4096 <= v -> v + 48 <= bv_unsigned x9 -> bv_unsigned x9 + 24 <= 2 ^ 64 ->
    (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws) = 1 ->
       x27 = Z_to_bv 64 (PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws)) /\
       bytes_at rsegs m v
         (PSR.rp_slot_bytes bs (PSW.rp_slot_width_model (bv_unsigned wn) bs (bv_signed ws)) (bv_signed ws)) /\
       bytes_at rsegs m (bv_unsigned wc) bs /\ addressable m (bv_unsigned wc) (bv_unsigned wn) /\
       bv_unsigned wc + bv_unsigned wn <= bv_unsigned x9 /\
       shadow_addr (bv_unsigned wc + bv_unsigned wn) <= bv_unsigned x9 /\
       ExecF.rng RNG (bv_unsigned wc) (bv_unsigned wn) /\
       ExecF.rng RNG (shadow_addr (bv_unsigned wc))
         (shadow_addr (bv_unsigned wc + bv_unsigned wn - 1) - shadow_addr (bv_unsigned wc) + 1)) ->
    (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws) = 0 ->
       bytes_at rsegs m v (repeat (Z_to_bv 8 90) 48)) ->
    rw_cells rsegs m (bv_unsigned x9 + 18) [CB 6 j6] ->
    ExecF.rng RNG v 48 -> ExecF.rng RNG (bv_unsigned x9 + 18) 6 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (m' : word -> option byte)
                    (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y28 y29 y30 y31 : word),
         ms' = MS (mkR x1 x2 x3 x4 y5 y6 y7 x8 x9 y10 y11 y12 y13 y14 y15 y16 y17 x18 y19 y20 y21 y22 x23
                    (Z_to_bv 64 ASAN_K) x25 (Z_to_bv 64 (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws)))
                    x27 y28 y29 y30 y31)
                  F (Z_to_bv 64 0x80ad8) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned x9 + 18, bv_unsigned x9 + 24)] m m' /\ wmono rsegs m m')
      (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws)))
               x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 v) wc ws wn x23 (Z_to_bv 64 ASAN_K) x25
               (Z_to_bv 64 (PSR.rp_slot_read_model (bv_unsigned wn) bs (bv_signed ws))) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x80920) fc None m (seg_rom rsegs)).
