(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-10: the addresses, frame shape and inlined-expected_value statement of reac-repacer/fuzz_uci's
   check_value in image A, in the form of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_iface.v and crtA_loop_stmt.v
   (origin/ossv/recipes 88154566652a); the expected_value statement is the footprint twin of the plain walk's
   continuation form (lib/Prog/check_value.v, Section Ev, ev_block / KFIN). *)
(* Modified by Theorem Labs, 2026-10: the straight-line segments of reac-repacer/fuzz_uci's check_value in image A, in the form
   and with the helpers of proofs/libreac/fuzz_decode/lib/A/Prog/crtA_segs.v (origin/ossv/recipes 88154566652a:
   crt_seg1_F .. crt_seg9_F, Z_to_le_bytes_to_Z, crt_le8_of_bytes, crt_c8s, crt_rw_c8s, crt_frame_words, crt_regs,
   crt_usub, crt_shift, crt_w, crt_finF, crt_memF, crt_pc) and of its lib/A/Prog/ReacDecodeLib.v rd_all. *)
(* Modified by Theorem Labs, 2026-10: from reac-repacer/fuzz_uci's lib/A/Prog/UciCvIface.v the frame cells (cv_fr)
   and the form of the cut points, and from its lib/A/Prog/UciCvSegs.v the shape of the segment statements cv_seg1_F
   and cv_end_F, restated for reac-repacer/fuzz_wire's check_copy on image A (its cut points, registers and
   addresses); the other segment statements are new. *)
(* check_copy_cgW_iface: what the pieces of the image-A walk of check_copy (fuzz_wire.asan 0x80c38 =
   wire_sigma WS_check_copy) share, for the caller-journal statement lib/A/Prog/check_copy_cg.v, in the form of
   reac-repacer/fuzz_uci's lib/A/Prog/UciCvIface.v and UciCvSegs.v (the walk of check_value): the cut points, the
   frame the prologue writes, and the footprint runs (lib/Lib/ExecF.v evtF) of the straight-line segments between
   the calls, as STATEMENTS. lib/A/Prog/check_copy_cgW_segs.v proves them; lib/A/Prog/check_copy_cgW_walk.v takes
   them as premises and lib/A/Prog/check_copy_cgW.v composes the two.

   Control flow (offsets from the entry, read from the neutral listing of image A):
     +0x000 `addi sp, sp, -0x40`, ra and s0 .. s5 stored at 0x38(sp) .. 8(sp); s3 := n, s4 := f; the shadow base s5
            through the GOT word 0x987e8 and its cell 0xa0778; s1 := c, a1 := n
     +0x03c call rp_copy_untag (0x813e0), returns +0x040
     +0x040 s0 := a0 (got); a0 := n + (n == 0); call malloc (trampoline 0x522f8) at +0x04c, returns +0x050
     +0x050 `beqz a0` to the abort (+0x1e8); s2 := a0 (u); `beqz s3` (n = 0) to +0x174
     +0x05c a0 := u, a1 := f, a2 := n; call __asan_memcpy (0x50c34) at +0x068, returns +0x06c
     +0x06c `bltu s3, 18` to +0x174; the tag test: four checked 1-byte loads of f[12], f[13], f[16], f[17] (checks at
            +0x080, +0x0a4, +0x0c4, +0x0e8; slow paths +0x1f0, +0x1fc, +0x220, +0x23c; report calls +0x1f8, +0x204,
            +0x22c, +0x244), each mismatch to +0x110 with a2 = n
     +0x100 a0 := u + 12, a2 := n - 16 (a1 = f + 16 from +0x0b8); call __asan_memcpy at +0x108, returns +0x10c
     +0x10c a2 := n - 4
     +0x110 (CC_WANT, a2 = ulen) `bltu s3, 50` to +0x174; the want test: checked loads of u[12], u[13], u[16]
            (+0x12c, +0x14c, +0x16c), mismatches to +0x174, u[16] = 0 to +0x1c0: u[17] (+0x1d4), a0 := ulen when
            u[17] = 0, else 0; `beq s0, a0` to +0x178, else the abort
     +0x174 `bnez s0` to the abort; +0x178 `beqz s0` to +0x190; a0 := c, a1 := u, a2 := got; call bcmp
            (trampoline 0x4157c) at +0x188, returns +0x18c; `bnez a0` to the abort
     +0x190 a0 := u; call free (trampoline 0x522f4) at +0x194, returns +0x198
     +0x198 a0 := s0 (got); the epilogue; `ret` at +0x1bc.
   +0x1e8 (__asan_handle_no_return) / +0x1ec (abort) and the eight report calls are the unreachable exits. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Cells Frame Step.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require ExecF.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import WirePSyms WirePAddr.
Import ListNotations.
Open Scope Z_scope.

Definition CC_ENTRY : Z := wire_sigma WS_check_copy.
Definition CC_AT (off : Z) : Z := CC_ENTRY + off.
Definition CC_RCU : Z := wire_sigma WS_rp_copy_untag.
Definition CC_MALLOC : Z := wire_sigma WS___interceptor_trampoline_malloc.
Definition CC_FREE : Z := wire_sigma WS___interceptor_trampoline_free.
Definition CC_MEMCPY : Z := wire_sigma WS___asan_memcpy.
Definition CC_BCMP : Z := wire_sigma WS___interceptor_trampoline_bcmp.

(* The cut points, as offsets from the entry: the return addresses of the six calls and the join of the tag test. *)
Definition CC_RET_RCU : Z := CC_AT 0x40.
Definition CC_RET_MALLOC : Z := CC_AT 0x50.
Definition CC_RET_CP1 : Z := CC_AT 0x6c.
Definition CC_RET_CP2 : Z := CC_AT 0x10c.
Definition CC_WANT : Z := CC_AT 0x110.
Definition CC_RET_BCMP : Z := CC_AT 0x18c.
Definition CC_RET_FREE : Z := CC_AT 0x198.

(* The frame: the caller's s5, s4, s3, s2, s1, s0, ra at 8(sp) .. 0x38(sp) of the 0x40-byte frame. *)
Definition cc_fr (c5 c4 c3 c2 c1 c0 cra : word) : list cell :=
  [C8 c5; C8 c4; C8 c3; C8 c2; C8 c1; C8 c0; C8 cra].

(* The 8-aligned cover of the shadow bytes of [x, x + n), the bytes the instrumented checks of x .. x + n - 1 read. *)
Definition cc_hull_lo (x : Z) : Z := shadow_addr x / 8 * 8.
Definition cc_hull_len (x n : Z) : Z := shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8.

(* ---- CC_ENTRY -> rp_copy_untag (ra = CC_RET_RCU): the frame, s3 := n, s4 := f, s5 := the shadow base, s1 := c,
   a1 := n ---- *)
Definition cc_seg_entry_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c f n lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp ->
    bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) -> bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) ->
    CELL_K + 8 <= bv_unsigned sp - 64 ->
    ExecF.rng RNG (bv_unsigned sp - 64) 64 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists m1 v0,
         ms' = MS (mkR (Z_to_bv 64 CC_RET_RCU) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2
                    s0 (Z_to_bv 64 c) (Z_to_bv 64 c) (Z_to_bv 64 n) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_RCU) fc None m1 (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
         rw_cells rsegs m1 (bv_unsigned sp - 64) (C8 v0 :: cc_fr s5 s4 s3 s2 s1 s0 ra))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_ENTRY) fc None m (seg_rom rsegs)).

(* ---- CC_RET_RCU -> malloc (ra = CC_RET_MALLOC): s0 := a0, a0 := n + (n == 0) ---- *)
Definition cc_seg_m_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    0 <= n < 2 ^ 63 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_MALLOC) sp gp tp t0 t1 t2 a0 s1 (Z_to_bv 64 (Z.max n 1)) a1 a2 a3 a4 a5
                    a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_MALLOC) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_RCU) fc None m (seg_rom rsegs)).

(* ---- CC_RET_MALLOC with a0 = u > 0, n = 0 and got = 0 -> free(u) (ra = CC_RET_FREE): `beqz a0` not taken,
   s2 := u, `beqz s3` taken to +0x174, `bnez s0` not taken, `beqz s0` taken to +0x190, a0 := u ---- *)
Definition cc_seg_z_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z),
    0 < P < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_FREE) sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5
                    a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_MALLOC) fc None m (seg_rom rsegs)).

(* ---- CC_RET_MALLOC with a0 = u > 0 and n > 0 -> __asan_memcpy(u, f, n) (ra = CC_RET_CP1) ---- *)
Definition cc_seg_cp1_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z),
    0 < P < 2 ^ 64 -> 0 < n < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_CP1) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) s4 (Z_to_bv 64 n) a3 a4 a5
                    a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8
               s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_MALLOC) fc None m (seg_rom rsegs)).

(* ---- CC_RET_CP1 with n < 18 and got = 0 -> free(u): `bltu s3, 18` taken to +0x174, `bnez s0` not taken,
   `beqz s0` taken to +0x190, a0 := u ---- *)
Definition cc_seg_short_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z),
    0 < P < 2 ^ 64 -> 0 <= n < 18 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_FREE) sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5
                    a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 s5
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_CP1) fc None m (seg_rom rsegs)).

(* ---- CC_RET_CP1 with n >= 18: the tag test on f's bytes 12, 13, 16, 17 (b12, b13, b16, b17). The frame f is
   addressable (each check reads a shadow byte inside the cover of f's shadow and allows the load). ---- *)
(* All four match (81 00 88 19): a0 := u + 12, a1 := f + 16, a2 := n - 16; __asan_memcpy (ra = CC_RET_CP2). *)
Definition cc_seg_tag_yes_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P f n : Z),
    0 < P -> P + n < 2 ^ 64 -> 18 <= n ->
    addressable m f n -> ExecF.rng RNG f n -> ExecF.rng RNG (cc_hull_lo f) (cc_hull_len f n) ->
    mrd rsegs m (wa (f + 12)) = Some (Z_to_bv 8 0x81) -> mrd rsegs m (wa (f + 13)) = Some (Z_to_bv 8 0) ->
    mrd rsegs m (wa (f + 16)) = Some (Z_to_bv 8 0x88) -> mrd rsegs m (wa (f + 17)) = Some (Z_to_bv 8 0x19) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a3' : word,
         ms' = MS (mkR (Z_to_bv 64 CC_RET_CP2) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (P + 12)) (Z_to_bv 64 (f + 16))
                    (Z_to_bv 64 (n - 16)) a3' a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 f)
                    (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_MEMCPY) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 f)
               (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_CP1) fc None m (seg_rom rsegs)).

(* Not all four match: CC_WANT with a2 = n (ulen). *)
Definition cc_seg_tag_no_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P f n b12 b13 b16 b17 : Z),
    0 < P -> P + n < 2 ^ 64 -> 18 <= n ->
    addressable m f n -> ExecF.rng RNG f n -> ExecF.rng RNG (cc_hull_lo f) (cc_hull_len f n) ->
    0 <= b12 < 256 -> 0 <= b13 < 256 -> 0 <= b16 < 256 -> 0 <= b17 < 256 ->
    mrd rsegs m (wa (f + 12)) = Some (Z_to_bv 8 b12) -> mrd rsegs m (wa (f + 13)) = Some (Z_to_bv 8 b13) ->
    mrd rsegs m (wa (f + 16)) = Some (Z_to_bv 8 b16) -> mrd rsegs m (wa (f + 17)) = Some (Z_to_bv 8 b17) ->
    ~ (b12 = 0x81 /\ b13 = 0 /\ b16 = 0x88 /\ b17 = 0x19) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a0' a1' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' (Z_to_bv 64 n) a3' a4 a5 a6 a7 (Z_to_bv 64 P)
                    (Z_to_bv 64 n) (Z_to_bv 64 f) (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_WANT) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 f)
               (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_CP1) fc None m (seg_rom rsegs)).

(* ---- CC_RET_CP2 -> CC_WANT: a2 := n - 4 (ulen) ---- *)
Definition cc_seg_cp2ret_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
    4 <= n < 2 ^ 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (n - 4)) a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5
                    s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_WANT) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_CP2) fc None m (seg_rom rsegs)).

(* ---- CC_WANT with n < 50 and got = 0 -> free(u): `bltu s3, 50` taken to +0x174, `bnez s0` not taken, `beqz s0`
   taken to +0x190, a0 := u ---- *)
Definition cc_seg_want_lo_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n : Z),
    0 < P < 2 ^ 64 -> 0 <= n < 50 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_FREE) sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5
                    a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 s5
               s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_WANT) fc None m (seg_rom rsegs)).

(* ---- CC_WANT with n >= 50, a2 = L (ulen) and s0 = g (got), where g is the want of u's bytes 12, 13, 16, 17
   (u12, u13, u16, u17): L when they are 88 19 00 00, else 0. u is addressable (each check allows its load). The
   test `beq s0, a0` is taken; g = 0: `bnez s0` not taken at +0x174 or `beq` to +0x178, `beqz s0` taken, free(u)
   (ra = CC_RET_FREE); g > 0: bcmp(c, u, g) with a0 := s1 = c (ra = CC_RET_BCMP). ---- *)
Definition cc_want (u12 u13 u16 u17 L : Z) : Z :=
  if ((u12 =? 0x88) && (u13 =? 0x19) && (u16 =? 0) && (u17 =? 0))%bool then L else 0.

Definition cc_seg_want_hi_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s1 a0 a1 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P n L u12 u13 u16 u17 : Z),
    0 < P -> 50 <= n -> 0 <= L < 2 ^ 63 ->
    addressable m P n -> ExecF.rng RNG P n -> ExecF.rng RNG (cc_hull_lo P) (cc_hull_len P n) ->
    0 <= u12 < 256 -> 0 <= u13 < 256 -> 0 <= u16 < 256 -> 0 <= u17 < 256 ->
    mrd rsegs m (wa (P + 12)) = Some (Z_to_bv 8 u12) -> mrd rsegs m (wa (P + 13)) = Some (Z_to_bv 8 u13) ->
    mrd rsegs m (wa (P + 16)) = Some (Z_to_bv 8 u16) -> mrd rsegs m (wa (P + 17)) = Some (Z_to_bv 8 u17) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists a1' a2' a3' : word,
         (cc_want u12 u13 u16 u17 L = 0 /\
          ms' = MS (mkR (Z_to_bv 64 CC_RET_FREE) sp gp tp t0 t1 t2 (Z_to_bv 64 0) s1 (Z_to_bv 64 P) a1' a2' a3'
                     a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5
                     t6)
                   F (Z_to_bv 64 CC_FREE) fc None m (seg_rom rsegs)) \/
         (0 < cc_want u12 u13 u16 u17 L /\
          ms' = MS (mkR (Z_to_bv 64 CC_RET_BCMP) sp gp tp t0 t1 t2 (Z_to_bv 64 L) s1 s1 (Z_to_bv 64 P)
                     (Z_to_bv 64 L) a3' a4 a5 a6 a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 (Z_to_bv 64 ASAN_K) s6 s7 s8
                     s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 CC_BCMP) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (cc_want u12 u13 u16 u17 L)) s1 a0 a1 (Z_to_bv 64 L) a3 a4 a5 a6
               a7 (Z_to_bv 64 P) (Z_to_bv 64 n) s4 (Z_to_bv 64 ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_WANT) fc None m (seg_rom rsegs)).

(* ---- CC_RET_BCMP with a0 = 0 -> free(u): `bnez a0` not taken, a0 := u ---- *)
Definition cc_seg_bcmpret_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR (Z_to_bv 64 CC_RET_FREE) sp gp tp t0 t1 t2 s0 s1 s2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                    s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 CC_FREE) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_BCMP) fc None m (seg_rom rsegs)).

(* ---- CC_RET_FREE -> the return: a0 := s0, ra and s0 .. s5 reloaded from the frame, sp += 0x40, `ret` ---- *)
Definition cc_seg_end_F : Prop :=
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (v0 c5 c4 c3 c2 c1 c0 cra : word),
    rw_cells rsegs m (bv_unsigned sp) (C8 v0 :: cc_fr c5 c4 c3 c2 c1 c0 cra) ->
    bv_unsigned sp + 64 < 2 ^ 64 ->
    ExecF.rng RNG (bv_unsigned sp) 64 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         ms' = MS (mkR cra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 c0 c1 s0 a1 a2 a3 a4 a5 a6 a7
                    c2 c3 c4 c5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc cra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CC_RET_FREE) fc None m (seg_rom rsegs)).
