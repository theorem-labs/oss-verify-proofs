(* Modified by Theorem Labs: copied from reac-repacer/fuzz_wire proofs/reac-repacer/fuzz_wire/lib/U/Prog/rp_frame_channels_c.v at 75e059c080d; module path, entry address and the addresses in comments set to fuzz_egress's.
   rp_frame_channels, reac-repacer src/repace_wire.c:74-86 (sha256 cfd1889a071e): fuzz_egress ubsan 44f6a3ebc228 at 0x1337c
   (0x74 bytes). Calls reac_frame_clean_len (contract reac_frame_clean_len_c.v) and reads the 8-byte reciprocal of 36 at
   A_K36 (`ld` at 0x133a0, used by `mulhu` / `srli 5` for the division by 36). Saves ra / s0 in a 16-byte frame.
   The premise mem_inv (no overlay byte on a read-only address) keeps the image's constants (A_M, A_T, A_K36, all in
   .rodata) out of reach of every store, the frame's included, so the walk reads them from the image. The
   UBSan build has no check in this function: its words equal the plain build's but for the jal and the ld offset. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import reac_frame_clean_len_c.
Import ListNotations.
Open Scope Z_scope.

Definition RP_FRAME_CHANNELS : Z := 0x1337c.
Definition A_K36 : Z := 0x103a0.
Definition K36 : Z := 0xe38e38e38e38e38f.

(* The C function on the signed `long len`: REAC_UPSTREAM_OVERHEAD = 52, REAC_UPSTREAM_BYTES_PER_CH = 36,
   REAC_MAX_CHANNELS = 40 (libreac include/reac/reac.h:24,65,66); `(int)` of the size_t quotient is the two's
   complement wrap to 32 bits (bv_swrap 32). *)
Definition rp_frame_channels_model (len : Z) : Z :=
  if len <? 0 then -1
  else
    let clean := reac_frame_clean_len_model len in
    if (clean <? 52) || negb ((clean - 52) mod 36 =? 0) then -1
    else
      let nch := bv_swrap 32 ((clean - 52) / 36) in
      if (nch <? 2) || (40 <? nch) || Z.odd nch then -1 else nch.

Definition rp_frame_channels_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (rp_frame_channels_model (bv_signed a0)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_FRAME_CHANNELS) fc None m (seg_rom rsegs)).
