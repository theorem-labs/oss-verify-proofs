(* rp_slot_write(f, n, slot, v) (reac-repacer src/repace_wire.c:126-140): nch = rp_slot_width(f, n, slot); if nch < 0
   return 0; else for each of the 12 samples s it writes v[s]'s low three bytes at the braid bytes of the slot
   (reac_braid_pos, <reac/reac_braid.h>: the pair's group at f + 50 + 3 * (s * nch + (slot & ~1)); even slot: lo, mid,
   hi at +3, +0, +1; odd slot: at +4, +5, +2; EgressFrame.braid_at / slot_write_upto) and returns 1. a0 = f, a1 = n, a2 = slot (int, sign-extended), a3 = v
   (12 int32, little-endian: vbs). It keeps a frame and calls rp_slot_width (32 more bytes below its sp): RP_SLOT_WRITE_STACK bytes in all.
   v is an int32 array: non-null and 4-aligned (UBSan checks both). *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c rp_slot_width_c.
Import ListNotations.
Open Scope Z_scope.

(* The stack it uses below its entry sp: its own frame plus rp_slot_width's 32 bytes. *)
Definition RP_SLOT_WRITE_STACK : Z := 112.

Definition RP_SLOT_WRITE : Z := 0x1346c.

Definition rp_slot_write_bytes (n : Z) (bs : list byte) (slot : Z) (vbs : list byte) : list byte :=
  let nch := rp_slot_width_model n bs slot in
  if nch <? 0 then bs else slot_write_upto nch slot vbs bs 12.

Definition rp_slot_write_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs vbs : list byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + RP_SLOT_WRITE_STACK <= bv_unsigned sp ->
    0 < bv_unsigned a0 ->
    bytes_at rsegs m (bv_unsigned a0) bs -> length bs = Z.to_nat (bv_unsigned a1) ->
    wr_at rsegs m (bv_unsigned a0) (bv_unsigned a1) ->
    bytes_at rsegs m (bv_unsigned a3) vbs -> length vbs = 48%nat -> 0 < bv_unsigned a3 -> bv_unsigned a3 mod 4 = 0 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - RP_SLOT_WRITE_STACK \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a3 + 48 <= bv_unsigned sp - RP_SLOT_WRITE_STACK \/ bv_unsigned sp <= bv_unsigned a3) ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned a3 \/ bv_unsigned a3 + 48 <= bv_unsigned a0) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (if rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) <? 0 then 0 else 1))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RP_SLOT_WRITE_STACK, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         bytes_at rsegs m' (bv_unsigned a0) (rp_slot_write_bytes (bv_unsigned a1) bs (bv_signed a2) vbs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_SLOT_WRITE) fc None m (seg_rom rsegs)).
