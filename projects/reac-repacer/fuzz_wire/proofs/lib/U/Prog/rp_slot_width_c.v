(* rp_slot_width, reac-repacer src/repace_wire.c:101-109 (sha256 cfd1889a071e): fuzz_wire ubsan 6e91fe0b5555 at 0x13a50
   (0x7c bytes). Reads f[16] / f[17] (is_audio, repace_wire.c:29-32) when n >= 50, then calls rp_frame_channels
   (contract rp_frame_channels_c.v) on (long)n. Saves ra / s0 in a 16-byte frame; with rp_frame_channels's frame the
   footprint below sp is 32 bytes. UBSan checks before the reads, each an inline `unimp` at 0x13ac8: f == NULL
   (0x13a70), f + 16 overflows (0x13a78), f + 17 overflows (0x13a88); the premise f <> 0 and bytes_at's bound rule them out. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c.
Import ListNotations.
Open Scope Z_scope.

Definition RP_SLOT_WIDTH : Z := 0x13a50.

Definition slot_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

(* The C function on the size_t n, the frame bytes bs and the int slot; `(long)n` is the two's complement wrap to
   64 bits (bv_swrap 64). *)
Definition rp_slot_width_model (n : Z) (bs : list byte) (slot : Z) : Z :=
  if (n <? 50) || negb (slot_byte bs 16 =? 0) || negb (slot_byte bs 17 =? 0) then -1
  else
    let nch := rp_frame_channels_model (bv_swrap 64 n) in
    if (nch <? 0) || (slot <? 0) || (nch <=? slot) then -1 else nch.

Definition rp_slot_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp ->
    (50 <= bv_unsigned a1 ->
       bv_unsigned a0 <> 0 /\ (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 16 \/ bv_unsigned sp <= bv_unsigned a0)) ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)))
                       a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_SLOT_WIDTH) fc None m (seg_rom rsegs)).
