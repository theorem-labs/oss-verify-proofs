(* rp_slot_read, reac-repacer src/repace_wire.c:111-124 (sha256 cfd1889a071e): fuzz_wire ubsan 6e91fe0b5555 at 0x13acc
   (0x194 bytes). Calls rp_slot_width (contract rp_slot_width_c.v) on (f, n, slot); when it returns nch >= 0, reads
   the 12 samples of the slot through reac_braid_pos (libreac include/reac/reac_braid.h:56-64, inlined in the loop at
   0x13b50..0x13c28, its pos[3] array at sp' = sp - 80) and writes v[0..11] (int32_t, little-endian). Saves ra and
   s0..s5 in an 80-byte frame; with rp_slot_width's 32 bytes the footprint below sp is 112 bytes. UBSan checks, each an
   inline `unimp` at 0x13c5c: f == NULL (0x13b00), f + 50 overflows (0x13b08), s * nch and s * nch + (slot & ~1)
   overflow int (0x13b58, 0x13b68), &pos[1] / &pos[2] overflow (0x13b84, 0x13b8c, 0x13ba4, 0x13bb0), a + pos[k]
   overflows (0x13bc0, 0x13bc4, 0x13bc8), &v[s] overflows or is NULL (0x13bcc, 0x13bd8), v misaligned or NULL
   (0x13bdc); the premises f <> 0, v <> 0, v mod 4 = 0 and the bounds of bytes_at / wr_at / stk rule them out. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import reac_frame_clean_len_c rp_frame_channels_c
  rp_slot_width_c.
Import ListNotations.
Open Scope Z_scope.

Definition RP_SLOT_READ : Z := 0x13acc.

(* reac_braid_pos's byte map, copied from libreac/fuzz_decode lib/Prog/reac_decode_c.v:14 (recipes 25e3d17bdb5,
   blob 1627341bfcc3, released): the offset of byte k (0 = lo, 1 = mid, 2 = hi) of time sample s of channel ch in
   an nch-wide braided audio block. *)
Definition braid_pos (s ch nch k : Z) : Z :=
  let g := 3 * (s * nch + (ch - ch mod 2)) in
  if ch mod 2 =? 0 then (if k =? 0 then g + 3 else if k =? 1 then g else g + 1)
  else (if k =? 0 then g + 4 else if k =? 1 then g + 5 else g + 2).

(* repace_wire.c:120-121: the 24-bit sample from the three braid bytes behind REAC_AUDIO_OFFSET = 50, sign-extended
   from bit 23. *)
Definition rp_sample (bs : list byte) (nch slot s : Z) : Z :=
  let b k := bv_unsigned (nth (Z.to_nat (50 + braid_pos s slot nch k)) bs (Z_to_bv 8 0)) in
  let x := b 0 + 256 * b 1 + 65536 * b 2 in
  if x <? 2^23 then x else x - 2^24.

(* v[0..11] as bytes: REAC_SAMPLES_PER_PKT = 12 int32_t, little-endian. *)
Definition rp_slot_bytes (bs : list byte) (nch slot : Z) : list byte :=
  flat_map (fun s => le4 (Z_to_bv 64 (rp_sample bs nch slot (Z.of_nat s)))) (seq 0 12).

Definition rp_slot_read_model (n : Z) (bs : list byte) (slot : Z) : Z :=
  if rp_slot_width_model n bs slot <? 0 then 0 else 1.

Definition rp_slot_read_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 112 <= bv_unsigned sp ->
    (50 <= bv_unsigned a1 ->
       bv_unsigned a0 <> 0 /\ bv_unsigned a1 <= Z.of_nat (length bs) /\ bytes_at rsegs m (bv_unsigned a0) bs /\
       (bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)) ->
    (0 <= rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2) ->
       bv_unsigned a3 <> 0 /\ bv_unsigned a3 mod 4 = 0 /\ wr_at rsegs m (bv_unsigned a3) 48 /\
       (bv_unsigned a3 + 48 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a3) /\
       (bv_unsigned a3 + 48 <= bv_unsigned a0 \/ bv_unsigned a0 + Z.of_nat (length bs) <= bv_unsigned a3)) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (rp_slot_read_model (bv_unsigned a1) bs (bv_signed a2)))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
         (if 0 <=? rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)
          then munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 48)] m m' /\
               bytes_at rsegs m' (bv_unsigned a3)
                 (rp_slot_bytes bs (rp_slot_width_model (bv_unsigned a1) bs (bv_signed a2)) (bv_signed a2))
          else munch [(bv_unsigned sp - 112, bv_unsigned sp)] m m'))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_SLOT_READ) fc None m (seg_rom rsegs)).
