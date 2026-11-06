From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* int rp_meter_counter(const uint8_t *f, size_t n, uint16_t *ctr)   repace_wire.c:57-67:
     size_t eo = (n > 13 && f[12] == 0x81 && f[13] == 0x00) ? 16 : 12;
     if (n < eo + 6 || n < 1000) return 0;
     if (!(f[eo] == 0x88 && f[eo + 1] == 0x19)) return 0;
     *ctr = (uint16_t)(f[eo + 2] | (f[eo + 3] << 8));
     return 1;
   The form is libreac/fuzz_decode's reac_frame_is_reac_c.v: the frame bytes are read only past the function's own
   early exits (bytes 12-13 once n >= 14, bytes eo..eo+3 once n >= 1000), and *ctr must be writable only when the
   function stores to it. The store is stated exactly: the memory after the call is the 2-byte little-endian store of
   the counter at ctr (write_to_mem, the semantics' own store), or the memory unchanged when the function returns 0. *)
Definition RP_METER_COUNTER : Z := 0x13588.

Definition meter_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition meter_eo (n : Z) (bs : list byte) : nat :=
  if (13 <? n) && (meter_byte bs 12 =? 0x81) && (meter_byte bs 13 =? 0x00) then 16 else 12.

Definition meter_ok (n : Z) (bs : list byte) : bool :=
  let eo := meter_eo n bs in
  (Z.of_nat eo + 6 <=? n) && (1000 <=? n) && (meter_byte bs eo =? 0x88) && (meter_byte bs (eo + 1) =? 0x19).

Definition meter_value (n : Z) (bs : list byte) : Z :=
  let eo := meter_eo n bs in meter_byte bs (eo + 2) + 256 * meter_byte bs (eo + 3).

Definition rp_meter_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (14 <= bv_unsigned a1 -> (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    (1000 <= bv_unsigned a1 -> (20 <= length bs)%nat) ->
    (meter_ok (bv_unsigned a1) bs = true -> wr_at rsegs m (bv_unsigned a2) 2) ->
    evt rsegs
      (fun ms' => exists a1' a3' a4' a5' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if meter_ok (bv_unsigned a1) bs then 1 else 0))
                       a1' a2 a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None
                  (if meter_ok (bv_unsigned a1) bs
                   then write_to_mem m a2 (le2 (Z_to_bv 64 (meter_value (bv_unsigned a1) bs))) else m)
                  (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_METER_COUNTER) fc None m (seg_rom rsegs)).

(* Satisfiability at check_meter's call (fuzz_wire.c:100-131, rp_meter_counter(f, n, &ctr)): a0 = the frame fuzz_dup
   put at the heap address 0x50010 (above every loaded segment, which end at or below 0x50000), a1 = n = 1064, its length,
   a2 = &ctr = rp_meter_counter's entry sp 0x7fffffffe690 + 0xe = 0x7fffffffe69e, where 0x7fffffffe690 = check_meter's
   entry sp 0x7fffffffe6c0 - check_meter's frame 0x30 (addi sp, sp, -0x30 at plain 0x13048 / U 0x1311c; &ctr is
   addi a2, sp, 0xe at plain 0x130c4 / U 0x131b4); the slot holds UNTOUCHED_CTR 0xa5c3 (little-endian). The
   frame is a REAC audio frame of 28 channels behind one 802.1Q tag (52 + 28 * 36 + 4 bytes; 0x81 0x00 at bytes
   12-13, EtherType 0x8819 at 16-17, counter 0x1234 at 18-19), so every guard holds: eo = 16, the call reads bytes 12,
   13, 16-19, stores 0x1234 at ctr and returns 1.
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition meter_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x81; 0x00; 0x00; 0x05;
                   0x88; 0x19; 0x34; 0x12; 0x00; 0x00] ++ repeat (Z_to_bv 8 0) 1042.

Definition meter_sat_mem : word -> option byte :=
  write_to_mem (write_to_mem (fun _ => None) (wa 0x50010) meter_sat_frame) (wa 0x7fffffffe69e)
    (map (Z_to_bv 8) [0xc3; 0xa5]).

Lemma meter_wr_at_write : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  wr_at rsegs (write_to_mem m (wa a) bs) a (Z.of_nat (length bs)).
Proof.
  intros m a bs H0 H1. split; [lia|]. split; [lia|]. intros i Hi.
  unfold wview. rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
  destruct (Z.leb_spec0 a (a + i)); destruct (Z.ltb_spec0 (a + i) (a + Z.of_nat (length bs))); cbn [andb];
    try (exfalso; lia).
  destruct (nth_error bs (Z.to_nat (a + i - a))) eqn:E; [cbv beta iota; discriminate|].
  apply nth_error_None in E. lia.
Qed.

Lemma rp_meter_counter_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let a1 := Z_to_bv 64 1064 in
  let a2 := Z_to_bv 64 0x7fffffffe69e in
  Z.of_nat (length meter_sat_frame) = bv_unsigned a1 /\
  meter_ok (bv_unsigned a1) meter_sat_frame = true /\ meter_value (bv_unsigned a1) meter_sat_frame = 0x1234 /\
  (14 <= bv_unsigned a1 -> (14 <= length meter_sat_frame)%nat /\
                           bytes_at rsegs meter_sat_mem (bv_unsigned a0) meter_sat_frame) /\
  (1000 <= bv_unsigned a1 -> (20 <= length meter_sat_frame)%nat) /\
  (meter_ok (bv_unsigned a1) meter_sat_frame = true -> wr_at rsegs meter_sat_mem (bv_unsigned a2) 2).
Proof.
  cbv zeta.
  assert (L : length meter_sat_frame = 1064%nat)
    by (unfold meter_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  rewrite !unsigned_lit by lia.
  split; [rewrite L; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
  split; [|split].
  - intros _. split; [rewrite L; lia|]. unfold meter_sat_mem.
    apply bytes_at_write_other;
      [apply bytes_at_write_same; rewrite ?L; lia | lia | rewrite ?map_length; cbn [length]; lia | rewrite L; lia].
  - intros _. rewrite L. lia.
  - intros _. unfold meter_sat_mem. apply (meter_wr_at_write _ _ (map (Z_to_bv 8) [0xc3; 0xa5]));
      rewrite ?map_length; cbn [length]; lia.
Qed.
