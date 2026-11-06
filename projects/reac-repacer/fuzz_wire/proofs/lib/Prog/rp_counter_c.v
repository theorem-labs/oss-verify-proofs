From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* Ported from libreac/fuzz_decode lib/Prog/reac_frame_counter_c.v (origin/ossv/recipes 25e3d17bdb5, blob a2a231d8f7b3):
   the text is unchanged except the name and the address. repace_wire.c:69-72. *)
Definition RP_COUNTER : Z := 0x13608.

Definition counter_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition counter_result (bs : list byte) : Z := counter_byte bs 14 + 256 * counter_byte bs 15.

Definition rp_counter_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (16 <= length bs)%nat ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (counter_result bs)) a1' a2 a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_COUNTER) fc None m (seg_rom rsegs)).

(* Satisfiability at check_counter's call (fuzz_wire.c:133-144): check_counter passes on only a frame of 18 bytes or
   more, as fuzz_dup copied it to the heap. The state: a0 = the frame's heap address 0x50010 (above every loaded
   segment, which end at or below 0x50000), the memory holds there a 340-byte REAC audio frame (8 channels, 52 + 8 * 36
   bytes; broadcast destination, EtherType 0x8819, counter 0x1234 at bytes 14-15, type 00 00).
   The contract leaves sp free; at this call it is rp_counter's entry sp 0x7fffffffe6b0 = check_counter's entry sp
   0x7fffffffe6c0 - check_counter's frame 0x10 (addi sp, sp, -0x10 at plain 0x13124 / U 0x13234).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x88; 0x19; 0x34; 0x12;
                   0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Lemma rp_counter_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let m := write_to_mem (fun _ => None) (wa 0x50010) sat_frame in
  length sat_frame = 340%nat /\
  (16 <= length sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) sat_frame.
Proof.
  cbv zeta.
  assert (L : length sat_frame = 340%nat) by (unfold sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  split; [exact L|]. split; [rewrite L; lia|].
  rewrite unsigned_lit by lia. apply bytes_at_write_same; rewrite ?L; lia.
Qed.
