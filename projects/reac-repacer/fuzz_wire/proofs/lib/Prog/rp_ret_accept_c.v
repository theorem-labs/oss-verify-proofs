From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* int rp_ret_accept(const uint8_t *f, size_t n) { return n >= 14 && is_reac(f); }   repace_wire.c:45-48, with
   is_reac(f) = f[12] == 0x88 && f[13] == 0x19 (repace_wire.c:17-20). The form is libreac/fuzz_decode's
   reac_frame_is_reac_c.v: the frame bytes are read only past the function's own early exit (n < 14). *)
Definition RP_RET_ACCEPT : Z := 0x13504.

Definition ret_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition ret_accept_result (n : Z) (bs : list byte) : Z :=
  if n <? 14 then 0
  else if (ret_byte bs 12 =? 0x88) && (ret_byte bs 13 =? 0x19) then 1 else 0.

Definition rp_ret_accept_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (14 <= bv_unsigned a1 -> (14 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ret_accept_result (bv_unsigned a1) bs)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_RET_ACCEPT) fc None m (seg_rom rsegs)).

(* Satisfiability at check_ret's call (fuzz_wire.c:72-84, rp_ret_accept(f, n)): a0 = the frame fuzz_dup put at the heap
   address 0x50010 (above every loaded segment, which end at or below 0x50000), a1 = n = 340, its length; the frame is a
   REAC audio frame (8 channels, 52 + 8 * 36 bytes; broadcast destination, EtherType 0x8819 at bytes 12-13), so the
   guard n >= 14 holds and the call reads bytes 12-13 and returns 1.
   The contract leaves sp free; at this call it is rp_ret_accept's entry sp 0x7fffffffe6b0 = check_ret's entry sp
   0x7fffffffe6c0 - check_ret's frame 0x10 (addi sp, sp, -0x10 at plain 0x12f78 / U 0x12ff8).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition ret_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x88; 0x19; 0x34; 0x12;
                   0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Lemma rp_ret_accept_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let a1 := Z_to_bv 64 340 in
  let m := write_to_mem (fun _ => None) (wa 0x50010) ret_sat_frame in
  Z.of_nat (length ret_sat_frame) = bv_unsigned a1 /\ ret_accept_result (bv_unsigned a1) ret_sat_frame = 1 /\
  (14 <= bv_unsigned a1 -> (14 <= length ret_sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) ret_sat_frame).
Proof.
  cbv zeta.
  assert (L : length ret_sat_frame = 340%nat)
    by (unfold ret_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  rewrite !unsigned_lit by lia.
  split; [rewrite L; reflexivity|]. split; [vm_compute; reflexivity|].
  intros _. split; [rewrite L; lia|]. apply bytes_at_write_same; rewrite ?L; lia.
Qed.
