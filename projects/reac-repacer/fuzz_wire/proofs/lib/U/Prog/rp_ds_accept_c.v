From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* int rp_ds_accept(const uint8_t *f, size_t n)   repace_wire.c:50-55:
     if (n < 18) return 0;
     return is_reac(f) || is_tagged_reac(f);
   is_reac(f) = f[12] == 0x88 && f[13] == 0x19 (repace_wire.c:17-20),
   is_tagged_reac(f) = f[12] == 0x81 && f[13] == 0x00 && f[16] == 0x88 && f[17] == 0x19 (repace_wire.c:23-26).
   The form is libreac/fuzz_decode's reac_frame_is_reac_c.v: the frame bytes are read only past the function's own
   early exit (n < 18). UBSan build: past that exit the pointer must be non-null (the check at 0x137ac traps on
   f = 0); is_tagged_reac is a separate function there (0x137e8), which rp_ds_accept jumps to (0x137e0). *)
Definition RP_DS_ACCEPT : Z := 0x1379c.

Definition ds_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition ds_accept_result (n : Z) (bs : list byte) : Z :=
  if n <? 18 then 0
  else if ((ds_byte bs 12 =? 0x88) && (ds_byte bs 13 =? 0x19))
          || ((ds_byte bs 12 =? 0x81) && (ds_byte bs 13 =? 0x00) && (ds_byte bs 16 =? 0x88) && (ds_byte bs 17 =? 0x19))
       then 1 else 0.

Definition rp_ds_accept_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (18 <= bv_unsigned a1 -> bv_unsigned a0 <> 0 /\ (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ds_accept_result (bv_unsigned a1) bs)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_DS_ACCEPT) fc None m (seg_rom rsegs)).

(* Satisfiability at check_downstream's call (fuzz_wire.c:86-98, rp_ds_accept(f, n)): a0 = the frame fuzz_dup put at
   the heap address 0x50010 (above every loaded segment, which end at or below 0x50000), a1 = n = 344, its length. The frame
   is a REAC audio frame of 8 channels behind one 802.1Q tag (52 + 8 * 36 + 4 bytes: 0x81 0x00 at bytes 12-13, VLAN 5,
   EtherType 0x8819 at bytes 16-17), so the guard n >= 18 holds, the call takes the tagged path (bytes 12, 13, 16, 17)
   and returns 1.
   The contract leaves sp free; at this call it is rp_ds_accept's entry sp 0x7fffffffe6b0 = check_downstream's entry sp
   0x7fffffffe6c0 - check_downstream's frame 0x10 (addi sp, sp, -0x10 at plain 0x12fc8 / U 0x1305c).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition ds_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x81; 0x00; 0x00; 0x05;
                   0x88; 0x19; 0x34; 0x12; 0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Lemma rp_ds_accept_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let a1 := Z_to_bv 64 344 in
  let m := write_to_mem (fun _ => None) (wa 0x50010) ds_sat_frame in
  Z.of_nat (length ds_sat_frame) = bv_unsigned a1 /\ ds_accept_result (bv_unsigned a1) ds_sat_frame = 1 /\
  (18 <= bv_unsigned a1 -> bv_unsigned a0 <> 0 /\ (18 <= length ds_sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) ds_sat_frame).
Proof.
  cbv zeta.
  assert (L : length ds_sat_frame = 344%nat)
    by (unfold ds_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  rewrite !unsigned_lit by lia.
  split; [rewrite L; reflexivity|]. split; [vm_compute; reflexivity|].
  intros _. split; [lia|]. split; [rewrite L; lia|]. apply bytes_at_write_same; rewrite ?L; lia.
Qed.
