From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* int rp_fwd_class(const uint8_t *f, size_t n, int bcast_only)   repace_wire.c:34-43:
     if (n < 18) return RP_FWD_DROP;
     if (!is_reac(f)) return RP_FWD_DROP;                  is_reac(f) = f[12] == 0x88 && f[13] == 0x19
     if (bcast_only && f[0] != 0xff) return RP_FWD_DROP;
     return is_audio(f) ? RP_FWD_AUDIO : RP_FWD_CTRL;      is_audio(f) = f[16] == 0x00 && f[17] == 0x00
   with RP_FWD_DROP = 0, RP_FWD_AUDIO = 1, RP_FWD_CTRL = 2 (include/repace_wire.h). bcast_only is tested on the whole
   register a2, as the code does (beqz a2). The form is libreac/fuzz_decode's reac_frame_is_reac_c.v: the frame
   bytes are read only past the function's own early exit (n < 18). UBSan build: past that exit the pointer must be
   non-null (the check at 0x136e0 traps on f = 0). *)
Definition RP_FWD_CLASS : Z := 0x136d8.

Definition fwd_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition fwd_class_result (n bcast : Z) (bs : list byte) : Z :=
  if n <? 18 then 0
  else if negb ((fwd_byte bs 12 =? 0x88) && (fwd_byte bs 13 =? 0x19)) then 0
  else if negb (bcast =? 0) && negb (fwd_byte bs 0 =? 0xff) then 0
  else if (fwd_byte bs 16 =? 0) && (fwd_byte bs 17 =? 0) then 1 else 2.

Definition rp_fwd_class_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    (18 <= bv_unsigned a1 -> bv_unsigned a0 <> 0 /\ (18 <= length bs)%nat /\ bytes_at rsegs m (bv_unsigned a0) bs) ->
    evt rsegs
      (fun ms' => exists a1' a2' a3' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                       (Z_to_bv 64 (fwd_class_result (bv_unsigned a1) (bv_unsigned a2) bs)) a1' a2' a3'
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RP_FWD_CLASS) fc None m (seg_rom rsegs)).

(* Satisfiability at check_forward's call (fuzz_wire.c:50-70, rp_fwd_class(f, n, bcast)): the input's first byte 0x01
   sets bcast = 1 (--bcast-only); a0 = the frame fuzz_dup put at the heap address 0x50010 (above every loaded segment,
   which end at or below 0x50000), a1 = n = 340, its length, a2 = bcast = 1. The frame is a REAC audio frame (8 channels,
   52 + 8 * 36 bytes; broadcast destination 0xff.., EtherType 0x8819, type 00 00), so the guard n >= 18 holds, the
   call takes its deepest path (bytes 12, 13, 0, 16, 17) and returns RP_FWD_AUDIO.
   The contract leaves sp free; at this call it is rp_fwd_class's entry sp 0x7fffffffe6a0 = check_forward's entry sp
   0x7fffffffe6c0 - check_forward's frame 0x20 (addi sp, sp, -0x20 at plain 0x12ee0 / U 0x12f3c).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition fwd_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x88; 0x19; 0x34; 0x12;
                   0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Lemma rp_fwd_class_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let a1 := Z_to_bv 64 340 in
  let a2 := Z_to_bv 64 1 in
  let m := write_to_mem (fun _ => None) (wa 0x50010) fwd_sat_frame in
  Z.of_nat (length fwd_sat_frame) = bv_unsigned a1 /\
  fwd_class_result (bv_unsigned a1) (bv_unsigned a2) fwd_sat_frame = 1 /\
  (18 <= bv_unsigned a1 -> bv_unsigned a0 <> 0 /\ (18 <= length fwd_sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) fwd_sat_frame).
Proof.
  cbv zeta.
  assert (L : length fwd_sat_frame = 340%nat)
    by (unfold fwd_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  rewrite !unsigned_lit by lia.
  split; [rewrite L; reflexivity|]. split; [vm_compute; reflexivity|].
  intros _. split; [lia|]. split; [rewrite L; lia|]. apply bytes_at_write_same; rewrite ?L; lia.
Qed.
