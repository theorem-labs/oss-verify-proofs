From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

(* static int is_tagged_reac(const uint8_t *f)   repace_wire.c:23-26:
     return f[12] == 0x81 && f[13] == 0x00 && f[16] == 0x88 && f[17] == 0x19;
   A separate function in the UBSan build only (inlined in the plain one): rp_ds_accept jumps to it (0x137e0) and
   rp_copy_untag calls it (0x139cc). It takes no length: both callers have passed n >= 18 (n >= 50) first, so the
   premise is the 18 bytes it can read; f = 0 traps (0x137e8), so a0 <> 0 is a premise. Form of libreac/fuzz_decode's
   reac_frame_is_reac_c.v. *)
Definition IS_TAGGED_REAC : Z := 0x137e8.

Definition tag_byte (bs : list byte) (i : nat) : Z := bv_unsigned (nth i bs (Z_to_bv 8 0)).

Definition tagged_result (bs : list byte) : Z :=
  if (tag_byte bs 12 =? 0x81) && (tag_byte bs 13 =? 0x00) && (tag_byte bs 16 =? 0x88) && (tag_byte bs 17 =? 0x19)
  then 1 else 0.

Definition is_tagged_reac_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte),
    bv_unsigned a0 <> 0 ->
    (18 <= length bs)%nat ->
    bytes_at rsegs m (bv_unsigned a0) bs ->
    evt rsegs
      (fun ms' => exists a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tagged_result bs)) a1' a2' a3
                       a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 IS_TAGGED_REAC) fc None m (seg_rom rsegs)).

(* Satisfiability at rp_copy_untag's call (0x139cc, from check_copy, fuzz_wire.c:184-210, rp_copy_untag(c, n)) and at
   rp_ds_accept's jump (0x137e0, from check_downstream, fuzz_wire.c:86-98): a0 = the frame fuzz_dup put at the heap address 0x50010
   (above every loaded segment, which end at or below 0x50000); the frame is a 344-byte REAC audio frame of 8 channels
   behind one 802.1Q tag (0x81 0x00 at bytes 12-13, EtherType 0x8819 at 16-17), so the call reads all four bytes and
   returns 1.
   The contract leaves sp free; at rp_copy_untag's call it is is_tagged_reac's entry sp 0x7fffffffe670 = rp_copy_untag's
   entry sp 0x7fffffffe690 (check_copy's entry sp 0x7fffffffe6c0 - check_copy's frame 0x30, addi sp, sp, -0x30 at
   0x13550) - rp_copy_untag's frame 0x20 (0x139ac); at rp_ds_accept's jump (a `j`, no frame) it is rp_ds_accept's entry sp
   0x7fffffffe6b0 = check_downstream's entry sp 0x7fffffffe6c0 - its frame 0x10 (0x1305c).
   sp convention of the fuzz_wire sat lemmas: 0x7fffffffe700 is LLVMFuzzerTestOneInput's entry sp; its frame is 0x40
   (addi sp, sp, -0x40 at plain 0x12d78 / U 0x12dc0), so every check_* is entered at sp 0x7fffffffe6c0. *)
Definition tag_sat_frame : list byte :=
  map (Z_to_bv 8) [0xff; 0xff; 0xff; 0xff; 0xff; 0xff; 0x00; 0x1d; 0xc1; 0x00; 0x00; 0x01; 0x81; 0x00; 0x00; 0x05;
                   0x88; 0x19; 0x34; 0x12; 0x00; 0x00] ++ repeat (Z_to_bv 8 0) 322.

Lemma is_tagged_reac_premises_sat :
  let a0 := Z_to_bv 64 0x50010 in
  let m := write_to_mem (fun _ => None) (wa 0x50010) tag_sat_frame in
  length tag_sat_frame = 344%nat /\ tagged_result tag_sat_frame = 1 /\
  bv_unsigned a0 <> 0 /\ (18 <= length tag_sat_frame)%nat /\ bytes_at rsegs m (bv_unsigned a0) tag_sat_frame.
Proof.
  cbv zeta.
  assert (L : length tag_sat_frame = 344%nat)
    by (unfold tag_sat_frame; rewrite app_length, map_length, repeat_length; reflexivity).
  rewrite !unsigned_lit by lia.
  split; [exact L|]. split; [vm_compute; reflexivity|]. split; [lia|]. split; [rewrite L; lia|].
  apply bytes_at_write_same; rewrite ?L; lia.
Qed.
