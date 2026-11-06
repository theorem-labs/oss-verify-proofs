(* check_read, fuzz_wire.c:212-251 (projects/reac-repacer/fuzz_wire/source): fuzz_wire ubsan 6e91fe0b5555 at 0x13300
   (592 bytes). A 160-byte frame (v[12] at sp', filled inline with 0x5a5a5a5a, be[6] of the inlined w_get at sp' + 50,
   ra / s0..s11 at sp' + 56); rp_slot_read (112 bytes below its sp = sp') brings the footprint below sp to 272 bytes.
   The contract: check_read returns normally (its abort() at 0x13548 and the UBSan traps at 0x13544 / 0x1354c are
   unreachable) from every state LLVMFuzzerTestOneInput calls it in (fuzz_wire.c:272 and :278): len <= W_RECV_MAX =
   1600, the frame c readable for len bytes outside the 272 stack bytes, mem_inv (rp_slot_read's premise), c <> 0 and
   sp mod 16 = 0 (rp_slot_read's f <> 0, v <> 0, v mod 4 = 0, v = sp - 160). The slot (a2) is any word. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_READ : Z := 0x13300.
Definition CHECK_READ_FRAME : Z := 160.
Definition CHECK_READ_STACK : Z := 272.

Definition check_read_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_READ_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
    bv_unsigned a1 <= 1600 ->
    bv_unsigned a0 <> 0 -> Z.of_nat (length bs) = bv_unsigned a1 -> bytes_at rsegs m (bv_unsigned a0) bs ->
    bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - CHECK_READ_STACK \/ bv_unsigned sp <= bv_unsigned a0 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_READ_STACK, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_READ) fc None m (seg_rom rsegs)).
