(* check_read, fuzz_wire.c:212-251 (projects/reac-repacer/fuzz_wire/source): fuzz_wire plain c8763dfc4e81 at 0x131d8
   (416 bytes). A 112-byte frame (v[12] at sp', be[6] of the inlined w_get at sp' + 50, ra / s0..s5 at sp' + 56); its
   callees memset (leaf, writes v[]) and rp_slot_read (64 bytes below its sp = sp') bring the footprint below sp to
   176 bytes. The contract: check_read returns normally (its abort() at 0x13374 is unreachable) from every state
   LLVMFuzzerTestOneInput calls it in (fuzz_wire.c:272 and :278): len <= W_RECV_MAX = 1600, the frame c readable for
   len bytes outside the 176 stack bytes, mem_inv (rp_slot_read's premise). The slot (a2) is any word. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_READ : Z := 0x131d8.
Definition CHECK_READ_FRAME : Z := 112.
Definition CHECK_READ_STACK : Z := 176.

Definition check_read_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + CHECK_READ_STACK <= bv_unsigned sp ->
    bv_unsigned a1 <= 1600 ->
    Z.of_nat (length bs) = bv_unsigned a1 -> bytes_at rsegs m (bv_unsigned a0) bs ->
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
