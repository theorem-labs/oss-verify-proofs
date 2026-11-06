(* check_gate(f, n, slot) (fuzz_egress.c:97-107): aborts unless rp_slot_width(f, n, slot) == want_width(f, n, slot).
   a0 = f, a1 = n (<= W_RECV_MAX = 1600 at its one call site), a2 = slot (int, sign-extended). It keeps a 48-byte frame
   and calls rp_slot_width (32 bytes below its sp) and want_width (no stack). The contract says it returns: the two
   answers agree for every frame of at most 1600 bytes. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition CHECK_GATE : Z := 0x1304c.

Definition check_gate_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (slot lo : Z),
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 80 <= bv_unsigned sp ->
    0 < bv_unsigned a0 ->
    bytes_at rsegs m (bv_unsigned a0) bs -> length bs = Z.to_nat (bv_unsigned a1) -> bv_unsigned a1 <= 1600 ->
    (bv_unsigned a0 + bv_unsigned a1 <= bv_unsigned sp - 80 \/ bv_unsigned sp <= bv_unsigned a0) ->
    a2 = Z_to_bv 64 slot -> -2^31 <= slot < 2^31 ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_GATE) fc None m (seg_rom rsegs)).
