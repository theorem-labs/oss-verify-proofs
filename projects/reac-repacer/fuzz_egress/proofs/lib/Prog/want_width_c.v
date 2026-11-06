From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib Require Import EgressFrame.
Import ListNotations.
Open Scope Z_scope.

(* want_width(f, n, slot) (fuzz_egress.c:89-95, w_width and w_is_audio inlined): a0 = f, a1 = n, a2 = slot (an int,
   sign-extended). The frame's n bytes are bs. It writes no memory and returns want_width_model n bs slot. *)
Definition WANT_WIDTH : Z := 0x131e8.

Definition want_width_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (slot : Z),
    bytes_at rsegs m (bv_unsigned a0) bs ->
    length bs = Z.to_nat (bv_unsigned a1) ->
    a2 = Z_to_bv 64 slot -> -2^31 <= slot < 2^31 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' a6' : word),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (want_width_model (bv_unsigned a1) bs slot))
                       a1' a2' a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 WANT_WIDTH) fc None m (seg_rom rsegs)).
