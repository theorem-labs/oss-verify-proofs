(* The machine contract of m_rx (fuzz/fuzz_transport.c:280-375, m_lost inlined) in the ubsan image. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TWorldMem TImg TSess0 TCb.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract.
Import ListNotations.
Open Scope Z_scope.

Definition m_rx_ENTRY : Z := 0x15908.
(* addi sp,sp,-128 at 0x15908 (ra, s0-s3 saved, struct spec_frame f at sp + 8); callees: spec_read_frame (32),
   host_offset (80), desk_named (16), m_wake (16), m_set, m_maybe_online, m_tick (0), bcmp, memcpy (kit, 0),
   all U/Prog/T/<g>_c.v: 128 + 80. *)
Definition m_rx_FRAME : Z := 208.

Definition m_rx_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (B B' : list byte) (fr : tframe) (n r : Z),
    a0 = Z_to_bv 64 (tf_addr fr) ->
    a1 = Z_to_bv 64 n ->
    tframe_at m sp m_rx_FRAME (Some fr) ->
    tf_addr fr + n < 2 ^ 64 ->   (* spec_read_frame (b, n) at 0x15924: its b + 30 must not wrap (0x151c4-0x151cc) *)
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo + m_rx_FRAME <= bv_unsigned sp ->
    w_off_stack W_BASE_UBSAN sp m_rx_FRAME ->
    mem_inv rsegs m ->
    wmem rsegs m B ->
    m_rx_m timg_ubsan (Some fr) B n = Some (B', r) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - m_rx_FRAME, bv_unsigned sp); (W_BASE_UBSAN, W_BASE_UBSAN + W_LEN)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ wmem rsegs m' B')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 m_rx_ENTRY) fc None m (seg_rom rsegs)).
