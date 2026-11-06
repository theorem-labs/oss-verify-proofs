(* set_state_cgW (image B): Theorem transport_set_state_cg_holds : the statement transport_set_state_cg_holds_stmt of
   lib/B/Prog/set_state_cg.v, the machine walk of set_state on fuzz_transport.asan-ubsan at 0x872cc (892 bytes), a
   G-form caller-journal walk with a class-2 side-stack frame of its own. It composes the three pieces at the cuts of
   lib/B/Prog/set_state_segs.v (sstb_holds_of): the head (entry .. 0x8741c, the stack malloc through
   lib/A/Prog/TransportGFrame.v gx_stack_malloc_at and the test of the state; set_state_seg_head.v sstb_head), the
   notice (0x87420 .. 0x874dc, __asan_memset, the store of the state and the indirect call of notice;
   set_state_seg_ntc.v sstb_ntc) and the release (0x874e0 .. the return, the frame's flag byte through
   lib/B/Prog/TransportGFrameB.v gx_flag_store_pi; set_state_seg_rel.v sstb_rel). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg set_state_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require set_state_seg_head set_state_seg_ntc
  set_state_seg_rel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_set_state_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_set_state_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@sstb_holds_of fx rc B MT (@set_state_seg_head.sstb_head fx rc B MT) (@set_state_seg_ntc.sstb_ntc fx rc B MT)
           (@set_state_seg_rel.sstb_rel fx rc B MT)).
Qed.

Print Assumptions transport_set_state_cg_holds.
