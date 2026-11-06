(* session_lost_cgW: Theorem transport_session_lost_cg_holds : the statement transport_session_lost_cg_holds_stmt of
   lib/A/Prog/session_lost_cg.v, the machine walk of session_lost on fuzz_transport.asan at 0x88f08 (944 bytes), a
   G-form caller-journal walk with a class-2 side-stack frame of its own. It composes the three pieces at the cuts of
   lib/A/Prog/SlostCut.v (slost_holds_of): the head (entry .. 0x89080, the stack malloc through
   lib/A/Prog/TransportGFrame.v gx_stack_malloc_at; lib/A/Prog/SlostHead.v slost_head), the notice (0x89084 .. 0x89134,
   __asan_memset and the indirect call of notice; SlostNtc.v slost_ntc) and the release (0x89138 .. the return, the
   frame's flag byte through gx_flag_store_pi; SlostRel.v slost_rel). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import session_lost_cg SlostCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require SlostHead SlostNtc SlostRel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_session_lost_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_session_lost_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@slost_holds_of fx rc B MT (@SlostHead.slost_head fx rc B MT) (@SlostNtc.slost_ntc fx rc B MT)
           (@SlostRel.slost_rel fx rc B MT)).
Qed.
