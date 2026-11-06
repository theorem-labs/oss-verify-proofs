(* diginet_session_submit_cgW: Theorem transport_diginet_session_submit_cg_holds : the statement
   transport_diginet_session_submit_cg_holds_stmt of lib/B/Prog/diginet_session_submit_cg.v, the machine walk of
   diginet_session_submit on fuzz_transport.asan-ubsan at 0x89aec. The nine branches to the trap word at 0x89d0c
   are decided by the runs (cp mod 4 = 0, s the constant g_s, queued <= 512 at the append, the search's index
   facts at its head).

   The walk is in four files:
   - lib/B/Prog/diginet_session_submit_segs.v: the context, the two cuts (APP, the append; LOOP, the search's head)
     and the facts every segment shares (what is kept of the caller, the command and the world; the post);
   - lib/B/Prog/diginet_session_submit_seg_app.v: from the cut APP to the return (queue full, or the store of
     queued + 1 and __asan_memcpy into the new entry);
   - lib/B/Prog/diginet_session_submit_seg_loop.v: from the cut LOOP, by YA0n.v SRr_loopZ, to the return (a match:
     __asan_memcpy into the entry and coalesced + 1) or to the cut APP (no match);
   - lib/B/Prog/diginet_session_submit_seg_entry.v: from the entry (the len test, the call of diginet_body_check
     lifted by TransportGCg.v gx_call_cg, refused + 1, the kind tests, the empty queue) to the return or a cut.
   Here they are put together at the statement's values. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_submit_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_submit_segs diginet_session_submit_seg_app diginet_session_submit_seg_loop
diginet_session_submit_seg_entry.
Import ListNotations.
Open Scope Z_scope.

Section ssw_holds. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.

Lemma ssw_holds : @transport_diginet_session_submit_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HSC LAWS MTL HGX HGE HBC HAI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cp r C Bw Bw'
    HJ Hra Hra4 Hgp Htp H10 H11 Hsp16 Hlo Hhi Htw Hm HL0 Hcp0 Hcp4 HSRC HC8 HOFF HNGR Hcnt Hev.
  set (c := mkSSW STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs cp r C Bw Bw').
  assert (HRT : ssw_rt B MT) by exact (conj HCELLS (conj HSC (conj LAWS (conj MTL (conj HGX (conj HGE (conj HBC HAI))))))).
  assert (HOK : ssw_ok B c)
    by exact (conj HJ (conj Hra (conj Hra4 (conj Hgp (conj Htp (conj H10 (conj H11 (conj Hsp16 (conj Hlo (conj Hhi
      (conj Htw (conj Hm (conj HL0 (conj Hcp0 (conj Hcp4 (conj HSRC (conj HC8 (conj HOFF (conj HNGR
      (conj Hcnt Hev)))))))))))))))))))).
  exact (ssw_seg_entry B MT (ssw_seg_app B MT) (ssw_seg_loop B MT (ssw_seg_app B MT)) c HRT HOK).
Qed.

End ssw_holds.

(* The statement of lib/B/Prog/diginet_session_submit_cg.v. *)
Theorem transport_diginet_session_submit_cg_holds :
  forall fx rc B MT, @transport_diginet_session_submit_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@ssw_holds fx rc B MT). Qed.

Print Assumptions transport_diginet_session_submit_cg_holds.
