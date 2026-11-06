(* maybe_online_cgW: Theorem transport_maybe_online_cg_holds, the statement transport_maybe_online_cg_holds_stmt of
   lib/A/Prog/maybe_online_cg.v: the machine walk of maybe_online on fuzz_transport.asan at 0x8b170 (1056 bytes),
   composed from its three pieces against the cuts of lib/A/Prog/MonCut.v (mon_holds_of):
     head  lib/A/Prog/MonHead.v  mon_head  the entry .. +0x1d0, then the notice cut or the release cut;
     ntc   lib/A/Prog/MonNtc.v   mon_ntc   +0x1d4 .. +0x28c (the memset and the call of notice), then the release cut;
     rel   lib/A/Prog/MonRel.v   mon_rel   +0x290 .. the return (the side-stack frame released). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import maybe_online_cg MonCut MonHead MonNtc MonRel.

Theorem transport_maybe_online_cg_holds :
  forall fx rc B MT, @transport_maybe_online_cg_holds_stmt fx rc B MT.
Proof.
intros fx rc B MT.
exact (@mon_holds_of fx rc B MT (@mon_head fx rc B MT) (@mon_ntc fx rc B MT) (@mon_rel fx rc B MT)).
Qed.
