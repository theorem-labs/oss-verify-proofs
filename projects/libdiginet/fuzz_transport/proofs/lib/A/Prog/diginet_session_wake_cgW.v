(* diginet_session_wake_cgW: the image-A ASan walk of diginet_session_wake (fuzz_transport.asan e89be137db17 at
   0x866fc = transport_sigma TS_diginet_session_wake, 1632 bytes), proved against the statement
   lib/A/Prog/diginet_session_wake_cg.v. The walk is cut into five pieces at the four pcs of
   lib/A/Prog/diginet_session_wake_seg_cut.v (+0x264, +0x350, +0x410, +0x434); each piece is a file of its own:
     lib/A/Prog/diginet_session_wake_seg_head.v  wake_head : wake_head_stmt  (the entry .. +0x260)
     lib/A/Prog/diginet_session_wake_seg_mid.v   wake_mid  : wake_mid_stmt   (+0x264 .. +0x34c)
     lib/A/Prog/diginet_session_wake_seg_ntc.v   wake_ntc_pc : wake_ntc_stmt (+0x350 .. +0x40c)
     lib/A/Prog/diginet_session_wake_seg_rel.v   wake_e2 : wake_e2_stmt, wake_rel : wake_rel_stmt
                                                                           (+0x410 .. +0x430, +0x434 .. the return)
   and the model facts they share are lib/A/Prog/diginet_session_wake_seg_keep.v. This file is the composition:
   the cut file's wake_holds_of applied to the five. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import diginet_session_wake_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
diginet_session_wake_seg_head diginet_session_wake_seg_mid diginet_session_wake_seg_ntc
diginet_session_wake_seg_rel.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.

(* The statement of lib/A/Prog/diginet_session_wake_cg.v. *)
Theorem transport_diginet_session_wake_cg_holds :
  forall fx rc B MT, @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@wake_holds_of fx rc B MT (@wake_head fx rc B MT) (@wake_mid fx rc B MT) (@wake_ntc_pc fx rc B MT)
           (@wake_e2 fx rc B MT) (@wake_rel fx rc B MT)).
Qed.

Print Assumptions transport_diginet_session_wake_cg_holds.
