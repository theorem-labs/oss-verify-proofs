(* diginet_session_wake_cgW (image B): the image-B ASan walk of diginet_session_wake (fuzz_transport.asan-ubsan
   41113a03c82f at 0x86a38 = transportb_sigma TB_diginet_session_wake, 1180 bytes), proved against the statement
   lib/B/Prog/diginet_session_wake_cg.v. The walk is cut into four pieces at the three pcs of
   lib/B/Prog/diginet_session_wake_seg_cut.v (+0x224, +0x2fc, +0x320); each piece is a file of its own:
     lib/B/Prog/diginet_session_wake_seg_head.v  wakeb_head : wakeb_head_stmt  (the entry .. +0x220)
     lib/B/Prog/diginet_session_wake_seg_mid.v   wakeb_mid  : wakeb_mid_stmt   (+0x224 .. +0x2f8)
     lib/B/Prog/diginet_session_wake_seg_rel.v   wakeb_e2 : wakeb_e2_stmt, wakeb_rel : wakeb_rel_stmt
                                                                             (+0x2fc .. +0x31c, +0x320 .. the return)
   with the model facts of lib/A/Prog/diginet_session_wake_seg_keep.v (image-free). This file is the composition:
   the cut file's wakeb_holds_of applied to the four. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
diginet_session_wake_seg_head diginet_session_wake_seg_mid diginet_session_wake_seg_rel.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.

(* The statement of lib/B/Prog/diginet_session_wake_cg.v. *)
Theorem transport_diginet_session_wake_cg_holds :
  forall fx rc B MT, @transport_diginet_session_wake_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@wakeb_holds_of fx rc B MT (@wakeb_head fx rc B MT) (@wakeb_mid fx rc B MT) (@wakeb_e2 fx rc B MT)
           (@wakeb_rel fx rc B MT)).
Qed.

Print Assumptions transport_diginet_session_wake_cg_holds.
