(* on_announce_cgW: Theorem transport_on_announce_cg_holds : the statement transport_on_announce_cg_holds_stmt of
   lib/B/Prog/on_announce_cg.v, the machine walk of on_announce (transport/src/diginet_session.c:184-221) on
   fuzz_transport.asan-ubsan at 0x87cc8 = transportb_sigma TB_on_announce (2244 bytes, a class-3 side-stack frame of
   its own), in the G form over G_HARNESS_B (XO = 0, OUT = []).
   The walk is cut at fourteen points (lib/B/Prog/OnannCutB.v) and composed by OnannCutB.v onann_holds_of from its
   pieces: on_announce_seg_head.v (the entry to the parse cut), on_announce_seg_lp.v (diginet_announce_parse),
   on_announce_seg_ign.v (an ignored announce), on_announce_seg_pf.v (personality_from_name and the cmd test),
   on_announce_seg_fm.v (find_mac's bcmp loop), on_announce_seg_dn.v (the desk notice), on_announce_seg_e0.v and
   on_announce_seg_sl1.v and on_announce_seg_wk.v (cmd 0xe0: g_s.foreign, the first inlined session_lost with its call
   of set_state, diginet_session_wake), on_announce_seg_e1.v, on_announce_seg_fn.v and on_announce_seg_sl2.v (cmd
   0xe1: maybe_online, or the foreign notice and the second inlined session_lost), on_announce_seg_tail.v (the three
   release cuts: the shadow bytes, __asan_set_shadow_f5, the flag store, the epilogue and `ret`). The kit the pieces
   share is on_announce_seg_kit.v and OnannKitB.v. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  on_announce_seg_head on_announce_seg_lp on_announce_seg_ign on_announce_seg_pf on_announce_seg_fm
  on_announce_seg_dn on_announce_seg_e0 on_announce_seg_sl1 on_announce_seg_wk on_announce_seg_e1
  on_announce_seg_fn on_announce_seg_sl2 on_announce_seg_tail.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module SH := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_head.
Module SLP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_lp.
Module SIG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_ign.
Module SPF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_pf.
Module SFM := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_fm.
Module SDN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_dn.
Module SE0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_e0.
Module SL1 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_sl1.
Module SWK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_wk.
Module SE1 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_e1.
Module SFN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_fn.
Module SL2 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_sl2.
Module STL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.on_announce_seg_tail.

Theorem transport_on_announce_cg_holds : forall fx rc B MT, @transport_on_announce_cg_holds_stmt fx rc B MT.
Proof.
intros fx rc B MT.
exact (@onann_holds_of fx rc B MT
  (@SH.onann_head_piece fx rc B MT) (@SLP.onann_lp_piece fx rc B MT) (@SIG.onann_ign_piece fx rc B MT)
  (@SPF.onann_pf_piece fx rc B MT) (@SFM.onann_fm_piece fx rc B MT) (@SDN.onann_dn_piece fx rc B MT)
  (@SE0.onann_e0_piece fx rc B MT) (@SL1.onann_sl1_piece fx rc B MT) (@SWK.onann_wk_piece fx rc B MT)
  (@SE1.onann_e1_piece fx rc B MT) (@SFN.onann_fn_piece fx rc B MT) (@SL2.onann_sl2_piece fx rc B MT)
  (@STL.onann_tail_piece fx rc B MT)).
Qed.

Print Assumptions transport_on_announce_cg_holds.
