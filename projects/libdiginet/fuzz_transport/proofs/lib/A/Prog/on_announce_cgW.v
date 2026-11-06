(* on_announce_cgW: Theorem transport_on_announce_cg_holds : the statement transport_on_announce_cg_holds_stmt of
   lib/A/Prog/on_announce_cg.v, the machine walk of on_announce on fuzz_transport.asan at 0x87a74 (2488 bytes), a
   G-form caller-journal walk with a class-4 side-stack frame of its own. It composes the pieces at the cuts of
   lib/A/Prog/OnannCut.v (onann_holds_of): the head (entry .. +0x208: the stack malloc, the header, the 72 shadow
   bytes; on_announce_seg_head.v), the parse (+0x20c .. +0x218: diginet_announce_parse; on_announce_seg_lp.v), the
   ignore arm (+0x21c; on_announce_seg_ign.v), the personality (+0x248; on_announce_seg_pf.v), find_mac's loop
   (+0x2a8; on_announce_seg_fm.v), the desk notice (+0x308; on_announce_seg_dn.v), the e0 arm (+0x3f4;
   on_announce_seg_e0.v), the first inlined session_lost (+0x424; on_announce_seg_sl1.v), the wake test and
   diginet_session_wake (+0x518; on_announce_seg_wk.v), the e1 arm and maybe_online (+0x548; on_announce_seg_e1.v),
   the foreign notice (+0x58c; on_announce_seg_fn.v), the second inlined session_lost (+0x65c;
   on_announce_seg_sl2.v) and the release (+0x73c .. the return: __asan_set_shadow_f5 and the frame's flag byte;
   on_announce_seg_tail.v). The shared lemmas are on_announce_seg_kit.v's. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require
  on_announce_seg_head on_announce_seg_lp on_announce_seg_ign on_announce_seg_pf on_announce_seg_fm
  on_announce_seg_dn on_announce_seg_e0 on_announce_seg_sl1 on_announce_seg_wk on_announce_seg_e1
  on_announce_seg_fn on_announce_seg_sl2 on_announce_seg_tail.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem transport_on_announce_cg_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT,
  @transport_on_announce_cg_holds_stmt fx rc B MT.
Proof.
  intros fx rc B MT.
  exact (@onann_holds_of fx rc B MT
           (@on_announce_seg_head.onann_piece_head fx rc B MT) (@on_announce_seg_lp.onann_piece_lp fx rc B MT)
           (@on_announce_seg_ign.onann_piece_ign fx rc B MT) (@on_announce_seg_pf.onann_piece_pf fx rc B MT)
           (@on_announce_seg_fm.onann_piece_fm fx rc B MT) (@on_announce_seg_dn.onann_piece_dn fx rc B MT)
           (@on_announce_seg_e0.onann_piece_e0 fx rc B MT) (@on_announce_seg_sl1.onann_piece_sl1 fx rc B MT)
           (@on_announce_seg_wk.onann_piece_wk fx rc B MT) (@on_announce_seg_e1.onann_piece_e1 fx rc B MT)
           (@on_announce_seg_fn.onann_piece_fn fx rc B MT) (@on_announce_seg_sl2.onann_piece_sl2 fx rc B MT)
           (@on_announce_seg_tail.onann_piece_tail fx rc B MT)).
Qed.

Print Assumptions transport_on_announce_cg_holds.
