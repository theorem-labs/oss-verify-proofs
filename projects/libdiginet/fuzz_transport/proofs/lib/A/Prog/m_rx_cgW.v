(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths and module names changed; 987 of its 1030 lines of code are new or changed and 1037 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/m_rx_seg_head.v, with its module paths and module names changed; 58 of its 110 lines of code are new or changed and 978 lines of the source are left out. *)
(* m_rx_cgW: Theorem transport_m_rx_cg_holds : the statement transport_m_rx_cg_holds_stmt of lib/A/Prog/m_rx_cg.v,
   the machine walk of m_rx (fuzz/fuzz_transport.c:280-375) on fuzz_transport.asan at 0x8488c = transport_sigma
   TS_m_rx (1716 bytes, frame 144).

   The walk holds an inner G journal started at m_rx's entry (m_rx_seg_glue.v mrx_inner_init; window MRX_STK below
   the entry sp, no footprint, no frame of its own) and is split at the cuts of m_rx_seg_kit.v:
     m_rx_seg_head.v   the entry: the frame, the 13 saves, n < 30, the header's checked loads -> MAC | EPI;
     m_rx_seg_mac.v    the three MAC compares (bcmp) -> DESK | EPI;
     m_rx_seg_desk.v   the desk test (bcmp with M.desk, or the OUI bcmp, __asan_memcpy into M.desk) -> BODY | EPI;
     m_rx_seg_body.v   S_CLOSED, M.last_rx, the switch with ACK and e3 -> DATA | HOST | ANNT | MO | LOST | TICK | EPI;
     m_rx_seg_host.v   host_offset's ten bcmp -> ANNT;
     m_rx_seg_annt.v   the announce tail (desk_named, e0 / e1) -> E0L | E0W | MO | LOST | TICK; E0W -> WAKE | TICK;
     m_rx_seg_data.v   cmd DATA -> TICK;
     m_rx_seg_calls.v  m_lost (LOST, E0L), m_maybe_online (MO), m_wake (WAKE), m_tick (TICK), the epilogue (EPI).
   Each segment proves its cut's continuation from its successors'; mrx_chain composes them into the walk from the
   entry (the kit's mrx_K_entry), and m_rx_seg_glue.v mrx_close turns the inner post into transport_mrx_post. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_lost_cg m_wake_cg m_maybe_online_cg m_tick_cg desk_named_cg check_state_data_cg m_rx_cg m_rx_seg_kit m_rx_seg_glue.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
  m_rx_seg_head m_rx_seg_mac m_rx_seg_desk m_rx_seg_body m_rx_seg_host m_rx_seg_annt m_rx_seg_data m_rx_seg_calls.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HCELLS : transport_cells B.
Hypothesis HMRX : trans_mrx_cells B.
Hypothesis HRO : trans_ro_rd_unowned B.
Hypothesis HNE : trans_rom_no_errno B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HGX : gx_ok tfibsegs B TG.G_HARNESS.
Hypothesis HGNE : gx_noerrno B TG.G_HARNESS.
Hypothesis HBCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp).
Hypothesis HMCPY : forall fx' : YK11.FPState, @aintrin_realizes fx' rc tfibsegs B OCpy (transport_sigma TS___asan_memcpy).
Hypothesis HML : forall fx' : YK11.FPState, @transport_m_lost_cg fx' rc B MT (transport_sigma TS_m_lost).
Hypothesis HDN : forall fx' : YK11.FPState, @transport_desk_named_cg fx' rc B MT (transport_sigma TS_desk_named).
Hypothesis HMW : forall fx' : YK11.FPState, @transport_m_wake_cg fx' rc B MT (transport_sigma TS_m_wake).
Hypothesis HMO : forall fx' : YK11.FPState, @transport_m_maybe_online_cg fx' rc B MT (transport_sigma TS_m_maybe_online).
Hypothesis HMT : forall fx' : YK11.FPState, @transport_m_tick_cg fx' rc B MT (transport_sigma TS_m_tick).
Variable sp1 : Z.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.
Variable Sc : astate.
Variable W : world tfibsegs.
Variable memc : word -> option byte.
Variable mdc : Model.
Variable fr : TI.tframe.
Variable n : Z.
Variable Bw' : list byte.
Variable r : Z.
Hypothesis HST : mrx_static B sp1 regs0 lyc Sc W memc mdc fr n.

(* The segments' premises, in the Section's order (fx and rc from the goal). *)
Local Ltac seg L :=
  exact (L B MT HCELLS HMRX HRO HNE LAWS MTL HGX HGNE HBCMP HMCPY HML HDN HMW HMO HMT
           sp1 regs0 lyc Sc W memc mdc fr n Bw' r HST).

(* The walk from the entry: every cut's continuation, from the epilogue back to the head. *)
Lemma mrx_chain : forall Bw : list byte, @mrx_K_entry fx rc B MT sp1 regs0 lyc Sc W memc mdc fr n Bw Bw' r.
Proof using All.
intros Bw.
assert (KEPI : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_EPI) (R_EPI Bw' r))
  by seg mrx_seg_epi.
assert (KTICK : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_TICK) (R_TICK Bw' r))
  by (refine (_ KEPI); seg mrx_seg_tick).
assert (KMO : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_MO) (R_MO Bw' r))
  by (refine (_ KTICK); seg mrx_seg_mo).
assert (KWAKE : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_WAKE) (R_WAKE Bw' r))
  by (refine (_ KTICK); seg mrx_seg_wake).
assert (KLOST : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_LOST) (R_LOST Bw' r))
  by (refine (_ KTICK); seg mrx_seg_lost).
assert (KE0W : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_E0W) (R_E0W Bw' r))
  by (refine (_ KWAKE KTICK); seg mrx_seg_e0w).
assert (KE0L : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_E0L) (R_E0L Bw' r))
  by (refine (_ KE0W); seg mrx_seg_e0l).
assert (KANNT : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_ANNT) (R_ANNT fr n sp1 lyc Sc Bw' r))
  by (refine (_ KE0L KE0W KMO KLOST KTICK); seg mrx_seg_annt).
assert (KHOST : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_HOST) (R_HOST fr n sp1 lyc Sc Bw' r))
  by (refine (_ KANNT); seg mrx_seg_host).
assert (KDATA : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_DATA) (R_DATA fr n sp1 lyc Sc Bw' r))
  by (refine (_ KTICK); seg mrx_seg_data).
assert (KBODY : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_BODY) (R_BODY fr n sp1 lyc Sc Bw' r))
  by (refine (_ KEPI KTICK KMO KLOST KDATA KHOST KANNT); seg mrx_seg_body).
assert (KDESK : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_DESK) (R_DESK fr n sp1 lyc Sc Bw' r))
  by (refine (_ KEPI KBODY); seg mrx_seg_desk).
assert (KMAC : @mrx_K fx rc B MT sp1 regs0 lyc Sc W memc mdc Bw' r (MRX_PC OFF_MAC) (R_MAC fr n sp1 lyc Sc Bw' r))
  by (refine (_ KEPI KDESK); seg mrx_seg_mac).
refine (_ Bw KEPI KMAC). seg mrx_seg_head.
Qed.

End seg.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.

(* The walk. *)
Lemma mrx_holds : @transport_m_rx_cg_holds_stmt fx rc B MT.
Proof.
unfold transport_m_rx_cg_holds_stmt.
intros HCELLS HMRX HRO HNE LAWS MTL HGX HGNE HBCMP HMCPY HML HDN HMW HMO HMT.
apply (mrx_top_of_entry B MT LAWS HGX).
intros sp1 regs0 lyc Sc W memc mdc fr n Bw' r HST.
exact (@mrx_chain fx rc B MT HCELLS HMRX HRO HNE LAWS MTL HGX HGNE HBCMP HMCPY HML HDN HMW HMO HMT
  sp1 regs0 lyc Sc W memc mdc fr n Bw' r HST).
Qed.

End top.

(* The statement of lib/A/Prog/m_rx_cg.v. *)
Theorem transport_m_rx_cg_holds : forall fx rc B MT, @transport_m_rx_cg_holds_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@mrx_holds fx rc B MT). Qed.

Print Assumptions transport_m_rx_cg_holds.
