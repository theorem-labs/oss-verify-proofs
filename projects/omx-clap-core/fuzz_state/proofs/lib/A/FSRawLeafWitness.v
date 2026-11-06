(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Satisfiability witnesses (a Theorem Labs lane 2026-10-29 21:4xZ) for the raw-frame conjunct of fuzz_state image A's six U leaves
   (FSupoisonAllocR.refill_leafU; FSupoisonAllocFK.drain_leafU / dr_leafU / cd_leafU / rcc_leafU / enq_leafU), at the
   REAL instance: B := AD2l.TfibB (fs.asan's own symbol table), TfibSyms by AD2l.TfibB_syms, AR_laws by YG0q.AR_laws_ok.
   Each Definition below is a closed walk theorem that PRODUCES its leaf, raw conjunct included, applied at that
   instance; fx / rc stay universally quantified as in fs's tops (FSClose). The leaf Props take no meter, so no
   trivial meter can make them vacuous. Each spec's leaf is reached for every pre-state its pre admits.
   rule 24: no function proved. *)
(* Modified by Theorem Labs, 2026-10: new file; witnesses for the route-1 raw-frame leaf conjuncts at fs's real image. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0m AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
  FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocRt FSupoisonAllocFcd FSupoisonAllocFrs FSupoisonAllocFdr
  FSupoisonAllocFdn FSupoisonAllocFeq FSupoisonAllocF.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS := YG0q.AR_laws_ok tfibsegs TfibB.

(* refill_leafU (FSupoisonAllocRt.LEAF_B2U / refill_leaf_initU, FSupoisonAllocRf.LEAF_GU) *)
Definition w_refill := FSupoisonAllocRt.tfib_refill_okU TfibB TfibB_syms.
(* cd_leafU *)
Definition w_cdealloc := FSupoisonAllocFcd.tfib_cdealloc_okU TfibB LAWS TfibB_syms.
(* rcc_leafU, both arms *)
Definition w_rchunk_prim := FSupoisonAllocFcd.tfib_rchunk_primU TfibB LAWS TfibB_syms.
Definition w_rchunk_sec := FSupoisonAllocFrs.tfib_rchunk_secU TfibB LAWS TfibB_syms.
Definition w_rchunk := FSupoisonAllocF.tfib_rchunk_of_armsU TfibB LAWS TfibB_syms w_rchunk_sec.
(* dr_leafU *)
Definition w_dorecycle := FSupoisonAllocFdr.tfib_dorecycle_okU TfibB LAWS TfibB_syms w_rchunk w_cdealloc.
(* drain_leafU *)
Definition w_drain := FSupoisonAllocFdn.tfib_drain_okU TfibB LAWS TfibB_syms w_dorecycle.
(* enq_leafU, both arms *)
Definition w_enqueue_room := FSupoisonAllocFeq.tfib_enqueue_roomU TfibB LAWS TfibB_syms.
Definition w_enqueue_nb := FSupoisonAllocFeq.tfib_enqueue_nbU TfibB LAWS TfibB_syms w_refill.
End w.
