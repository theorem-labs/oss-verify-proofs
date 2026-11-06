(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Satisfiability witnesses (a Theorem Labs lane 2026-10-29 21:4xZ) for the raw-frame conjunct of fuzz_state image B's six U leaves
   (FSupoisonAllocR.refill_leafU; FSupoisonAllocFK.drain_leafU / dr_leafU / cd_leafU / rcc_leafU / enq_leafU), at the
   REAL instance: B := YD2l.TfibBU (fs.asan-ubsan's own symbol table), TfibSyms by YD2l.TfibBU_syms, AR_laws by
   YG0q.AR_laws_ok over B's YB1v.tfibsegs. Each Definition below is a closed walk theorem that PRODUCES its leaf, raw
   conjunct included, applied at that instance; fx / rc stay universally quantified as in fs's tops (FSCloseB). The leaf
   Props take no meter, so no trivial meter can make them vacuous. Image-B twin of lib/A/FSRawLeafWitness.v.
   rule 24: no function proved. *)
(* Modified by Theorem Labs, 2026-10: new file; witnesses for the route-1 raw-frame leaf conjuncts at fs's real image B. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require
  FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocRt FSupoisonAllocFcd FSupoisonAllocFrs FSupoisonAllocFdr
  FSupoisonAllocFdn FSupoisonAllocFeq FSupoisonAllocF.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Let LAWS := YG0q.AR_laws_ok tfibsegs TfibBU.

(* refill_leafU (FSupoisonAllocRt.LEAF_B2U / refill_leaf_initU, FSupoisonAllocRf.LEAF_GU) *)
Definition w_refill := FSupoisonAllocRt.tfib_refill_okU TfibBU TfibBU_syms.
(* cd_leafU *)
Definition w_cdealloc := FSupoisonAllocFcd.tfib_cdealloc_okU TfibBU LAWS TfibBU_syms.
(* rcc_leafU, both arms *)
Definition w_rchunk_prim := FSupoisonAllocFcd.tfib_rchunk_primU TfibBU LAWS TfibBU_syms.
Definition w_rchunk_sec := FSupoisonAllocFrs.tfib_rchunk_secU TfibBU LAWS TfibBU_syms.
Definition w_rchunk := FSupoisonAllocF.tfib_rchunk_of_armsU TfibBU LAWS TfibBU_syms w_rchunk_sec.
(* dr_leafU *)
Definition w_dorecycle := FSupoisonAllocFdr.tfib_dorecycle_okU TfibBU LAWS TfibBU_syms w_rchunk w_cdealloc.
(* drain_leafU *)
Definition w_drain := FSupoisonAllocFdn.tfib_drain_okU TfibBU LAWS TfibBU_syms w_dorecycle.
(* enq_leafU, both arms *)
Definition w_enqueue_room := FSupoisonAllocFeq.tfib_enqueue_roomU TfibBU LAWS TfibBU_syms.
Definition w_enqueue_nb := FSupoisonAllocFeq.tfib_enqueue_nbU TfibBU LAWS TfibBU_syms w_refill.
End w.
