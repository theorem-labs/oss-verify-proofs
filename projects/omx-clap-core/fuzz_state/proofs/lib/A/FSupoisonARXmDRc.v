(* fuzz_state image A: DIfaceR at the any-user-poison instance ARX_ARU with no callee-spec premise: lib/A/FSReallocAG.v's
   H_difR_U closed (a Theorem Labs lane, 2026-10-29).

   rule 24: no function proved (kind: instance lift - lib/A/FSupoisonARXmDR.fs_difR_U fed a Theorem Labs lane's U walks).

   [fs_difR_U_closed] is the conclusion of FSupoisonARXmDR.fs_difR_U with its four U-raw callee specs discharged by
   a Theorem Labs lane's ARU twins of the released free sub-walks, composed as lib/A/FSupoisonAllocF.v:59-61 composes them for
   afree_realizes_ofU:
     tfib_enqueue_spec_nbRU true   FSupoisonAllocFeq.tfib_enqueue_nbU (refill: FSupoisonAllocRt.tfib_refill_okU)
     tfib_enqueue_spec_nbRU false  FSupoisonAllocFeq.tfib_enqueue_roomU
     tfib_drain_specRU             FSupoisonAllocFdn.tfib_drain_okU over FSupoisonAllocFdr.tfib_dorecycle_okU
     tfib_rchunk_specRU            FSupoisonAllocF.tfib_rchunk_of_armsU (FSupoisonAllocFcd.tfib_rchunk_primU,
                                   FSupoisonAllocFrs.tfib_rchunk_secU)
     tfib_cdealloc_specRU          FSupoisonAllocFcd.tfib_cdealloc_okU; its premise ly_tsd ly = TFIB_TSD from the AR of
                                   the pre (am_tsd) and TfibSyms (ts_tsd), as FSupoisonAllocF.v:46 does.
   Each walk's spec is the FSupoisonAllocFK spec; FSupoisonARXmDR's U-raw specs are those, by conversion, once the FK leaves
   carry the raw conjunct (a Theorem Labs lane, a working branch).  AR_laws is YG0q.AR_laws_ok at
   tfibsegs.  No as_dhash premise: no walk here reads the depot.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AF0l AF0m AF0x AFl0 AFl1 AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif DeallocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGif1dr CLenqcgifRaw.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoisonARXm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require
FSupoisonAllocRt FSupoisonAllocFcd FSupoisonAllocFrs FSupoisonAllocFdr FSupoisonAllocFdn FSupoisonAllocFeq FSupoisonAllocF.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoisonARXmDR.
Import ListNotations.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module DR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonARXmDR.
Module FRt := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocRt.
Module Fcd := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFcd.
Module Frs := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFrs.
Module Fdr := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFdr.
Module Fdn := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFdn.
Module Feq := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFeq.
Module FSF := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocF.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* Recycle, both chunk kinds (FSupoisonAllocF.v:43). *)
Lemma rchunk_RU : DR.tfib_rchunk_specRU B.
Proof. exact (FSF.tfib_rchunk_of_armsU B LAWS TB (Frs.tfib_rchunk_secU B LAWS TB)). Qed.

(* CacheDealloc, its ly_tsd premise from the pre's AR (FSupoisonAllocF.v:46). *)
Lemma cdealloc_RU : DR.tfib_cdealloc_specRU B.
Proof.
intros ly X c off U W regs mem md PRE. pose proof PRE as (((M & _) & _) & _).
exact (Fcd.tfib_cdealloc_okU B LAWS TB ly X c off U W regs mem md PRE
  ltac:(rewrite (am_tsd B ly X _ M); apply (ts_tsd _ TB))).
Qed.

(* Drain over DoRecycle over Recycle and CacheDealloc (FSupoisonAllocF.v:60-61). *)
Lemma drain_RU : DR.tfib_drain_specRU B.
Proof.
exact (Fdn.tfib_drain_okU B LAWS TB (Fdr.tfib_dorecycle_okU B LAWS TB rchunk_RU (Fcd.tfib_cdealloc_okU B LAWS TB))).
Qed.

(* Enqueue, both values of need_new_batch (FSupoisonAllocF.v:59). *)
Lemma enqueue_RU : forall nbq, DR.tfib_enqueue_spec_nbRU B nbq.
Proof.
intros [|]; [exact (Feq.tfib_enqueue_nbU B LAWS TB (FRt.tfib_refill_okU B TB)) | exact (Feq.tfib_enqueue_roomU B LAWS TB)].
Qed.
End a.

(* The deliverable: FSReallocAG.v's H_difR_U at DIfaceRcgif's parameters, for every Up, with no callee-spec premise. *)
Theorem fs_difR_U_closed : forall {fx : YK11.FPState} {rc : YM05.RunCeil} B, TfibSyms B -> forall L24, 16385 <= L24 ->
  forall Up,
  DIfaceR B (fun tr S => tr_admit (as_universe B) S tr) (ARX_ARU tfibsegs B TFIB_INST Up) (ARX_ARU tfibsegs B TFIB_INST Up)
    (aowned B) rpre_dealloc_cgif qtight (fpreU tfibsegs B Up) (CLenqcgifRaw.dpost_enq_cgif B) drain_body L24 qloose
    (DGif1dr.DRq_cgif B).
Proof.
intros fx rc B TB L24 HL24 Up.
exact (DR.fs_difR_U B TB L24 HL24 (enqueue_RU B TB) (drain_RU B TB) (rchunk_RU B TB) (cdealloc_RU B TB) Up).
Qed.

About fs_difR_U_closed.
Print Assumptions fs_difR_U_closed.
