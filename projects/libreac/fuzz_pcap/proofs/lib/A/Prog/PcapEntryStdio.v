(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file (a Theorem Labs lane). *)

(* fuzz_pcap's entry instance (PcapEntryInst.pcap_entry_inst, B := AD2l.PcapB, MT := YCbp.ameter_triv): the stdio
   premises of item (D) of a Theorem Labs lane's list, each a lemma whose type is the instance's
   hypothesis type with the instance's statement variables at these values, all by their defining names:

     FM_RA         := PStdioImgA.FM_MALLOC_RA      the return of musl fmemopen's malloc call (PStdioImgA.v:46)
     CTX           := ACej.CTX_pcap_source_open    the call spines of pcap_source_open's two calls (ACej.v:40), the
                                                   trace lane's own list; its four spines are the two landings PP_K2,
                                                   PP_K7 (PcapEntryDefs.v:200, :211), each with and without RA_LLVMF
                                                   (PcapEntryA.v:15)
     mc_lo, mc_hi  := AE39.MC_LO / AE39.MC_HI      the core's window of __strchrnul's word constants (AE39.v:27-28),
                                                   the names a Theorem Labs lane binds at the instance (a Theorem Labs lane, 12:16Z)

   Lemma (hypothesis of pcap_entry_inst)   proof                                                      fit
     pcap_entry_AFMEMOPEN (AFMEMOPEN)      PFmemopenC.pcap_afmemopen_closed at PcapB, with             conversion
                                           PcapBFacts.PcapB_LAWS, AD2l.PcapB_syms, the Section's ASIL
                                           and PcapBFacts.PcapB_AMALLOC4 (SK by name)
     pcap_entry_HCTX (HCTX)                computation (memZL over CTX)                                constr_eq
     pcap_entry_HCTX_A (HCTX_A)            computation (memZL over CTX)                                constr_eq
     pcap_entry_HFMU (HFMU)                computation over AD2l.PcapB_universe (= ACej.Tfib_universe)  constr_eq
     pcap_entry_TRAMP_MEMCPY (PFreadC's    AD1o.ocpy_of_icpt at PcapB, with AD2l.PcapB_syms and         conversion
       memcpy-trampoline premise)          PcapBFacts.PcapB_LAWS
     pcap_entry_AFREAD (AFREAD)            PFreadC.pcap_afread_closed at PcapB, with PcapB_LAWS,        conversion
                                           PcapB_syms, the Section's ASIL and pcap_entry_TRAMP_MEMCPY

   Each conversion is delta (with iota) of named Definitions only, and each site carries a `conversion:` comment; the
   build log shows each one as a CONCL_FIT or ARGS_FIT CONVERSION line:
   - AB1v.tfibsegs := Asan.M.loaded_segments (AB1v.v:13) and pa_segs PI_pcap := Asan.M.loaded_segments
     (PcapEntryTop.v:140-141), at ASIL (stated, as the instance states it, at Asan.M.loaded_segments) and at the
     segments of each conclusion;
   - AFMEMOPEN: PFmemopenI.FM_ENTRY (PFmemopenI.v:106) and pa_sigma PI_pcap PS___interceptor_trampoline_fmemopen
     (PcapAddr.v:16) are the same number; PFmemopenC states the window as two numerals, which AE39.MC_LO / MC_HI
     compute to (AE39.v:27-28 through AE3a.v:15-16; AE39.v:31 mc_bounds states the two equalities);
   - AFREAD: PFreadI.FR_ENTRY (PFreadI.v:164) and pa_sigma PI_pcap PS___interceptor_trampoline_fread (PcapAddr.v:34)
     are the same number;
   - TRAMP_MEMCPY: PFreadC's premise is about PStdioImgA.TRAMP_MEMCPY (PStdioImgA.v:50, the memcpy trampoline
     __interceptor_trampoline_memcpy = __wrap_memcpy, not __asan_memcpy); AD1o.ocpy_of_icpt (AD1o.v:82) is about
     pc_wrap_memcpy (as_code B), and pc_wrap_memcpy (as_code PcapB) = pc_wrap_memcpy AF0l.Tfib_code (AD2l.v:19,
     AF0l.v:14) is the same number. AE2q.asan_memcpy_realizes (the instance's HCPY) is about pc_asan_memcpy, another
     function, and is not used here.

   The sink head SK and the source-image laws ASIL (asource_img_laws SK Asan.M.loaded_segments PcapB pcap_KS) are
   Section parameters, so the lemmas hold at every SK: the instance passes SK := PcapSinkHeads.asan_sink_head and its
   inst_ASIL (PcapEntryInst.v:351, from AD1u.tfib_ASIL), whose type is ASIL's at that SK. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapEntryTop PcapEntryFinal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFreadISpec PFmemopenISpec PStdioImgA PFmemopenC
  PFreadC.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 YO09 YO05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop YG0p.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YCbp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase PcapRelro PcapRelroA PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceK.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require AB1v AF0l AD2l AD1o ACej AE39 PcapBFacts.
From OSSVerify.libreac.fuzz_pcap.images Require Asan.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceClose
  PcapSourceOpenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Open Scope Z_scope.

(* `fitc_s L` is PcapEntryInst's `fitc`: PcapEntryFinal's `fit` (arguments logged by args_fit), except that a
   conclusion that is the goal only up to conversion is accepted and logged as a `CONCL_FIT CONVERSION` line with
   both types. *)
Local Ltac fitc_s L :=
  PcapEntryFinal.args_fit L;
  lazymatch goal with |- ?G =>
    let T := type of L in
    tryif constr_eq T G then idtac
    else idtac "CONCL_FIT CONVERSION: the term" L "has the type" T "where the goal is" G;
    exact L
  end.

Section stdio.
Context {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Local Notation B := AD2l.PcapB.
Local Notation MT := YCbp.ameter_triv.
Local Notation SEGS := Asan.M.loaded_segments.
Local Notation PIp := (@PcapEntryTop.PI_pcap rc).
Local Notation SEGSp := (@pa_segs rc pcap_listing PIp).
Local Notation VALp a := (@pa_val rc pcap_listing PIp a).
(* The instance's statement variables, at the values above. *)
Local Notation FM_RA := PStdioImgA.FM_MALLOC_RA.
Local Notation CTX := ACej.CTX_pcap_source_open.
Local Notation mc_lo := AE39.MC_LO.
Local Notation mc_hi := AE39.MC_HI.

(* ASIL's type is the instance's inst_ASIL's (PcapEntryInst.v:351) at SK := asan_sink_head. *)
Hypothesis ASIL : asource_img_laws SK SEGS B pcap_KS.

(* ---- HCTX (tail_R1's spines, landing PP_K7) and HCTX_A (pe_A's, landing PP_K2): CTX holds both, with and without
   the return into target_run. ---- *)
Lemma pcap_entry_HCTX : In [VALp A_TEXT + PP_K7; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K7] CTX.
Proof. split; apply ACej.memZL_In; vm_compute; reflexivity. Qed.

Lemma pcap_entry_HCTX_A : In [VALp A_TEXT + PP_K2; RA_LLVMF] CTX /\ In [VALp A_TEXT + PP_K2] CTX.
Proof. split; apply ACej.memZL_In; vm_compute; reflexivity. Qed.

(* ---- HFMU: fmemopen's malloc traces under each spine of CTX are in PcapB's trace universe. ---- *)
Lemma pcap_entry_HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).
Proof.
  rewrite AD2l.PcapB_universe. split.
  - apply ACej.memZL_In. vm_compute. reflexivity.
  - intros c Hc. apply ACej.memZL_In.
    refine (ACej.allb_In (fun c => ACej.memZL (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
      flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) ACej.Tfib_universe)
      CTX c _ Hc).
    vm_compute. reflexivity.
Qed.

Set Printing All.
(* ---- AFMEMOPEN ---- *)
Lemma pcap_entry_AFMEMOPEN : forall fx : YK11.FPState,
  @PFmemopenISpec.afmemopen_spec fx rc SK SEGSp B pcap_KS MT CTX
    (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fmemopen) FM_RA mc_lo mc_hi.
Proof.
  intros fx.
  (* conversion: ASIL at Asan.M.loaded_segments = AB1v.tfibsegs (AB1v.v:13); the conclusion's segments tfibsegs =
     pa_segs PI_pcap (AB1v.v:13, PcapEntryTop.v:140-141), its entry PFmemopenI.FM_ENTRY = pa_sigma PI_pcap
     PS___interceptor_trampoline_fmemopen (PFmemopenI.v:106, PcapAddr.v:16), its window's two numerals = AE39.MC_LO /
     AE39.MC_HI (AE39.v:27-28, AE3a.v:15-16) *)
  fitc_s (@PFmemopenC.pcap_afmemopen_closed fx rc B SK MT CTX (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms ASIL
    (@PcapBFacts.PcapB_AMALLOC4 fx rc SK)).
Qed.

(* ---- AFREAD ---- *)
(* premise of pcap_afread_closed (the fread interceptor calls the memcpy trampoline 0x51510); the instance's HCPY is
   AE2q.asan_memcpy_realizes at __asan_memcpy 0x51514, wired by a Theorem Labs lane. Proved here from AD1o.ocpy_of_icpt at PcapB. *)
Lemma pcap_entry_TRAMP_MEMCPY : forall fx : YK11.FPState,
  @aintrin_realizes fx rc AB1v.tfibsegs B OCpy PStdioImgA.TRAMP_MEMCPY.
Proof.
  intros fx.
  (* conversion: pc_wrap_memcpy (as_code PcapB) = PStdioImgA.TRAMP_MEMCPY (AD2l.v:19, AF0l.v:14, PStdioImgA.v:50) *)
  fitc_s (@AD1o.ocpy_of_icpt fx rc B AD2l.PcapB_syms (@PcapBFacts.PcapB_LAWS rc)).
Qed.

Lemma pcap_entry_AFREAD : forall fx : YK11.FPState,
  @PFreadISpec.afread_spec fx rc SK SEGSp B pcap_KS (@pa_sigma rc pcap_listing PIp PS___interceptor_trampoline_fread).
Proof.
  intros fx.
  (* conversion: ASIL at Asan.M.loaded_segments = AB1v.tfibsegs (AB1v.v:13); the conclusion's segments tfibsegs =
     pa_segs PI_pcap (AB1v.v:13, PcapEntryTop.v:140-141) and its entry PFreadI.FR_ENTRY = pa_sigma PI_pcap
     PS___interceptor_trampoline_fread (PFreadI.v:164, PcapAddr.v:34) *)
  fitc_s (@PFreadC.pcap_afread_closed fx rc SK B (@PcapBFacts.PcapB_LAWS rc) AD2l.PcapB_syms ASIL
    (pcap_entry_TRAMP_MEMCPY fx)).
Qed.
Unset Printing All.

End stdio.
