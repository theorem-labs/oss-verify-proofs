(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the assembly of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86718 .. 0x8693c) from its segment lemmas, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v (cl_A_okX: a function's statement from the CL_*_stmtX segment statements) and A/ACfj.v (a loop closed by well-founded induction over its segment lemmas). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import ConstsViewDef StrnlenDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require
LLVMFuzzerTestOneInput_s41 LLVMFuzzerTestOneInput_s42 LLVMFuzzerTestOneInput_s43 LLVMFuzzerTestOneInput_s44
LLVMFuzzerTestOneInput_s45 LLVMFuzzerTestOneInput_s46 LLVMFuzzerTestOneInput_s48.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the split loop, closed by well-founded induction on the bytes of the line left to scan: its first half (head
   to the strcspn return, or the first exit) and its second half (the end of the word, back to the head with
   fewer bytes left, or the other two exits) *)
Lemma aw_Sloop_glue : forall m,
  (forall nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> AW_S_stmt B MT m nm) ->
  (AW_E_stmt B MT m -> forall nm, (forall nm', (nm' < nm)%nat -> AW_S_stmt B MT m nm') -> AW_S2_stmt B MT m nm) ->
  AW_E_stmt B MT m -> forall nm, AW_S_stmt B MT m nm.
Proof.
intros m S1 S2 E nm. induction nm as [nm IH] using (well_founded_ind lt_wf).
exact (S1 nm (S2 E nm IH) E).
Qed.

(* the segment from its seven pieces: after send_message (LT_W_stmt) to the five checks (LT_K_stmt) *)
Lemma lt_seg_W_of : forall m,
  (AW_M_stmt B MT m -> AW_W_stmt B MT m) ->
  ((forall j, AW_T_stmt B MT m j) -> AW_J_stmt B MT m -> AW_M_stmt B MT m) ->
  (AW_J_stmt B MT m -> forall j, AW_T_stmt B MT m j) ->
  ((forall nm, AW_S_stmt B MT m nm) -> LT_K_stmt B MT m -> AW_J_stmt B MT m) ->
  (forall nm, AW_S2_stmt B MT m nm -> AW_E_stmt B MT m -> AW_S_stmt B MT m nm) ->
  (AW_E_stmt B MT m -> forall nm, (forall nm', (nm' < nm)%nat -> AW_S_stmt B MT m nm') -> AW_S2_stmt B MT m nm) ->
  (LT_K_stmt B MT m -> AW_E_stmt B MT m) ->
  LT_K_stmt B MT m -> LT_W_stmt B MT m.
Proof.
intros m SM ST STl SJ S1 S2 SE HK.
exact (LT_W_of_AW_W B MT m
  (SM (ST (STl (SJ (aw_Sloop_glue m S1 S2 (SE HK)) HK)) (SJ (aw_Sloop_glue m S1 S2 (SE HK)) HK)))).
Qed.

(* the runtime entries the segment reaches, as LLVMFuzzerTestOneInput_c.v:186-192 states them *)
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRNLEN : astrnlen_whole_realizesM SEGS B 0x10358 0x10378 (SIG CS___interceptor_trampoline_strnlen).
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
(* the per-binary facts, by cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.

(* segment 6 of the walk: after send_message (0x86718) to the five checks (0x8693c). The continuation is the
   LTA form (the statement at every FP state); this segment reaches it at the FP state it was entered with. *)
Theorem lt_seg_W : forall m, LTA_K B MT m -> LT_W_stmt B MT m.
Proof.
intros m HKA. pose proof (HKA fx) as HK.
exact (lt_seg_W_of m
  (LLVMFuzzerTestOneInput_s41.aw_seg_M B MT AMALLOC4 ASTRNLEN HB LAWS TL MTL IMG m)
  (LLVMFuzzerTestOneInput_s42.aw_seg_T B MT LAWS AMEMCPY m)
  (LLVMFuzzerTestOneInput_s43.aw_seg_Tloop B MT LAWS m)
  (LLVMFuzzerTestOneInput_s44.aw_seg_J B MT AMEMCPY LAWS m)
  (fun nm => LLVMFuzzerTestOneInput_s45.aw_seg_S1 B MT ASTRSPN ASTRCSPN HB LAWS IMG m nm)
  (LLVMFuzzerTestOneInput_s48.aw_seg_S2 B MT LAWS m)
  (LLVMFuzzerTestOneInput_s46.aw_seg_E B MT LAWS m)
  HK).
Qed.

End e.
End f.
End d.
